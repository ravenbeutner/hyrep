(*    
    Copyright (C) 2024

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <https://www.gnu.org/licenses/>.
*)

module Repair

open System

open FsOmegaLib.SAT
open FsOmegaLib.NSA
open FsOmegaLib.Operations

open Util
open Configuration
open Statement
open SMT
open SMTUtil
open HyperLTL
open SymbolicExecution
open SyGuS
open Verify

let instrumentProgram (program : Program<'L, Annotation>) (repairLocations : list<string * (FunctionName * 'L)>) = 

    let repairLocationsMap = Map.ofList repairLocations

    let statementMap = 
        repairLocationsMap
        |> Map.map (fun _ (functionName, l) -> 
            program.Functions.[functionName].LocationMap.[l] |> fst
            )
        
    let annotationMap = 
        repairLocationsMap
        |> Map.map (fun _ (functionName, l) -> 
            program.Functions.[functionName].LocationMap.[l] |> snd
            )
    
    let varMap = 
        annotationMap 
        |> Map.map (fun _ x -> x.AssignedVariables |> Set.toList)

    let holeIdMap = 
        repairLocations
        |> List.mapi (fun i (label, _) -> label, "hole" + string(i))
        |> Map.ofList

    let statementWithHoleMap = 
        repairLocationsMap
        |> Map.keys
        |> Seq.map (fun label  -> 
            let s = 
                match statementMap.[label] with 
                | VarAssign (x, _) -> VarAssign (x, Expression.Hole(holeIdMap.[label], varMap.[label] |> List.map Expression.Var))
                | If(_, s1, s2) -> If (Expression.Hole(holeIdMap.[label], varMap.[label] |> List.map Expression.Var), s1, s2)
                | While(_, s) -> While (Expression.Hole(holeIdMap.[label], varMap.[label] |> List.map Expression.Var), s)
                | x -> raise <| GeneralError $"Cannot repair statement {x}"
            
            label, s
            )
        |> Map.ofSeq

    let modifiedProgram = 
        (program, Map.keys repairLocationsMap) 
        ||> Seq.fold (fun prog label -> 
            let functionName, l = repairLocationsMap.[label]

            let updatedFunctionBody = 
                {prog.Functions.[functionName] with 
                    LocationMap = 
                        prog.Functions.[functionName].LocationMap
                        |> Map.add l (statementWithHoleMap.[label], annotationMap.[label])
                        }

            {
                prog with 
                    Functions = 
                        prog.Functions
                        |> Map.add functionName updatedFunctionBody
            }
        )

    let returnTypeMap = 
        statementMap
        |> Map.map (fun label s -> 
            match s with 
            | VarAssign (x, _) -> 
                let functionName, _ = repairLocationsMap.[label]
                program.Functions.[functionName].TypeMapping.[x] |> VarType.asSMTSort
            | If _ -> SmtSort.BOOL
            | While _ -> SmtSort.BOOL
            | x -> raise <| GeneralError $"Cannot repair statement {x}"
        )

    let argTypeMap = 
        varMap
        |> Map.map (fun label x -> 
            let functionName, _ = repairLocationsMap.[label]

            x |> List.map (fun x -> x, program.Functions.[functionName].TypeMapping.[x] |> VarType.asSMTSort)
            )

    let functionSketchMapping = 
        repairLocationsMap
        |> Map.keys
        |> Seq.map (fun label -> 
            let functionSketch = 
                match returnTypeMap.[label] with 
                | SmtSort.INT -> 
                    Grammar.integerSketch (List.map snd argTypeMap.[label])
                | SmtSort.BOOL -> 
                    Grammar.booleanSketch (List.map snd argTypeMap.[label])
                | SmtSort.STRING -> 
                    Grammar.stringSketch (List.map snd argTypeMap.[label])

            holeIdMap.[label], functionSketch
        )
        |> Map.ofSeq

    
    varMap, holeIdMap, modifiedProgram, returnTypeMap, argTypeMap, functionSketchMapping


let deInstrument (varMap : Map<string, list<Var>>) (holeIdMap : Map<string, string>) (functionDefinitions : list<SmtFunctionDefinition<string>>) = 
    functionDefinitions
    |> List.map (fun f -> 

        let label = 
            Map.keys holeIdMap
            |> Seq.find (fun label -> holeIdMap.[label] = f.Symbol)

        let arg = 
            f.Arguments
            |> List.map fst

        let renamingMap = 
            List.zip arg varMap.[label] 
            |> Map.ofList

        let t = f.Term |> Term.map (fun x -> renamingMap.[x])

        label, t
        )
    |> Map.ofList

let repair (config: Configuration) (program : Program<'L, Annotation>) (prefix : list<Quantifier * TraceVariable>, nsa : NSA<int,HyperLTLAtom>) (repairLocations : list<string * (FunctionName * 'L)>) =   
    prefix
    |> List.iter (fun (q, _) -> 
        if q <> FORALL then 
            raise <| GeneralError $"Repair is only applicable to universal formulas"
    )
    
    
    let varMap, holeIdMap, modifiedProgram, returnTypeMap, argTypeMap, functionSketchMapping = instrumentProgram program repairLocations

    // ===================== Perform SE and construct constraints =====================

    // Symbolically execute the program with the hole inserted
    let seContainer = 
        SymbolicExecution.startSE modifiedProgram config.RepairOptions.UnrollingDepth

    let finalConstraint  = generateVerificationConditionUniversalFormula seContainer (prefix |> List.map snd, nsa)

    // ===================== Construct SyGuS Constraints =====================

    config.Logger.LogN $"We are looking for repair functions with return type %A{returnTypeMap} with arguments %A{argTypeMap}"

    let instance = 
        {
            SyGuSInstance.Constraints = [finalConstraint]; 
            TypeMapping = 
                finalConstraint 
                |> Term.freeVars
                |> Seq.map (fun (x, pi) -> 
                    (x, pi), seContainer.InputTypeMapping.[x] |> VarType.asSMTSort
                    )
                |> Map.ofSeq
            VarStringer = fun (x, pi) -> x + "_" + pi
            FunctionSketchMapping = functionSketchMapping
        }

    let res = SyGuS.solveSyGuS config SmtLogic.ALL instance
    
    match res with 
    | Result.Error err -> raise <| GeneralError $"Error during SyGuS solving: %s{err}" 
    | Result.Ok None -> 
        // Could not find a repair
        None
    | Result.Ok (Some x) -> 
        x 
        |> deInstrument varMap holeIdMap
        |> Some


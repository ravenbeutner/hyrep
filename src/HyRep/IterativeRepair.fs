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

module IterativeRepair

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
open TransparentRepair

let private generateConditionsIterativeRepair (seContainerOriginal: SymbolicExecutionContainer<'L>) (seContainerPrev: SymbolicExecutionContainer<'L>) (seContainerRepair: SymbolicExecutionContainer<'L>) (prefix : list<TraceVariable>, nsa : NSA<int,HyperLTLAtom>) (outputVariables : list<Var>) = 
    // fixedTraceVar gives the variable used to encode the iteration constraint
    let fixedTraceVar = prefix.[0]

    // =============== Subset ===============
    let repairAndOriginalAgree = TransparentRepair.compareOutputs seContainerOriginal seContainerRepair outputVariables Agree

    let prevAndOriginalAgree = TransparentRepair.compareOutputs seContainerOriginal seContainerPrev outputVariables Agree

    let preservesSubset = 
        Term.App(IMPLIES, [prevAndOriginalAgree; repairAndOriginalAgree])
        |> Term.map (fun x -> (x, fixedTraceVar))
    // =============== Subset - END ===============
    
    // =============== Strict Subset ===============
    let prevAndOriginalDisagree = TransparentRepair.compareOutputs seContainerOriginal seContainerPrev outputVariables Disagree

    let strictSubset = 
        Term.App(AND, [prevAndOriginalDisagree; repairAndOriginalAgree])
        |> Term.map (fun x -> (x, fixedTraceVar))

    let existentiallyQuantifiedVars = 
        strictSubset
        |> Term.freeVars
        |> Seq.map (fun (x, pi) -> 
            assert(seContainerOriginal.InputTypeMapping.[x] = seContainerRepair.InputTypeMapping.[x])
            assert(seContainerOriginal.InputTypeMapping.[x] = seContainerPrev.InputTypeMapping.[x])
                
            (x, pi), seContainerOriginal.InputTypeMapping.[x] |> VarType.asSMTSort
            )
        |> Seq.toList

    let quantifiedStrictSubset = 
        Term.Exists(existentiallyQuantifiedVars, strictSubset)
    // =============== Strict Subset - END ===============
    
    // =============== Correct ===============
    let repairIsCorrect = Verify.generateVerificationConditionUniversalFormula seContainerRepair (prefix, nsa)
    // =============== Correct END ===============

    [repairIsCorrect; preservesSubset; quantifiedStrictSubset]


let findBetterRepair (config: Configuration) (programOriginal : Program<'L, Annotation>) (programPrev : Program<'L, Annotation>) (prefix : list<TraceVariable>, nsa : NSA<int,HyperLTLAtom>) (outputVariables : list<Var>) (repairLocations : list<string * (FunctionName * 'L)>) = 
    
    let varMap, holeIdMap, modifiedProgram, returnTypeMap, argTypeMap, functionSketchMapping = Repair.instrumentProgram programOriginal repairLocations
    
    // ===================== Perform SE and construct constraints =====================
    let seContainerOriginal = 
        SymbolicExecution.startSE programOriginal config.RepairOptions.UnrollingDepth

    let seContainerPrev = 
        SymbolicExecution.startSE programPrev config.RepairOptions.UnrollingDepth

    let seContainerRepair = 
        SymbolicExecution.startSE modifiedProgram config.RepairOptions.UnrollingDepth


    let finalConstraints  = generateConditionsIterativeRepair seContainerOriginal seContainerPrev seContainerRepair (prefix, nsa) outputVariables

    // ===================== Construct SyGuS Constraints =====================
        
    config.Logger.LogN $"We are looking for repair functions with return type %A{returnTypeMap} with arguments %A{argTypeMap}"

    let instance = 
        {
            SyGuSInstance.Constraints = finalConstraints; 
            TypeMapping = 
                finalConstraints 
                |> List.map Term.freeVars
                |> Set.unionMany
                |> Seq.map (fun (x, pi) -> 
                    (x, pi), seContainerOriginal.InputTypeMapping.[x] |> VarType.asSMTSort
                    )
                |> Map.ofSeq
            VarStringer = fun (x, pi) -> x + "_" + pi
            FunctionSketchMapping = functionSketchMapping
        }

    let res = SyGuS.solveSyGuS config SmtLogic.ALL instance

    match res with 
    | Result.Error err -> raise <| GeneralError $"Error in SyGuS solver: %s{err}" 
    | Result.Ok None -> 
        // Could not find a repair
        None
    | Result.Ok (Some x) -> 
        x 
        |> Repair.deInstrument varMap holeIdMap
        |> Some

let iterativeRepair (config: Configuration) (program : Program<'L, Annotation>) (prefix : list<Quantifier * TraceVariable>, nsa : NSA<int,HyperLTLAtom>) (outputVariables : list<Var>) (repairLocations : list<string * (FunctionName * 'L)>) =   
    prefix
    |> List.iter (fun (q, _) -> 
        if q <> FORALL then 
            raise <| GeneralError $"Iterative repair currently only applicable to universal formulas"
    )

    // Find SOME repair as a starting point 
    match Repair.repair config program (prefix, nsa) repairLocations with 
    | None -> 
        // Could not find any repair 
        None
    | Some initRepairTerm -> 

        let rec searchUntilOptimumFound (iterationCount : int) (temp : Map<string,Term<Var>>) = 
            printfn "================= Intermediate SOLUTION ================="
            for (l, t) in temp |> Map.toSeq do
                printfn $"{l}: {Term.toSMTLibString id t}"
            printfn "========================================================="

            if Option.isSome config.RepairOptions.IterationBound && iterationCount >= config.RepairOptions.IterationBound.Value then 
                temp
            else

                let programPrev = 
                    (program, repairLocations)
                    ||> Seq.fold (fun prog (label, (functionName, l)) -> 
                        let e = Expression.fromTerm temp.[label]
                        Statement.Program.replaceExpression prog (functionName, l) e
                        )
                
                let r = findBetterRepair config program programPrev (prefix |> List.map snd, nsa) outputVariables repairLocations

                match r with 
                | None -> 
                    temp
                | Some t -> 
                    searchUntilOptimumFound (iterationCount + 1) t

        let sol = searchUntilOptimumFound 0 initRepairTerm

        Some sol


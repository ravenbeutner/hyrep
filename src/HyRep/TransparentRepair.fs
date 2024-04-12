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

module TransparentRepair

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

type AgreeOrDisagree = 
    | Agree 
    | Disagree

let compareOutputs (seContainerA: SymbolicExecutionContainer<'L>) (seContainerB: SymbolicExecutionContainer<'L>) (outputVariables : list<Var>) (m : AgreeOrDisagree) = 
    let differentOutputTerm = 
        List.allPairs seContainerA.SymbolicPaths seContainerB.SymbolicPaths
        |> List.map (fun (symbolicPathA, symbolicPathB) -> 
            
            let joinedLength = min symbolicPathA.ObservationStates.Length symbolicPathB.ObservationStates.Length

            let differentOutputs = 
                List.zip symbolicPathA.ObservationStates[0..joinedLength-1] symbolicPathB.ObservationStates[0..joinedLength-1]
                |> List.map (fun (a, b) -> 
                    outputVariables
                    |> List.filter (fun x -> Map.containsKey x a && Map.containsKey x b) // Only consider outputs that are defined on BOTH paths
                    |> List.map (fun x -> 
                        let left = a.[x] |> Expression.asTerm 
                        let right = b.[x] |> Expression.asTerm 

                        Term.App(EQ, [left; right])
                        )
                    )
                |> List.concat
                |> fun x -> Term.App(AND, x)
                |> fun x -> 
                    match m with 
                    | Disagree ->  Term.App(NOT, [x])
                    | Agree -> x

            // We want an input assignment that takes those two paths and has different outputs
            Term.App(AND, differentOutputs :: symbolicPathA.PathConstraints  @ symbolicPathB.PathConstraints )
            )
        |> fun x -> Term.App(OR, x)

    differentOutputTerm


// transparentVariable gives the variable w.r.t. which the solution should be transparent
let private generateConditionsTransparentRepair  (seContainerOriginal: SymbolicExecutionContainer<'L>) (seContainerRepair: SymbolicExecutionContainer<'L>) (prefix : list<TraceVariable>, nsa : NSA<int,HyperLTLAtom>) (outputVariables : list<Var>) (fixedTraceVar : TraceVariable) = 
    
    let differentOutputFormula = 
        compareOutputs seContainerOriginal seContainerRepair outputVariables Disagree
        |> Term.map (fun x -> x, fixedTraceVar)

    // ==================== Second Part ================
    // On all inputs where the first part holds, we require that some combination of other traces can result in a violation

    let existPathsThatCauseViolation = 
        Verify.generateVerificationConditionUniversalFormula seContainerOriginal (prefix, nsa)
        |> fun x -> Term.App(NOT, [x])

    let existentiallyQuantifiedVariables = 
        existPathsThatCauseViolation
        |> Term.freeVars
        |> Seq.choose (fun (x, pi) -> 
            // We quantify over all variables, except those indexed with "transparentVariable" (which is part of the original pair of paths that disagree in their output)
            if pi = fixedTraceVar then 
                None 
            else 
                Some ((x, pi), seContainerOriginal.InputTypeMapping.[x] |> VarType.asSMTSort)
            )
        |> Seq.toList

    let conclusion = 
        Term.Exists (existentiallyQuantifiedVariables, existPathsThatCauseViolation)
        
    let repairIsTransparent = 
        Term.App(IMPLIES, [differentOutputFormula; conclusion])
        |> Term.simplify

    // ==================== REPAIR is correct ================
    // On all inputs where the first part holds, we require that some combination of other traces can result in a violation

    let repairIsCorrect = Verify.generateVerificationConditionUniversalFormula seContainerRepair (prefix, nsa)

    [repairIsTransparent; repairIsCorrect]


let transparentRepair (config: Configuration) (program : Program<'L, Annotation>) (prefix : list<Quantifier * TraceVariable>, nsa : NSA<int,HyperLTLAtom>) (outputVariables : list<Var>) (repairLocations : list<string * (FunctionName * 'L)>) =   
    prefix
    |> List.iter (fun (q, _) -> 
        if q <> FORALL then 
            raise <| GeneralError $"Transparent repair is only applicable to universal formulas"
    )

    let varMap, holeIdMap, modifiedProgram, returnTypeMap, argTypeMap, functionSketchMapping = Repair.instrumentProgram program repairLocations

    // ===================== Perform SE and construct constraints =====================

    // Symbolically execute the repaired and original program
    let seContainerOriginal = 
        SymbolicExecution.startSE program config.RepairOptions.UnrollingDepth

    let seContainerRepair = 
        SymbolicExecution.startSE modifiedProgram config.RepairOptions.UnrollingDepth


    let finalConstraints  = generateConditionsTransparentRepair seContainerOriginal seContainerRepair (prefix |> List.map snd, nsa) outputVariables (prefix.[0] |> snd)


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
        None
    | Result.Ok (Some x) -> 
        x 
        |> Repair.deInstrument varMap holeIdMap 
        |> Some

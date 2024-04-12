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

module Verify

open System

open FsOmegaLib.SAT
open FsOmegaLib.NSA

open Util
open Configuration
open Statement
open SMT
open SMTUtil
open HyperLTL
open SymbolicExecution

let rec private allPathsOfGivenLength (nsa : NSA<'T, 'L>) (length : int) = 
    let rec walk (currentState : 'T) (length: int) = 
        if length <= 0 then 
            [[]]
        else 
            nsa.Edges.[currentState]
            |> List.map (fun (g, ss) -> 
                walk ss (length - 1)
                |> List.map (fun gl -> 
                    g :: gl
                    )
                )
            |> List.concat

    nsa.InitialStates
    |> Set.toList
    |> List.map (fun s -> walk s length)
    |> List.concat

/// Construct a formula that encodes that the given path combination has some accepting run in the nsa
let constructSafetySatisfactionFormula (nsa: NSA<'T,Term<Var * TraceVariable>>) (pathCombination: Map<TraceVariable,SymbolicExecutionPath<'L>>) = 
    let joinedShortestLength = 
        Map.values pathCombination
        |> Seq.map (fun x -> x.ObservationStates)
        |> Seq.map List.length
        |> Seq.min

    let paths = 
        allPathsOfGivenLength nsa joinedShortestLength

    let observationsSatisfyBody = 
        paths 
        |> List.map (fun path -> 
            path 
            |> List.mapi (fun i f -> 
                f 
                |> List.map (fun clause -> 
                    clause 
                    |> List.map (fun l -> 

                        let b = 
                            nsa.APs.[Literal.getValue l]
                            |> Term.bindAndMap (fun (x, pi) -> 
                                
                                if pathCombination.ContainsKey pi |> not || pathCombination.[pi].ObservationStates.[i].ContainsKey x |> not then 
                                    raise <| GeneralError $"To evaluate the HyperLTL property at the {i}th observation step, we need the symbolic value of ({x}_{pi}). This value is however not defined in the program."

                                pathCombination.[pi].ObservationStates.[i].[x]
                                |> Expression.asTerm
                                |> Term.map (fun x -> x, pi)
                            )

                        match l with 
                        | PL _ -> b 
                        | NL _ -> Term.App(NOT, [b])
                    )
                    |> fun x -> Term.App(AND, x)
                )
                |> fun x -> Term.App(OR, x)
            )
            |> fun x -> Term.App(AND, x)
        )
        |> fun x -> Term.App(OR, x)

    observationsSatisfyBody

let generateVerificationCondition (seContainer: SymbolicExecutionContainer<'L>) (prefix : list<Quantifier * TraceVariable>, nsa : NSA<int,HyperLTLAtom>) = 
    
    let rec generateConditions (pathCombination : Map<TraceVariable, SymbolicExecutionPath<'L>>) (prefix : list<Quantifier * TraceVariable>)  =
        match prefix with 
        | [] -> constructSafetySatisfactionFormula nsa pathCombination
        | (q, pi) :: xs -> 
            let cases = 
                seContainer.SymbolicPaths
                |> List.map (fun s -> 
                    let pathCondition = 
                        s.PathConstraints
                        |> fun x -> Term.App(AND, x)
                        |> Term.map (fun x -> x, pi)

                    let body = generateConditions (Map.add pi s pathCombination) xs 

                    let quantifierPrefixInputs = 
                        seContainer.InputTypeMapping
                        |> Map.toList
                        |> List.map (fun (x, t) -> (x, pi), VarType.asSMTSort t)

                    match q with 
                    | FORALL -> Term.Forall (quantifierPrefixInputs, Term.App (IMPLIES, [pathCondition; body]))
                    | EXISTS -> Term.Exists (quantifierPrefixInputs, Term.App (AND, [pathCondition; body]))
                    )
            
            match q with 
            | FORALL -> Term.App (AND, cases)
            | EXISTS -> Term.App (OR, cases)

            |> Term.simplify

    generateConditions Map.empty prefix



/// Generate quantifier-free encoding for \forall^* formulas, the formula should be valid, i.e., hold for all possible variable assignments
let generateVerificationConditionUniversalFormula (seContainer: SymbolicExecutionContainer<'L>) (prefix : list<TraceVariable>, nsa : NSA<int,HyperLTLAtom>) = 
    let finalFormula = 
        prefix
        |> List.map (fun pi -> pi, seq seContainer.SymbolicPaths)
        |> Map.ofList
        |> Util.cartesianProductMap
        |> Seq.toList
        |> List.map (fun pathCombination -> 
            // Encode that one of the paths can be taken using the formulas at observation points
            let observationsSatisfyBody = constructSafetySatisfactionFormula nsa pathCombination

            let indexedPathConstraint = 
                pathCombination
                |> Map.map (fun pi x -> 
                    x.PathConstraints
                    |> List.map (Term.map (fun x -> x, pi))
                    )
                |> Map.values
                |> List.concat
                |> fun x -> Term.App(AND, x) 

            Term.App (AND, [indexedPathConstraint; observationsSatisfyBody]) // AND, IMPLIES
            )
        |> fun x -> Term.App(OR, x) // OR, AND
        |> Term.simplify

    finalFormula


let verify (config: Configuration) (program : Program<'L, 'A>) (prefix : list<Quantifier * TraceVariable>, nsa : NSA<int,HyperLTLAtom>)  =  
    let seContainer = 
        SymbolicExecution.startSE program config.RepairOptions.UnrollingDepth

    if prefix |> List.forall (fun (q, _) -> q = FORALL) then 
        config.Logger.LogN "Use encoding for \\forall^* formulas"

        let finalConstraint  = generateVerificationConditionUniversalFormula seContainer (prefix |> List.map snd, nsa)

        let instance = 
            {
                SmtInstance.Term = finalConstraint
                TypeMapping = fun (x, _) -> seContainer.InputTypeMapping.[x] |> VarType.asSMTSort
                VarStringer = fun (x, pi) -> x + "_" + pi
            }

        let res = SMTUtil.checkValidDirect config.SolverConfiguration ALL instance

        match res with 
        | SmtSatResult.SAT -> true 
        | SmtSatResult.UNSAT -> false 
        | SmtSatResult.UNKNOWN -> raise <| GeneralError $"Solver returned unknown"
        | SmtSatResult.ERROR err -> raise <| GeneralError $"Solver Error: %s{err}"
    
    else 
        config.Logger.LogN "Use encoding for full HyperLTL"

        let finalConstraint = generateVerificationCondition seContainer (prefix, nsa)

        let instance = 
            {
                SmtInstance.Term = finalConstraint; 
                TypeMapping = fun _ -> failwith ""
                VarStringer = fun (x, pi) -> x + "_" + pi
            }

        let res = SMTUtil.checkSatDirect config.SolverConfiguration ALL instance

        match res with 
        | SmtSatResult.SAT -> false // TODO
        | SmtSatResult.UNSAT -> true 
        | SmtSatResult.UNKNOWN -> raise <| GeneralError $"Solver returned unknown"
        | SmtSatResult.ERROR err -> raise <| GeneralError $"Solver Error: %s{err}"


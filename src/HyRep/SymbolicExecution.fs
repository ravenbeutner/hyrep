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

module SymbolicExecution 

open SMT
open Statement

type SymbolicStore = Map<Var, Expression<Var>>

type private SymbolicExecutionState<'L> = 
    {
        SymbolicStore : SymbolicStore
        PathConstraints : list<Term<Var>>
        ObservationStates : list<SymbolicStore> // Record the current symbolic state at each observe statement
        Depth : int
        CurrentFunction : FunctionName
        TraversedLabels : list<FunctionName * 'L>
    }

let rec private symbolicExecution (program : Program<'L, 'A>) (targetDepth : option<int>) (state : SymbolicExecutionState<'L>) (location : 'L) : list<SymbolicExecutionState<'L>> = 
    if Option.isSome targetDepth && state.Depth >= targetDepth.Value then 
        state |> List.singleton
    else 
        let statement, _ = program.Functions.[state.CurrentFunction].LocationMap.[location]
        
        match statement with 
        | Skip -> 
            {state with Depth = state.Depth + 1; TraversedLabels = state.TraversedLabels @ [state.CurrentFunction, location]}
            |> List.singleton
        | VarAssign(x, e) -> 
            let newE = 
                e 
                |> Expression.bind (fun x -> 
                    state.SymbolicStore.[x]
                    )
            
            {state with SymbolicStore = state.SymbolicStore |> Map.add x newE; TraversedLabels = state.TraversedLabels @ [state.CurrentFunction, location]}
            |> List.singleton
        | If (e, s1, s2) -> 
            let eTerm = 
                e
                |> Expression.bind (fun x -> 
                    state.SymbolicStore.[x]
                    )
                |> Expression.asTerm

            let res1 = symbolicExecutionList program targetDepth {state with Depth = state.Depth + 1; PathConstraints = eTerm :: state.PathConstraints; TraversedLabels = state.TraversedLabels @ [state.CurrentFunction, location]} s1
            let res2 = symbolicExecutionList program targetDepth {state with Depth = state.Depth + 1; PathConstraints = (Term.App(SmtOperator.NOT, [eTerm])) :: state.PathConstraints; TraversedLabels = state.TraversedLabels @ [state.CurrentFunction, location]} s2
        
            List.append res1 res2
        | Assume (e) -> 
            let eTerm = 
                e
                |> Expression.bind (fun x -> 
                    state.SymbolicStore.[x]
                    )
                |> Expression.asTerm 

            {state with PathConstraints = eTerm :: state.PathConstraints; Depth = state.Depth + 1; TraversedLabels = state.TraversedLabels @ [state.CurrentFunction, location]}
            |> List.singleton
        | While(e, s) -> 
            // This will generate infinitely many symbolic paths 

            let eTerm = 
                e
                |> Expression.bind (fun x -> 
                    state.SymbolicStore.[x]
                    )
                |> Expression.asTerm


            let termPath = {state with PathConstraints = (Term.App(SmtOperator.NOT, [eTerm])) :: state.PathConstraints; Depth = state.Depth + 1; TraversedLabels = state.TraversedLabels @ [state.CurrentFunction, location]}

            termPath ::
            symbolicExecutionList program targetDepth {state with PathConstraints = eTerm :: state.PathConstraints; Depth = state.Depth + 1; TraversedLabels = state.TraversedLabels @ [state.CurrentFunction, location]} (s @ [location])
        | Observe -> 
            {state with Depth = state.Depth + 1; ObservationStates = state.ObservationStates @ [state.SymbolicStore]; TraversedLabels = state.TraversedLabels @ [state.CurrentFunction, location]}
            |> List.singleton

        | FunctionCallAssign (returnVars, functionName, args) -> 
            let functionDefinition = 
                program.Functions.[functionName]

            let stateForFunctionCall = 
                {
                    SymbolicExecutionState.SymbolicStore = 
                        List.zip functionDefinition.Arguments args
                        |> List.map (fun  (x, e) -> 
                            x, Expression.bind (fun x -> state.SymbolicStore.[x]) e
                            )
                        |> Map.ofList
                    PathConstraints = state.PathConstraints
                    ObservationStates = state.ObservationStates
                    Depth = state.Depth + 1
                    CurrentFunction = functionName
                    TraversedLabels = state.TraversedLabels @ [state.CurrentFunction, location]
                }

            // We execute the body of the function and, afterwards, execute the remaining program
            let functionCallResults = 
                symbolicExecutionList program targetDepth stateForFunctionCall functionDefinition.Locations

            functionCallResults
            |> List.map (fun s -> 

                // Update the value of all variables that are bound by the return value
                let updatedReturnVariables = 
                    List.zip returnVars functionDefinition.ReturnExpressions
                    |> List.map (fun (x, e) -> 
                        x, Expression.bind (fun y -> s.SymbolicStore.[y]) e
                        )
                    |> Map.ofList

                // Update the variables assigned by the function 
                {
                    SymbolicExecutionState.SymbolicStore = 
                        Util.updateMap state.SymbolicStore updatedReturnVariables
                    PathConstraints = state.PathConstraints
                    ObservationStates = state.ObservationStates
                    Depth = state.Depth + 1
                    CurrentFunction = state.CurrentFunction
                    TraversedLabels = state.TraversedLabels // Do not add label when returning
                }
                )
and private symbolicExecutionList (program : Program<'L, 'A>) (targetDepth : option<int>) (state : SymbolicExecutionState<'L>) (locationList : list<'L>) =
    match locationList with 
    | [] -> [state] 
    | l :: ls -> 
        symbolicExecution program targetDepth state l 
        |> List.map (fun x -> 
            symbolicExecutionList program targetDepth x ls
            )
        |> List.concat

type SymbolicExecutionPath<'L> = 
    {
        SymbolicStore : SymbolicStore
        PathConstraints : list<Term<Var>>
        ObservationStates : list<SymbolicStore> // Record the current symbolic state at each observe statement
        TraversedLabels : list<FunctionName * 'L>
    }

type SymbolicExecutionContainer<'L> = 
    {
        SymbolicPaths : list<SymbolicExecutionPath<'L>>
        InputTypeMapping : Map<Var, VarType>
    }

let startSE (program : Program<'L, 'A>) (targetDepth : option<int>) = 
    let mainFunctionDefinition = 
        program.Functions.[program.MainFunction]

    let initState = 
        {
            SymbolicExecutionState.SymbolicStore = 
                mainFunctionDefinition.Arguments
                |> List.map (fun x -> 
                    x, Expression.Var x
                    )
                |> Map.ofList
            PathConstraints = []                
            ObservationStates = []
            Depth = 0
            CurrentFunction = program.MainFunction
            TraversedLabels = []
        }

    let paths = symbolicExecutionList program targetDepth initState mainFunctionDefinition.Locations

    {
        SymbolicExecutionContainer.SymbolicPaths = 
            paths 
            |> List.map (fun x -> 
                {
                    SymbolicExecutionPath.SymbolicStore = x.SymbolicStore
                    PathConstraints = x.PathConstraints
                    ObservationStates = x.ObservationStates
                    TraversedLabels = x.TraversedLabels
                }
            )
        InputTypeMapping = 
            mainFunctionDefinition.Arguments
            |> List.map (fun x -> 
                x, mainFunctionDefinition.TypeMapping.[x]
                )
            |> Map.ofList 
    }

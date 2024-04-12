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

module SyGuS

open System
open System.IO

open Util 
open Configuration
open SMT
open SMTUtil
open Grammar


type SyGuSInstance<'T when 'T: comparison> = 
    {
        Constraints : list<Term<'T>>
        TypeMapping :  Map<'T, SmtSort>
        VarStringer :  'T -> String
        FunctionSketchMapping : Map<String, FunctionSketch>
    }

let solveSyGuS 
    (config : Configuration)
    (logic : SmtLogic) 
    (instance : SyGuSInstance<'T>) = 

    let syntString = 
        instance.FunctionSketchMapping
        |> Map.toList
        |> List.map (fun (f, s) -> 
            Grammar.FunctionSketch.toSyGuSString s f
            )
        |> String.concat "\n"

    let declareVarsString  =
        instance.Constraints
        |> List.map Term.freeVars
        |> Set.unionMany
        |> Set.toList
        |> List.map (fun x -> 
            let sort = instance.TypeMapping.[x]

            "(declare-var " + 
            instance.VarStringer x + 
            " " +
            SmtSort.asString sort +
            ")"
            )
        |> String.concat "\n"

    let logicString =  "(set-logic " + SmtLogic.asString logic + ")"

    let constraintsString =
        instance.Constraints
        |> List.map Term.simplify
        |> List.map (fun x -> Term.toSMTLibString instance.VarStringer x)
        |> List.map (fun x -> "(constraint " + x + ")")
        |> String.concat "\n"


    let query =
        logicString + "\n" + 
        syntString + "\n" + 
        declareVarsString + "\n" + 
        constraintsString + "\n" + 
        "(check-synth)"

        
    let pathToFile = Path.Combine [|config.SolverConfiguration.MainPath; "query.sl"|]

    // Write the query to the file     
    File.WriteAllText(pathToFile, query)

    let res = Util.SystemCallUtil.systemCall config.SolverConfiguration.Cvc5Path pathToFile

    if res.Stderr.Trim() <> "" then 
        Result.Error (res.Stderr.Trim())
    else 
        let out = res.Stdout.Trim()

        if out = "fail" || out = "infeasible" then 
            Result.Ok None 
        else 
            let functionList = 
                match SMT.Parser.parseModel out with 
                | Result.Error e -> raise <| GeneralError $"Could not parse solution: %s{e}" 
                | Result.Ok x -> x

            Result.Ok (Some functionList)


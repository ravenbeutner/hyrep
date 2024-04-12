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

module SMTUtil

open System
open System.IO
open FSharp.Collections

open Configuration
open SMT


type SmtSatResult = 
    | SAT 
    | UNSAT 
    | UNKNOWN 
    | ERROR of String

type SmtLogic = 
    | ALL 

module SmtLogic = 
    let asString (l : SmtLogic) = 
        match l with 
        | ALL -> "ALL"

type SmtInstance<'T when 'T: comparison> = 
    {
        Term : Term<'T>
        TypeMapping : 'T -> SmtSort 
        VarStringer : 'T -> string
    }


/// Check if a given SMT Formula is satisfiable
let checkSatDirect 
    (config : SolverConfiguration)
    (logic : SmtLogic) 
    (instance : SmtInstance<'T>)
    =

    // Write the variables types for the SMTLIB query
    let declareVarsString =
        instance.Term
        |> Term.freeVars
        |> Set.toList
        |> List.map (fun x -> 
            let sort = instance.TypeMapping x
            "(declare-fun " + 
            instance.VarStringer x + 
            " () " +
            SmtSort.asString sort +
            ")"
        )
        |> String.concat "\n"

    let query =
        "(set-logic " + SmtLogic.asString logic + ")\n" +
        declareVarsString + "\n" + 
        "(assert\n" +
        Term.toSMTLibString instance.VarStringer instance.Term +
        "\n)" + "\n" +
        "(check-sat)"

    let pathToFile = Path.Combine [|config.MainPath; "query.smt2"|]

    // Write the query to the file     
    File.WriteAllText(pathToFile, query)

    let args = pathToFile

    let res = Util.SystemCallUtil.systemCall config.Cvc5Path args
    
    if res.Stderr.Trim() <> "" then 
        SmtSatResult.ERROR (res.Stderr.Trim())
    else 
        if res.Stdout.Trim() = "unsat" then 
            SmtSatResult.UNSAT
        elif res.Stdout.Trim() = "sat" then 
            SmtSatResult.SAT
        elif res.Stdout.Trim() = "unknown" then 
            SmtSatResult.UNKNOWN
        else 
            SmtSatResult.ERROR $"Unexpected output by SMT solver: %s{res.Stdout}"

let checkValidDirect 
    (config : SolverConfiguration)
    (logic : SmtLogic) 
    (instance : SmtInstance<'T>)
    =

    let res = checkSatDirect config logic {instance with Term = Term.App(NOT, [instance.Term])}

    match res with 
    | SmtSatResult.SAT -> SmtSatResult.UNSAT
    | SmtSatResult.UNSAT -> SmtSatResult.SAT 
    | SmtSatResult.ERROR e -> SmtSatResult.ERROR e 
    | SmtSatResult.UNKNOWN -> SmtSatResult.UNKNOWN

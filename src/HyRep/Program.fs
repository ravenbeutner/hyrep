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

module Program 

open System
open System.IO

open FsOmegaLib.Operations

open Util
open SMT
open Statement
open Configuration
open InputInstance
open CommandLineParser

let findMarkedLocations (program : Program<'L, Annotation>) = 
    let markedLocations = 
        program.Functions
        |> Map.toSeq
        |> Seq.map (fun (name, body) -> 
            body.LocationMap
            |> Map.toSeq
            |> Seq.choose (fun (l, (_, a)) -> 
                match a.Marker with 
                | Some marker -> Some (marker, (name, l))
                | None -> None
                ) 
            )
        |> Seq.concat
        |> Seq.toList
        

    if markedLocations.IsEmpty then 
        raise <| GeneralError $"At least one repair location must be marked"

    if List.length markedLocations <> (markedLocations |> List.map fst |> List.distinct |> List.length) then 
        raise <| GeneralError $"Some label is used more than once"

    markedLocations
        
let run (args: array<String>) = 
    let sw = System.Diagnostics.Stopwatch()
    let swTotal = System.Diagnostics.Stopwatch()

    swTotal.Start()

    sw.Start()

    let cmdArgs = 
        match CommandLineParser.parseCommandLineArguments (Array.toList args) with 
        | Result.Ok x -> x 
        | Result.Error err -> 
            raise <| GeneralError $"Error when parsing arguments: %s{err}"

    let solverConfig = Configuration.getConfig()

    let logger = 
        {
            Logger.Log = 
                fun s -> if cmdArgs.LogPrintouts then printf $"{s}"
        }


    let inputFile = 
        match cmdArgs.InputFile with 
        | Some f -> f 
        | None -> raise <| GeneralError $"No input file is specified"

    let inputcontent =   
        try 
            File.ReadAllText inputFile
        with 
            | err -> 
                printfn $"Could not open/read file %s{inputFile}"
                exit 0

    let input = 
        match InputInstance.Parser.parseInputInstance inputcontent with 
        | Result.Ok x -> x 
        | Result.Error err -> 
            raise <| GeneralError $"Error when parsing input instance: %s{err}"

    match RepairInstance.findError input with 
    | Some err -> 
        raise <| GeneralError $"%s{err}"
    | None -> ()

    let config = 
        {
            SolverConfiguration = solverConfig
            Logger = logger
            RepairOptions = 
                {
                    UnrollingDepth = input.UnrollingDepth
                    IterationBound = input.IterationBound
                }
        }

    let program = 
        match Program.annotateProgram input.Program with 
        | Result.Ok x -> x
        | Result.Error err -> raise <| GeneralError $"Error in the program: %s{err}"
    
    sw.Restart()

    // Convert the LTL body of the formula to an NSA
    let nsa = 
        match FsOmegaLib.Operations.LTLConversion.convertLTLtoNSA false config.SolverConfiguration.MainPath config.SolverConfiguration.Ltl2tgbaPath input.Formula.LTLMatrix with 
        | Success x -> x 
        | Fail e -> raise <| GeneralError $"{e.DebugInfo}"

    match cmdArgs.Mode with 
    | None -> raise <| GeneralError "Must given a repair/verification mode"
    | Some Verify -> 
        let r = Verify.verify config program (input.Formula.QuantifierPrefix, nsa)
        if r then 
            printfn "SAT"
        else
            printfn "UNSAT"
    | Some Repair | Some TransparentRepair | Some IterativeRepair -> 
        let repairLocations = findMarkedLocations program

        let repairExpressions =
            match cmdArgs.Mode with 
            | Some Repair -> 
                Repair.repair config program (input.Formula.QuantifierPrefix, nsa) repairLocations
            | Some TransparentRepair -> 
                TransparentRepair.transparentRepair config program (input.Formula.QuantifierPrefix, nsa) input.Outputs repairLocations
            | Some IterativeRepair -> 
                IterativeRepair.iterativeRepair config program (input.Formula.QuantifierPrefix, nsa) input.Outputs repairLocations
            | _ -> failwith ""

        printfn "\n================= Final SOLUTION ================="
        match repairExpressions with 
        | None -> 
            printfn "No repair found"
        | Some x -> 
            for (label, t) in Map.toSeq x do 
                printfn $"{label} : {Term.toSMTLibString id t}"
        printfn "====================================================\n"


    config.Logger.LogN ""
    config.Logger.LogN $"Total Time: %i{swTotal.ElapsedMilliseconds} ms (= %.4f{(double(swTotal.ElapsedMilliseconds) / 1000.0)} s)"
    
    0


[<EntryPoint>]
let main args = 
    try 
        run args
    with 
    | GeneralError err ->
        printfn $"========================== ERROR ==========================\n" 
        printfn $"%s{err}"
        printfn $"\n===========================================================" 
        reraise()
    
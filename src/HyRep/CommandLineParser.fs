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

module CommandLineParser

open System

type Mode = 
    | Verify
    | Repair
    | TransparentRepair
    | IterativeRepair

type CommandLineArguments = 
    {
        Mode : option<Mode>
        InputFile : option<String>
        LogPrintouts : bool
    }

    static member Default = 
        {
            Mode = None
            InputFile = Option.None
            LogPrintouts = false
        }

let rec private splitByPredicate (f : 'T -> bool) (xs : list<'T>) = 
    match xs with 
        | [] -> [], []
        | x::xs -> 
            if f x then 
                [], x::xs 
            else 
                let r1, r2 = splitByPredicate f xs 
                x::r1, r2

let parseCommandLineArguments (args : list<String>) =
    let rec parseArgumentsRec (args : list<String>) (opt : CommandLineArguments) = 

        match args with 
        | [] -> Result.Ok opt
        | x :: xs -> 
            match x with 
            | "--log" -> 
                parseArgumentsRec xs { opt with LogPrintouts = true }
            | "--verify" -> 
                parseArgumentsRec xs { opt with Mode = Some Verify }
            | "--repair" -> 
                parseArgumentsRec xs { opt with Mode = Some Repair }
            | "--trans" -> 
                parseArgumentsRec xs { opt with Mode = Some TransparentRepair }
            | "--iter" -> 
                parseArgumentsRec xs { opt with Mode = Some IterativeRepair }
            | s when s <> "" && s.Trim().StartsWith "-" -> 
                Result.Error ("Option " + s + " is not supported" )
            | x -> 
                // When no option is given, we assume that this is the input 
                if opt.InputFile.IsSome then 
                    Result.Error "Input file cannot be given more than once"
                else 
                    parseArgumentsRec xs {opt with InputFile = x |> Some}
        
    parseArgumentsRec args CommandLineArguments.Default

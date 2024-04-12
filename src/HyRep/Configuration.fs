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

module Configuration 

open System.IO

open Util
open FsOmegaLib.JSON 

type SolverConfiguration = 
    {
        MainPath : string
        Ltl2tgbaPath : string
        Cvc5Path: string
    }

let private parseConfigFile (s : string) =
    match FsOmegaLib.JSON.Parser.parseJsonString s with 
    | Result.Error err -> raise <| GeneralError $"Could not parse config file: %s{err}"
    | Result.Ok x -> 
        {
            MainPath = "./" 
            Ltl2tgbaPath = 
                (JSON.tryLookup "ltl2tgba" x)
                |> Option.defaultWith (fun _ -> raise <| GeneralError "No field 'ltl2tgba' found")
                |> JSON.tryGetString
                |> Option.defaultWith (fun _ -> raise <| GeneralError "Field 'ltl2tgba' must contain a string")
            Cvc5Path = 
                (JSON.tryLookup "cvc5" x)
                |> Option.defaultWith (fun _ -> raise <| GeneralError "No field 'cvc5' found")
                |> JSON.tryGetString
                |> Option.defaultWith (fun _ -> raise <| GeneralError "Field 'cvc5' must contain a string")
        }

let getConfig() = 
    // By convention the paths.json file is located in the same directory as the HyRep executable
    let configPath = 
        System.IO.Path.Join [|System.IO.Path.GetDirectoryName(System.Reflection.Assembly.GetExecutingAssembly().Location); "paths.json"|]
                     
    // Check if the path to the config file is valid , i.e., the file exists
    if System.IO.FileInfo(configPath).Exists |> not then 
        raise <| GeneralError "The paths.json could not be found"            
    
    // Parse the config File
    let configContent = 
        try
            File.ReadAllText configPath
        with 
            | _ -> 
                raise <| GeneralError "Could not open paths.json file"

    let solverConfig = parseConfigFile configContent

    if System.IO.FileInfo(solverConfig.Ltl2tgbaPath).Exists |> not then 
        raise <| GeneralError "The path to the ltl2tgba executable does not exist" 
    
    if System.IO.FileInfo(solverConfig.Cvc5Path).Exists |> not then 
        raise <| GeneralError "The path to the cvc5 executable does not exist" 

    solverConfig



type Logger = 
    {
        Log : string -> unit
    }

    member this.LogN = fun s -> this.Log (s + "\n")


type RepairOptions = 
    {
        UnrollingDepth : option<int>
        IterationBound : option<int>
    }
    
type Configuration = 
    {
        SolverConfiguration : SolverConfiguration
        Logger : Logger
        RepairOptions : RepairOptions
    }
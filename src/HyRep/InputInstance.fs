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

module InputInstance

open FsOmegaLib.LTL

open Util 

open SMT
open HyperLTL
open Statement

type RepairInstance = 
    {
        Name : string
        Program : Program<string, DefaultAnnotation>
        Formula : HyperLTL
        Outputs : list<Var>
        UnrollingDepth : option<int>
        IterationBound : option<int>
    }

module RepairInstance = 
    exception private ErrorFound of string

    let findError (instance : RepairInstance) = 
        try 
            match HyperLTL.findError instance.Formula with
            | Some err -> raise <| ErrorFound err 
            | None -> ()

            let vars = 
                instance.Program.Functions
                |> Map.toSeq
                |> Seq.map (fun (_, body) -> 
                    body.TypeMapping
                    |> Map.keys
                    )
                |> Seq.concat

            
            instance.Formula.LTLMatrix
            |> LTL.allAtoms 
            |> Seq.iter (fun x -> 
                x 
                |> Term.usedVars
                |> Seq.iter (fun (y, _) -> 
                    if Seq.contains y vars |> not then 
                        raise <| ErrorFound $"The HyperLTL specification refers to variable %s{y}, which is not declared in the program"
                    )
                
                    )

            instance.Outputs
            |> Seq.iter (fun y -> 
                if Seq.contains y vars |> not then 
                    raise <| ErrorFound $"Variable %s{y} is declared as an observable but not declared in the program"
            )

            if Option.isNone instance.UnrollingDepth && Program.containsLoops instance.Program then 
                raise <| ErrorFound $"The program contains loops, so an unrolling depth must be given"

            None 
        with
        | ErrorFound e -> Some e


type private RepairInstanceTemp = 
    {
        Name : option<string>
        Program : option<Program<string, DefaultAnnotation>>
        Formula : option<HyperLTL>
        Outputs : option<list<Var>>
        UnrollingDepth : option<int>
        IterationBound : option<int>
    }

    static member Default = 
        {
            Name = None
            Program = None
            Formula = None
            Outputs = None
            UnrollingDepth = None
            IterationBound = None
        }

module Parser = 
    open FParsec

    let commentLineParser =
        (skipString "//" .>> restOfLine false)

    let commentBlockParser =
        skipString "/*" >>. manyCharsTill anyChar (skipString "*/")
        |>> ignore

    let ws = spaces .>> sepEndBy (commentLineParser <|> commentBlockParser) spaces // whitespace and comment parser

    let mutable private c = 0 

    let labelGenerator () = 
        let r = c 
        c <- c + 1 
        "l" + string r

    let private inputElementParser (config : RepairInstanceTemp) = 
        let programParser = 
            skipString "[program]" >>. ws >>. Statement.Parser.programParser labelGenerator
            |>> (fun p -> {config with Program = Some p})

        
        let formulaParser = 
            skipString "[formula]" >>. ws >>. HyperLTL.Parser.hyperLTLParser
            |>> (fun f -> {config with Formula = Some f})

        let outputsParser = 
            skipString "[outputs]" >>. ws >>. many (Statement.Parser.variableParser .>> ws)
            |>> (fun f -> {config with Outputs = Some f})
         
        let nameParser = 
            skipString "[name]" >>. ws >>. many1Chars (digit <|> letter)
            |>> (fun x -> {config with Name = Some x}) 

        let depthParser = 
            skipString "[depth]" >>. ws >>. pint32
            |>> (fun x -> {config with UnrollingDepth = Some x}) 

        let iterParser = 
            skipString "[iter]" >>. ws >>. pint32
            |>> (fun x -> {config with IterationBound = Some x}) 

       
        ws
        >>. choice [ 
                programParser
                formulaParser
                outputsParser
                nameParser
                depthParser
                iterParser
            ]
        .>> ws

    let rec private inputParser (config: RepairInstanceTemp) =
        (attempt (inputElementParser config) >>= inputParser)
        <|>% config

    let parseInputInstance s = 

        let parser = inputParser RepairInstanceTemp.Default .>> spaces .>> eof
        let res = run parser s
        match res with
            | Success (res, _, _) -> 
                {
                    RepairInstance.Name = res.Name |> Option.defaultValue ""
                    Program = res.Program |> Option.defaultWith (fun _ -> raise <| GeneralError $"Must specify program")
                    Formula = res.Formula |> Option.defaultWith (fun _ -> raise <| GeneralError $"Must specify formula")
                    Outputs = res.Outputs |> Option.defaultWith (fun _ -> raise <| GeneralError $"Must specify outputs")
                    UnrollingDepth = res.UnrollingDepth
                    IterationBound = res.IterationBound
                }
                |> Result.Ok
            | Failure (err, _, _) -> Result.Error err

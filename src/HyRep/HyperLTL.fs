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

module HyperLTL 

open FsOmegaLib.LTL

open SMT

type Quantifier = FORALL | EXISTS
type TraceVariable = string

type HyperLTLAtom = 
    Term<string * TraceVariable> 

type HyperLTL = 
    {
        QuantifierPrefix : list<Quantifier * TraceVariable>
        LTLMatrix : LTL<HyperLTLAtom>
    }

module HyperLTL = 
    exception private NotWellFormedException of string 

    let findError (formula : HyperLTL) =
        try 
            let traceVars = formula.QuantifierPrefix |> List.map snd

            if traceVars |> set |> Set.count <> List.length traceVars then 
                raise <| NotWellFormedException $"Some trace variable is used more than once."

            LTL.allAtoms formula.LTLMatrix
            |> Set.iter (fun f -> 
                f
                |> Term.usedVars
                |> Set.iter (fun (_, pi) -> 
                if List.contains pi traceVars |> not then 
                    raise <| NotWellFormedException $"Trace Variable %s{pi} is used but not defined in the prefix"
                )
            )

            None
        with 
        | NotWellFormedException msg -> Some msg

module Parser =
    open FParsec
    
    let private keywords =
        [
            "X"
            "G"
            "F"
            "U"
            "W"
            "R"
        ]
        
    let traceVarParser : Parser<string, unit> =
        attempt (
            pipe2
                letter
                (manyChars (letter <|> digit))
                (fun x y -> string(x) + y)
            >>= fun s ->
                if List.contains s keywords then
                    fail ""
                else preturn s
            )
    
    let tracePrefixParser =
        let existsTraceParser = 
            skipString "exists " >>. spaces >>. traceVarParser .>> spaces .>> pchar '.'
            |>> fun pi -> (EXISTS, pi)

        let forallTraceParser = 
            skipString "forall " >>. spaces >>. traceVarParser .>> spaces .>> pchar '.'
            |>> fun pi -> (FORALL, pi)

        spaces >>.
        many1 (choice [existsTraceParser; forallTraceParser] .>> spaces)
        .>> spaces

    let private hyperLTLAtomParser =
        let indexedVarParser =
            tuple2
                (Statement.Parser.variableParser)
                (pchar '_' >>. traceVarParser)

        between (pchar '{') (spaces >>. pchar '}') (SMT.Parser.infixTermParser indexedVarParser)

    let hyperLTLParser : Parser<HyperLTL, unit> =     
        pipe2
            tracePrefixParser
            (FsOmegaLib.LTL.Parser.ltlParser hyperLTLAtomParser)
            (fun x y -> {HyperLTL.QuantifierPrefix = x; LTLMatrix = y})
    
    let parseHyperLTL s =    
        let full = hyperLTLParser .>> spaces .>> eof
        let res = run full s
        match res with
        | Success (res, _, _) -> Result.Ok res
        | Failure (err, _, _) -> Result.Error err

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

module Util 

open System
open System.Collections.Generic

exception GeneralError of String

let dictToMap (d : Dictionary<'A, 'B>) = 
    d
    |> Seq.map (fun x -> x.Key, x.Value)
    |> Map.ofSeq

let mergeMaps m1 m2 = 
    Seq.append (Map.toSeq m1) (Map.toSeq m2)
    |> Map.ofSeq

let rec mergeMapsMany l = 
    match l with 
    | [] -> Map.empty
    | x :: xs -> mergeMaps x (mergeMapsMany xs)

/// Add all entries in m2 to m1 (possibly overwriting existing values)
let updateMap m1 m2 = 
    Map.fold (fun m x k -> Map.add x k m) m1 m2


/// Compute the cartesian product of a list of sets
let rec cartesianProduct (LL: list<seq<'a>>) =
    match LL with
    | [] -> Seq.singleton []
    | L :: Ls ->
        seq {
            for x in L do
                for xs in cartesianProduct Ls -> x :: xs
        }

/// Given a map A -> seq<B> compute all possible maps A -> B that are obtained by picking some element from that set for each key in A
let cartesianProductMap (m : Map<'A, seq<'B>>) =
    m 
    |> Map.toList
    |> List.map (fun (k, s) -> 
        s
        |> Seq.map (fun x -> (k, x))
        )
    |> cartesianProduct
    |> Seq.map (fun l -> 
        l 
        |> Map.ofList
        )

module GraphUtil =
    let hasCycle (_ : Map<'T, Set<'T>>) = 
        false

module SystemCallUtil = 

    type SystemCallResult = 
        {
            Stdout : String 
            Stderr : String 
            ExitCode : int
        }

    let systemCall (cmd: string) (arg: string) = 
        let psi =
            System.Diagnostics.ProcessStartInfo(cmd, arg)

        psi.UseShellExecute <- false
        psi.RedirectStandardOutput <- true
        psi.RedirectStandardError <- true
        psi.CreateNoWindow <- true
        let p = System.Diagnostics.Process.Start(psi)
        let output = System.Text.StringBuilder()
        let error = System.Text.StringBuilder()
        p.OutputDataReceived.Add(fun args -> output.Append(args.Data) |> ignore)
        p.ErrorDataReceived.Add(fun args -> error.Append(args.Data) |> ignore)
        p.BeginErrorReadLine()
        p.BeginOutputReadLine()
        p.WaitForExit()

        {
            SystemCallResult.Stdout = output.ToString();
            Stderr = error.ToString()
            ExitCode = p.ExitCode
        }
            
module ParserUtil = 
    open FParsec

    let programVariableParser : Parser<String, unit> = 
        pipe2 
            (letter <|> digit)
            (many (letter <|> digit <|> pchar '.'))
            (fun x y -> x::y |> List.toArray |> String)

    /// Parser that parses everything between two '"'
    let escapedStringParser : Parser<string, unit> =
        let escapedCharParser : Parser<string, unit> =  
            anyOf "\"\\/bfnrt"
            |>> fun x -> 
                match x with
                | 'b' -> "\b"
                | 'f' -> "\u000C"
                | 'n' -> "\n"
                | 'r' -> "\r"
                | 't' -> "\t"
                | c   -> string c

        between
            (pchar '"')
            (pchar '"')
            (stringsSepBy (manySatisfy (fun c -> c <> '"' && c <> '\\')) (pstring "\\" >>. escapedCharParser)) 

    let pipe6 a b c d e f fu = 
        pipe5
            (a .>>. b)
            c 
            d 
            e 
            f 
            (fun (a, b) c d e f -> fu a b c d e f)

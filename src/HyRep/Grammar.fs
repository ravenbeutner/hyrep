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

module Grammar 

open System 

open FParsec

open Util
open SMT

type NonTerminal = string


type Production = 
    | Constant of SmtSort
    | Term of Term<string>

module Production = 
    
    let toSMTLibString (p : Production) =
        match p with 
        | Constant s -> "(Constant " + SmtSort.asString s + ")"
        | Term t -> Term.toSMTLibString id t 

type Grammar = 
    {
        Rules: list<NonTerminal * SmtSort * list<Production>>
    }

let private integerGrammar (intVars : list<String>) (boolVars : list<String>) = 

    let intNonTerminal = "nt@I"
    let boolNonTerminal = "nt@B"

    assert (List.contains intNonTerminal (intVars @ boolVars) |> not)
    assert (List.contains boolNonTerminal (intVars @ boolVars) |> not)

    let intProductions = 
        (
            intVars
            |> List.map (fun x -> x |> Term.Var |> Production.Term)
        )
        @
        [Production.Constant INT]
        @
        (
            [
                Term.App(ADD, [Term.Var intNonTerminal; Term.Var intNonTerminal]);
                Term.App(SUB, [Term.Var intNonTerminal; Term.Var intNonTerminal]);
                Term.App(ITE, [Term.Var boolNonTerminal; Term.Var intNonTerminal; Term.Var intNonTerminal])
            ]
            |> List.map Production.Term
        )
    
    let boolProductions = 
        (boolVars
        |> List.map (fun x -> x |> Term.Var |> Production.Term))
        @
        ([
            Term.App(AND, [Term.Var boolNonTerminal; Term.Var boolNonTerminal]);
            Term.App(OR, [Term.Var boolNonTerminal; Term.Var boolNonTerminal]);
            Term.App(NOT, [Term.Var boolNonTerminal]);
            Term.App(EQ, [Term.Var intNonTerminal; Term.Var intNonTerminal]);
            Term.App(LE, [Term.Var intNonTerminal; Term.Var intNonTerminal]);
            Term.App(GT, [Term.Var intNonTerminal; Term.Var intNonTerminal]);
        ]
        |> List.map Production.Term)



    {
        Rules = 
            [
                (intNonTerminal, SmtSort.INT, intProductions)
                (boolNonTerminal, SmtSort.BOOL, boolProductions)
            ]
    }


let private booleanGrammar (intVars : list<String>) (boolVars : list<String>) = 

    let intNonTerminal = "nt@I"
    let boolNonTerminal = "nt@B"

    assert (List.contains intNonTerminal (intVars @ boolVars) |> not)
    assert (List.contains boolNonTerminal (intVars @ boolVars) |> not)

    let intProductions = 
        (
            intVars
            |> List.map (fun x -> x |> Term.Var |> Production.Term)
        )
        @
        [Production.Constant INT]
        @
        (
            [
                Term.App(ADD, [Term.Var intNonTerminal; Term.Var intNonTerminal]);
                Term.App(SUB, [Term.Var intNonTerminal; Term.Var intNonTerminal]);
            ]
            |> List.map Production.Term
        )
    
    let boolProductions = 
        (boolVars
        |> List.map (fun x -> x |> Term.Var |> Production.Term))
        @
        ([
            Term.BoolConst true;
            Term.BoolConst false;
            Term.App(AND, [Term.Var boolNonTerminal; Term.Var boolNonTerminal]);
            Term.App(OR, [Term.Var boolNonTerminal; Term.Var boolNonTerminal]);
            Term.App(NOT, [Term.Var boolNonTerminal]);
            Term.App(EQ, [Term.Var intNonTerminal; Term.Var intNonTerminal]);
            Term.App(LE, [Term.Var intNonTerminal; Term.Var intNonTerminal]);
            Term.App(GT, [Term.Var intNonTerminal; Term.Var intNonTerminal]);
        ]
        |> List.map Production.Term)



    {
        Rules = 
            [
                (boolNonTerminal, SmtSort.BOOL, boolProductions)
                (intNonTerminal, SmtSort.INT, intProductions)
            ]
    }

let private stringGrammar (stringVars : list<String>) = 

    let stringNonTerminal = "nt@S"

    assert (List.contains stringNonTerminal stringVars |> not)

    let stringProductions = 
        (
            stringVars
            |> List.map (fun x -> x |> Term.Var |> Production.Term)
        )
        @
        (
            ["a"; "b"; "c"; "d"]
            |> List.map (fun x -> x |> Term.StringConst |> Production.Term)
        )
        @
        (
            [
                Term.App(APP, [Term.Var stringNonTerminal; Term.Var stringNonTerminal]);
            ]
            |> List.map Production.Term
        )
    
    {
        Rules = 
            [
                (stringNonTerminal, SmtSort.STRING, stringProductions)
            ]
    }

type FunctionSketch = 
    {
        Arguments : list<String * SmtSort>
        ReturnSort : SmtSort 
        Grammar : Grammar
    }

module FunctionSketch = 

    let toSyGuSString (sketch : FunctionSketch) (name : String) = 
        let argumentString = 
            sketch.Arguments
            |> List.map (fun (x, s) -> 
                "(" + x + " " + SmtSort.asString s + ")"
                )
            |> String.concat " "
            |> fun x -> "(" + x + ")"

        let preString = 
            sketch.Grammar.Rules
            |> List.map (fun (x, s, _) -> 
                "(" + x + " " + SmtSort.asString s + ")"
                )
            |> String.concat " "
            |> fun x -> "(" + x + ")"
        

        let defineString = 
            sketch.Grammar.Rules
            |> List.map (fun (x, s, productions) -> 
                
                let productionsString = 
                    productions
                    |> List.map Production.toSMTLibString
                    |> String.concat " "
                    |> fun x -> "(" + x + ")"

                "(" + x + " " + SmtSort.asString s + " " + productionsString + ")"
                )
            |> String.concat "\n"
            |> fun x -> "(" + x + ")"

        "(synth-fun " + 
        name + 
        " " + 
        argumentString + 
        " " + 
        SmtSort.asString sketch.ReturnSort + 
        "\n" + 
        preString + 
        "\n" + 
        defineString + 
        "\n)"



let integerSketch (argTypes : list<SmtSort>) = 

    let argumentVars = 
        argTypes 
        |> List.mapi (fun i x -> "a" + string(i), x)

    let intVars = 
        argumentVars |> List.filter (fun (_, s) -> s = INT) |> List.map fst
    
    let boolVars = 
        argumentVars |> List.filter (fun (_, s) -> s = BOOL) |> List.map fst

    let grammar = integerGrammar intVars boolVars

    {
        Arguments = argumentVars
        ReturnSort = INT 
        Grammar = grammar
    }

let booleanSketch (argTypes : list<SmtSort>) = 

    let argumentVars = 
        argTypes 
        |> List.mapi (fun i x -> "a" + string(i), x)

    let intVars = 
        argumentVars |> List.filter (fun (_, s) -> s = INT) |> List.map fst
    
    let boolVars = 
        argumentVars |> List.filter (fun (_, s) -> s = BOOL) |> List.map fst

    let grammar = booleanGrammar intVars boolVars

    {
        Arguments = argumentVars
        ReturnSort = BOOL 
        Grammar = grammar
    }

let stringSketch (argTypes : list<SmtSort>) = 

    let argumentVars = 
        argTypes 
        |> List.mapi (fun i x -> "a" + string(i), x)

    let stringVars = 
        argumentVars |> List.filter (fun (_, s) -> s = STRING) |> List.map fst
    
    let grammar = stringGrammar stringVars

    {
        Arguments = argumentVars
        ReturnSort = STRING 
        Grammar = grammar
    }

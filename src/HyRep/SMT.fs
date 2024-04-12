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

module SMT 

open System
open FSharp.Collections

open Util

type PrePost = PRE | POST

type SmtSort =
    | INT 
    | BOOL
    | STRING

module SmtSort = 
    let rec asString (s : SmtSort) = 
        match s with
        | INT -> "Int"
        | BOOL -> "Bool"
        | STRING -> "String"


type SmtOperator =   
    // Arithmetic
    | ADD 
    | SUB 
    | MUL 
    | MIN
    // Boolean
    | NOT 
    | AND
    | OR
    | IMPLIES
    // Equality
    | EQ 
    // Comparison
    | LE 
    | GE 
    | LT 
    | GT 
    // String functions
    | APP // str.++
    | LEN // str.len
    //
    | ITE
    // Free functions, used, e.g., for SyGuS encoding
    | FreeFunction of string

module SmtOperator = 
    let asSmtLibString o = 
        match o with 
        | ADD -> "+"
        | SUB -> "-"
        | MUL -> "*"
        | MIN -> "-"
        | NOT -> "not"
        | AND-> "and"
        | OR -> "or"
        | IMPLIES -> "=>"
        | EQ -> "="
        | LE -> "<="
        | GE -> ">="
        | LT -> "<"
        | GT -> ">"
        | LEN -> "str.len"
        | APP -> "str.++"
        | ITE -> "ite"
        | FreeFunction f -> f

type Value = 
    | IntValue of int64
    | BoolValue of bool 
    | StringValue of string

/// The type representing an SMT formula
type Term<'T when 'T : comparison> =
    | Var of 'T
    | IntConst of int64
    | StringConst of string
    | BoolConst of bool
    | App of SmtOperator * list<Term<'T>>
    | Forall of list<'T * SmtSort> * Term<'T>
    | Exists of list<'T * SmtSort> * Term<'T>
    | Let of list<'T * Term<'T>> * Term<'T>


module Term = 
    /// Returns all Vars used in this term
    let rec usedVars (t : Term<'T>) =
        match t with
        | Var v -> Set.singleton v 
        | IntConst _  | BoolConst _ | StringConst _ -> Set.empty
        | App (_, l) -> l |> List.map usedVars |> Set.unionMany
        | Forall(v, t) | Exists(v, t)   -> 
            (usedVars t, v)
            ||> List.fold (fun s (x, _) -> Set.add x s)
        | Let(_, _) -> raise <| NotImplementedException()
    
    let rec usedFunctions (t : Term<'T>) =
        match t with
        | Var _ | IntConst _  | BoolConst _ | StringConst _ -> Set.empty
        | App (n, l) -> l |> List.map usedFunctions |> Set.unionMany |> Set.add n
        | Forall(_, t) | Exists(_, t) -> usedFunctions t
        | Let(_, _) -> raise <| NotImplementedException()

    // Returns all vars that are free (i.e., not bond by some quantifier) in this term
    let rec freeVars (t : Term<'T>) =
        match t with
        | Var v -> Set.singleton v 
        | IntConst _  | BoolConst _ | StringConst _ -> Set.empty
        | App(_, l) ->
            l |> List.map freeVars |> Set.unionMany 
        | Forall(v, f) | Exists(v, f)   -> 
            List.fold (fun s (x, _)-> Set.remove x s) (freeVars f) v
        | Let(_, _) -> raise <| NotImplementedException()

    let rec topLevelConjuncts (t : Term<'T>) = 
        match t with 
        | App(AND, l) -> 
            l |> List.map topLevelConjuncts |> List.concat
        | _ -> [t]

    /// Replaces all vars by the result of applying a function, i.e., map a function over the term
    let rec map (m : 'T -> 'a) (t : Term<'T>) = 
        match t with
        | Var s -> Var (m s)
        | IntConst i -> IntConst i
        | BoolConst i -> BoolConst i
        | StringConst i -> StringConst i
        | App(n, l) -> App(n, List.map (map m) l)
        | Forall(v, t) -> Forall(List.map (fun (x, s) -> (m x, s)) v, map m t)
        | Exists(v, t) -> Exists(List.map (fun (x, s) -> (m x, s)) v, map m t)
        | Let _ -> raise <| NotImplementedException()
        
    /// Replaces all vars by the result of applying a function, i.e., map a function over the term
    let rec bind (m : 'T -> Term<'T>) (t : Term<'T>) = 
        match t with
        | Var s -> m s
        | IntConst i -> IntConst i
        | BoolConst i -> BoolConst i
        | StringConst i -> StringConst i
        | App(name, l) -> App(name, List.map (bind m) l)
        | Forall(v, t) -> Forall(List.map (fun (x, s) -> (x, s)) v, bind m t)
        | Exists(v, t) -> Exists(List.map (fun (x, s) -> (x, s)) v, bind m t)
        | Let _ -> raise <| NotImplementedException()
    
    let rec bindAndMap (m : 'T -> Term<'A>) (t : Term<'T>) = 
        match t with
        | Var s -> m s
        | IntConst i -> IntConst i
        | BoolConst i -> BoolConst i
        | StringConst i -> StringConst i
        | App(name, l) -> App(name, List.map (bindAndMap m) l)
        | Forall _ | Exists _ -> raise <| NotImplementedException()
        | Let _ -> raise <| NotImplementedException()
    
    let rec resolveLets (t : Term<'T>) = 
        match t with
        | Var s -> Var s
        | IntConst i -> IntConst i
        | BoolConst i -> BoolConst i
        | StringConst i -> StringConst i
        | App(n, l) -> App(n, List.map resolveLets l)
        | Forall(v, t) -> Forall(List.map (fun (x, s) -> (x, s)) v, resolveLets t)
        | Exists(v, t) -> Exists(List.map (fun (x, s) -> (x, s)) v, resolveLets t)
        | Let (bindings, body) ->   
            let m = Map.ofList bindings
            body
            |> resolveLets
            |> bind (fun x -> 
                if Map.containsKey x m then 
                    m.[x]
                else 
                    Var x 
                )
        
    let rec simplify (t : Term<'T>) = 
        match t with
        | Var s -> Var s
        | IntConst i -> IntConst i
        | BoolConst i -> BoolConst i
        | StringConst i -> StringConst i
        | App(ADD, l) -> 
            l 
            |> List.map simplify
            |> List.map (fun x -> 
                match x with 
                | App(ADD, l1) -> l1
                | _ -> [x])
            |> List.concat 
            |> fun x -> if x.Length = 1 then x.[0] else App(ADD, x)
        | App(MIN, [t]) -> 
            match simplify t with 
            | App(MIN, [t1]) -> t1
            | t1 -> App(MIN, [t1])
        | App(MUL, l) -> 
            l 
            |> List.map simplify
            |> List.map (fun x -> 
                match x with 
                | App(MUL, l1) -> l1
                | _ -> [x])
            |> List.concat 
            |> fun x -> if x.Length = 1 then x.[0] else App(MUL, x)
        | App(AND, l) -> 
            l 
            |> List.map simplify
            |> List.map (fun x -> 
                match x with 
                | App(AND, l1) -> l1
                | _ -> [x])
            |> List.concat 
            |> function 
                | [] -> BoolConst true 
                | [x] -> x 
                | xs -> App(AND, xs)
        | App(OR, l) -> 
            l 
            |> List.map simplify
            |> List.map (fun x -> 
                match x with 
                | App(OR, l1) -> l1
                | _ -> [x])
            |> List.concat 
            |> function 
                | [] -> BoolConst false 
                | [x] -> x 
                | xs -> App(OR, xs)
        | App(NOT, [t]) -> 
            match simplify t with 
            | App(NOT, [t1]) -> t1
            | t1 -> App(NOT, [t1])
        | App(ITE, [t1; t2; t3]) -> 
            match simplify t1 with 
            | BoolConst true -> simplify t2
            | BoolConst false -> simplify t3
            | t1' -> App(ITE, [t1'; simplify t2; simplify t3])
        | Forall(v, t) -> 
            if List.isEmpty v then 
                simplify t 
            else 
                Forall(List.map (fun (x, s) -> (x, s)) v, simplify t)
        | Exists(v, t) -> 
            if List.isEmpty v then 
                simplify t 
            else 
                Exists(List.map (fun (x, s) -> (x, s)) v, simplify t)
        | Let _ -> raise <| NotImplementedException()
        | App (f, l) -> 
            App(f, List.map simplify l)

    let rec evaluate (context : 'T -> Value) (t : Term<'T>) = 
        match t with
        | Var x -> context x
        | IntConst i -> IntValue i
        | BoolConst (i: bool) -> BoolValue i
        | StringConst i -> StringValue i
        | App(ADD, args) -> 
            args 
            |> List.map (evaluate context)
            |> List.map (function 
                | IntValue x -> x 
                | x -> raise <| GeneralError $"Could evaluate ADD on %A{x}"
                )
            |> List.sum
            |> IntValue
        | App(MIN, [t1]) ->  
            match evaluate context t1 with 
            | IntValue x -> IntValue -x 
            | x -> raise <| GeneralError $"Could evaluate ADD on %A{x}"
        | App(MUL, args) -> 
            args 
            |> List.map (evaluate context)
            |> List.map (function 
                | IntValue x -> x 
                | x -> raise <| GeneralError $"Could evaluate MUL on %A{x}"
                )
            |> List.fold (*) 1L
            |> IntValue
        | App(AND, args) -> 
            args 
            |> List.map (evaluate context)
            |> List.map (function 
                | BoolValue x -> x 
                | x -> raise <| GeneralError $"Could evaluate ADD on %A{x}"
                )
            |> List.forall id
            |> BoolValue
        | App(OR, args) -> 
            args 
            |> List.map (evaluate context)
            |> List.map (function 
                | BoolValue x -> x 
                | x -> raise <| GeneralError $"Could evaluate ADD on %A{x}"
                )
            |> List.exists id
            |> BoolValue
        | App(NOT, [t]) -> 
            match evaluate context t with 
            | BoolValue b -> BoolValue (not b)
            | x -> raise <| GeneralError $"Could evaluate NOT on %A{x}"
        | App(ITE, [t1; t2; t3]) -> 
            match evaluate context t1 with 
            | BoolValue true -> evaluate context t2
            | BoolValue false -> evaluate context t3
            | x -> raise <| GeneralError $"Could evaluate ITE on %A{x}"
        | App(EQ, [t1; t2]) ->  
            match evaluate context t1, evaluate context t2 with 
            | IntValue x1, IntValue x2 -> BoolValue (x1 = x2)
            | BoolValue x1, BoolValue x2 -> BoolValue (x1 = x2)
            | StringValue x1, StringValue x2 -> BoolValue (x1 = x2)
            | x -> raise <| GeneralError $"Could evaluate EQ on %A{x}"
        | App(LE, [t1; t2]) ->  
            match evaluate context t1, evaluate context t2 with 
            | IntValue x1, IntValue x2 -> BoolValue (x1 <= x2)
            | x -> raise <| GeneralError $"Could evaluate LE on %A{x}"
        | App(GE, [t1; t2]) ->  
            match evaluate context t1, evaluate context t2 with 
            | IntValue x1, IntValue x2 -> BoolValue (x1 >= x2)
            | x -> raise <| GeneralError $"Could evaluate GE on %A{x}"
        | App(LT, [t1; t2]) ->  
            match evaluate context t1, evaluate context t2 with 
            | IntValue x1, IntValue x2 -> BoolValue (x1 < x2)
            | x -> raise <| GeneralError $"Could evaluate LT on %A{x}"
        | App(GT, [t1; t2]) ->  
            match evaluate context t1, evaluate context t2 with 
            | IntValue x1, IntValue x2 -> BoolValue (x1 > x2)
            | x -> raise <| GeneralError $"Could evaluate GT on %A{x}"
        | Forall _ -> 
            raise <| GeneralError $"Cannot evaluate forall"
        | Exists _ -> 
            raise <| GeneralError $"Cannot evaluate exists"
        | Let _ -> raise <| NotImplementedException()
        | App (f, _) -> 
            raise <| GeneralError $"Unknown operator {f} or used with a wrong number of arguments"

    let rec mapFreeVars (m : 'T -> 'T) (t : Term<'T>) = 
        match t with
        | Var s -> Var (m s)
        | IntConst i -> IntConst i
        | BoolConst i -> BoolConst i
        | StringConst i -> StringConst i
        | App(f, l) -> App (f, List.map (mapFreeVars m) l)
        | Forall(v, t) -> 
            Forall(v, mapFreeVars (fun x -> if List.exists (fun (y, _) -> x = y) v then x else m x) t)
        | Exists(v, t) -> 
            Exists(v, mapFreeVars (fun x -> if List.exists (fun (y, _) -> x = y) v then x else m x) t)
        | Let _ -> raise <| NotImplementedException()
        
    
    let subst (a : list<'T * 'T>) (t : Term<'T>) = 
        t
        |> map (fun x -> 
            match List.tryFind (fun (y, _) -> y = x) a with 
                | None -> x 
                | Some (_, r) -> r
            )

    /// Given a term with string variables, computes a string in SMTLIB format
    let rec toSMTLibString (varStringer : 'T -> String) (t : Term<'T>)  =
        match t with
        | Var v -> varStringer v
        | IntConst n -> string(n)
        | BoolConst b -> 
            match b with 
            | true -> "true"
            | false -> "false"
        | StringConst c -> "\"" + c + "\""
        | App(f, l) ->
            l 
            |> List.map (toSMTLibString varStringer)
            |> String.concat " "
            |> fun x -> "(" + SmtOperator.asSmtLibString f + " " + x + ")"
        | Forall (v, b) -> 
            let bodyString = toSMTLibString varStringer b
            match v with 
                | [] -> 
                    bodyString
                | _ -> 
                    let args = 
                        v 
                        |> List.map (fun (v, s) -> "(" + varStringer v + " " + SmtSort.asString s + ")")
                        |> String.concat " "

                    "(forall (" + args + ")" + bodyString + ")"

        | Exists (v, b) -> 
            let bodyString = toSMTLibString varStringer b
            match v with 
                | [] -> 
                    bodyString
                | _ -> 
                    let args = 
                        v 
                        |> List.map (fun (v, s) -> "(" + varStringer v + " " + SmtSort.asString s + ")")
                        |> String.concat " "

                    "(exists (" + args + ")" + bodyString + ")"

        | Let (bindings, body) -> 
            let bindingsString = 
                bindings
                |> List.map (fun (n, t) -> 
                    "("+ varStringer n + " " + toSMTLibString varStringer t + ")"
                )
                |> String.concat " "

            "(let (" + bindingsString + ")" + toSMTLibString varStringer body + ")"
     
type SmtFunctionDefinition<'T when 'T: comparison> = 
    {
        Symbol : 'T;
        Arguments : list<'T * SmtSort>;
        Sort : SmtSort
        Term : Term<'T>
    }

module Parser = 
    open FParsec


    let private reservedWords = 
        [
            "BINARY"
            "DECIMAL"
            "HEXADECIMAL" 
            "NUMERAL" 
            "STRING"
            "_" 
            "!" 
            "as" 
            "let" 
            "exists" 
            "forall" 
            "match" 
            "par"
        ]

    /// Parses any possible symbol as defined by the SMTLIB standard
    let symbolParser : Parser<string, unit> = 
        let specialSymbolParser = 
            choice [
                pchar '~'
                pchar '!'
                pchar '@'
                pchar '%'
                pchar '^'
                pchar '&'
                pchar '*'
                pchar '_'
                pchar '-'
                pchar '+'
                pchar '='
                pchar '<'
                pchar '>'
                pchar '.'
                pchar '?'
                pchar '/'
            ]
        
        let simpleSymbolParser = 
            pipe2
                (letter <|> specialSymbolParser)
                (many (letter <|> digit <|> specialSymbolParser))
                (fun x y -> x :: y |> List.toArray |> String)

        let escapedStringParser = 
            pipe3 
                (pchar '|')
                (many (satisfy (fun c -> c <> '\\' && c <> '|')))
                (pchar '|')
                // We ignore the |s
                (fun _ x _ -> x |> List.toArray |> String)

        attempt
            (
                escapedStringParser <|> simpleSymbolParser
                >>= fun x -> if List.contains x reservedWords then fail "" else preturn x
            )

    let private operatorParser = 
        choice [
            stringReturn "str.++" APP;
            stringReturn "str.len" LEN;

            stringReturn "+" ADD;
            stringReturn "-" SUB;
            stringReturn "*" MUL;
            stringReturn "and" AND;
            stringReturn "or" OR;

            stringReturn "=" EQ;
            stringReturn "<=" LE;
            stringReturn ">=" GE;
            
            stringReturn "<" LT;
            stringReturn ">" GT;
            
            stringReturn "ite" ITE;

            stringReturn "not" NOT;
        ]

    
    let private attributeParser =
        let keywordParser = 
            skipChar ':' >>. symbolParser

        let attributeValueParser = 
            many1Chars (letter <|> digit)

        keywordParser .>> spaces .>>. attributeValueParser

    /// Parses an SMT Sort
    let sortParser = 
        choice [
            stringReturn "Int" SmtSort.INT
            stringReturn "Bool" SmtSort.BOOL
            stringReturn "String" SmtSort.STRING
        ]

    /// Given a parser for variables, construct a parser for SMT Lib formulas
    let termParser (varParser : Parser<'T, unit>) = 
        let termParser, termParserRef  = createParserForwardedToRef()
        
        let variableParser =
            varParser
            |>> Var

        let intConstParser =
            pint64 |>> IntConst

        let boolConstParser =
            stringReturn "true" (BoolConst true) <|> stringReturn "false" (BoolConst false)

        let stringConstParser =
            between (skipChar '"') (skipChar '"') (manyChars (satisfy (fun c -> c <> '"')))
            |>> StringConst

        let appParser = 
            pipe3
                (skipChar '(' >>. spaces >>. operatorParser .>> spaces) 
                (many (termParser .>> spaces) .>> spaces)
                (skipChar ')')
                (fun f l _ -> App(f, l))

        let letParser =
            let parseAssign =
                spaces >>.
                pipe2
                    (skipChar '(' >>. varParser)
                    (spaces >>. termParser)
                    (fun x y -> (x, y))
                .>> spaces .>> skipChar ')'


            let parseSeq =
                spaces >>. skipChar '(' >>.
                many parseAssign
                .>> spaces .>> skipChar ')'

            pipe2
                (skipString "(let" >>. parseSeq)
                (termParser .>> spaces .>> skipChar ')')
                (fun a b -> Let(a, b))
            

        // Try all available parser and take the first that succeeds. Parsing is easy as the SMTLIB formula is in prefix notation. 
        do termParserRef.Value <-
            spaces >>. choice [ 
                boolConstParser
                intConstParser
                stringConstParser
                appParser
                letParser
                variableParser 
            ] .>> spaces

        termParser

    /// Given a parser for variables, construct a parser for SMT Lib formulas
    let infixTermParser (varParser : Parser<'a, unit>) = 
        let termParser, termParserRef  = createParserForwardedToRef()
        
        let variableParser =
            varParser
            |>> Var

        let intConstParser =
            pint64 |>> IntConst

        let boolConstParser =
            stringReturn "true" (BoolConst true) <|> stringReturn "false" (BoolConst false)

        let stringConstParser =
            between (skipChar '"') (skipChar '"') (manyChars (satisfy (fun c -> c <> '"')))
            |>> StringConst

        let parParser =
            skipString "("
            >>.
            termParser
            .>> skipChar ')'


        let opp : OperatorPrecedenceParser<Term<'a>,unit,unit>=
            new OperatorPrecedenceParser<Term<'a>, unit, unit>()

        // a helper function for adding infix operators to opp
        let addInfixOperator string precedence associativity f =
            opp.AddOperator(
                InfixOperator(string, spaces, precedence, associativity, f)
            )

        let addPrefixOperator string precedence associativity f =
            opp.AddOperator(
                PrefixOperator(string, spaces, precedence, associativity, f)
            )

        let addTernaryOperator lstring rstring precedence associativity f =
            opp.AddOperator(
                TernaryOperator(lstring, spaces, rstring, spaces, precedence, associativity, f)
            )

        
        addInfixOperator "str.++" 90 Associativity.Left (fun e1 e2 -> Term.App (APP, [e1; e2]))
        


        addInfixOperator "+" 90 Associativity.Left (fun e1 e2 -> Term.App (ADD, [e1; e2]))
        addInfixOperator "-" 80 Associativity.Left (fun e1 e2 -> Term.App (SUB, [e1; e2]))
        addPrefixOperator "-" 100 true (fun x -> Term.App (MIN, [x]))

        addInfixOperator "=" 70 Associativity.Left (fun e1 e2 -> Term.App (EQ, [e1; e2]))
        addInfixOperator "!=" 70 Associativity.Left (fun e1 e2 -> Term.App(NOT, [Term.App (EQ, [e1; e2])]))
        addInfixOperator "<=" 70 Associativity.Left (fun e1 e2 -> Term.App (LE, [e1; e2]))
        addInfixOperator ">=" 70 Associativity.Left (fun e1 e2 -> Term.App (GE, [e1; e2]))
        addInfixOperator "<" 70 Associativity.Left (fun e1 e2 -> Term.App (LT, [e1; e2]))
        addInfixOperator ">" 70 Associativity.Left (fun e1 e2 -> Term.App (GT, [e1; e2]))

        addInfixOperator "&" 50 Associativity.Left (fun e1 e2 -> Term.App (AND, [e1; e2]))
        
        addInfixOperator "|" 40 Associativity.Left (fun e1 e2 -> Term.App (OR, [e1; e2]))
        addPrefixOperator "!" 60 true (fun x -> Term.App (NOT, [x]))
        addInfixOperator "=>" 30 Associativity.Left (fun e1 e2 -> Term.App (IMPLIES, [e1; e2]))

        addPrefixOperator "str.len" 90 true (fun e1 -> Term.App (LEN, [e1]))

        addTernaryOperator "?" ":" 30 Associativity.None (fun s1 s2 s3 -> Term.App (ITE, [s1; s2; s3]))

        let basicParser = 
            spaces >>. choice [ 
                (attempt variableParser)
                intConstParser
                stringConstParser
                boolConstParser
                parParser
            ] .>> spaces


        opp.TermParser <- basicParser

        do termParserRef.Value <- opp.ExpressionParser

        termParser

    let private functionDefinitionParser (varParser : Parser<'T,_>) = 
        let argParser = 
            skipChar '(' >>. varParser .>> spaces .>>. sortParser .>> spaces .>> skipChar ')'

        pipe4 
            (varParser .>> spaces)
            (skipChar '(' >>. spaces >>. many (argParser .>> spaces) .>> spaces .>> skipChar ')' .>> spaces)
            (sortParser .>> spaces)
            (termParser varParser)
            (fun a b c d -> 
                {
                    SmtFunctionDefinition.Symbol = a 
                    SmtFunctionDefinition.Arguments = b 
                    SmtFunctionDefinition.Sort = c 
                    SmtFunctionDefinition.Term = d
                }
            )

    let private modelResponseParser varParser =   
        skipString "(define-fun" >>. spaces >>. functionDefinitionParser varParser .>> spaces .>> skipChar ')'

    /// Given a variable parser, construct a parser for a model returned by Z3
    let private modelParser (varParser : Parser<'T, _>) =
        spaces >>. skipChar '(' >>. spaces >>.  many (modelResponseParser varParser .>> spaces) .>> spaces .>> skipChar ')'
        

    /// Given a parser for variables, parses a given string to a term
    let parseTerm s = 
        let parser = 
            spaces >>. termParser symbolParser .>> spaces .>> eof
        let res = run parser s
        match res with
            | Success (res, _, _) -> Result.Ok res
            | Failure (err, _, _) -> Result.Error err

    
    /// Given a variable parser and a string, parse the string to a model
    let parseModel (s : string) = 
        let parser = modelParser symbolParser .>> spaces .>> eof
        let res = run parser s
        match res with
            | Success (res, _, _) -> Result.Ok res
            | Failure (err, _, _) -> Result.Error err

   
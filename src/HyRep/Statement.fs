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

module Statement 

open System
open System.Collections.Generic
open FSharp.Collections

open Util
open SMT

type Var = String

type VarType = 
    | IntType
    | BoolType
    | StringType

module VarType = 
    let asSMTSort (t : VarType) = 
        match t with 
        | IntType -> SmtSort.INT
        | BoolType -> SmtSort.BOOL
        | StringType -> SmtSort.STRING
            

type TypeMapping = Map<Var, VarType>

type HoleId = string

type ExpressionOperator =   
    | ADD 
    | SUB 
    | MUL 
    | MIN 
    //
    | NOT 
    | AND
    | OR
    //
    | EQ 
    | LE 
    | GE 
    | LT 
    | GT 
    //
    | ITE
    //
    | APP 
    | LEN

module ExpressionOperator = 
    let toSmtOperator o = 
        match o with 
        | ADD -> SmtOperator.ADD
        | SUB -> SmtOperator.SUB
        | MUL -> SmtOperator.MUL
        | MIN -> SmtOperator.MIN
        //
        | NOT -> SmtOperator.NOT
        | AND -> SmtOperator.AND
        | OR -> SmtOperator.OR
        //
        | EQ -> SmtOperator.EQ
        | LE -> SmtOperator.LE
        | GE -> SmtOperator.GE
        | LT -> SmtOperator.LT
        | GT -> SmtOperator.GT
        //
        | ITE -> SmtOperator.ITE
        //
        | APP -> SmtOperator.APP
        | LEN -> SmtOperator.LEN

    let fromSmtOperator o = 
        match o with 
        | SmtOperator.ADD -> ADD
        | SmtOperator.SUB -> SUB
        | SmtOperator.MUL -> MUL
        | SmtOperator.MIN -> MIN
        //
        | SmtOperator.NOT -> NOT
        | SmtOperator.AND -> AND
        | SmtOperator.OR -> OR
        | SmtOperator.IMPLIES -> raise <| GeneralError "Cannot convert implies to program expression"
        //
        | SmtOperator.EQ -> EQ
        | SmtOperator.LE -> LE
        | SmtOperator.GE -> GE
        | SmtOperator.LT -> LT
        | SmtOperator.GT -> GT
        //
        | SmtOperator.ITE -> ITE
        //
        | SmtOperator.APP -> APP
        | SmtOperator.LEN -> LEN
        //
        | SmtOperator.FreeFunction _ -> raise <| GeneralError "Cannot convert free function to expression"
        
type Expression<'T when 'T: comparison> = 
    | IntConst of int
    | BoolConst of bool
    | StringConst of string
    | Var of 'T
    | App of ExpressionOperator * list<Expression<'T>>
    //
    | Hole of HoleId * list<Expression<'T>>

module Expression = 

    let rec usedVars (e : Expression<'T>) = 
        match e with 
        | IntConst _ | BoolConst _ | StringConst _ -> Set.empty
        | Var x -> Set.singleton x 
        | App(_, args) -> args |> List.map usedVars |> Set.unionMany
        | Hole(_, args) -> args |> List.map usedVars |> Set.unionMany

    let rec usedHoleIds (e : Expression<'T>) = 
        match e with 
        | IntConst _ | BoolConst _ | StringConst _ | Var _ -> Set.empty
        | Hole(n, args) -> args |> List.map usedHoleIds |> Set.unionMany |> Set.add n
        | App(_, args) -> args |> List.map usedHoleIds |> Set.unionMany


    let rec inferType (typeEnv : 'T -> VarType) (e : Expression<'T>) = 
        match e with 
        | IntConst _ -> IntType |> Some
        | BoolConst _ -> BoolType |> Some
        | StringConst _ -> StringType |> Some
        | Var x -> typeEnv x |> Some
        // ============== Arithmetic Functions ==============
        | App (ADD, [e1; e2]) | App (SUB, [e1; e2]) | App (MUL, [e1; e2]) -> 
            match inferType typeEnv e1, inferType typeEnv e2 with 
            | Some IntType, Some IntType -> Some IntType
            | _ -> None
        | App (MIN, [e]) ->
            match inferType typeEnv e with 
            | Some IntType -> Some IntType
            | _ -> None
        | App (LE, [e1; e2]) | App (GE, [e1; e2])| App (LT, [e1; e2])| App (GT, [e1; e2]) -> 
            match inferType typeEnv e1, inferType typeEnv e2 with 
            | Some IntType, Some IntType -> Some BoolType
            | _ -> None
        // ============== Bool Functions ==============
        | App (NOT, [e]) ->
            match inferType typeEnv e with 
            | Some BoolType -> Some BoolType
            | _ -> None
        | App (AND, [e1; e2]) | App (OR, [e1; e2]) ->
            match inferType typeEnv e1, inferType typeEnv e2 with 
            | Some BoolType, Some BoolType -> Some BoolType
            | _ -> None
        
        // ============== String Functions ==============
        | App (APP, [e1; e2]) -> 
            match inferType typeEnv e1, inferType typeEnv e2 with 
            | Some StringType, Some StringType -> Some StringType
            | _ -> None
        | App (LEN, [e1]) -> 
            match inferType typeEnv e1 with 
            | Some StringType -> Some IntType
            | _ -> None
        // ============== General Functions ==============
        | App (EQ, [e1; e2]) -> 
            match inferType typeEnv e1, inferType typeEnv e2 with 
            | Some x, Some y when x = y -> Some BoolType
            | _ -> None
        | App (ITE, [e1; e2; e3]) ->
            match inferType typeEnv e1, inferType typeEnv e2, inferType typeEnv e3 with 
            | Some BoolType, Some t1, Some t2 when t1 = t2 -> Some t1 
            | _ -> None
        // ============== Hole Functions ==============
        | Hole _ -> 
            None
        | App (_, _) -> 
            None

    
    let rec map f (e : Expression<'T>) = 
        match e with 
        | IntConst c -> IntConst c 
        | StringConst c -> StringConst c 
        | BoolConst c -> BoolConst c 
        | Var x -> Var (f x) 
        | App(o, args) -> App(o, args |> List.map (map f))
        | Hole(n, args) -> Hole(n, args |> List.map (map f))

    let rec bind f (e : Expression<'T>) = 
        match e with 
        | IntConst c -> IntConst c 
        | StringConst c -> StringConst c 
        | BoolConst c -> BoolConst c 
        | Var x -> f x
        | App(o, args) -> App(o, args |> List.map (bind f))
        | Hole(n, l) -> Hole(n, l |> List.map (bind f))

    let rec asTerm (e : Expression<'T>) = 
        match e with 
        | IntConst c -> Term.IntConst c 
        | StringConst c -> Term.StringConst c 
        | BoolConst c -> Term.BoolConst c 
        | Var x -> Term.Var x 
        | App(f, args) -> Term.App(ExpressionOperator.toSmtOperator f, args |> List.map asTerm)
        | Hole (f, args) -> Term.App(SmtOperator.FreeFunction f, args |> List.map asTerm)

    let rec fromTerm (t : Term<'T>) = 
        match t with 
        | Term.IntConst c -> IntConst (int c)
        | Term.StringConst c -> StringConst c 
        | Term.BoolConst c -> BoolConst c 
        | Term.Var x -> Var x 
        | Term.App(f, args) -> App(ExpressionOperator.fromSmtOperator f, args |> List.map fromTerm)
        | Exists _ | Forall _ | Let _ -> failwith ""   

type FunctionName = string

type Statement<'L when 'L: comparison> = 
    | Skip
    | VarAssign of Var * Expression<Var>
    | If of Expression<Var> * list<'L> * list<'L>
    | Assume of Expression<Var>
    | While of Expression<Var> * list<'L>
    | FunctionCallAssign of list<Var> * FunctionName * list<Expression<Var>>
    //
    | Observe


type FunctionBody<'L, 'A when 'L: comparison> = 
    {
        Arguments : list<Var>
        ReturnTypes : list<VarType>
        ReturnExpressions : list<Expression<Var>>

        TypeMapping : Map<Var, VarType>
        LocationMap : Map<'L, Statement<'L> * 'A>
        Locations : list<'L>
    }

module FunctionBody = 
    
    let containsLoops (body : FunctionBody<'L, 'A>) =
        body.LocationMap
        |> Map.values
        |> Seq.exists (fun (s, _) -> match s with While _ -> true | _ -> false)
       
type Program<'L, 'A when 'L: comparison> =  
    {
        Functions : Map<FunctionName, FunctionBody<'L, 'A>>
        MainFunction : FunctionName;
    }

type Annotation = 
    {
        AssignedVariables : Set<Var>
        Marker : option<string>
    }

type DefaultAnnotation = 
    {
        Marker : option<string>
    }

module Program = 
    let containsLoops (p : Program<'L, 'A>) = 
        p.Functions
        |> Map.values
        |> Seq.exists FunctionBody.containsLoops

    let rec usedFunctions (p : FunctionBody<'L, 'A>) = 
        p.LocationMap
        |> Map.values
        |> Seq.map fst
        |> Seq.choose (function 
            | FunctionCallAssign (_, name, _) -> Some name 
            | _ -> None
            )
        |> set

    let replaceExpression (p : Program<'L, 'A>) (functionName : FunctionName, l : 'L) (newE : Expression<Var>) = 
        {
            p with 
                Functions = 
                    p.Functions
                    |> Map.add functionName (
                        {p.Functions.[functionName] with 
                            LocationMap = 
                                p.Functions.[functionName].LocationMap
                                |> Map.add l (
                                        match p.Functions.[functionName].LocationMap.[l] with 
                                        | VarAssign (x, _), a -> VarAssign(x, newE), a
                                        | If (_, s1, s2), a -> If(newE, s1, s2), a
                                        | While (_, s1), a -> While(newE, s1), a
                                        | _ -> failwith ""
                                    )
                            }
                    )
        }

    exception private FoundError of string

    type private CurrentContext = 
        {
            AssignedVariables : Set<Var>
        }

    let rec annotateProgram (program : Program<'L, DefaultAnnotation>) = 
        let annotateFunctionBody(functionBody : FunctionBody<'L, DefaultAnnotation>) =  
            let annotatedLocationMap = new Dictionary<_,_>()

            let rec check (visitedLocation : Set<'L>) (context : CurrentContext) (l : 'L) = 
                let varEnv x = 
                    if Set.contains x context.AssignedVariables |> not then 
                        raise <| FoundError $"Variable {x} is used in an assignment expression but not initiated"
                    else 
                        functionBody.TypeMapping.[x]

                let s, a = functionBody.LocationMap.[l]

                annotatedLocationMap.Add (l, (s, {Annotation.AssignedVariables = context.AssignedVariables; Marker = a.Marker}))

                match s with 
                | Skip -> 
                    context 
                | Observe -> 
                    context
                | VarAssign(x, e) -> 
                    if functionBody.TypeMapping.ContainsKey x |> not then 
                        raise <| FoundError $"Variable {x} is assigned but not declared"

                    match Expression.inferType varEnv e with 
                    | Some t -> 
                        if t <> functionBody.TypeMapping.[x] then
                            raise <| FoundError $"In assignment %s{x} := %A{e} the type of %s{x} (%A{functionBody.TypeMapping.[x]}) does not match that of the expression (%A{t})"
                    | _ -> 
                        raise <| FoundError $"In assignment %s{x} := %A{e} the expression could not be typed."

                    {context with AssignedVariables = Set.add x context.AssignedVariables}
                | If (e, s1, s2) -> 
                    match Expression.inferType varEnv e with 
                    | Some BoolType -> ()
                    | _ -> 
                        raise <| FoundError $"In conditional: expression %A{e} could not be typed with bool"

                    let c1 = checkList (Set.add l visitedLocation) context s1 
                    let c2 = checkList (Set.add l visitedLocation) context s2

                    {context with AssignedVariables = Set.intersect c1.AssignedVariables c2.AssignedVariables}
                | Assume (e) -> 
                    match Expression.inferType varEnv e with 
                    | Some BoolType -> () 
                    | _ -> raise <| FoundError $"In assume: expression %A{e} could not be typed with bool"

                    {context with AssignedVariables = context.AssignedVariables}

                | While(e, s1) -> 
                    match Expression.inferType varEnv e with 
                    | Some BoolType -> () 
                    | _ -> raise <| FoundError $"In while loop: expression %A{e} could not be typed with bool"

                    let c1 = checkList (Set.add l visitedLocation) context s1 
                    
                    {context with AssignedVariables = c1.AssignedVariables}
                | FunctionCallAssign (r, functionName, args) -> 
                    let f = program.Functions.[functionName]

                    let retTypes = f.ReturnTypes
                    let argTypes = f.Arguments |> List.map (fun x -> f.TypeMapping.[x])

                    if List.length r <> List.length retTypes then 
                        raise <| FoundError $"In call to %s{functionName}: Mismatch in return dimension"

                    if List.length args <> List.length argTypes then 
                        raise <| FoundError $"In call to %s{functionName}: Mismatch in argument dimension"

                    List.zip r retTypes
                    |> List.iteri (fun i (x, t) -> 
                        if functionBody.TypeMapping.[x] <> t then 
                            raise <| FoundError $"In Call to %s{x}: Mismatch in the type of the %i{i}th return"   
                    )

                    List.zip args argTypes
                    |> List.iteri (fun i (e, t) -> 
                        match Expression.inferType varEnv e with 
                        | Some t' -> 
                            if t <> t' then 
                                raise <| FoundError $"In Call to %s{functionName}: Mismatch in the type of the %i{i}th argument."   
                        | None -> 
                            raise <| FoundError $"In Call to %s{functionName}: The %i{i}th argument could not be typed."   
                    )

                    {context with AssignedVariables = Set.union (set r) context.AssignedVariables}
                        
            and checkList (visitedLocation : Set<'L>) (context : CurrentContext) (locationList : list<'L>) = 
                match locationList with 
                | [] -> context 
                | l :: xs -> 
                    let c1 = check visitedLocation context l 
                    checkList (Set.add l visitedLocation) c1 xs


            let initContext = 
                {
                    CurrentContext.AssignedVariables = functionBody.Arguments |> set
                }

            // Run over the program, we do not care about the context after execution, this will fill annotatedLocationMap
            let _ = checkList Set.empty initContext functionBody.Locations


            {
                Arguments = functionBody.Arguments
                ReturnTypes = functionBody.ReturnTypes
                ReturnExpressions = functionBody.ReturnExpressions

                TypeMapping = functionBody.TypeMapping
                LocationMap = annotatedLocationMap |> Util.dictToMap
                Locations = functionBody.Locations
            }

            
        try 

            // Check for cycles in the call graph
            let g = 
                program.Functions
                |> Map.map (fun _ functionBody -> usedFunctions functionBody)

            program.Functions
            |> Map.iter (fun name f -> 
                usedFunctions f
                |> Set.iter (fun n -> 
                    if Map.containsKey n g |> not then 
                        raise <| FoundError $"Function %s{name} calls function %s{n} which is not defined"
                    )
                )

            if Util.GraphUtil.hasCycle g then 
                raise <| FoundError $"A cycle in the call graph. This is not supported"

            {
                Program.MainFunction = program.MainFunction
                Functions = 
                    program.Functions
                    |> Map.map (fun _ x -> annotateFunctionBody x)
            }
            |> Result.Ok

        with 
        | FoundError err -> Result.Error err

type private AlgebraicStatement = 
    | Skip
    | VarAssign of Var * Expression<Var>
    | If of  Expression<Var> * list<AlgebraicStatement> * list<AlgebraicStatement>
    | Assume of Expression<Var>
    | While of Expression<Var> * list<AlgebraicStatement>
    | FunctionCallAssign of list<Var> * FunctionName * list<Expression<Var>>
    | Observe
    | MarkedStatement of string * AlgebraicStatement

module private AlgebraicStatement = 
    let rec convertToStatement (labelGenerator : unit -> 'L) (s : AlgebraicStatement) = 
        match s with 
        | Skip -> 
            let l = labelGenerator()
            l, Map.ofList [l, (Statement.Skip, {DefaultAnnotation.Marker = None})]
        | VarAssign(x, e) -> 
            let l = labelGenerator()
            l, Map.ofList [l, (Statement.VarAssign(x, e), {DefaultAnnotation.Marker = None})]
        | Assume e -> 
            let l = labelGenerator()
            l, Map.ofList [l, (Statement.Assume e, {DefaultAnnotation.Marker = None})]
        | Observe -> 
            let l = labelGenerator()
            l, Map.ofList [l, (Statement.Observe, {DefaultAnnotation.Marker = None})]
        | FunctionCallAssign(a, b, c) -> 
            let l = labelGenerator()
            l, Map.ofList [l, (Statement.FunctionCallAssign(a, b, c), {DefaultAnnotation.Marker = None})]
        | If(e, s1, s2) -> 
            let l = labelGenerator()
            let r1 = s1 |> List.map (convertToStatement labelGenerator)
            let r2 = s2 |> List.map (convertToStatement labelGenerator)

            let m = Util.mergeMapsMany (List.map snd r1 @ List.map snd r2)
        
            l, Map.add l (Statement.If(e, List.map fst r1, List.map fst r2), {DefaultAnnotation.Marker = None}) m
        | While(e, s1) -> 
            let l = labelGenerator()
            let r1 = s1 |> List.map (convertToStatement labelGenerator)

            let m = Util.mergeMapsMany (List.map snd r1)
        
            l, Map.add l (Statement.While(e, List.map fst r1), {DefaultAnnotation.Marker = None}) m
        | MarkedStatement (marker, s1) -> 
            let l, m = convertToStatement labelGenerator s1

            let statement, an = m.[l]

            // Overwrite the map to mark the statement
            l, Map.add l (statement, {an with Marker = Some marker}) m 


module Parser = 
    open FParsec

    let commentLineParser =
        (skipString "//" .>> restOfLine false)

    let commentBlockParser =
        skipString "/*" >>. manyCharsTill anyChar (skipString "*/")
        |>> ignore

    let ws = spaces .>> sepEndBy (commentLineParser <|> commentBlockParser) spaces // whitespace and comment parser

    let private keywords = 
        [
            "if";
            "else";
            "while";
            "int";
            "bool";
            "proc";
            "return";
            "observe";
            "str.++";
            "str.len";
        ]

    let variableParser =
        Util.ParserUtil.programVariableParser
        >>= (fun x -> 
            if List.contains x keywords then 
                fail ""
            else 
                preturn x
            )

    let functionNameParser = variableParser

    /// Given a parser for variables, construct a parser for SMT Lib formulas
    let private expressionParser (atomParser : Parser<'T, unit>) = 
        let expressionParser, expressionParserRef  = createParserForwardedToRef()
        
        let varParser =
            atomParser .>> ws
            |>> Var

        let boolConstParser =
            stringReturn "true" (Expression.BoolConst true) <|> stringReturn "false" (Expression.BoolConst false)

        let intConstParser =
            pint32 |>> IntConst

        let stringConstParser =
            between (skipChar '"') (skipChar '"') (manyChars (satisfy (fun c -> c <> '"')))
            |>> StringConst

        let ifParser = 
            pipe3
                (skipString "if" >>. ws >>. expressionParser .>> ws)
                (skipString "then" >>. ws >>. expressionParser .>> ws)
                (skipString "else" >>. ws >>. expressionParser .>> ws)
                (fun a b c -> App(ITE, [a; b; c]))

        let parParser =
            skipString "("
            >>.
            expressionParser
            .>> skipChar ')'

    
        let opp = new OperatorPrecedenceParser<Expression<'T>, unit, unit>()

        // a helper function for adding infix operators to opp
        let addInfixOperator string precedence associativity f =
            opp.AddOperator(
                InfixOperator(string, ws, precedence, associativity, f)
            )

        let addPrefixOperator string precedence associativity f =
            opp.AddOperator(
                PrefixOperator(string, ws, precedence, associativity, f)
            )

        let addTernaryOperator leftString rightString precedence associativity f =
            opp.AddOperator(
                TernaryOperator(leftString, ws, rightString, ws, precedence, associativity, f)
            )


        addInfixOperator "str.++" 90 Associativity.Left (fun e1 e2 -> App(APP, [e1; e2]))
       
        addInfixOperator "+" 90 Associativity.Left (fun e1 e2 -> App(ADD, [e1; e2]))
        addInfixOperator "*" 95 Associativity.Left (fun e1 e2 -> App(MUL, [e1; e2]))
        addInfixOperator "-" 80 Associativity.Left (fun e1 e2 -> App(SUB, [e1; e2]))
        addPrefixOperator "-" 100 true (fun x -> App(MIN, [x]))

        addInfixOperator "==" 70 Associativity.None (fun e1 e2 -> App(EQ, [e1; e2]))
        addInfixOperator "!=" 70 Associativity.None (fun e1 e2 -> App(NOT, [App(EQ, [e1; e2])]))
        addInfixOperator "<=" 70 Associativity.None (fun e1 e2 -> App(LE, [e1; e2]))
        addInfixOperator ">=" 70 Associativity.None (fun e1 e2 -> App(GE, [e1; e2]))
        addInfixOperator "<" 70 Associativity.None (fun e1 e2 -> App(LT, [e1; e2]))
        addInfixOperator ">" 70 Associativity.None (fun e1 e2 -> App(GT, [e1; e2]))

        addInfixOperator "&&" 50 Associativity.Left (fun e1 e2 -> App(AND, [e1; e2]))
        addInfixOperator "||" 40 Associativity.Left (fun e1 e2 -> App(OR, [e1; e2]))
        addPrefixOperator "!" 60 true (fun x -> App(NOT, [x]))

        addPrefixOperator "str.len" 90 true (fun e1 -> App(LEN, [e1]))

        addTernaryOperator "?" ":" 30 Associativity.None (fun e1 e2 e3 -> App(ITE, [e1; e2; e3]))
        

        let basicParser = 
            ws >>. choice [ 
                boolConstParser 
                stringConstParser
                intConstParser
                ifParser
                parParser
                intConstParser
                varParser
            ] .>> ws


        opp.TermParser <- basicParser

        do expressionParserRef.Value <- opp.ExpressionParser
        
        expressionParser

    let typeParser = 
        (stringReturn "int" VarType.IntType)
        <|>
        (stringReturn "bool" VarType.BoolType)
        <|>
        (stringReturn "string" VarType.StringType)


    let statementParser labelGenerator = 
        let statementParser, statementParserRef  = createParserForwardedToRef()

        let statementListParser = many1 statementParser

        let assumeParser = 
            skipString "assume" >>. ws >>. (expressionParser variableParser)
            |>> Assume

        let skipParser =  
            stringReturn "skip" Skip

        let callParser =  
            pipe3
                (skipString "call" >>. ws >>. sepBy1 (variableParser .>> ws) (skipChar ',' .>> ws) .>> ws .>> skipString "=" .>> ws)
                (functionNameParser .>> ws)
                (skipChar '(' >>. sepBy1 ((expressionParser variableParser) .>> ws) (skipChar ',' .>> ws) .>> ws .>> skipChar ')')
                (fun ret functionName args -> FunctionCallAssign(ret, functionName, args))

        let assignParser = 
            attempt(
            variableParser .>> ws .>> skipChar '=' .>> ws
            >>= (fun v -> 
                    attempt(
                        expressionParser variableParser
                        |>> (fun e -> VarAssign(v, e)) 
                    )
                )
            )

        let observeParser = 
            stringReturn "observe" Observe


        let ifParser = 
            let elIfParser = 
                pipe2
                    (skipString "elif" >>. ws >>. (expressionParser variableParser) .>> ws)
                    (skipChar '{' >>. statementListParser .>> skipChar '}' .>> ws)
                    (fun g s -> (g, s))

            let elseParser = 
                (skipString "else" >>. ws >>. skipChar '{' >>. ws >>. statementListParser .>> skipChar '}')

            pipe4 
                (attempt (skipString "if" >>. ws >>. (expressionParser variableParser) .>> ws)) 
                (skipChar '{' >>. statementListParser .>> skipChar '}' .>> ws)
                (many (elIfParser .>> ws))
                (opt elseParser)
                (fun g m eif el -> 
                    let el = Option.defaultValue [] el
                    let a = 
                        (eif, el)
                        ||> List.foldBack (fun (g, s) x -> [If(g, s, x)])
                    If(g, m, a)
                    )

        let whileParser =  
            pipe2 
                (skipString "while" >>. ws >>. (expressionParser variableParser) .>> ws)
                (skipChar '{' >>. statementListParser .>> skipChar '}')
                (fun g p -> While(g, p))
            
        let parParser =  
            skipChar '{' >>. statementParser .>> skipChar '}'
    
        let markedStatementParser = 
            pipe2
                (skipChar '@' >>. ws >>. opt(skipChar '{' >>. ws >>. many1Chars (letter <|> digit) .>> ws .>> skipChar '}'))
                (ws >>. statementParser)
                (fun marker s -> MarkedStatement (marker |> Option.defaultValue "@", s))

        do 
            statementParserRef.Value <-
                ws >>. choice 
                    [
                        markedStatementParser
                        skipParser .>> ws .>> skipChar ';'
                        whileParser
                        callParser .>> ws .>> skipChar ';'
                        assumeParser .>> ws .>> skipChar ';'
                        ifParser
                        assignParser .>> ws .>> skipChar ';'
                        parParser
                        observeParser .>> ws .>> skipChar ';'
                    ] .>> ws

        statementListParser
        |>> fun x -> 
            x 
            |> List.map (AlgebraicStatement.convertToStatement labelGenerator)

    let typeDeclarationParser = 
        let typeMappingParser = 
            pipe2 
                (typeParser .>> spaces)
                (variableParser .>> ws .>> skipChar ';')
                (fun t x -> (x, t))

        ws >>. many (typeMappingParser .>> ws)
        |>> Map.ofList
    
    let private functionReturnTypeParser =  
        stringReturn "void" []
        <|>
        (sepBy1 (typeParser .>> ws) (skipChar ',' .>> ws))

    let functionDefinitionParser labelGenerator =
        Util.ParserUtil.pipe6
            functionReturnTypeParser
            (ws >>. functionNameParser .>> ws)
            (skipChar '(' >>. spaces >>. sepBy (typeParser .>>. (spaces >>. variableParser .>> spaces)) (skipChar ',' .>> spaces) .>> spaces .>> skipChar ')' .>> ws)
            (skipChar '{' >>. typeDeclarationParser .>> ws)
            (statementParser labelGenerator .>> ws)
            (opt (skipString "return" >>. ws >>. sepBy (expressionParser variableParser .>> ws) (skipChar ',' .>> ws) .>> ws .>> skipChar ';') .>> ws .>> skipChar '}')
            (fun returnTypes name args  typeMapping body returnExpressions -> 
                name, {
                    FunctionBody.Arguments = args |> List.map snd
                    ReturnTypes = returnTypes
                    ReturnExpressions = returnExpressions |> Option.defaultValue []
                    TypeMapping = 
                        Util.mergeMaps (args |> List.map (fun (x, y) -> (y, x)) |> Map.ofList) typeMapping 
                    LocationMap = body |> List.map snd |> Util.mergeMapsMany
                    Locations = body |> List.map fst
                }
            )

    let programParser labelGenerator = 
        ws >>. many (functionDefinitionParser labelGenerator .>> ws) .>> ws
        |>> fun functions -> 
            {
                Program.Functions = functions |> Map.ofList
                MainFunction = "main"
            }

     /// Given a parser for variables, parses a given string to a term
    let parseProgram (labelGenerator : unit -> 'L) (s: string) = 
        let parser = ws >>. programParser labelGenerator .>> ws .>> eof
        let res = run parser s
        match res with
            | Success (res, _, _) -> Result.Ok res
            | Failure (err, _, _) -> Result.Error err

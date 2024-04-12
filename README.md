# HyRep: Automated Program Repair For Hyperproperties

This repository contains HyRep - a SyGuS-based repair tool for hyperproperties. 
HyRep is based on the theory presented in 

> Beutner, Hsu, Bonakdarpour, Finkbeiner. Syntax-Guided Automated Program Repair for Hyperproperties. CAV 2024


## Structure 

This repository is structured as follows:

- `src/` contains the source code of HyRep (written in F#). 
- `app/` is the target folder for the build. The final HyRep executable will be placed here (when build from sources).
- `benchmarks/` contains various benchmarks.

## Build

You can either build HyRep from sources or use the provided Docker image. 
To get a quick startup, we recommend using the provided Docker image, as this already takes care of all the dependencies. 

### Dependencies

To build HyRep, you need the following dependencies:

- [.NET 7 SDK](https://dotnet.microsoft.com/en-us/download) (tested with version 7.0.203)
- [spot](https://spot.lrde.epita.fr/) (tested with version 2.11.6)
- [cvc5](https://cvc5.github.io/) (tested with version 1.0.8)

Install the .NET 7 SDK (see [here](https://dotnet.microsoft.com/en-us/download) for details).
Download and build _spot_ (details can be found [here](https://spot.lrde.epita.fr/)). 
Clone and build _cvc5_ (details can be found [here](https://cvc5.github.io/)). 
You can place the _spot_ and _cvc5_ executables in any location of your choosing, and provide HyRep with the _absolute_ path (see details below).

### Build HyRep

To build HyRep run the following (when in the main directory of this repository).

```shell
cd src/HyRep
dotnet build -c "release" -o ../../app
cd ../..
```

Afterward, the `HyRep` executable is located in the `app/` folder.

#### Connect Spot and CVC5 to HyRep

HyRep requires the _ltl2tgba_ executable from the spot library and the _cvc5_ executable. 
HyRep is designed such that it only needs the **absolute** path to these executables, so they can be installed and placed at whatever location fits best.
The absolute paths are specified in a `paths.json` configuration file. 
This file must be located in the *same* directory as the HyRep executables (this convention makes it easy to find the config file, independent of the relative path HyRep is called from). 
We provide a template file `app/paths.json` that **needs to be modified**. 
After having built _spot_ and _cvc5_, paste the absolute path to _spot_'s *ltl2tgba* and the _cvc5_ executable to the `paths.json` file. 
For example, if `/usr/bin/ltl2tgba` is the *ltl2tgba* executables and `/usr/cvc5/bin/cvc5` is the _cvc5_ executable, the content of `app/paths.json` should be

```json
{
    "ltl2tgba": "/usr/bin/ltl2tgba",
    "cvc5": "/usr/cvc5/bin/cvc5"
}
```

After you have modified the configuration file you can use HyRep by running the following
 
```shell
./app/HyRep <option> <instancePath>
```

where `<instancePath>` is the (path to the) input instance and `<option>` defines the operation that HyRep should perform.
A first example (useful for the smoke test) is given in Section [A first example](#a-first-example-smoke-test).


## A First Example (Smoke Test)

To test that the paths have been set up correctly, we can verify a small example instance from the paper. 
For this, run

```shell
./app/HyRep --verify ./benchmarks/iterative/1_edas/edas.txt
```

HyRep should output `UNSAT`.


# Input to HyRep

In this section, we first discuss the command-line options of HyRep, followed by the structure of supported input. 
A call to HyRep has the form `<opp> <instancePath>`, where `<instancePath>` is a (path to) the repair instance, and `<opp>` is the operation that HyRep should perform.

## Operations

HyRep supports multiple operations (`<opp>`):

- **Verification** (`--verify`) checks if the original program already satisfies the property
- **Repair** (`--repair`) tries to find _some_ repair that satisfies the property
- **Transparent Repair** (`--trans`) tries to find a _transparent_ repair
- **Iterative Repair** (`--iter`) iteratively tries to find better and better repairs


## Specifying Repair Instance 

A simple repair instance has the following basic format:

```
[program]
<program>

[formula]
<formula>

[outputs]
<var>
....
<var>
```

where `<program>`, `<formula>`, and `<var>` are defined below. 

**Comments:** 
Lines beginning with a `//` are comments and ignored during parsing. 
Multi-line comments have the form `/* .... */`. 

**Symbolic Execution Depth:**
If the program contains loops, HyRep bounds the depth of the symbolic execution.
By adding 

```
[depth]
<n>
```

to the input file (where `<n>` is a natural number), the user can specify the maximal execution depth.
If the loop contains loops, some depth _must_ be specified. 


**Iterative Repair Depth:**
During iterative repair, HyRep searches for better and better repairs, leading to a potentially infinite sequence of repairs.
By adding 

```
[iter]
<n>
```

to the input file (where `<n>` is a natural number), the user can specify the maximal number of iteration steps.
If this number is reached during repair, HyRep prints the most recent repair. 


### Specifying Programs

HyRep repairs programs in a simple imperative (`C`-like) programming language. 
To express asynchronous (hyper) properties, the language features explicit `observe` statements (cf. [1]).

Concretely, a program has the form 

```
void main(<type> <var>, ..., <type> <var>) {
    <type> <var>;
    ....
    <type> <var>;


    <statementList>

    return;
}
```

**Variables:**
Program variables (`<var>`) can be any (non-reserved) sequence consisting of letters and digits (starting with a letter).
_All_ variables used in the body of the function must be declared (either in the initial declaration of the function or via the function arguments).
The variables listed as arguments to the `main` function are considered as inputs.

**Types:**
Each variable is assigned a type.
Supported types (`<type>`) are `int`, `bool`, and `string`.

**Expressions:**
Expressions (`<expression>`) are defined as follows:
- `<var>`: Evaluates the value currently bound to the variable
- `<n>`, where `<n>` is any integer: Evaluates to the constant integer
- `true` (resp. `false`): Evaluates the boolean constant true (resp. false)
- `"<string>"`, where `<string>` is any sequence of characters not containing `"`: Evaluates to the string constant
- `<expression> <binOpp> <expression>`, where `<binOpp>` is a binary operator. Supported operations are `+`, `-`, `*`, `&&`, `||`, `==`, `!=`, `>=`, `<=`, `>`, `<`, and `str.++` (string concatenation).
- `<unOpp> <expression>`, where `<unOpp>` is an unary operator. Supported operations are `!` (negation) and `-` (unary minus).
- `<expression> ? <expression> : <expression>`


**Statements:**
Statements (`<statement>`) have the form 
- `skip`: Does nothing
- `<var> = <expression>;`: Assigns the result of evaluating of `<expression>` to variable `<var>`.
- `if <expression> {<statementList> else {<statementList>}`: Branches on whether or not `<expression>` evaluates to `true`.
- `while <expression> {<statementList>}`: Executes `<statementList>` as long as `<expression>` evaluates to `[t]`.
- `observe;`: Observes the current state (cf. [1])

A statement list (`<statementList>`) is a defined as sequence `<statement> <statement> .... <statement>` of statements. 

**Marked Statements:**
Additionally, statements can be marked (this will include all locations that qualify as repair candidates).
To mark a statement, write `@{<label>} <statement>`, where `<label>` is the label of this marked location (any string consisting of letters and digits not containing `}`).
If multiple locations are marked, the labels must be distinct. 
If there exists a single repair location, you can simply write `@ <statement>`, and HyRep will automatically use the predefined label `@`. 

#### Example

Consider the following example Boolean program.

```
void main(int amount, int balance)
{
    int ErrorLog;

    ErrorLog = 0;

    observe;
    if (amount > balance){
        balance = 0;
        ErrorLog = 1;
    }
    else {
        balance = balance - amount;
    }

    @{label1} balance = balance;

    observe;
    return;
}
```

### Specifying Hyperproperties

The property is defined in an extension of HyperLTL. 
A HyperLTL formula consists of an LTL-like body, preceded by a quantifier prefix of trace variables.
A trace variable (`<tvar>`) is any (non-reserved) sequence consisting of letters and digits (starting with a letter).

Formally, a Hyper2LTL formula has the form `<prefix> <body>`.

Here `<body>` can be one of the following:
- `1`: specifies the boolean constant true
- `0`: specifies the boolean constant false
- `{ <formula> }`, where `<formula>` is an expression over variables of the form `<var>_<tvar>`. Each variable `<var>_<tvar>` refers to the value of `<var>` on the trace bound to `<tvar>`.
- `(<body>)`: Parenthesis
- `<body> & <body>`: Conjunction
- `<body> | <body>`: Disjunction
- `<body> -> <body>`: Implication
- `<body> <-> <body>`: Equivalence
- `<body> U <body>`: Until
- `<body> W <body>`: Weak Until
- `<body> R <body>`: Release
- `F <body>`: Eventually
- `G <body>`: Globally
- `X <body>`: Next
- `! <body>`: Negation

The operators follow the usual operator precedences. To avoid ambiguity, we recommend always placing parenthesis around each construct. 

The quantifier prefix `<prefix>` can be one of the following:

- The empty string
- Universal or existential trace quantification `forall <tvar>. <prefix>` and `exists <tvar>. <prefix>`. 


An example property is the following: 

```
forall pi. forall pii. 
{0 < amount_pi} & {0 < amount_pii} & {0 < balance_pi} & {0 < balance_pii} & {balance_pi = balance_pii} 
-> 
G{ErrorLog_pi = ErrorLog_pii} 
```

Note that the formula is only evaluated on the observable states during the program's execution (s). 
See [1] for details on this asynchronous version of HyperLTL. 

### HyRep Output

Depending on the operation performed by HyRep the output differs. 
When run in `--verification` mode, HyRep outputs `SAT` or `UNSAT`.
When run in repair mode (`--repair`, `--trans`, or `--iter`) HyRep outputs repair expression.
Each output has the form 

```
================= SOLUTION =================
<label> : <expression>
...
<label> : <expression>
============================================
```
denoting a repair for each of the marked program statements. 
The final repair can be obtained by replacing the expression (e.g., the guard or assignment) at the specified location with the listed expression.

In general, HyRep's termination depends on the SyGuS solver. If the solver does not terminate (and, e.g., prove that no solution exists), neither does HyRep.

Note that when run in `--iter` mode, HyRep tries to produce a sequence of better and better repair candidates, which results in non-terminating behavior. 
Instead, HyRep will output all intermediate repairs it has found. 
By using the `[iter]` option in the repair instance, you can bound the number of iteration steps.  


## References

[1] Beutner, Hsu, Bonakdarpour, Finkbeiner. Syntax-Guided Automated Program Repair for Hyperproperties. CAV 2024

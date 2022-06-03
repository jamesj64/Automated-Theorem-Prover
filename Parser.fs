namespace Frosty

open System
open System.Text.RegularExpressions
open FParsec

module Parser =

    type Formula = 
        | Atom of string 
        | Not of Formula 
        | And of Formula * Formula 
        | Or of Formula * Formula 
        | Implies of Formula * Formula
        | Iff of Formula * Formula

    let parseAtom : Parser<Formula, unit>  = spaces >>. (many1Satisfy isLetter |>> Atom) .>> spaces

    let opp = new OperatorPrecedenceParser<Formula, unit, unit>()

    let parseFormula = opp.ExpressionParser

    let term =
        choice [
            attempt parseAtom
            attempt (between (pstring "(" >>. spaces) (pstring ")" >>. spaces) parseFormula)
        ]
    
    opp.TermParser <- term

    opp.AddOperator(InfixOperator("⇔", spaces, 1, Associativity.Right, fun x y -> Iff(x, y)))
    opp.AddOperator(InfixOperator("⇒", spaces, 2, Associativity.Right, fun x y -> Implies(x, y)))
    opp.AddOperator(InfixOperator("∨", spaces, 3, Associativity.Right, fun x y -> Or(x, y)))
    opp.AddOperator(InfixOperator("∧", spaces, 4, Associativity.Right, fun x y -> And(x, y)))
    opp.AddOperator(PrefixOperator("~", spaces, 5, true, Not))
    
    let prettyPrint formula =
        let rec prettyPrintF formula =
            match formula with
                | And(x, y) -> $"({prettyPrintF x} ∧ {prettyPrintF y})"
                | Or(x, y) -> $"({prettyPrintF x} ∨ {prettyPrintF y})"
                | Implies(x, y) -> $"({prettyPrintF x} ⇒ {prettyPrintF y})"
                | Iff(x, y) -> $"({prettyPrintF x} ⇔ {prettyPrintF y})"
                | Not x -> $"¬{prettyPrintF x}"
                | Atom x -> x
        formula |> (prettyPrintF >> fun x -> if x.[0] = '(' then x.Substring(1, x.Length - 2) else x)

    let prettyPrintMany formulas =
        List.map prettyPrint formulas
        |> List.fold (fun x y -> $"{x}\n{y}") ""

    let uglyPrint formula =
        let rec prettyPrintF formula =
            match formula with
                | And(x, y) -> $"({prettyPrintF x} & {prettyPrintF y})"
                | Or(x, y) -> $"({prettyPrintF x} || {prettyPrintF y})"
                | Implies(x, y) -> $"({prettyPrintF x} -> {prettyPrintF y})"
                | Iff(x, y) -> $"({prettyPrintF x} <-> {prettyPrintF y})"
                | Not x -> $"-{prettyPrintF x}"
                | Atom x -> x
        formula |> (prettyPrintF >> fun x -> if x.[0] = '(' then x.Substring(1, x.Length - 2) else x)

    let run parser str =
        let parser = parser .>> eof
        match run parser str with
            | Success (result, _, _) -> result
            | Failure (msg, _, _) -> failwith msg

    let parse str : Option<Formula> =
        try
            Some (run parseFormula str)
        with
            | _ -> None

    let rec format str =
        fun x -> Regex.Replace(x, "<-->|<->|≡|⟷", "⇔")
        >> fun x -> Regex.Replace(x, "-->|->|→|⊃", "⇒")
        >> fun x -> Regex.Replace(x, "!|¬|-", "~")
        >> fun x -> Regex.Replace(x, "&&|&", "∧")
        >> fun x -> Regex.Replace(x, "\|\||\|", "∨")
        >> fun x -> Regex.Replace(x, "\[", "(")
        >> fun x -> Regex.Replace(x, "\]", ")")
        <| str

    let splitPremisesChar str = 
        Regex.Split(str, "\n")
        |> Array.map (format >> parse)
        |> Array.filter (fun x -> x <> None)
        |> Array.map
            (fun x ->
                match x with
                    | Some x -> x
                    | _ -> failwith "this should never be called")
        |> List.ofArray

    let splitPremisesUnchar str =
        Regex.Split(str, "\n")
        |> Array.map (format >> parse >>
            (fun x ->
                match x with
                    | Some x -> x
                    | _ -> failwith "Could not parse input."))

    let prettyParse = 
        format >> parse
        >> function
            | Some x -> prettyPrint x
            | None -> "Could not parse input."

    let prettySplit str = Array.map prettyPrint (splitPremisesUnchar str)

    let firstAndLast (formulas: List<Formula>) = formulas.[formulas.Length - 1], List.take (formulas.Length - 1) formulas
        

    let singleParse str =
        let fm = (format >> parse) str
        match fm with
        | Some x -> x
        | _ -> failwith "Could not parse input"
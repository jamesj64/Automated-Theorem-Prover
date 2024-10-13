namespace Frosty

open FrostyProver
open Parser
open System

module Program =


    let helpPolish () =
        Console.ForegroundColor <- ConsoleColor.Yellow
        Console.WriteLine("\u001b[1mpolish\u001b[0m")
        Console.ResetColor()
        Console.WriteLine("Converts the supplied formula or list of formulas, each separated by a line, to Polish notation.")
        
    let helpFormat () =
        Console.ForegroundColor <- ConsoleColor.Yellow
        Console.WriteLine("\u001b[1mformat\u001b[0m")
        Console.ResetColor()
        Console.WriteLine("Formats the supplied formula or list of formulas, each separated by a line.")

    let properUsage () =
        // Use Console.WriteLine to display "Commands" in bold.
        Console.WriteLine("\u001b[1mCommands\u001b[0m")
        Console.WriteLine("------------------------------")

        // Set the console text color to yellow for command names
        Console.ForegroundColor <- ConsoleColor.Yellow
        Console.WriteLine("\u001b[1mprove\u001b[0m")
        Console.ResetColor()
        Console.WriteLine("Writes a natural deduction proof of the inputted formula/argument")

        Console.WriteLine()

        Console.ForegroundColor <- ConsoleColor.Yellow
        Console.WriteLine("\u001b[1mformat\u001b[0m")
        Console.ResetColor()
        Console.WriteLine("Formats the supplied formula or list of formulas, each separated by a line.")
        
        Console.WriteLine()
        
        Console.ForegroundColor <- ConsoleColor.Yellow
        Console.WriteLine("\u001b[1mpolish\u001b[0m")
        Console.ResetColor()
        Console.WriteLine("Converts the supplied formula or list of formulas, each separated by a line, to Polish notation.")
        
        Console.WriteLine()

        Console.ForegroundColor <- ConsoleColor.Yellow
        Console.WriteLine("\u001b[1mhelp\u001b[0m")
        Console.ResetColor()
        Console.WriteLine("Lists all commands. Specify a command to see more information about the given command.")

    let helpProve () =
        Console.WriteLine("\u001b[1mProve\u001b[0m")
        Console.WriteLine("------------------------------")
        Console.WriteLine("Writes a proof for a given formula/argument")
        Console.WriteLine()

        Console.WriteLine("\u001b[1mExample Usage\u001b[0m")
        Console.WriteLine()
        Console.WriteLine("./frosty prove 'p -> p'")
        Console.WriteLine("Explanation: attempts to prove the formula P ⇒ P is a tautology")
        Console.WriteLine()
        Console.WriteLine("./frosty prove 'p->q' 'q->r' 'p->r'")
        Console.WriteLine("Explanation: attempts to prove that the following arugment is valid")
        Console.WriteLine("1. P ⇒ Q")
        Console.WriteLine("2. Q ⇒ R")
        Console.WriteLine("3. P ⇒ R")
        Console.WriteLine()
        Console.WriteLine("Note that formulas should be placed in quotes.")
        Console.WriteLine()

        // Print "Allowed Symbols" in bold
        Console.WriteLine("\u001b[1mAllowed Symbols\u001b[0m")
        
        // Set the console text color to yellow for the symbols
        Console.ForegroundColor <- ConsoleColor.Yellow
        Console.WriteLine("Negation: `¬`, `~`, `!`, `-`")
        Console.WriteLine("Conjunction: `∧`, `&`, `&&`")
        Console.WriteLine("Disjunction: `∨`, `|`, `||`")
        Console.WriteLine("Material Conditional: `⇒`, `→`, `⊃`, `->`, `-->`")
        Console.WriteLine("Material Biconditional: `⇔`, `⟷`, `≡`, `<->`, `<-->`")
        Console.ResetColor()

        // Notify about allowed symbols
        Console.WriteLine("Any of the symbols listed above are allowed, in addition to parentheses, brackets, spaces, and letters.")
        Console.WriteLine()

        // Print "Additional Information about Syntax" in bold
        Console.WriteLine("\u001b[1mAdditional Information about Syntax\u001b[0m")
        
        // Write numbered points with normal text
        Console.WriteLine("1. Formulas should be written in infix notation.")
        Console.WriteLine("2. The truth-functional operators obey the standard precedence rules. The above operators are listed according to their relative precedence (descending).")
        Console.WriteLine("3. Each of the above binary operators is right-associative. For example, `P ⇒ Q ⇒ P` will be treated as `P ⇒ (Q ⇒ P)`.")

    let proveCommand (args: List<string>) =
        try
            let resp = ((fun (x, y) -> prove y x) << firstAndLast << parsePremisesChar) args
            printf "%s" resp
        with
        | exn ->
            printfn "%s" exn.Message

    [<EntryPoint>]
    let main (argv: string array) =
        Console.OutputEncoding <- Text.Encoding.UTF8
        if argv.Length > 1 then
            let command: string = argv.[0]
            let remainingArgs: List<string> = List.ofArray (Array.skip 1 argv)
            match command with
            | "prove" ->
                proveCommand remainingArgs
            | "polish" ->
                printf "%s" <| (polishPrintMany << parsePremisesChar) remainingArgs
            | "format" ->
                printfn "%s" <| (prettyPrintMany << parsePremisesChar) remainingArgs
            | "help" ->
                match argv.[1] with
                | "prove" ->
                    helpProve()
                | "polish" ->
                    helpPolish()
                | "format" ->
                    helpFormat()
                | _ ->
                    properUsage()
            | _ ->
                printfn "%s" "Incorrect Usage."
                properUsage()

        else
            properUsage()
        0 // return an integer exit code
namespace Frosty

open System.IO
open System.Threading.Tasks
open System.Collections.Generic
open Parser
open DSharpPlus
open DSharpPlus.CommandsNext.Attributes
open DSharpPlus.Entities
open DSharpPlus.Net
open DSharpPlus.Exceptions
open DSharpPlus.CommandsNext
open FrostyProver

type FrostyCommands() =

    inherit BaseCommandModule ()

    member private self.ping (ctx: CommandContext) = async {
        do! ctx.TriggerTypingAsync() |> Async.AwaitTask
        let emoji = DiscordEmoji.FromName(ctx.Client, ":ping_pong:")
        do! ctx.RespondAsync(sprintf "%s Pong! Socket latency: %ims" (string emoji) (ctx.Client.Ping)) |> Async.AwaitTask |> Async.Ignore
    }

    [<Command("ping"); Description("Responds with socket latency")>]
    member public self.pingAsync(ctx: CommandContext) =
        self.ping(ctx) |> Async.StartAsTask :> Task

    member private self.format (ctx: CommandContext, formula: string) = async {
        do! ctx.TriggerTypingAsync() |> Async.AwaitTask
        try
            do! ctx.RespondAsync((splitPremisesChar >> prettyPrintMany) formula) |> Async.AwaitTask |> Async.Ignore
        with
            _ -> do! ctx.RespondAsync("Could not parse input.") |> Async.AwaitTask |> Async.Ignore
    }

    [<Command("format"); Description("Formats formula")>]
    member public self.formatAsync (ctx: CommandContext, [<Description "Formula or list of formulas separated by line break to format"; RemainingText>] formula: string) =
        self.format(ctx, formula) |> Async.StartAsTask :> Task
    
    member private self.prove (ctx: CommandContext, formula: string) = async {
        do! ctx.TriggerTypingAsync() |> Async.AwaitTask
        try
            let response = (splitPremisesChar >> firstAndLast >> (fun (x,y) -> prove y x) >> stringifyProof) formula
            if response.Length > 2000 then
                do! ctx.RespondAsync("Valid. Proof too long to send.") |> Async.AwaitTask |> Async.Ignore
            else
                do! ctx.RespondAsync(response) |> Async.AwaitTask |> Async.Ignore
        with
            _ ->
                do! ctx.RespondAsync("Could not parse input.") |> Async.AwaitTask |> Async.Ignore
    }

    [<Command("prove"); Description("Formats formula")>]
    member public self.proveAsync (ctx: CommandContext, [<Description "Formula or list of formulas separated by line to prove"; RemainingText>] formula: string) =
        self.prove(ctx, formula) |> Async.StartAsTask :> Task
    
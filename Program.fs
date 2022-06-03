namespace Frosty

open System
open System.IO
open System.Text
open Newtonsoft.Json
open DSharpPlus
open DSharpPlus.Entities
open System.Threading.Tasks
open DSharpPlus.CommandsNext

module Program =

    type config = {
        token: string
        prefix: string
    }

    let loadConfig () =
        let utf8 = new UTF8Encoding false
        use fs = File.OpenRead("config.json")
        use sr = new StreamReader(fs, utf8)
        let json = sr.ReadToEnd()

        sr.Dispose()
        fs.Dispose()

        JsonConvert.DeserializeObject<config>(json)

    [<EntryPoint>]
    let main argv =
        let mConfig = loadConfig()

        let config = DiscordConfiguration ()
        config.Token <- mConfig.token
        config.TokenType <- TokenType.Bot
        config.AutoReconnect <- true
        
        let client = new DiscordClient(config)

        let commandConfig = CommandsNextConfiguration ()
        commandConfig.StringPrefixes <- [mConfig.prefix]

        let commands = client.UseCommandsNext(commandConfig)
        commands.RegisterCommands<FrostyCommands>()

        client.ConnectAsync(new DiscordActivity("?help", ActivityType.ListeningTo))
        |> Async.AwaitTask
        |> Async.RunSynchronously
        
        Task.Delay(-1)
        |> Async.AwaitTask
        |> Async.RunSynchronously
        0 // return an integer exit code
module Program

open System.Reflection
open Mono.Reflection
open System
open DecompileContext
open ExpressionTreeToString

[<EntryPoint>]
let main _ = 
    let printDebugInfo = true
    let template = 
        [
            //typeof<Template.While>
            //typeof<Template.List>
            //typeof<Template.If>
            //typeof<Template.DeepTransform>
            //typeof<Dish.Program.MoneyTransferContext>
            CSharp,false, typeof<csharp.Template>
        ]
    template
    |> Seq.map(fun (l,dt,t) ->
        (l,dt,t),
          t.GetMethods()
          |> Seq.filter(fun m ->
            m.DeclaringType = t
          )
    ) |> Seq.iter(fun ((l,dt,t),ms) -> 
         ms
         |> Seq.iter(fun m ->
            printfn $"Evaluating %s{m.Name}"
            let ``delegate`` =
                ExpressionTree.methodToExpressionTree true l m
            
            //printfn "%s" (Mono.Linq.Expressions.CSharp.ToCSharpCode(``delegate``))
            printfn "%s" (``delegate``.ToString("Factory methods", "C#"))
            
            let self = Activator.CreateInstance(t)
            let arguments = 
                 m.GetParameters()
                 |> Array.map(fun p -> 
                     if p.ParameterType.IsValueType then
                         Activator.CreateInstance(p.ParameterType) |> box 
                     else
                        null
                 ) 
            printfn $"Execute %s{m.Name}?"
            System.Console.ReadLine() |> ignore
            let res = ``delegate``.Compile().DynamicInvoke(arguments |> Array.append [|self|]) 
            let actualResult = m.Invoke(self,arguments)
            if res = actualResult then
                res
                |> unbox
                |> printfn "Method executed successfully. Result: %A"
            else 
                failwith $"Unexpected result got %A{res} but expected %A{actualResult}"
        )
    )
    0
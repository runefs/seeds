module Program

open System.Reflection
open Mono.Reflection
open System
open DecompileContext

let printAst (expr : DecompileContext.CompiledExpression) = 
    let rec innerPrint ident expr = 
        let identation = System.String(' ',ident)
        match expr with
        DecompileContext.Expr(_,e) -> printfn "%s%A" identation e
        | DecompileContext.CompiledExpression.Pop _ as p -> printfn "%s%A" identation p.Expression
        | DecompileContext.Exprs(exprs) -> 
            let ident = ident + 4
            printfn "Expr ("
            exprs 
            |> List.iter(innerPrint ident)
            printfn ")"
            
        | e -> failwithf "Can't print %A" e
    innerPrint 0 expr

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
             let methodBodyAst,parameters,variables =
                ExpressionTree.methodToExpressionTree l dt m
             if printDebugInfo then 
                printAst methodBodyAst
             let ``delegate`` = 
                 ExpressionTree.compile methodBodyAst parameters variables
             let self = Activator.CreateInstance(t)
             let arguments = 
                 m.GetParameters()
                 |> Array.map(fun p -> 
                     if p.ParameterType.IsValueType then
                         Activator.CreateInstance(p.ParameterType) |> box 
                     else
                        null
                 ) 
             let res = ``delegate``.DynamicInvoke(arguments |> Array.append [|self|]) 
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
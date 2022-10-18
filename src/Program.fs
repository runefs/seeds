module Program

open System.Reflection
open Mono.Reflection
open System
let printAst (expr : ExpressionTree.CompiledExpression) = 
    let rec innerPrint ident expr = 
        let identation = System.String(' ',ident)
        match expr with
        ExpressionTree.Expr(_,e) -> printfn "%s%A" identation e
        | ExpressionTree.CompiledExpression.Pop _ as p -> printfn "%s%A" identation p.Expression
        | ExpressionTree.Exprs(exprs) -> 
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
            typeof<Template.DeepTransform>
            //typeof<Dish.Program.MoneyTransferContext>
        ]
    template
    |> Seq.map(fun t ->
        t,t.GetMethods()
          |> Seq.filter(fun m ->
            m.DeclaringType = t
          )
    ) |> Seq.iter(fun (t,ms) -> 
         ms
         |> Seq.iter(fun m ->
             
             
             let methodBodyAst,parameters,variables =   
                 m
                 |> ExpressionTree.methodToExpressionTree true
             if printDebugInfo then 
                printAst methodBodyAst
             let ``delegate`` = 
                 ExpressionTree.compile methodBodyAst parameters variables
             let arguments = 
                 m.GetParameters()
                 |> Array.map(fun p -> 
                     if p.ParameterType.IsValueType then
                         Activator.CreateInstance(p.ParameterType) |> box 
                     else
                        null
                 ) |> Array.append [|Activator.CreateInstance(t) |]
             let res = ``delegate``.DynamicInvoke(arguments) 
             match res with
             null when m.ReturnType = typeof<System.Void> || m.ReturnType = typeof<unit> ->
                 printfn "Method executed successfully"
             | null -> 
                 printfn "Expected a value but got null"
             | res -> 
                 res
                 |> unbox
                 |> printfn "Method executed successfully. Result: %A"
        )
    )
    0
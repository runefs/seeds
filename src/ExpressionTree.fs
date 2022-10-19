module ExpressionTree

open System.Linq.Expressions
open System.Reflection
open System.Reflection.Emit
open DecompileContext

let methodToExpressionTree lang deepTransform (methodInfo : System.Reflection.MethodInfo) =
    DecompileContext(deepTransform,methodInfo)
    |> (match lang with
        Language.CSharp -> CSharpDecompiler.methodToExpressionTree
        | Language.FSharp -> failwith "Not implemented yet" //FSharpDecompiler.methodToExpressionTree
    )

let compile expr (parameters : ParameterExpression seq) variables = 
    let exprs = 
        match expr with
        Expr(_,e) -> [e]
        | CompiledExpression.Pop _ as p -> [p.Expression]
        | Exprs(exprs) -> 
            let exprs = 
                match exprs |> List.map(fun e -> e.Expression) |> List.rev with
                result::body -> 
                    result::(*(Expression.Label(DecompileContext.ReturnLabel) :> Expression)::*)body
                | [] -> []
            exprs |> List.rev
        | e -> failwithf "Don't know how to finish off with %A" e
    
    let expr = Expression.Block(variables |> Seq.map snd,exprs) :> Expression
    let lambda = Expression.Lambda(Expression.Block(expr),parameters)
#if DEBUG    
    printfn "%s" (Mono.Linq.Expressions.CSharp.ToCSharpCode(lambda))
#endif
    lambda.Compile() 
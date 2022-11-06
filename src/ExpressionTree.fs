module ExpressionTree

open System.Linq.Expressions
open DecompileContext

let methodToExpressionTree emitTrace lang (methodInfo : System.Reflection.MethodInfo) =
    let expr,variableCollection = 
        methodInfo
        |> (match lang with
            Language.CSharp -> CSharp.Decompiler.methodToExpressionTree emitTrace
            | Language.FSharp -> failwith "Not implemented yet" //FSharpDecompiler.methodToExpressionTree
        )
    printfn $"%s{expr.ToString()}"

    let lambda = Expression.Lambda(Expression.Block(expr),variableCollection.AllParameters)
    lambda

let compile (lambda : LambdaExpression)= 
    lambda.Compile() 
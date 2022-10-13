module CSharpDecompiler

open System.Linq.Expressions
open System.Reflection
open System.Reflection.Emit
open DecompileContext


let rec methodToExpressionTree (ctx : DecompileContext) =
    let rec inner (stack : Stack) instructions : BlockExpression = 
        let stack = 
            //remove redundant bunconditional branch to make it easier to interpret
            match stack.Peek() with
            None -> stack
            | Some (PartialExpr(Statement(UnconditionalBranch o)),_) ->
                match instructions with
                [] -> stack
                | (_,offset)::_ when o = offset -> stack.Pop() |> snd
                | _ -> stack
            | _ -> stack
        let readCondition condition = 
            //printfn "if true: %A" ifTrue   
            let lhs, rhs, stack = 
                match condition with
                False | True -> 
                    let (rhs : BlockExpression * int),stack = stack.Pop()
                    let lhs = 
                        if (rhs |> fst).Expression.Type = typeof<bool> then None
                        else Expression.Constant(1) :> Expression |> Some
                    lhs,rhs,stack
                | _ -> 
                    let lhs,stack = stack.Pop()
                    let rhs, stack = stack.Pop()
                    (lhs |> fst).Expression |> Some, rhs ,stack
 
            let conditionalOffset = rhs |> snd
            let rhs = (rhs |> fst).Expression
 
            let test = 
                 match lhs,condition with
                 Some lhs, GreaterThanEqual -> Expression.GreaterThanOrEqual(lhs,rhs) :> Expression
                 | Some lhs, GreaterThan -> Expression.GreaterThan(lhs,rhs) :> Expression
                 | Some lhs, LessThanEqual -> Expression.LessThanOrEqual(lhs,rhs) :> Expression
                 | Some lhs, LessThan -> Expression.LessThan(lhs,rhs) :> Expression
                 | Some lhs, NotEqual -> Expression.NotEqual(lhs,rhs) :> Expression
                 | Some lhs, Equal -> Expression.Equal(lhs,rhs) :> Expression
                 | None,True -> Expression.IsTrue rhs :> Expression
                 | None,False -> Expression.IsFalse rhs :> Expression
                 | Some lhs,True -> Expression.Equal(lhs,rhs) :> Expression
                 | Some lhs,False -> Expression.NotEqual(lhs,rhs) :> Expression
                 | None,condition -> failwithf "Not supported. %A is binary but only one argument provided" condition
            test,conditionalOffset,stack
        let readWhileBlock condition block = 
            let test, conditionalOffset, stack = readCondition condition
            let breakLabel = Expression.Label("break");
            let test =
                Expr(typeof<System.Void>,
                    Expression.IfThen(
                        Expression.Not(test),
                        Expression.Goto breakLabel) :> Expression)

            let body = 
                match inner Stack.Empty block with
                Exprs(exprs) -> exprs
                | Expr _ as e -> [e]
                | ex -> failwithf "Not implemented for while body %A" ex
            
            let whileBlock = 
                Exprs(test::body).Expression            
            let loop = 
                Expression.Loop(
                    whileBlock,
                    breakLabel
                )
            (Expr(typeof<System.Void>,loop :> Expression),conditionalOffset) |> stack.Push

        let readIfBlock condition ifTrue ifFalse =
           
           let _,lastOffset = 
               match ifTrue with
               [] -> ifFalse |> List.last
               | l -> l |> List.last
           let ifEndLabel = Expression.Label(sprintf "_IIF_target%d" lastOffset)
           let trim block =
                let block =  
                   match block with
                   [] -> block
                   | _ -> 
                       match block |> List.last with
                       Statement(Return),_ -> 
                           block |> List.take (block.Length - 1)
                       | _ -> block

                block
                |> List.map(function
                    Statement(Return),offset -> 
                        Statement(Goto ifEndLabel),offset
                    | i -> i
                )

           let ifTrueBlock = ifTrue |> trim |> inner Stack.Empty
           let ifFalseBlock = ifFalse |> trim |> inner Stack.Empty
           
           let gotoEnd = Expression.Goto(ifEndLabel)
           let ifResultType = ifFalseBlock.Type
           let resultOfIfExpression = 
               if ifResultType = typeof<unit> || ifResultType = typeof<System.Void> then
                   Expression.Label(Expression.Label("IF Result placeholder")) :> Expression
               else
                   ctx.GetOrCreateVariable ifResultType <| sprintf "__IIF__%d" lastOffset :> Expression
                   
           let trimBlock ifblock =
               
               let store result tail = 
                   if (ifResultType = typeof<unit> || ifResultType = typeof<System.Void>) |> not then
                       Expr(ifResultType,Expression.Assign(resultOfIfExpression, result))::tail
                   else
                       tail
               let trimmed =  
                   match ifblock with
                   Exprs(exprs) -> 
                        let exprs = 
                           match exprs |> List.rev with
                           PartialExpr(Statement (UnconditionalBranch _ ))::tail -> 
                               tail 
                           | exprs -> exprs

                        let exprs = 
                            match exprs
                                  |> List.filter(function
                                     PartialExpr(Statement(Nop)) -> false
                                     | _ -> true
                                  )  with
                            (Expr(_,e) as ret)::res::tail when (e :? GotoExpression) ->
                                ret::(store res.Value tail) |> List.rev
                            | res::tail ->
                                store res.Value tail |> List.rev
                            | [] -> []

                        Exprs(exprs)
                        
                   | e -> e
               Expr(typeof<System.Void>,gotoEnd)
               |> trimmed.Append
               
           let ifFalse = 
               ifFalseBlock
               |> trimBlock
           let ifTrue = 
               ifTrueBlock
               |> trimBlock
           
           //printfn "if true: %A" ifTrue   
           let test, conditionalOffset, stack = readCondition condition
           let ifBlock = 
               let exp = 
                   if ifTrueBlock = Empty then
                       Expression.IfThen(test,ifFalse.Expression) :> Expression 
                   else
                       Expression.IfThenElse(test,ifTrue.Expression,ifFalse.Expression) :> Expression 
               Expr(ifTrue.Type,exp)
         
           let block =
               ifBlock.Append(Expr(typeof<unit>,Expression.Label(ifEndLabel)))
                       .Append(Expr(ifTrue.Type,resultOfIfExpression))
           
           (block,conditionalOffset) |> stack.Push
        let readArguments isStatic (parameters : ParameterInfo []) = 
            let parameterCount = 
                if isStatic then
                    parameters.Length
                else
                    parameters.Length + 1
            let args,stack = 
                stack.Take parameterCount
            let convertArguments (arguments : (BlockExpression * int) list) = 
                arguments
                |> List.mapi(fun i (a,_) -> 
                    let exprType = a.Type
                    let parameterType = parameters.[i].ParameterType
                    if parameterType.IsAssignableFrom exprType then
                        a.Expression
                    elif parameterType.IsAssignableTo exprType then
                        Expression.Convert(a.Expression,parameterType) :> Expression
                    else
                        failwithf "Can't convert %A of type: %s to the required type of %s" a.Expression a.Type.Name parameterType.Name
                    )
            let args =  
                if isStatic then
                    args
                    |> convertArguments
                else
                    (args |> List.head |> fst).Expression::
                    (args
                    |> List.tail
                    |> convertArguments)
                |> Array.ofList
            let instance,args = 
                if isStatic then
                    None, if args.Length > 0 then args |> Some else None
                else 
                    assert(args |> Array.isEmpty |> not)
                    match args with
                    [|instance|] -> 
                        Some instance, None
                    | instanceAndArgs -> 
                        instanceAndArgs |> Array.head |> Some, instanceAndArgs |> Array.tail |> Some
            instance,args,stack
        let storeLocal index offset =
            let (value,_),stack = stack.Pop()
            let name = sprintf "local_%d" index
            let local =  ctx.GetOrCreateVariable value.Type name
            let expr =  Expression.Assign(local,value.Expression) :> Expression
            (Expr(value.Type,expr),offset) |> stack.Push

        let loadLocal index offset = 
            let name = sprintf "local_%d" index
            let var = ctx.GetVariable name
            (Expr(var.Type,var),offset) |> stack.Push
        match instructions with
        (Expression(LoadField(f)),_)::tail ->
            let (instance,instanceOffset),stack = stack.Pop()
            
            let exp = 
                Expression.Field(instance.Expression,f) :> Expression
            let expr = 
                Expr(f.FieldType, exp)
            inner ((expr,instanceOffset) |> stack.Push) tail
        | (Expression(This),offset)::tail ->
            let expr = 
                let arg = ctx.GetParameterExpressionByName "this"
                Expr(arg.Type, arg)
            inner ((expr,offset) |> stack.Push) tail
        | (Expression(Add),offset)::tail ->
            let (lhs,_),stack = stack.Pop()
            let (rhs,_),stack = stack.Pop()
            let expr = 
                Expr(lhs.Type,Expression.Add(lhs.Expression,rhs.Expression))
            inner ((expr,offset) |> stack.Push) tail
        | (Expression(CompareEqual),offset)::tail ->
            let (lhs,_),stack = stack.Pop()
            let (rhs,_),stack = stack.Pop()
            let expr = 
                Expr(typeof<bool>,Expression.Equal(lhs.Expression,rhs.Expression))
            inner ((expr,offset) |> stack.Push) tail
        | (Statement(Goto label),offset)::tail ->
            inner  ((Expr(typeof<System.Void>,Expression.Goto label),offset) |> stack.Push) tail
        | (Expression(Constant c),offset)::tail ->
            let expr = 
                match c with
                Byte n -> Expression.Constant(n,typeof<byte>)
                | Int16 n -> Expression.Constant(n,typeof<int16>)
                | Int n -> Expression.Constant(n,typeof<int>)
                | Int64 n -> Expression.Constant(n,typeof<int64>)
                | String n -> Expression.Constant(n,typeof<string>)
                | Single n -> Expression.Constant(n,typeof<single>)
                | Float n -> Expression.Constant(n,typeof<float>)
                | Null -> Expression.Constant(null)
                
            inner ((Expr(c.Type,expr :> Expression),offset) |> stack.Push) tail
        | (Expression(CtorInvocation c),offset)::tail ->
            let parameters = c.GetParameters()
            let _,args,stack = 
                parameters
                |> readArguments true
            assert((args.IsNone && parameters |> Array.isEmpty) || (args.Value.Length = parameters.Length))
            let expr = 
                match args with
                Some args -> 
                    Expression.New(c, args) :> Expression
                | None | Some [||] -> 
                    Expression.New(c) :> Expression
            inner ((Expr(c.DeclaringType,expr),offset) |> stack.Push) tail
        | (Expression(MethodInvocation m),offset)::tail ->
            let instance,args,stack = 
                m.GetParameters()
                |> readArguments m.IsStatic
            
            let expr = 
                //TODO: Handle recursive or indirectly recursive functions (A calling B calling A)
                //Pass in a function table for previously visited functions as an argument?
                if ctx.DeepTransform && m.DeclaringType = ctx.DeclaringType then
                    let expr, _, vars = methodToExpressionTree (DecompileContext(ctx.DeepTransform,m))
                    ctx.AddVariables vars
                    match args with
                    None -> expr
                    | Some args ->  
                        let localParams = 
                            m.GetParameters()               
                            |> Array.mapi(fun i param ->
                                i,param.Name
                            ) |> Map.ofArray
                        Exprs(
                            (args
                            |> List.ofArray
                            |> List.mapi(fun index a ->
                                
                                let varName = m.Name + "____param__" + localParams.[index]
                                match ctx.TryGetVariable varName with
                                None -> 
                                    printfn "Couldn't find %s in %A" varName ctx.Variables
                                    None
                                | Some variable -> 
                                    Expr(a.Type,Expression.Assign(variable,a) :> Expression) |> Some
                            ) |> List.filter Option.isSome
                            |> List.map Option.get
                            )@[expr]
                        )
                else
                    let expr = 
                        match instance,args with
                        None,None ->
                            Expression.Call(m) :> Expression
                        | Some instance, None ->
                            Expression.Call(instance,m) :> Expression
                        | None,Some args ->
                            Expression.Call(m, args) :> Expression
                        | Some instance, Some args ->
                            Expression.Call(instance,m, args) :> Expression
                    Expr(m.ReturnType,expr)
            inner ((expr,offset) |> stack.Push) tail
        |  (Statement (StoreLocal (Ordinal(iden))),offset)::tail ->
            inner (storeLocal iden offset) tail
        |  (Statement (StoreLocal (Builder(builder))),offset)::tail ->
            inner (storeLocal builder.LocalIndex offset) tail
        |  (Expression (LoadLocal (Ordinal(iden))),offset)::tail ->
            inner (loadLocal iden offset) tail
        |  (Expression (LoadLocal (Builder(builder))),offset)::tail ->            
            inner (loadLocal builder.LocalIndex offset) tail
        | (Statement(Pop),_)::tail ->
            let (exp,offset),stack = stack.Pop()
            let stack = (BlockExpression.Pop(exp),offset) |> stack.Push
              
            inner stack tail 
        | [] | [(Statement(Return),_)] -> 
            let expressions = 
                stack.ToList()
                |> List.filter(fun (expr,_) -> 
                    expr <> PartialExpr(Statement(Nop))
                )
                |> List.rev 
                |> List.map fst
            match expressions with
            [e] when e = Empty -> Empty
            | [e] -> (e.Type,e.Expression) |> Expr
            | [] -> Empty
            | exprs -> Exprs(exprs)
        | (Statement(Return),offset)::tail ->
            let returnType = ctx.ReturnType
            let result = ctx.Result
            let stack = 
                match stack.TryPop() with
                None -> stack
                | Some((e,_),stack) -> 
                    if returnType <> typeof<System.Void> && returnType <> typeof<unit> then
                        stack.Push(Expr(result.Type,Expression.Assign(result,e.Expression)), offset)
                    else
                        stack
            let stack = 
                (Expr(returnType,Expression.Return(DecompileContext.ReturnLabel)),offset) |> stack.Push
            let stack = 
                if returnType <> typeof<System.Void> && returnType <> typeof<unit> then
                    (Expr(returnType,result),offset) |> stack.Push
                else
                    stack
            inner stack tail
        | (Expression(LoadArgument ident),offset)::tail ->
            let arg = ctx.GetParameterExpression ident
            inner ((Expr(arg.Type,arg),offset) |> stack.Push) tail
        | (h,offset)::tail ->  
            inner ((PartialExpr h,offset) |> stack.Push) tail
    let expressionBlock = 
        match inner Stack.Empty ctx.Instructions with
        Exprs(exprs) -> 
            Exprs(exprs)
        | Expr _ as e -> Exprs([e])
        | b -> failwithf "Couldn't read the expression block %A" b
    let infoMap = ctx.ParameterOrdinals
    let arguments = 
        ctx.ParameterExpressions
        |> Seq.sortBy(fun (name,_) ->
            match infoMap |> Map.tryFind name with
            None -> -1
            | Some i -> i
        ) |> Seq.map(fun (_,exp) -> exp :?> ParameterExpression)
    expressionBlock, arguments, ctx.Variables
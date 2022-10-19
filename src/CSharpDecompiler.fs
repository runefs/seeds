module CSharpDecompiler

open System.Linq.Expressions
open System.Reflection
open System.Reflection.Emit
open DecompileContext

type Stack = Stack<CompiledExpression * int>

let rec methodToExpressionTree (ctx : DecompileContext) =
    let rec inner (stack : Stack) (instructions : (StackInstruction * int) list) : CompiledExpression = 

        let compileExpression offset e  = inner Stack.Empty [StackInstruction.Expression e,offset]
        let compileComparison offset =
            function
            GreaterThanEqual(lhs,rhs) -> 
                let lhs = compileExpression offset lhs
                let rhs = compileExpression offset rhs
                Expression.GreaterThanOrEqual(lhs.Expression,rhs.Expression)
            | GreaterThan(lhs,rhs) -> 
                let lhs = compileExpression offset lhs
                let rhs = compileExpression offset rhs
                Expression.GreaterThan(lhs.Expression,rhs.Expression)
            | LessThanEqual(lhs,rhs) -> 
                let lhs = compileExpression offset lhs
                let rhs = compileExpression offset rhs
                Expression.LessThanOrEqual(lhs.Expression,rhs.Expression)
            | LessThan(lhs,rhs) -> 
                let lhs = compileExpression offset lhs
                let rhs = compileExpression offset rhs
                Expression.LessThan(lhs.Expression,rhs.Expression)
            | NotEqual(lhs,rhs) -> 
                let lhs = compileExpression offset lhs
                let rhs = compileExpression offset rhs
                Expression.NotEqual(lhs.Expression,rhs.Expression)
            | Equal(lhs,rhs) -> 
                let lhs = compileExpression offset lhs
                let rhs = compileExpression offset rhs
                Expression.Equal(lhs.Expression,rhs.Expression)
            | True(e) -> 
                Expression.Equal((e |> compileExpression offset).Expression, Expression.Constant true)
            | False(e) -> 
                Expression.NotEqual((e |> compileExpression offset).Expression, Expression.Constant true)

        let compileBoolean offset comp = 
            Expr(typeof<bool>,comp |> compileComparison offset)

        let stack = 
            if stack <> Stack<_>.Empty then
                //remove redundant unconditional branch to make it easier to interpret
                match stack.Peek() with
                None -> stack
                | Some (PartialExpr(Statement(UnconditionalBranch o)),_) ->
                    match instructions with
                    [] -> stack
                    | (_,offset)::_ when o <= offset -> stack.Pop() |> snd
                    | _ -> stack
                | _ -> stack
            else
                stack
        
        let readArguments offset isStatic args (parameters : ParameterInfo [])  = 
            let args = 
                args
                |> List.map (fun arg -> compileExpression offset arg,offset)
            let convertArguments (arguments : (CompiledExpression * int) list) = 
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
            instance,args

        let storeLocal index (valueExpr : StackExpression) offset =
            let value = compileExpression offset valueExpr
            let name = sprintf "local_%d" index
            let local =  ctx.GetOrCreateVariable value.Type name
            let expr =  Expression.Assign(local,value.Expression) :> Expression
            (Expr(value.Type,expr),offset) |> stack.Push

        let loadLocal index offset = 
            let name = sprintf "local_%d" index
            let var = ctx.GetVariable name
            (Expr(var.Type,var),offset) |> stack.Push
      
            
        match instructions with
        (Statement(UnconditionalBranch(target)),offset)::(n,offset')::tail when target > offset && target <= offset' ->
            //jumping to next instruction is a nop
            (n,offset')::tail |> inner stack
        | (Statement(UnconditionalBranch(target)),o)::tail ->
            let nextOffset = tail |> List.head |> snd
            let loopEnd = 
                tail |> List.tryFind(function
                    (Statement(ConditionalBranch(_,target')),_) -> 
                        printfn $"(%d{target} > %d{o} && %d{target'} <= %d{nextOffset})" 
                        (target > o && target' <= nextOffset)
                    | _ -> false
                ) |> Option.map snd
            match loopEnd with
            Some loopEndOffset ->
                let loopBlock = tail |> List.takeWhile (fun (_,offset) -> offset <= loopEndOffset)
                match loopBlock |> List.last with
                (Statement(ConditionalBranch(cmp,target')),o)-> 
                    let breakLabel = Expression.Label($"label__%d{o}")
                    let loopBody = 
                        (inner Stack.Empty (loopBlock |> List.take (loopBlock.Length - 1))).Expression
                    let preamble = 
                        loopBlock 
                        |> List.skipWhile(fun (_,offset) ->
                            target > offset
                        ) |> List.takeWhile (fun (_,offset) -> 
                            offset < loopEndOffset
                        )
                
                    let condition = compileComparison o cmp
                    let loopCondition = 
                        Expression.Block(
                            (preamble |> inner Stack.Empty).Expression,
                            Expression.IfThenElse(condition, loopBody,Expression.Break breakLabel)
                        )
                    inner ((Expr(typeof<System.Void>,Expression.Loop(loopCondition,breakLabel)), o) |> stack.Push) (tail |> List.skip loopBlock.Length)
                | _ -> failwith $"Unknown pattern %A{loopBlock} in %A{tail}"
            | _ -> failwith $"Expected a loop %A{tail}"
                
        | (Statement(ConditionalBranch(False(condition),endTrueBlock)),blockStart)::tail ->
            let trueBlock = tail |> List.takeWhile(fun (_,o) -> o < endTrueBlock) 
            let remaining = tail |> List.skip trueBlock.Length
            let condition = compileExpression blockStart condition  
            let trueBlock,elseBlock,remaining = 
                match trueBlock |> List.last with
                (Statement(UnconditionalBranch(endElseBlock)),_) ->
                    let elseBlock =  remaining |> List.takeWhile(fun (_,o) -> o < endElseBlock)
                    let remaining = remaining |> List.skip elseBlock.Length
                    let elseBlock = 
                        match elseBlock |> List.last with
                        (Statement(UnconditionalBranch(offset)),_) ->
                            if remaining.Head |> snd >= offset then
                                elseBlock |> List.take (elseBlock.Length - 1)
                            else
                                elseBlock
                        | _ -> elseBlock
                    let trimmedThenBlock = trueBlock |> List.take (trueBlock.Length - 1) 
                    let resultingThenBlock = (inner Stack.Empty trimmedThenBlock)
                    let elseBlock = (elseBlock |> inner Stack.Empty)
                    resultingThenBlock,elseBlock,remaining
                | _ -> trueBlock |> inner Stack.Empty,Empty, remaining
            
            let exp = 
                if elseBlock = Empty then
                    Expression.IfThen(condition.Expression,trueBlock.Expression) :> Expression 
                else
                    Expression.IfThenElse(condition.Expression,trueBlock.Expression,elseBlock.Expression) :> Expression 
            let ifExpression = 
                Expr(typeof<System.Void>,exp), blockStart 
            let stack = ifExpression |> stack.Push
            inner stack remaining
        | (Expression(LoadField(f)),_)::tail ->
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
        | (Expression(Add(lhs,rhs)),offset)::tail ->
            let expr = 
                let lhs = compileExpression offset lhs 
                Expr(lhs.Type,Expression.Add(lhs.Expression,(compileExpression offset rhs ).Expression))
            inner ((expr,offset) |> stack.Push) tail
        | (Expression(Boolean(expr)),offset)::tail ->
            let expr = compileBoolean offset expr
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
        | (Expression(CtorInvocation(c,args)),offset)::tail ->
            let parameters = c.GetParameters()
            let _,args = 
                parameters
                |> readArguments offset true args
            assert((args.IsNone && parameters |> Array.isEmpty) || (args.Value.Length = parameters.Length))
            let expr = 
                match args with
                Some args -> 
                    Expression.New(c, args) :> Expression
                | None | Some [||] -> 
                    Expression.New(c) :> Expression
            inner ((Expr(c.DeclaringType,expr),offset) |> stack.Push) tail
        | (Expression(MethodInvocation(m,args)),offset)::tail ->
            let instance,args = 
                m.GetParameters()
                |> readArguments offset m.IsStatic args
            
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
        |  (Statement (StoreLocal (Ordinal(iden), expr)),offset)::tail ->
            let stack = storeLocal iden expr offset
            inner stack tail
        |  (Statement (StoreLocal (Builder(builder), expr)),offset)::tail ->
            let stack = storeLocal builder.LocalIndex expr offset
            inner stack tail
        |  (Expression (LoadLocal (Ordinal(iden))),offset)::tail ->
            inner (loadLocal iden offset) tail
        |  (Expression (LoadLocal (Builder(builder))),offset)::tail ->            
            inner (loadLocal builder.LocalIndex offset) tail
        | (Statement(Pop exp),offset)::tail ->
            let exp = compileExpression offset (exp.GetExpression())  
            let stack = (CompiledExpression.Pop(exp),offset) |> stack.Push
              
            inner stack tail 
        | [] -> 
            let expressions = 
                stack.ToList()
                |> List.filter(fun (expr,_) -> 
                    expr <> PartialExpr(Statement(Nop))
                )
                |> List.map fst
            match expressions with
            [e] when e = Empty -> Empty
            | [e] -> (e.Type,e.Expression) |> Expr
            | [] -> Empty
            | exprs -> Exprs(exprs)
        | (StackInstruction.Expression(Return expr),offset)::tail ->
            let returnType = ctx.ReturnType
            let result = (expr |> compileExpression offset)
            let stack = 
                match tail with
                [] ->
                    //there's an implicit return at the last expression
                    //Adding an explicit return will cause an infinite loop 
                    //because the return instruction will come after the return label 
                    (result,offset) |> stack.Push 
                | _ -> 
                    //early return
                    (Expr(returnType,Expression.Return(DecompileContext.ReturnLabel,result.Expression,returnType))
                     ,offset) |> stack.Push
            inner stack tail
        | (Expression(LoadArgument ident),offset)::tail ->
            let arg = ctx.GetParameterExpression ident
            inner ((Expr(arg.Type,arg),offset) |> stack.Push) tail
        | (h,offset)::tail ->  
            printfn $"Partial/Unmatched (%A{h}, %d{offset})"
            inner ((PartialExpr h,offset) |> stack.Push) tail
    let expressionBlock =
        let res = 
            try 
                inner Stack.Empty ctx.Instructions
            with e ->
                eprintfn $"Failed to understand %A{ctx.Instructions}" 
                reraise()
        match res with
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
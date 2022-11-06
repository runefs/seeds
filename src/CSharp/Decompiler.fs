namespace CSharp
module rec Decompiler = 
    open Types
    open System.Linq.Expressions
    open DecompileContext

    type Stack = Stack<Expression * int>
    let rnd = System.Random()
    let forEach (collection : Expression) loopContent = 
        let getEnumerator = collection.Type.GetMethod("GetEnumerator")
        let enumeratorType = getEnumerator.ReturnType
        let getCurrent = enumeratorType.GetMethod("get_Current")
        let elementType = getCurrent.ReturnType
        let loopVar = Expression.Parameter(elementType)
        let getEnumeratorCall = Expression.Call(collection, getEnumerator)
        let enumeratorVar = Expression.Variable(enumeratorType, "enumerator")

        let enumeratorAssign = Expression.Assign(enumeratorVar, getEnumeratorCall)
        
        let moveNextCall = Expression.Call(enumeratorVar, enumeratorType.GetMethod("MoveNext"))

        let breakLabel = Expression.Label("LoopBreak")

        Expression.Block( [|enumeratorVar|],
                            enumeratorAssign,
                            Expression.Loop(
                                Expression.IfThenElse(
                                    Expression.Equal(moveNextCall, Expression.Constant(true)),
                                    Expression.Block([|loopVar|],
                                        Expression.Assign(loopVar, Expression.Property(enumeratorVar, "Current")),
                                        loopContent
                                    ) :> Expression,
                                    Expression.Break(breakLabel)
                                ),
                            breakLabel)
        )
    let exprToList (e :Expression)=
        match e with
        :? BlockExpression as block -> block.Expressions |> List.ofSeq
        | _ -> [e]

    let forLoop decompileBlock decompileExpression (variableCollection : VariableCollection) target offset tail = 
        let nextOffset = tail |> List.head |> snd
       
        tail |> List.tryFind(function
            (Statement(ConditionalBranch(_,target')),_) -> 
                (target > offset && target' <= nextOffset)
            | _ -> false
        ) |> Option.map snd
        |> Option.bind (fun loopEndOffset ->
            let loopBlock = 
                tail |> List.takeWhile (fun (_,offset) -> offset <= loopEndOffset)
            match loopBlock |> List.last with
            (Statement(ConditionalBranch(cmp,target')),o)->
                
                let preample =
                    let pre =
                        loopBlock 
                        |> List.skipWhile(fun (_,offset) ->
                            target > offset
                        ) |> List.takeWhile (fun (_,offset) -> 
                            offset < loopEndOffset
                        )
                    match pre with
                    [] -> None
                    | p -> Some p
                let condition = Boolean(cmp) |> Some
                let content = loopBlock |> List.take (loopBlock.Length - 1)
                let expr : Expression = 
                    let preample = 
                        preample
                        |> Option.map(fun preample -> decompileBlock variableCollection preample []  |> exprToList)
                    let vc = variableCollection.Child()
                    let condition = 
                        match condition with
                        None -> Expression.Constant(true) :> Expression
                        | Some c -> decompileExpression vc c
                    let content = decompileBlock vc content []
                    let ``break`` = Expression.Label($"break%d{rnd.Next()}")
                    let body = 
                        match preample with
                        None -> 
                            [
                                Expression.IfThenElse(
                                    condition,
                                    content,
                                    Expression.Goto(``break``)
                                ) :> Expression
                            ]
                        | Some preample ->
                            preample@
                            [    
                                Expression.IfThenElse(
                                    condition,
                                    content,
                                    Expression.Goto(``break``)
                                )
                            ] 
                    Expression.Loop(
                        Expression.Block(
                            vc.AllVariables(),
                            body
                        ),``break``
                    )    
                Some(Some expr, loopBlock.Length + 1 )
            | _ -> Some(None,0)
        ) |> Option.orElse(Some(None,0))
        |> Option.get
        
    let tracer (offset : int) =
        Expression.Call(
            null,
            typeof<System.Console>.GetMethod("WriteLine", [| typeof<int> |] ),
            Expression.Constant(offset)
        ) :> Expression
    let readForeach _  = None,0
    let decompileBlock emitTrace (compileExpression : VariableCollection -> StackExpression -> Expression)  (compileStatement : VariableCollection -> StackStatement -> Expression) m =
        let ctx = DecompileContext(m)
        let vc = VariableCollection(m)
        let returnLabel = Expression.Label("return target")
        let mutable resultVar = None
        let resultName = "*<>__result"
        let rec inner  (variableCollection : VariableCollection) instructions acc : Expression =
            let acc = 
                match instructions with
                (Statement(_),offset)::_ when emitTrace -> (offset |> tracer)::acc
                | _ -> acc
                
            let compileExpression' = compileExpression 
            let compileExpression = compileExpression variableCollection
            let compileStatement = compileStatement variableCollection

            let expr,count = 
                match instructions with
                [] -> None,0
                | (Expression(MethodInvocation(m,[collection])),offset)::tail when m.Name = "GetEnumerator" ->
                        match readForeach instructions with
                        (Some(expr),count)->
                            Some expr,count
                        | (None,0) -> 
                            let expr = Expression.Call(collection |> compileExpression,m) :> Expression
                            Some expr, 1
                        | _ -> failwith $"unexpected return from forEach at %d{offset}"
                | (Expression(Return(Some(expr))),offset)::tail ->
                    match tail with
                    [] ->
                        //there's an implicit return at the last expression
                        //Adding an explicit return will cause an infinite loop 
                        //because the return instruction will come after the return label 
                        expr 
                        |> compileExpression
                        |> Some,1
                    | _ -> 
                        let expr = expr |> compileExpression
                        let result = Expression.Block(
                                Expression.Assign(variableCollection.GetOrCreateVariable m.ReturnType resultName,expr),
                                Expression.Return returnLabel
                        )
                        resultVar <- variableCollection.GetOrCreateVariable m.ReturnType resultName |> Some
                        Some(result),1
                | (Statement(ReturnTarget),_)::tail | (Expression(Return(None)),_)::tail -> 
                    None,1
                | (Statement(UnconditionalBranch(target)),offset)::tail when target > offset ->
                    tail
                    |> forLoop inner compileExpression' variableCollection target offset
                        
                        
                | (Statement(ConditionalBranch(False(condition),endTrueBlock)),_)::tail ->
                    let trueBlock = tail |> List.takeWhile(fun (_,o) -> o < endTrueBlock) 
                    let remaining = tail |> List.skip trueBlock.Length
                    let condition = condition |> compileExpression
                    let trueBlock,elseBlock,remaining = 
                        match trueBlock |> List.last with
                        (Statement(UnconditionalBranch(endElseBlock)),_) ->
                            let elseBlock = remaining |> List.takeWhile(fun (_,o) -> o < endElseBlock)
                            let remaining = remaining |> List.skip elseBlock.Length
                            let elseBlock = 
                                match elseBlock |> List.last with
                                (Statement(UnconditionalBranch(offset)),_) ->
                                    if remaining.Head |> snd >= offset then
                                        elseBlock |> List.take (elseBlock.Length - 1)
                                    else
                                        elseBlock
                                | _ -> elseBlock
                            let trimmedThenBlock = 
                                inner (variableCollection.Child()) (trueBlock
                                    |> List.take (trueBlock.Length - 1)) []
                                
                            let elseBlock = inner (variableCollection.Child()) elseBlock []
                            trimmedThenBlock,elseBlock |> Some,remaining
                        | _ -> inner (variableCollection.Child()) trueBlock [], None,remaining
                    let expr : Expression = 
                        match elseBlock with
                        None ->  Expression.IfThen(condition,trueBlock)
                        | Some elseBlock -> Expression.IfThenElse(condition,trueBlock,elseBlock)
                    Some expr,(instructions.Length - remaining.Length)
                | (Expression(e),o)::_ -> 
                    e |> compileExpression |> Some,1
                | (Statement(s),o)::_ -> 
                    let s = s |> compileStatement
                    Some(s),1
            let rtn = 
                match resultVar with
                None -> []
                | Some v ->
                    [
                        Expression.Label(returnLabel) :> Expression
                        v
                    ]
            let tail = instructions |> List.skip count
            match expr,tail with
            None,[] -> 
                let res = acc |> List.fold(fun rev (e : Expression) -> e::rev) rtn
                Expression.Block(variableCollection.AllVariables(), res) :> Expression
            | Some(expr),[] -> 
                let res = expr::acc |> List.fold(fun rev (e : Expression) -> e::rev) rtn
                Expression.Block(variableCollection.AllVariables(), res) :> Expression
            | Some(expr),tail ->
                expr::acc |> inner variableCollection tail 
            | None,tail ->
                inner variableCollection tail acc 

        let optimzedInstruction = 
            ctx.Instructions
            //|> Optimizer.optimize

        inner vc optimzedInstruction [],vc

    let compileBoolean compileExpression =
        function
        GreaterThanEqual(lhs,rhs) -> 
            let lhs = compileExpression  lhs
            let rhs = compileExpression  rhs
            Expression.GreaterThanOrEqual(lhs,rhs)
        | GreaterThan(lhs,rhs) -> 
            let lhs = compileExpression  lhs
            let rhs = compileExpression  rhs
            Expression.GreaterThan(lhs,rhs)
        | LessThanEqual(lhs,rhs) -> 
            let lhs = compileExpression  lhs
            let rhs = compileExpression  rhs
            Expression.LessThanOrEqual(lhs,rhs)
        | LessThan(lhs,rhs) -> 
            let lhs = compileExpression  lhs
            let rhs = compileExpression rhs
            Expression.LessThan(lhs,rhs)
        | NotEqual(lhs,rhs) -> 
            let lhs = compileExpression lhs
            let rhs = compileExpression rhs
            Expression.NotEqual(lhs,rhs)
        | Equal(lhs,rhs) -> 
            let lhs = compileExpression lhs
            let rhs = compileExpression rhs
            Expression.Equal(lhs,rhs)
        | True(e) -> 
            Expression.Equal((e |> compileExpression), Expression.Constant true)
        | False(e) -> 
            Expression.NotEqual((e |> compileExpression), Expression.Constant true)

    let compileExpression (variableCollection: VariableCollection) expr : Expression = 
        let compileExpression = compileExpression variableCollection
        let compileBoolean = compileBoolean compileExpression
        let readArguments = readArguments variableCollection
        match expr with
            NewArray(type',elements) ->
                let compiledElements = 
                    elements 
                    |> List.map (fst >> compileExpression)
                    |> Array.ofList
                Expression.NewArrayInit(type',compiledElements) :> Expression
            | LoadField(instance,f) ->
                Expression.Field(compileExpression instance,f) :> Expression
            | This ->
                variableCollection.GetArgument "this"

            | Add(lhs,rhs) ->
                let lhs = compileExpression lhs 
                Expression.Add(lhs,(compileExpression rhs ))
                
            | Boolean(expr)->
                compileBoolean expr
            | Constant c ->
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
                    
                expr
            | CtorInvocation(c: System.Reflection.ConstructorInfo,argExpressions) ->
                let parameters = c.GetParameters()
                let _,args= 
                    readArguments true argExpressions parameters

                assert((args.IsNone && parameters |> Array.isEmpty) || (args.Value.Length = parameters.Length))

                let expr = 
                    match args with
                    Some args -> 
                        Expression.New(c, args) :> Expression
                    | None | Some [||] -> 
                        Expression.New(c) :> Expression
                expr
            | MethodInvocation(m,args) ->
                
                let instance,args = 
                    m.GetParameters()
                    |> readArguments m.IsStatic args
                
                match instance,args with
                None,None ->
                    Expression.Call(m) :> Expression
                | Some instance, None ->
                    Expression.Call(instance,m) :> Expression
                | None,Some args ->
                    Expression.Call(m, args) :> Expression
                | Some instance, Some args ->
                    Expression.Call(instance,m, args) :> Expression
            |  LoadLocal (iden) ->
                let name = sprintf "local_%d" iden
                variableCollection.[name]
            | LoadArgument ident ->
                variableCollection.GetArgument ident
            | h ->  
                failwith  $"Partial/Unmatched (%A{h})"
    let readArguments ctx (isStatic : bool) (args : StackExpression list) (parameters : System.Reflection.ParameterInfo []) : Expression option * Expression [] option = 
        let compileExpression = compileExpression ctx      
        let args = 
            args
            |> List.map compileExpression
        let convertArguments (arguments : Expression list) = 
            arguments
            |> List.mapi(fun i a -> 
                let exprType = a.Type
                let parameterType = parameters.[i].ParameterType
                if parameterType.IsAssignableFrom exprType then
                    a
                elif parameterType.IsAssignableTo exprType then
                    Expression.Convert(a,parameterType) :> Expression
                else
                    failwithf "Can't convert %A of type: %s to the required type of %s" a a.Type.Name parameterType.Name
            )
        let args =  
            if isStatic then
                args
                |> convertArguments
            else
                (args |> List.head)::
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

    let compileStatement 
              variableCollection 
              stmt =
        let decompileExpression = compileExpression variableCollection
        match stmt with
        | Goto label ->
            Expression.Goto(label) :> Expression
        |  StoreLocal (iden, valueExpr) ->
            let value = decompileExpression valueExpr
            let name = sprintf "local_%d" iden
            let local =  variableCollection.GetOrCreateVariable value.Type name
            let expr =  Expression.Assign(local,value) :> Expression
            expr
        | Pop exp ->
            exp |> decompileExpression
        | stmt->  
            failwith $"Partial/Unmatched (%A{stmt})"
    
    let methodToExpressionTree emitTrace method =
        
        try 
            decompileBlock emitTrace compileExpression compileStatement method
        with e ->
            eprintfn $"Failed to understand %A{method.Name}" 
            reraise()
module ExpressionTree

open System.Reflection
open System.Reflection.Emit
open System.Linq.Expressions
open Mono.Reflection

type Constant =
    Byte of byte
    | Int16 of int16
    | Int of int
    | Int64 of int64
    | String of string
    | Single of single
    | Float of float
    | Null
    with member x.Type
            with get() = 
                match x with
                Byte _ -> typeof<byte>
                | Int16 _ -> typeof<int16>
                | Int _ -> typeof<int>
                | Int64 _ -> typeof<int64>
                | String _ -> typeof<string>
                | Single _ -> typeof<single>
                | Float _ -> typeof<float>
                | Null -> typeof<obj>
type Local = 
    Ordinal of int
    | Builder of LocalVariableInfo
type Comparison = 
    GreaterThanEqual
    | GreaterThan
    | LessThanEqual
    | LessThan
    | NotEqual
    | Equal
    | True
    | False

type Stack private(_stack) = 
    member __.Pop() = 
        _stack |> List.head, Stack(_stack |> List.tail)
    member __.TryPop() = 
        _stack |> List.tryHead
        |> Option.map(fun head ->
            head, Stack(_stack |> List.tail)
        )
    member __.Push(elem) = 
        Stack(elem::_stack)
    member __.Take n = 
        _stack |> List.take n |> List.rev, Stack(_stack |> List.skip n)
    member __.ToList() = 
        _stack
    static member Empty with get() = Stack(List.empty)

and BlockExpression = 
    Expr of System.Type * Expression
    | Exprs of BlockExpression list
    | Pop of BlockExpression
    | PartialExpr of StackInstruction
    | Empty
    with member x.Expression 
           with get() =
               match x with
               Expr (_,e) -> e
               | Exprs (es) -> 
                    Expression.Block(
                        es
                        |> List.map(fun e -> e.Expression)
                    ) :> Expression
               | Pop e -> e.Expression
               | a -> failwithf "Should be an Expression (%A)" a
         member x.Value 
           with get() = 
               match x with
               Expr (_,e) -> e
               | Exprs(es) -> 
                    let expressions = 
                        es 
                        |> List.filter(function
                            PartialExpr _ -> false
                            | Expr(_,e) -> e.Type <> typeof<unit> && e.Type <> typeof<System.Void>
                            | _ -> true
                        ) 
                    match expressions with
                    [] -> Expression.Constant(null) :> Expression
                    | es -> (es |> List.last).Expression
               | Pop e -> e.Expression
               | a -> failwithf "Should be an Expression (%A)" a

         member x.Type 
           with get() =
               match x with
               Expr (t,_) -> t
               | Exprs _ -> x.Value.Type
               | Pop e -> e.Type
               | a -> failwithf "Should be n Expression (%A)" a
         member x.Append expr = 
             match x with
             Expr _ | Pop _  -> Exprs(x::[expr])
             | Empty -> expr
             | Exprs (es) -> 
                  Exprs(es@[expr])
             | a -> failwithf "Should be an Expression (%A)" a
        
and StackExpression =
    | Constant of Constant
    | MethodInvocation of MethodInfo
    | CtorInvocation of ConstructorInfo
    | Cast of System.Type
    | LoadLocal of Local
    | LoadField of FieldInfo
    | This
    | LoadArgument of int
    | Add

and StackStatement = 
    StoreField
    | StoreLocal of Local
    | Pop
    | Return
    | Goto of LabelTarget
    | ConditionalBranch of Condition: Comparison * Offset: int
    | UnconditionalBranch of offset: int
    | Nop
and StackInstruction =
    Expression of StackExpression 
    | Statement of StackStatement
and Instruction = 
    Block of BlockExpression
    | StackInstruction of StackInstruction


let returnLabel = Expression.Label("return target")
let returnTarget = Expression.Label(returnLabel) :> Expression

let rec methodToExpressionTree deepTransform (methodInfo : System.Reflection.MethodInfo) =
    let readInstructions (instructions : seq<Mono.Reflection.Instruction>) = 
        instructions
        |> Seq.filter(fun inst -> inst.OpCode <> OpCodes.Nop)
        |> Seq.map(fun inst ->
            let offset = inst.Offset
            let i = 
                match inst.OpCode with
                | op when (op = OpCodes.Call 
                           || op = OpCodes.Callvirt) -> 
                    let mi = inst.Operand :?> MethodInfo
                    MethodInvocation(mi) |> Expression
                | op when ((op = OpCodes.Call 
                           || op = OpCodes.Callvirt
                           || op = OpCodes.Newobj) && inst.Operand :? ConstructorInfo) ->
                            let ci = inst.Operand :?> ConstructorInfo
                            CtorInvocation(ci) |> Expression
                | op when op = OpCodes.Ldc_I4 ->
                    Int(inst.Operand |> unbox |> int) |> Constant |> Expression
                | op when op = OpCodes.Ldc_I4_S ->
                    let value = 
                        match inst.Operand with
                        :? System.SByte as s -> s |> int
                        | :? System.Byte as b -> b |> int
                        | operand -> failwithf "Should not happen %A" operand
                    Int(value) |> Constant |> Expression
                | op when op = OpCodes.Ldc_I4_0 -> Int(0) |> Constant |> Expression
                | op when op = OpCodes.Ldc_I4_1 -> Int(1) |> Constant |> Expression
                | op when op = OpCodes.Ldc_I4_2 -> Int(2) |> Constant |> Expression
                | op when op = OpCodes.Ldc_I4_3 -> Int(3) |> Constant |> Expression
                | op when op = OpCodes.Ldc_I4_4 -> Int(4) |> Constant |> Expression
                | op when op = OpCodes.Ldc_I4_5 -> Int(5) |> Constant |> Expression
                | op when op = OpCodes.Ldc_I4_6 -> Int(6) |> Constant |> Expression
                | op when op = OpCodes.Ldc_I4_7 -> Int(7) |> Constant |> Expression
                | op when op = OpCodes.Ldc_I4_8 -> Int(8) |> Constant |> Expression
                | op when op = OpCodes.Ldc_I4_M1 -> Int(-1) |> Constant |> Expression
                | op when op = OpCodes.Ldc_I8 ->
                    Int64(inst.Operand |> unbox |> int64) |> Constant |> Expression
                | op when op = OpCodes.Castclass -> 
                    Cast(inst.Operand :?> System.Type) |> Expression
                | op when op = OpCodes.Ldstr ->
                    String(inst.Operand :?> string) |> Constant |> Expression
                | op when (op = OpCodes.Stloc || op = OpCodes.Stloc_S) -> 
                    let local = 
                        if inst.Operand :? System.Reflection.LocalVariableInfo then Builder(inst.Operand :?> System.Reflection.LocalVariableInfo)
                        else Local.Ordinal(inst.Operand |> unbox |> int16 |> int)
                    local |> StoreLocal |> Statement
                | op when op = OpCodes.Stloc_0 -> 0 |> Ordinal |> StoreLocal |> Statement
                | op when op = OpCodes.Stloc_1 -> 1 |> Ordinal |> StoreLocal |> Statement
                | op when op = OpCodes.Stloc_2 -> 2 |> Ordinal |> StoreLocal |> Statement
                | op when op = OpCodes.Stloc_3 -> 3 |> Ordinal |> StoreLocal |> Statement
                | op when op = OpCodes.Stfld -> StoreField |> Statement
                | op when op = OpCodes.Pop -> Pop |> Statement
                | op when op = OpCodes.Ret -> Return |> Statement
                | op when op = OpCodes.Ldfld -> LoadField(inst.Operand :?> FieldInfo) |> Expression
                | op when op = OpCodes.Ldloc ->
                    let local  = 
                        if inst.Operand :? LocalBuilder then Builder(inst.Operand :?> LocalBuilder)
                        else Local.Ordinal(inst.Operand |> unbox |> int16 |> int)
                    local |> LoadLocal |> Expression
                | op when op = OpCodes.Ldloc_0 ->  0 |> Ordinal |> LoadLocal |> Expression
                | op when op = OpCodes.Ldloc_1 ->  1 |> Ordinal |> LoadLocal |> Expression
                | op when op = OpCodes.Ldloc_2 ->  2 |> Ordinal |> LoadLocal |> Expression
                | op when op = OpCodes.Ldloc_3 ->  3 |> Ordinal |> LoadLocal |> Expression
                | op when (op = OpCodes.Beq
                           || op = OpCodes.Beq_S)
                    -> 
                    let offset = (inst.Operand :?> Mono.Reflection.Instruction).Offset
                    (Equal,offset) |> ConditionalBranch |> Statement
                | op when op = OpCodes.Bge
                          || op = OpCodes.Bge_S
                          || op = OpCodes.Bge_Un
                          || op = OpCodes.Bge_Un_S
                    -> 
                    let offset = (inst.Operand :?> Mono.Reflection.Instruction).Offset
                    (GreaterThan,offset) |> ConditionalBranch |> Statement
                | op when op = OpCodes.Bgt
                          || op = OpCodes.Bgt_S
                          || op = OpCodes.Bgt_Un
                          || op = OpCodes. Bgt_Un_S
                    -> 
                    let offset = (inst.Operand :?> Mono.Reflection.Instruction).Offset
                    (GreaterThanEqual,offset) |> ConditionalBranch |> Statement
                | op when op = OpCodes.Ble
                          || op = OpCodes.Ble_S
                          || op = OpCodes.Ble_Un
                          || op = OpCodes.Ble_Un_S
                    -> 
                    let offset = (inst.Operand :?> Mono.Reflection.Instruction).Offset
                    (LessThan,offset) |> ConditionalBranch |> Statement
                | op when op = OpCodes.Blt
                          || op = OpCodes.Blt_S
                          || op = OpCodes.Blt_Un
                          || op = OpCodes.Blt_Un_S
                    -> 
                    let offset = (inst.Operand :?> Mono.Reflection.Instruction).Offset
                    (LessThanEqual,offset) |> ConditionalBranch |> Statement
                | op when op = OpCodes.Bne_Un
                          || op = OpCodes.Bne_Un_S
                    -> 
                    let offset = (inst.Operand :?> Mono.Reflection.Instruction).Offset
                    (NotEqual,offset) |> ConditionalBranch |> Statement
                | op when op = OpCodes.Brfalse
                          || op = OpCodes.Brfalse_S
                    -> 
                    let offset = (inst.Operand :?> Mono.Reflection.Instruction).Offset
                    (False,offset) |> ConditionalBranch |> Statement
                | op when op = OpCodes.Brtrue
                          || op = OpCodes.Brtrue_S
                    -> 
                    let offset = (inst.Operand :?> Mono.Reflection.Instruction).Offset
                    (True,offset) |> ConditionalBranch |> Statement
                | op when (op = OpCodes.Br || op = OpCodes.Br_S) -> 
                    let offset = (inst.Operand :?> Mono.Reflection.Instruction).Offset
                    offset |> UnconditionalBranch |> Statement
                | op when op = OpCodes.Ldarg_0 -> This |> Expression
                | op when op = OpCodes.Ldarg_1 -> LoadArgument 1 |> Expression
                | op when op = OpCodes.Ldarg_2 -> LoadArgument 2 |> Expression
                | op when op = OpCodes.Ldarg_3 -> LoadArgument 3 |> Expression
                | op when op = OpCodes.Ldarg -> LoadArgument (inst.Operand |> unbox |> int) |> Expression
                | op when op = OpCodes.Nop -> Nop |> Statement
                | op when op = OpCodes.Ldnull -> Null |> Constant |> Expression
                | op when op = OpCodes.Add -> Add |> Expression
                | op when op = OpCodes.Ldloc_S ->
                    inst.Operand :?> System.Reflection.LocalVariableInfo |> Builder |> LoadLocal |> Expression
                    ////////////////////////////////////////
                    (*| op when inst.Operand :? System.Type -> 
                        let typeOperand = inst.Operand :?> System.Type
                        match op with
                        op when (op = OpCodes.Ldtoken //0 -> 1
                                || op = OpCodes.Sizeof) //0 -> 1
                                  Statement(Type)
                        op when (op = OpCodes.Box
                                 || op = OpCodes.Unbox
                                 || op = OpCodes.Unbox_Any
                                 ||op = OpCodes.Isinst) ->
                                 Expression(Cast(op,typeOperand))
                        op when (op = OpCodes.Ldobj
                                 || op = OpCodes.Mkrefany
                                 || op = OpCodes.Newarr
                                 || op = OpCodes.Refanyval) ->
                                Expression(Create(op,typeOperand))
                        op when (|| op = OpCodes.Ldelem
                                 || op = OpCodes.Ldelema)
                                 Expression(Binary ArrayElement(op,typeOperand))
                        op when (OpCodes.Cpobj //2 -> 0
                                 || op = OpCodes.Stobj // 2 -> 0
                                 || op = OpCodes.Stelem // 3 -> 0
                                 || op = OpCodes.Initobj //1 -> 0
                               ) ->
                        TypeOperation(op,inst.Operand :?> System.Type)
                    | op when (op = OpCodes.Ldarga
                               || op = OpCodes.Starg) ->
                        Value(Int16(op,inst.Operand |> unbox |> int16))
                    | op when (op = OpCodes.Ldarga_S
                               || op = OpCodes.Starg_S) ->
                        Value(Byte(op,inst.Operand |> unbox |> byte))
                    | op when op = OpCodes.Ldc_I4 ->
                        Value(Int(op,inst.Operand |> unbox |> int32))
                    | op when (op = OpCodes.Ldc_I4_S && inst.Operand :? byte) ->
                       Value(Byte(op,inst.Operand |> unbox |> byte))
                    | op when (op = OpCodes.Ldc_I4_S) ->
                        Value(SByte(op,inst.Operand |> unbox |> sbyte))
                    | op when op = OpCodes.Ldc_I8 ->
                        Value(Int64(op,inst.Operand |> unbox |> int64))
                    | op when op = OpCodes.Ldc_R4 ->
                        Value(Single(op,inst.Operand |> unbox |> single))
                    | op when op = OpCodes.Ldc_R8 ->
                        Value(Float(op,inst.Operand |> unbox |> float))
                    | op when (op = OpCodes.Ldfld
                               || op = OpCodes.Ldflda 
                               || op = OpCodes.Ldsfld
                               || op = OpCodes.Ldsflda
                               || (op = OpCodes.Ldtoken && inst.Operand :? FieldInfo) ) -> 
                        Value(Field(op,inst.Operand :?> FieldInfo))
                    | op when (op = OpCodes.Stfld
                               || op = OpCodes.Stsfld ) -> 
                        StoreField(op,inst.Operand :?> FieldInfo) |> Unary
                    | op when op = OpCodes.Ldarg_0 ->
                        RoleSelf |> This |> Value 
                    | op when ((op = OpCodes.Ldloc) && inst.Operand :? int16) ->
                        Value(Local(Ordinal(inst.Operand |> unbox |> int16)))
                    | op when ((op = OpCodes.Ldloca) && inst.Operand :? int16) ->
                        Value(Local(Address(inst.Operand |> unbox |> int16)))
                    | op when ((op = OpCodes.Stloc) && inst.Operand :? int16) ->
                        StoreLocal(Ordinal(inst.Operand |> unbox |> int16)) |> Unary
                    | op when (op = OpCodes.Ldloc && inst.Operand :? LocalBuilder) ->
                        Value(Local(Builder(inst.Operand :?> LocalBuilder)))
                    | op when (op = OpCodes.Ldloca_S) ->
                        Value(Local(ShortAddress(inst.Operand |> unbox |> byte)))
                    | op when (op = OpCodes.Stloc_S) ->
                        StoreLocal(ShortAddress(inst.Operand |> unbox |> byte)) |> Unary
                    | op when op = OpCodes.Ldstr ->
                        Value(String(inst.Operand :?> string))
                    | op when op = OpCodes.Switch ->
                        Switch(inst.Operand :?> Label [])
                    | op when op = OpCodes.Sub ->
                        Computation(Subtraction)
                    | op when ((op = OpCodes.Ldtoken
                               || op = OpCodes.Ldvirtftn
                               || op = OpCodes.Ldftn) && inst.Operand :? MethodInfo) ->
                        failwith "not implemented yet"
                    | op when op = OpCodes.Calli -> failwith "Calli not supported" *)
                | op -> failwithf "Not implemented yet %A" op
            i,offset
        ) |> List.ofSeq

    let instructions = 
        methodInfo.GetInstructions()
        |> Seq.filter(fun inst -> inst.OpCode <> OpCodes.Nop)
        |> readInstructions
    let mutable variables : Map<string,_> = Map.empty
    let getOrCreateVariable t name =
        let actualName = methodInfo.Name + "__" + name
        match variables |> Map.tryFind actualName with
        None ->
            let v = Expression.Variable(t,actualName)
            variables <- variables.Add(actualName,v)
            v
        | Some v -> v

    let declaredParameters = 
        (methodInfo.GetParameters()
          |> Seq.map(fun p -> p.ParameterType, p.Name)
          |> Seq.toList
         )
    let parameters = 
        if methodInfo.IsStatic then
            declaredParameters
        else
            (methodInfo.DeclaringType,"this")
            ::declaredParameters
        |> List.mapi(fun i (argType,name) ->
           i, argType,name
        ) 
    
    let parameterExpressions = 
        parameters
        |> List.map(fun (_,argType,name) ->
            //this will always be a parameter
            if deepTransform && name <> "this" then
                name, getOrCreateVariable argType <| "__param__" + name :> Expression
            else
                name,Expression.Parameter(argType,name) :> Expression
        ) |> Map.ofList
    let parameterNames = 
        parameters
        |> List.map(fun (i,_,name) ->
            i,name
        ) |> Map.ofList
   
    let returnType = methodInfo.ReturnType
    let result = 
        if returnType = typeof<unit> || returnType = typeof<System.Void> then
            Expression.Label(Expression.Label("Result placeholder")) :> Expression
        else
            getOrCreateVariable returnType "result" :> Expression
    let rec inner (stack : Stack) instructions : BlockExpression = 
        
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
                   getOrCreateVariable ifResultType <| sprintf "__IIF__%d" lastOffset :> Expression
                   
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
            let local =  getOrCreateVariable value.Type name
            let expr =  Expression.Assign(local,value.Expression) :> Expression
            (Expr(value.Type,expr),offset) |> stack.Push

        let loadLocal index offset = 
            let name = sprintf "local_%d" index
            let var = variables.[name]
            (Expr(var.Type,var),offset) |> stack.Push
        match instructions with
        (Statement(ConditionalBranch(condition,originalBranchOffset)),originalOffset)::blockAndTail ->
            match blockAndTail with
            (Statement(UnconditionalBranch(_)),_)
            ::(Statement(UnconditionalBranch(ifTrueStart)),_)
            ::tail ->
                let ifFalse,ifTrueAndTail = 
                    tail
                    |> List.partition(fun (_,offset) -> offset <= ifTrueStart && offset < ifTrueStart)
                let ifBlockEnd = 
                    match ifFalse |> List.last with
                    Statement(UnconditionalBranch(offset)),_ -> offset
                    | _,falseEnd -> 
                        let trueAndRemaining =
                            tail
                            |> List.filter(fun (_,offset) -> offset > falseEnd)
                        
                        trueAndRemaining
                        |> List.tryFind(fun (exp,offset) -> 
                           match exp with
                           Statement(Return) -> offset > falseEnd
                           | _ -> false
                        ) |> Option.map(fun (_,offset) -> offset + 1)
                        |> Option.orElse(instructions |> List.last |> snd |> Some)
                        |> Option.get
                let ifTrue,remaining = 
                    ifTrueAndTail
                    |> List.partition(fun (_,offset) -> offset < ifBlockEnd)
                let stack = 
                   readIfBlock condition ifTrue ifFalse
                inner stack remaining
            | _ -> 
                let potentialWhileBlock,remaining = 
                    blockAndTail
                    |> List.partition(fun (_,o) -> o < originalBranchOffset)
                let firstOperandOffset = (stack.Pop() |> snd).Pop() |> fst |> snd
                match potentialWhileBlock |> List.last with
                Statement(UnconditionalBranch(branchToOffset)),_ when branchToOffset = firstOperandOffset ->
                    let stack = readWhileBlock condition (potentialWhileBlock |> List.take (potentialWhileBlock.Length - 1))
                    inner stack remaining
                | _ -> failwith "Do not understand block"       
        | (Expression(LoadField(f)),_)::tail ->
            let (instance,instanceOffset),stack = stack.Pop()
            
            let exp = 
                Expression.Field(instance.Expression,f) :> Expression
            let expr = 
                Expr(f.FieldType, exp)
            inner ((expr,instanceOffset) |> stack.Push) tail
        | (Expression(This),offset)::tail ->
            let expr = 
                let arg = parameterExpressions.["this"]
                Expr(arg.Type, arg)
            inner ((expr,offset) |> stack.Push) tail
        | (Expression(Add),offset)::tail ->
            let (lhs,_),stack = stack.Pop()
            let (rhs,_),stack = stack.Pop()
            let expr = 
                Expr(lhs.Type,Expression.Add(lhs.Expression,rhs.Expression))
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
                if deepTransform && m.DeclaringType = methodInfo.DeclaringType then
                    let expr, _, vars = methodToExpressionTree deepTransform m
                    variables <- 
                        vars
                        |> Map.fold(fun vs  name expr ->
                            match vs |> Map.tryFind name with
                            None -> vs.Add(name,expr)
                            | Some _ -> vs
                        ) variables
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
                                match variables |> Map.tryFind varName with
                                None -> 
                                    printfn "Couldn't find %s in %A" varName variables
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
            let stack = 
                match stack.TryPop() with
                None -> stack
                | Some((e,_),stack) -> 
                    if returnType <> typeof<System.Void> && returnType <> typeof<unit> then
                        stack.Push(Expr(result.Type,Expression.Assign(result,e.Expression)), offset)
                    else
                        stack
            let stack = 
                (Expr(returnType,Expression.Return(returnLabel)),offset) |> stack.Push
            let stack = 
                if returnType <> typeof<System.Void> && returnType <> typeof<unit> then
                    (Expr(returnType,result),offset) |> stack.Push
                else
                    stack
            inner stack tail
        | (Expression(LoadArgument ident),offset)::tail ->
            let arg = parameterExpressions.[parameterNames.[ident]]
            inner ((Expr(arg.Type,arg),offset) |> stack.Push) tail
        | (h,offset)::tail ->  
            inner ((PartialExpr h,offset) |> stack.Push) tail
    let expressionBlock = 
        match inner Stack.Empty instructions with
        Exprs(exprs) -> 
            Exprs(exprs)
        | Expr _ as e -> Exprs([e])
        | b -> failwithf "Couldn't read the expression block %A" b
    let infoMap = 
        parameterNames
        |> Map.toList
        |> List.map(fun (i,name) -> name, i)
        |> Map.ofList

    let arguments = 
        parameterExpressions
        |> Map.toList
        |> List.sortBy(fun (name,_) ->
            match infoMap |> Map.tryFind name with
            None -> -1
            | Some i -> i
        ) |> List.map(fun (_,exp) -> exp :?> ParameterExpression)
    expressionBlock, arguments, variables

let compile expr (arguments : ParameterExpression list) variables = 
    let exprs = 
        match expr with
        Expr(_,e) -> [e]
        | BlockExpression.Pop _ as p -> [p.Expression]
        | Exprs(exprs) -> 
            let exprs = 
                match exprs |> List.map(fun e -> e.Expression) |> List.rev with
                result::body -> 
                    result::returnTarget::body
                | [] -> []
            exprs |> List.rev
        | e -> failwithf "Don't know how to finish off with %A" e
    
    let expr = Expression.Block(variables |> Map.toList |> List.map snd,exprs) :> Expression
    let parameters = 
        arguments
        |> List.toSeq
    let lambda = Expression.Lambda(Expression.Block(expr),parameters)
#if DEBUG    
    printfn "%s" (Mono.Linq.Expressions.CSharp.ToCSharpCode(lambda))
#endif
    lambda.Compile()
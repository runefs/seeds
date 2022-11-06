module DecompileContext


open System.Reflection
open System.Reflection.Emit
open System.Linq.Expressions
open Mono.Reflection
open Types

type DecompileContext(methodInfo : System.Reflection.MethodInfo) = 
    let popInt (stack : Stack<_>) = 
        match stack.Pop() with
        (Expression(Constant(c)),_),stack ->
            c.AsInt(), stack
        | (inst,offset),stack -> failwith $"Tried to read %A{inst} at %d{offset} as an int"
        
    let readInstructions (instructions : seq<Mono.Reflection.Instruction>) = 
        let isLoadLocal op = 
            OpCodes.Ldloc_0 = op
            || OpCodes.Ldloc_1 = op
            || OpCodes.Ldloc_2 = op
            || OpCodes.Ldloc_3 = op
            || OpCodes.Ldloc_S = op
            || OpCodes.Ldloca_S = op
            || OpCodes.Ldloc = op

        let isStoreLocal op = 
            OpCodes.Stloc_0 = op
            || OpCodes.Stloc_1 = op
            || OpCodes.Stloc_2 = op
            || OpCodes.Stloc_3 = op
            || OpCodes.Stloc_S = op
            || OpCodes.Stloc = op    
        let returnLabel = 
            match instructions |> Seq.rev |> Seq.toList with
            ret::ld::_ when (ret.OpCode = OpCodes.Ret && ld.OpCode |> isLoadLocal) ->
                let ordinal = 
                    match ld.OpCode with
                    op when OpCodes.Ldloc_0 = op -> 0
                    | op when  OpCodes.Ldloc_1 = op -> 1
                    | op when  OpCodes.Ldloc_2 = op -> 2
                    | op when  OpCodes.Ldloc_3 = op -> 3
                    | op when  OpCodes.Ldloc_S = op -> (ld.Operand |> unbox |> int16 |> int)
                    | op when  OpCodes.Ldloca_S = op -> (ld.Operand |> unbox |> int16 |> int)
                    | op when  OpCodes.Ldloc = op ->  (ld.Operand |> unbox |> int16 |> int)
                    | op -> failwith $"Unexpected opcode %A{op}"

                (ld.Offset,ordinal) |> Some
            | _ -> None
        (
#if DEBUG
        instructions
        |> Seq.iter(printfn "%A")
#endif
        instructions
        |> Seq.filter(fun inst -> inst.OpCode <> OpCodes.Nop)
        |> Seq.fold(fun (stack : Stack<StackInstruction * int>) inst ->
            let offset = inst.Offset
            let i, stack = 
                match inst.OpCode with
                | op when (op = OpCodes.Call 
                           || op = OpCodes.Callvirt) -> 
                    let mi = inst.Operand :?> MethodInfo
                    let paramsCount = 
                        let parameters = mi.GetParameters()
                        if mi.IsStatic then parameters.Length
                        else parameters.Length + 1
                    let args,stack = stack.Take paramsCount
                    let args : StackExpression list = 
                        args 
                        |> List.map(function 
                            (Expression e),_ -> e 
                            | (Statement s),_-> failwith $"Expected an expression but got a statement %A{s}"
                        ) 
                    MethodInvocation(mi, args) |> Expression, stack
                | op when ((op = OpCodes.Call 
                           || op = OpCodes.Callvirt
                           || op = OpCodes.Newobj) && inst.Operand :? ConstructorInfo) ->
                    let ci = inst.Operand :?> ConstructorInfo
                    let paramsCount = ci.GetParameters().Length
                    let args,stack = stack.Take paramsCount
                    let args = 
                        args 
                        |> List.map(function 
                            (Expression e),_ -> e 
                            | (Statement s),_-> failwith $"Expected an expression but got a statement %A{s}"
                        ) 
                    CtorInvocation(ci, args) |> Expression, stack
                | op when op = OpCodes.Ldc_I4 ->
                    Int(inst.Operand |> unbox |> int) |> Constant |> Expression, stack
                | op when op = OpCodes.Ldc_I4_S ->
                    let value = 
                        match inst.Operand with
                        :? System.SByte as s -> s |> int
                        | :? System.Byte as b -> b |> int
                        | operand -> failwithf "Should not happen %A" operand
                    Int(value) |> Constant |> Expression, stack
                | op when op = OpCodes.Ldc_I4_0 -> Int(0) |> Constant |> Expression, stack
                | op when op = OpCodes.Ldc_I4_1 -> Int(1) |> Constant |> Expression, stack
                | op when op = OpCodes.Ldc_I4_2 -> Int(2) |> Constant |> Expression, stack
                | op when op = OpCodes.Ldc_I4_3 -> Int(3) |> Constant |> Expression, stack
                | op when op = OpCodes.Ldc_I4_4 -> Int(4) |> Constant |> Expression, stack
                | op when op = OpCodes.Ldc_I4_5 -> Int(5) |> Constant |> Expression, stack
                | op when op = OpCodes.Ldc_I4_6 -> Int(6) |> Constant |> Expression, stack
                | op when op = OpCodes.Ldc_I4_7 -> Int(7) |> Constant |> Expression, stack
                | op when op = OpCodes.Ldc_I4_8 -> Int(8) |> Constant |> Expression, stack
                | op when op = OpCodes.Ldc_I4_M1 -> Int(-1) |> Constant |> Expression, stack
                | op when op = OpCodes.Ldc_I8 ->
                    Int64(inst.Operand |> unbox |> int64) |> Constant |> Expression, stack
                | op when op = OpCodes.Castclass -> 
                    let (o : StackInstruction,_),stack = stack.Pop()
                    let type' = inst.Operand :?> System.Type
                    let expr = o.GetExpression()
                    Cast(type', expr) |> Expression, stack
                | op when op = OpCodes.Ldstr ->
                    String(inst.Operand :?> string) |> Constant |> Expression, stack
                | op when (op = OpCodes.Stloc || op = OpCodes.Stloc_S) -> 
                    let local = 
                        if inst.Operand :? System.Reflection.LocalVariableInfo then (inst.Operand :?> System.Reflection.LocalVariableInfo).LocalIndex
                        else inst.Operand |> unbox |> int16 |> int
                    
                    let (o,_),stack = stack.Pop()
                    StoreLocal(local,o.GetExpression()) |> Statement, stack

                | op when op = OpCodes.Stloc_0 -> 
                    let (o,_),stack = stack.Pop()
                    StoreLocal(0, o.GetExpression()) |> Statement, stack
                | op when op = OpCodes.Stloc_1 -> 
                    let (o,_),stack = stack.Pop()
                    StoreLocal(1, o.GetExpression()) |> Statement, stack
                | op when op = OpCodes.Stloc_2 -> 
                    let (o,_),stack = stack.Pop()
                    StoreLocal(2, o.GetExpression()) |> Statement, stack
                | op when op = OpCodes.Stloc_3 -> 
                    let (o,_),stack = stack.Pop()
                    StoreLocal(3, o.GetExpression()) |> Statement, stack
                //| op when op = OpCodes.Stfld -> StoreField |> Statement
                | op when op = OpCodes.Pop -> 
                    match stack.Pop() with
                    ((Expression(expr),_),stack) -> 
                        StackStatement.Pop(expr) |> Statement, stack
                    | e -> failwith $"Expected an expression but got %A{e}"
                | op when op = OpCodes.Ret -> 
                    let (o,_),stack = stack.Pop()
                    match o with
                    Statement(ReturnTarget) -> None |> Return |> Expression,stack
                    | Expression(e) -> e |> Some |> Return |> Expression, stack
                    | s -> failwith $"Expected a return target or an expression %A{s}"
                | op when op = OpCodes.Ldfld -> 
                    let instance,stack = 
                        match stack.Pop() with
                        ((Expression(e),_),stack) -> e, stack
                        | e -> failwith $"Expected an expression but got %A{e}"
                    LoadField(instance,inst.Operand :?> FieldInfo) |> Expression, stack
                | op when op = OpCodes.Ldloc ->  
                    if inst.Operand :? LocalBuilder then (inst.Operand :?> LocalBuilder).LocalIndex
                    else (inst.Operand |> unbox |> int16 |> int)
                    |> LoadLocal |> Expression, stack
                | op when (op |> isLoadLocal) && returnLabel.IsSome && inst.Offset = (returnLabel.Value |> fst) ->
                    Statement(ReturnTarget),stack
                | op when op = OpCodes.Ldloc_0 ->  0 |> LoadLocal |> Expression, stack
                | op when op = OpCodes.Ldloc_1 ->  1 |> LoadLocal |> Expression, stack
                | op when op = OpCodes.Ldloc_2 ->  2 |> LoadLocal |> Expression, stack
                | op when op = OpCodes.Ldloc_3 ->  3 |> LoadLocal |> Expression, stack
                | op when (op = OpCodes.Beq
                           || op = OpCodes.Beq_S)
                    -> 
                    let offset = (inst.Operand :?> Mono.Reflection.Instruction).Offset
                    let ((lhs,_),(rhs,_)), stack = stack.PopTuple() 
                    (Equal(lhs.GetExpression(),rhs.GetExpression()),offset) |> ConditionalBranch |> Statement , stack
                | op when op = OpCodes.Bge
                          || op = OpCodes.Bge_S
                          || op = OpCodes.Bge_Un
                          || op = OpCodes.Bge_Un_S
                    -> 
                    let ((lhs,_),(rhs,_)), stack = stack.PopTuple()
                    let offset = (inst.Operand :?> Mono.Reflection.Instruction).Offset
                    (GreaterThan(lhs.GetExpression(),rhs.GetExpression()),offset) |> ConditionalBranch |> Statement, stack
                | op when op = OpCodes.Bgt
                          || op = OpCodes.Bgt_S
                          || op = OpCodes.Bgt_Un
                          || op = OpCodes. Bgt_Un_S
                    -> 
                    let ((lhs,_),(rhs,_)), stack = stack.PopTuple()
                    let offset = (inst.Operand :?> Mono.Reflection.Instruction).Offset
                    (GreaterThanEqual(lhs.GetExpression(),rhs.GetExpression()),offset) |> ConditionalBranch |> Statement, stack
                | op when op = OpCodes.Ble
                          || op = OpCodes.Ble_S
                          || op = OpCodes.Ble_Un
                          || op = OpCodes.Ble_Un_S
                    -> 
                    let ((lhs,_),(rhs,_)), stack = stack.PopTuple()
                    let offset = (inst.Operand :?> Mono.Reflection.Instruction).Offset
                    (LessThan(lhs.GetExpression(),rhs.GetExpression()),offset) |> ConditionalBranch |> Statement, stack
                | op when op = OpCodes.Blt
                          || op = OpCodes.Blt_S
                          || op = OpCodes.Blt_Un
                          || op = OpCodes.Blt_Un_S
                    -> 
                    let ((lhs,_),(rhs,_)), stack = stack.PopTuple()
                    let offset = (inst.Operand :?> Mono.Reflection.Instruction).Offset
                    (LessThanEqual(lhs.GetExpression(),rhs.GetExpression()),offset) |> ConditionalBranch |> Statement, stack
                | op when op = OpCodes.Bne_Un
                          || op = OpCodes.Bne_Un_S
                    -> 
                    let ((lhs,_),(rhs,_)), stack = stack.PopTuple()
                    let offset = (inst.Operand :?> Mono.Reflection.Instruction).Offset
                    (NotEqual(lhs.GetExpression(),rhs.GetExpression()),offset) |> ConditionalBranch |> Statement, stack
                | op when op = OpCodes.Brfalse
                          || op = OpCodes.Brfalse_S
                    -> 
                    let (o,_), stack = stack.Pop()
                    let offset = (inst.Operand :?> Mono.Reflection.Instruction).Offset
                    (False(o.GetExpression()),offset) |> ConditionalBranch |> Statement, stack
                | op when op = OpCodes.Brtrue
                          || op = OpCodes.Brtrue_S
                    -> 
                    let (o,_), stack = stack.Pop()
                    let offset = (inst.Operand :?> Mono.Reflection.Instruction).Offset
                    (True(o.GetExpression()),offset) |> ConditionalBranch |> Statement, stack
                | op when (op = OpCodes.Br || op = OpCodes.Br_S) -> 
                    let target = (inst.Operand :?> Mono.Reflection.Instruction).Offset
                    match returnLabel with
                    Some (offset,ld) when offset = target ->
                        let lastExpr (stack : Stack<_>)= 
                            match stack.Pop() with
                            (Statement(StoreLocal(n,exp)),_), stack when ld = n -> exp,stack
                            | (Expression(e),_), stack -> e,stack
                            | s,_ -> failwith $"Unexpected early return construct %A{s}"
                        let expr,stack = lastExpr stack
                        expr |> Some |> Return |> Expression, stack
                    | _ ->
                        target
                        |> UnconditionalBranch |> Statement, stack
                | op when op = OpCodes.Ldarg_0 -> This |> Expression, stack
                | op when op = OpCodes.Ldarg_1 -> LoadArgument 1 |> Expression, stack
                | op when op = OpCodes.Ldarg_2 -> LoadArgument 2 |> Expression, stack
                | op when op = OpCodes.Ldarg_3 -> LoadArgument 3 |> Expression, stack
                | op when op = OpCodes.Ldarg -> LoadArgument (inst.Operand |> unbox |> int) |> Expression, stack
                | op when op = OpCodes.Nop -> Nop |> Statement, stack
                | op when op = OpCodes.Ldnull -> Null |> Constant |> Expression, stack
                | op when op = OpCodes.Add -> 
                    let ((lhs,_),(rhs,_)), stack = stack.PopTuple()
                    Add(lhs.GetExpression(),rhs.GetExpression()) |> Expression, stack
                | op when op = OpCodes.Ceq -> 
                    let ((lhs,_),(rhs,_)), stack = stack.PopTuple()
                    Boolean(Equal(lhs.GetExpression(),rhs.GetExpression())) |> Expression, stack
                | op when op = OpCodes.Clt -> 
                    let ((lhs,_),(rhs,_)), stack = stack.PopTuple()
                    Boolean(LessThan(lhs.GetExpression(),rhs.GetExpression())) |> Expression, stack
                | op when (op = OpCodes.Ldloc || op = OpCodes.Ldloc_S) -> 
                    let local = 
                        if inst.Operand :? System.Reflection.LocalVariableInfo then (inst.Operand :?> System.Reflection.LocalVariableInfo).LocalIndex
                        else inst.Operand |> unbox |> int16 |> int
                    local |> LoadLocal |> Expression, stack
                | op when (op = OpCodes.Leave || op = OpCodes.Leave_S) ->
                    (inst.Operand :?> Mono.Reflection.Instruction).Offset
                    |> Leave
                    |> Statement,stack
                | op when op = OpCodes.Endfinally ->
                    EndFinally
                    |> Statement, stack
                | op when (inst.Operand :? System.Type )-> 
                    let typeOperand = inst.Operand :?> System.Type
                    match op with
                    | op when op = OpCodes.Newarr ->
                        let elemCount,stack = stack |> popInt
                        let elements,stack = stack.Take elemCount
                        let elements = 
                            elements
                            |> List.map(function
                                (Expression e),offset -> e,offset
                                | e,offset -> failwith $"Expected an expression for an array element but got %A{e} at %d{offset}"
                            )
                        Expression(NewArray(typeOperand, elements)), stack

                    | _ -> failwith $"Typed op not implemented yet %A{op}"
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
            stack.Push(i,offset)
        ) Stack<_>.Empty).ToList()
        
    let instructions = 
        methodInfo.GetInstructions()
        |> Seq.filter(fun inst -> inst.OpCode <> OpCodes.Nop)
        |> readInstructions
   
    let returnType = methodInfo.ReturnType
    let result = 
        if returnType = typeof<unit> || returnType = typeof<System.Void> then
            Expression.Label(Expression.Label("Result placeholder")) :> Expression
        else
            Expression.Parameter(returnType, "<>__result__") :> Expression
    static let returnLabel = Expression.Label("return target")
    member __.ReturnType = returnType
    member __.Instructions = instructions
    member __.DeclaringType = methodInfo.DeclaringType
    static member ReturnLabel = returnLabel
    member __.MethodName with get() = methodInfo.Name
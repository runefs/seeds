module DecompileContext


open System.Reflection
open System.Reflection.Emit
open System.Linq.Expressions
open Mono.Reflection

type Language = 
    CSharp | FSharp

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

type BooleanExpression = 
    GreaterThanEqual of lhs: StackExpression * rhs: StackExpression
    | GreaterThan of lhs: StackExpression * rhs: StackExpression
    | LessThanEqual of lhs: StackExpression * rhs: StackExpression
    | LessThan of lhs: StackExpression * rhs: StackExpression
    | NotEqual of lhs: StackExpression * rhs: StackExpression
    | Equal of lhs: StackExpression * rhs: StackExpression
    | True of StackExpression
    | False of StackExpression

and Stack<'a> private(_stack : 'a list) = 
    static let _empty = Stack<'a>(List.empty)
    member __.Pop() = 
        _stack |> List.head, Stack(_stack |> List.tail)
    member __.Peek() = 
        _stack |> List.tryHead
    member __.TryPop() = 
        _stack |> List.tryHead
        |> Option.map(fun head ->
            head, Stack(_stack |> List.tail)
        )
    member __.Push(elem : 'a) = 
        Stack(elem::_stack)
    member __.Take n : 'a list * Stack<'a> = 
        _stack |> List.take n |> List.rev, Stack(_stack |> List.skip n)
    member __.PopTuple() : ('a * 'a) * Stack<'a> = 
        let rhs = _stack.Head
        let lhs = _stack.Tail.Head
        (lhs,rhs),Stack(_stack.Tail.Tail)
    member __.ToList() = 
        _stack |> List.rev
    static member Empty with get() = _empty

and CompiledExpression = 
    Expr of System.Type * Expression
    | Exprs of CompiledExpression list
    | Pop of CompiledExpression
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
    | MethodInvocation of MethodInfo * StackExpression list
    | CtorInvocation of ConstructorInfo * StackExpression list
    | Cast of System.Type * StackExpression
    | LoadLocal of Local
    | LoadField of FieldInfo
    | This
    | LoadArgument of int
    | Add of lhs: StackExpression * rhs: StackExpression
    | Boolean of BooleanExpression
    | Return of StackExpression

and StackStatement = 
    StoreField of StackExpression
    | StoreLocal of Local * StackExpression
    | Pop of StackInstruction
    | Goto of LabelTarget
    | ConditionalBranch of Condition: BooleanExpression * Offset: int
    | UnconditionalBranch of offset: int
    | Nop
and StackInstruction =
    Expression of StackExpression 
    | Statement of StackStatement
    member x.GetExpression() = 
        match x with
        Expression e -> e 
        | Statement s -> failwith $"Expected an expression but got a statement %A{s}"

and Instruction = 
    Block of CompiledExpression
    | StackInstruction of StackInstruction

type DecompileContext(deepTransform,methodInfo : System.Reflection.MethodInfo) = 
    let readInstructions (instructions : seq<Mono.Reflection.Instruction>) = 
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
                        if inst.Operand :? System.Reflection.LocalVariableInfo then Builder(inst.Operand :?> System.Reflection.LocalVariableInfo)
                        else Local.Ordinal(inst.Operand |> unbox |> int16 |> int)
                    
                    let (o,_),stack = stack.Pop()
                    StoreLocal(local,o.GetExpression()) |> Statement, stack

                | op when op = OpCodes.Stloc_0 -> 
                    let (o,_),stack = stack.Pop()
                    StoreLocal(0 |> Ordinal, o.GetExpression()) |> Statement, stack
                | op when op = OpCodes.Stloc_1 -> 
                    let (o,_),stack = stack.Pop()
                    StoreLocal(1 |> Ordinal, o.GetExpression()) |> Statement, stack
                | op when op = OpCodes.Stloc_2 -> 
                    let (o,_),stack = stack.Pop()
                    StoreLocal(2 |> Ordinal, o.GetExpression()) |> Statement, stack
                | op when op = OpCodes.Stloc_3 -> 
                    let (o,_),stack = stack.Pop()
                    StoreLocal(3 |> Ordinal, o.GetExpression()) |> Statement, stack
                //| op when op = OpCodes.Stfld -> StoreField |> Statement
                | op when op = OpCodes.Pop -> 
                    let (o,_),stack = stack.Pop()
                    Pop(o) |> Statement, stack
                | op when op = OpCodes.Ret -> 
                    let (o,_),stack = stack.Pop()
                    Return(o.GetExpression()) |> Expression, stack
                | op when op = OpCodes.Ldfld -> LoadField(inst.Operand :?> FieldInfo) |> Expression, stack
                | op when op = OpCodes.Ldloc ->
                    let local  = 
                        if inst.Operand :? LocalBuilder then Builder(inst.Operand :?> LocalBuilder)
                        else Local.Ordinal(inst.Operand |> unbox |> int16 |> int)
                    local |> LoadLocal |> Expression, stack
                | op when op = OpCodes.Ldloc_0 ->  0 |> Ordinal |> LoadLocal |> Expression, stack
                | op when op = OpCodes.Ldloc_1 ->  1 |> Ordinal |> LoadLocal |> Expression, stack
                | op when op = OpCodes.Ldloc_2 ->  2 |> Ordinal |> LoadLocal |> Expression, stack
                | op when op = OpCodes.Ldloc_3 ->  3 |> Ordinal |> LoadLocal |> Expression, stack
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
                    let offset = (inst.Operand :?> Mono.Reflection.Instruction).Offset
                    offset |> UnconditionalBranch |> Statement, stack
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
                | op when op = OpCodes.Ldloc_S ->
                    inst.Operand :?> System.Reflection.LocalVariableInfo |> Builder |> LoadLocal |> Expression, stack
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
            if deepTransform then
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
    static let returnLabel = Expression.Label("return target")
    member __.GetOrCreateVariable = getOrCreateVariable
    member __.Result = result
    member __.ReturnType = returnType
    member __.GetParameterExpression ident = parameterExpressions.[parameterNames.[ident]]
    member __.GetParameterExpressionByName name = parameterExpressions.[name]
    member __.ParameterExpressions = parameterExpressions |> Map.toSeq
    member __.Parameters = parameters
    member __.DeclaredParameters = declaredParameters
    member __.Instructions = instructions
    member __.Variables = variables |> Map.toSeq
    member __.GetVariable name = 
        let qualifiedName = $"%s{methodInfo.Name}__%s{name}"
        variables |> Map.tryFind qualifiedName
        |> Option.orElse(
            try
                variables.[qualifiedName] |> Some
            with :? System.Collections.Generic.KeyNotFoundException ->
                failwith $"Tried finding var '%s{qualifiedName}/%s{name}' in %A{variables}"
                None
        ) |> Option.get
    member __.TryGetVariable name = 
        let qualifiedName = $"%s{methodInfo.Name}__%s{name}"
        variables |> Map.tryFind qualifiedName
        |> Option.orElse(variables |> Map.tryFind name)
    member __.DeepTransform = deepTransform
    member __.DeclaringType = methodInfo.DeclaringType
    member __.ParameterOrdinals = 
        parameterNames
        |> Map.toSeq
        |> Seq.map(fun (i,name) -> name, i)
        |> Map.ofSeq
    member __.AddVariables vars = 
        variables <- 
            vars
            |> Seq.fold(fun vs (name, expr) ->
                match vs |> Map.tryFind name with
                None -> vs.Add(name,expr)
                | Some _ -> vs
            ) variables
    static member ReturnLabel = returnLabel
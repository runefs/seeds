[<AutoOpen>]
module Types

open System.Reflection
open System.Linq.Expressions

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
         member x.AsInt() = 
             match x with 
             Byte n ->n |> int
            | Int16 n ->n |> int
            | Int n ->n
            | Int64 n ->n |> int
            | String _ 
            | Single _ 
            | Float _ 
            | Null -> failwith $"Invalid type. Expected an interger type but got %s{x.Type.Name}"

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
        
and StackExpression =
    | Constant of Constant
    | MethodInvocation of MethodInfo * StackExpression list
    | CtorInvocation of ConstructorInfo * StackExpression list
    | Cast of System.Type * StackExpression
    | LoadLocal of int
    | LoadField of instance: StackExpression * FieldInfo
    | This
    | LoadArgument of int
    | Add of lhs: StackExpression * rhs: StackExpression
    | Boolean of BooleanExpression
    | Return of StackExpression option
    | NewArray of System.Type * elements: (StackExpression * int) list

and StackStatement = 
    StoreField of StackExpression
    | StoreLocal of int * StackExpression
    | Pop of StackExpression
    | Goto of LabelTarget
    | ConditionalBranch of Condition: BooleanExpression * Offset: int
    | UnconditionalBranch of target: int
    | Leave of target: int
    | EndFinally
    | ReturnTarget
    | Nop
and StackInstruction =
    Expression of StackExpression 
    | Statement of StackStatement
    member x.GetExpression() = 
        match x with
        Expression e -> e 
        | Statement s -> failwith $"Expected an expression but got a statement %A{s}"

type VariableCollection private(rootName : string, inherited : VariableCollection option, args, this : System.Type option) =
    let parameterName i = 
        $"%s{i}__Param__"
    let isParameter (n : string) = n.EndsWith "__Param__"
    let mutable variables = 
        let s = 
            match this with
            None -> Map.empty
            | Some t -> Map.empty.Add(parameterName "this",(-1,Expression.Parameter(t)))
        args
        |> List.fold(fun args (t,(i:int),name) ->
            let p = Expression.Parameter(t,name)
            args
            |> Map.add (i + 1 |> string |> parameterName) (i,p)
            |> Map.add (name |> parameterName) (i,p)
        ) s
   
    static let _empty = VariableCollection("",None,[],None)
    static member Empty = _empty
    member private x.GetQualifiedName name = 
        $"%s{x.RootName}__%s{name}"
    member private x.ParameterName (i : int) =
        i |> string |> parameterName
    
    member x.GetOrCreateVariable(t: System.Type) (name: string) = 
        let actualName = x.GetQualifiedName name
        match x.TryGet name with
        None ->
            let v = Expression.Variable(t,actualName)
            variables <- variables.Add(actualName,(variables |> Map.count, v))
            v
        | Some v -> 
            v
    new(methodInfo : MethodInfo) =
        let ``this`` = 
            if methodInfo.IsStatic |> not then
                methodInfo.DeclaringType |> Some
            else None
        let args = 
            methodInfo.GetParameters()
            |> Array.mapi(fun i a -> a.ParameterType,i,a.Name)
            |> Array.toList
        VariableCollection(methodInfo.Name, None,args,``this``)
    member x.TryGet name : ParameterExpression option= 
        inherited 
        |> Option.bind(fun inherited -> inherited.TryGet name)
        |> Option.orElse(
            variables
            |>Map.tryFind name
            |> Option.map snd
            |> Option.orElse(
                variables 
                |> Map.tryFind (x.GetQualifiedName name)
                |> Option.map snd
            )
        )
    member x.GetArgument (i : int) = 
        x.[i |> string |> parameterName]
    member x.GetArgument (i : string) = 
        x.[i |> parameterName]
    member x.AddArgument(t,(i:int)) = 
        i |> x.ParameterName |> x.GetOrCreateVariable t  
    member x.AddArgument(t,(i:string)) = 
        i |> parameterName |> x.GetOrCreateVariable t
    member x.AllVariables() = 
        variables |> Map.toArray
        |> Array.filter(fst >> isParameter >> not) 
        |> Array.map(snd)
        |> Array.sortBy fst
        |> Array.map snd
    member __.RootName =
        match inherited with
        None-> rootName
        | Some i when i.RootName = "" -> rootName
        | Some i -> 
            if rootName = "" then i.RootName
            else $"%s{i.RootName}__%s{rootName}"
    member x.Item with get(name) = 
        match x.TryGet(name) with
        None -> failwith $"No variable or parameter with the name: '%s{name}' in %A{variables}"
        | Some v -> v
    member x.AllParameters with get() = 
        variables
        |> Map.toArray
        |> Array.filter(fst >> isParameter)
        |> Array.map snd
        |> Array.sortBy fst
        |> Array.map snd
        |> Array.distinct
    member x.Child() =
       VariableCollection("",Some x,[],None)
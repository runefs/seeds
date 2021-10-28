module Template

type List() =
   member __.Create() = 
       [for i in 1..10 -> i]
   member __.Create2() = 
       [for i in 1..10 -> 
           i * int(System.Random().Next())
           ]

type While() = 
    member __.While() = 
        let mutable lst = 0
        while lst < 10 do
            printfn "%d" lst
            lst <- lst + 1
        
        printfn "Final result: %d" lst
        printfn ""
    (*member __.While2() = 
        let mutable lst = List().Create()
        while lst |> List.isEmpty |> not do
            printfn "Head: %d" (lst |> List.head)
            lst <- lst |> List.tail*)
type DeepTransform() = 
    member __.Square arg = arg + arg
    member this.Square2 = 
        this.Square 2

type If() = 
    let localField = true
    let localVal = 5
    member __.If() = 
       let x = 
          if 1 = 2 then
              printfn "ERROR 1"
              -1
          else
              printfn "some OTHER line"
              1
       x
   
    member __.IfDifferent() =
        if 1 <> 2 then
           printfn "some line"          
           2
        else
           printfn "ERROR 2"
           -1

    member __.IfField() = 
        if localField then
           printfn "some line"          
           3
        else
           printfn "ERROR 3"
           -1
          
    member x.IfLocal() = 
        let localVar = true 
        if localVar then          
           let res = 4
           x.IfNoElse res
           res                                                                                                                                                                                  
        else
           printfn "ERROR 4"
           -1

    member __.IfNoElse arg = 
        if localVal > arg then
           printfn "sub method %d" arg
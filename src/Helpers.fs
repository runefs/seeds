module Helpers

open System.Reflection
open System.Reflection.Emit
open Mono.Reflection


let printMethod printDebug lineMarker (mi : MethodInfo) =
    printfn "*** %s ***" mi.Name
    let sprintfOffset = sprintf "IL_%04X"
    let printInstruction (inst : Instruction) = 
        let indent = sprintf "\t %s%s" lineMarker <| sprintfOffset inst.Offset
        let operand = inst.Operand
        if operand |> isNull then
            printfn "%s %A" indent inst.OpCode
        elif operand :? Instruction then
            let operand = inst.Operand :?> Instruction
            printfn "%s %A Label: %s " indent inst.OpCode (operand.Offset |> sprintfOffset)
        else
            printfn "%s %A (%s) %A" indent inst.OpCode (operand.GetType().Name) operand
    let inst = 
        mi.GetInstructions()
        |> Seq.filter(fun inst -> inst.OpCode <> OpCodes.Nop)
    if printDebug  then
        inst
        |> Seq.iter (printInstruction)
        printfn "*******************"
        printfn ""
    inst
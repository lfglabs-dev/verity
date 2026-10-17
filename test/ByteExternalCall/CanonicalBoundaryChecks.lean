import Compiler.SolidityImport.TransactionAccess
import Verity.Core.Model.DenoteByteExternalCalls

open Compiler.CompilationModel Denote
open SolidityImport.Transactions

private def oracle : DenoteOracle :=
  { mappingSlot := fun _ _ => 0, keccakMemorySlice := fun _ _ _ => 0 }

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def failed : StmtOutcome → Bool
  | .revert => true
  | _ => false

private def state : DenoteState :=
  { world := Verity.defaultState.writePhysicalMemoryValue 64 128,
    bindings := [], byteCallGas := some 100000 }

private def module := Compiler.ECM.SolidityStaticCall.uint256Module "result" 0xa035b1fe 2

private def revertBytes : StmtOutcome → List UInt8
  | .revertWithData bytes => bytes
  | _ => [0xff]

private def nextState : StmtOutcome → IO DenoteState
  | .continue next => pure next
  | _ => throw (IO.userError "expected byte-call continuation")

def main : IO UInt32 := do
  check (failed (execStmt oracle [] state (.ecm module [.literal 23, .literal 1, .literal 255])))
    "missing adversary must fail as instrumentation"
  let short := DenoteByteExternalCalls.staticAdversary fun _ _ => (true, [0], [.contractSlot 23 7])
  let configured := { state with byteCallAdversary := some short }
  let args : List Expr := [.literal 23, .literal 1, .literal 255]
  let prepared ← IO.ofExcept (prepareByteStaticCall oracle [] configured "result" 0xa035b1fe 2 args)
  check (prepared.request.calldata == [0xa0, 0x35, 0xb1, 0xfe] ++
    wordBytes 1 ++ wordBytes 255) "unaligned ABI scratch encoding differs"
  check ((prepared.frame.world.memory 64).val == 224) "allocation pointer differs"
  let (shortOutcome, touched) ← IO.ofExcept
    (executeByteStaticCall oracle [] configured module "result" 0xa035b1fe 2 args)
  check (revertBytes shortOutcome == []) "short success must revert empty"
  check (touched == [.contractSlot 23 7]) "short success lost foreign access"
  let raw := (List.range 65).map UInt8.ofNat
  let success := DenoteByteExternalCalls.staticAdversary fun _ _ =>
    (true, raw, [.contractSlot 23 9])
  let full := { configured with byteCallAdversary := some success }
  let next ← nextState (execStmt oracle [] full (.ecm module args))
  check (next.rawReturndata == some raw) "oversized response buffer truncated"
  check (evalExpr oracle [] next .returndataSize == some 65) "raw returndata size differs"
  let copied ← nextState (execStmt oracle [] next
    (.returndataCopy (.literal 7) (.literal 1) (.literal 33)))
  check ((List.range 33).all fun i =>
    (copied.world.physicalByte (7+i)).val == i+1) "unaligned raw copy differs"
  check ((copied.world.physicalByte 6).val == 0 &&
    (copied.world.physicalByte 40).val == 0) "raw copy overwrote outside bytes"
  check (failed (execStmt oracle [] next
    (.returndataCopy (.literal 7) (.literal 64) (.literal 2)))) "out-of-bounds copy accepted"
  check (revertBytes (execStmt oracle [] next .revertReturndata) == raw) "revert buffer padded"
  check (failed (execStmt oracle [] { full with byteCallGas := none } (.ecm module args)))
    "missing gas must fail as instrumentation"
  check (failed (execStmt oracle [] full (.ecm { module with writesState := true } args)))
    "contradictory descriptor metadata accepted"
  check (failed (execStmt oracle [] full (.ecm module [.literal 23]))) "wrong arity accepted"
  let rawFail := DenoteByteExternalCalls.staticAdversary fun _ _ =>
    (false, [0, 1, 0], [.contractSlot 23 11])
  let reverted := { full with byteCallAdversary := some rawFail }
  let traced ← IO.ofExcept (traceStraightLine oracle [] reverted [.ecm module args])
  check (revertBytes traced.outcome == [0, 1, 0]) "failure bytes changed"
  check (traced.touched == [.contractSlot 23 11]) "cancelled foreign access lost"
  -- Sequential evaluation: the second argument reads bytes written by the first.
  let memoryArgs : List Expr := [.mload (.literal 64), .literal 1, .mload (.literal 132)]
  let dependent ← IO.ofExcept
    (prepareByteStaticCall oracle [] full "result" 0xa035b1fe 2 memoryArgs)
  check (dependent.request.target == 224) "target evaluated before scratch allocation"
  check (dependent.request.calldata == [0xa0, 0x35, 0xb1, 0xfe] ++
    wordBytes 1 ++ wordBytes 1) "arguments evaluated before preceding stores"
  -- Legacy calls overwrite the exact buffer rather than leaking stale bytes.
  let legacy := {
    next with
    externalCallSucceeded := fun _ => true
    externalCallReturnValues := fun _ => [1]
  }
  let overwritten ← nextState (execStmt oracle [] legacy
    (.externalCallBind ["legacy"] "mock" []))
  check (overwritten.rawReturndata.isNone) "legacy call retained stale raw buffer"
  check (evalExpr oracle [] overwritten .returndataSize == some 32) "legacy size did not replace raw size"
  -- Fresh transactions erase physical memory as well as word observations.
  let fresh := beginTransaction next.world
  check ((fresh.physicalByte 128).val == 0 && (fresh.memory 64).val == 0)
    "transaction retained physical scratch bytes"
  let emitted ← IO.ofExcept (Compiler.ECM.SolidityStaticCall.compileUint256 "result" 0xa035b1fe 0
    [Compiler.Yul.YulExpr.ident "__solidity_static_ptr"])
  let scratch := match emitted with
    | [_, .block (.let_ name _ :: _)] => name
    | _ => ""
  check (!scratch.isEmpty && scratch != "__solidity_static_ptr")
    "emitted scratch local captured target argument"
  IO.println "canonical byte-call boundary checks passed"
  return 0

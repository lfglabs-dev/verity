import Compiler.SolidityImport.TransactionAccess
open Compiler.CompilationModel
open Compiler.CompilationModel.SolidityImport.Transactions

private def oracle : Denote.DenoteOracle := ⟨fun _ _ => 0, fun _ _ _ => 0⟩
private def fields : List Field :=
  [{ name := "gate", ty := .uint256, slot := some 0 },
   { name := "out", ty := .uint256, slot := some 1 }]
private def initial : Denote.DenoteState :=
  { world := (Verity.defaultState.writeSlot 0 1).writeSlot 1 5, bindings := [] }
private def forbidden : Stmt := .letVar "unused" (.storage "missing")
private def selected : List Stmt :=
  [.setStorage "out" (.literal 7),
   .ite (.eq (.storage "out") (.literal 7))
     [.returnValues [.storage "out"]] [forbidden],
   forbidden]

def main : IO Unit := do
  let result ← IO.ofExcept (traceStraightLine oracle fields initial
    [.ite (.storage "gate") selected [forbidden], forbidden])
  unless result.touched == [.slot 0, .slot 1, .slot 1, .slot 1] do
    throw (IO.userError "trace included unexecuted accesses or missed executed accesses")
  match result.outcome with
  | .stop state =>
      unless state.world.readSlot 1 == 7 && state.observedReturnWords == some [7] do
        throw (IO.userError "trace lost branch state or return words")
  | _ => throw (IO.userError "expected selected branch early return")
  let failed ← IO.ofExcept (traceStraightLine oracle fields initial
    [.ite (.storage "gate") [.setStorage "out" (.literal 9), .panic .divisionByZero, forbidden]
      [forbidden], forbidden])
  unless failed.touched == [.slot 0, .slot 1] do
    throw (IO.userError "reverted branch accesses were lost or continued after panic")
  match failed.outcome with
  | .revertWithData bytes =>
      unless bytes.length == 36 do throw (IO.userError "panic bytes were lost")
  | _ => throw (IO.userError "expected rich panic outcome")
  let bad := traceStraightLine oracle fields initial [.ite (.literal 0) [] [forbidden]]
  match bad with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "executed unsupported read was accepted")
  let memoryLoop ← IO.ofExcept (traceStraightLine oracle fields initial
    [.mstore (.storage "gate") (.storage "out"),
     .forEach "i" (.literal 2)
       [.setStorage "out" (.add (.storage "out") (.mload (.storage "gate")))],
     .returnValues [.storage "out"]])
  unless memoryLoop.touched ==
      [.slot 0, .slot 1, .slot 1, .slot 0, .slot 1, .slot 1, .slot 0, .slot 1, .slot 1] do
    throw (IO.userError "memory/loop trace missed expression reads or iteration accesses")
  match memoryLoop.outcome with
  | .stop state =>
      unless state.observedReturnWords == some [15] do
        throw (IO.userError "loop did not carry Denote state between iterations")
  | _ => throw (IO.userError "loop return was not observed")
  let emptyLoop ← IO.ofExcept (traceStraightLine oracle fields initial
    [.forEach "i" (.literal 0) [forbidden], .returnValues [.localVar "i"]])
  unless emptyLoop.touched == [] do throw (IO.userError "empty loop observed its body")
  match emptyLoop.outcome with
  | .stop state =>
      unless state.observedReturnWords == some [0] do
        throw (IO.userError "empty loop omitted initial index binding")
  | _ => throw (IO.userError "empty loop return was not observed")
  let loopBody : List Stmt :=
    [.setStorage "out" (.localVar "i"),
     .ite (.eq (.localVar "i") (.literal 1)) [.panicCode (.literal 0x32)] [],
     .setStorage "out" (.literal 9)]
  let loopRevert ← IO.ofExcept (executeTracedBody oracle fields initial.world []
    [.forEach "i" (.literal 3) loopBody, forbidden])
  unless loopRevert.touched == [.slot 1, .slot 1, .slot 1] &&
      !loopRevert.frame.success && loopRevert.frame.world.readSlot 1 == 5 &&
      loopRevert.frame.data == [0x4e, 0x48, 0x7b, 0x71] ++ List.replicate 31 0 ++ [0x32] do
    throw (IO.userError "loop revert lost touches/payload/rollback or ran later iterations")
  let nested ← IO.ofExcept (traceStraightLine oracle fields initial
    [.forEach "i" (.storage "gate")
      [.forEach "j" (.literal 2) [.setStorage "out" (.localVar "j")]],
     .returnValues [.storage "out"]])
  unless nested.touched == [.slot 0, .slot 1, .slot 1, .slot 1] do
    throw (IO.userError "nested loop count/body accesses differ")
  match traceStraightLine oracle fields initial [.forEach "i" (.literal 1) [forbidden]] with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "loop accepted an executed unsupported read")
  IO.println "selected branch, state advancement, early return, panic and rejection checks passed"

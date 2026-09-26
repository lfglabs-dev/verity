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
  IO.println "selected branch, state advancement, early return, panic and rejection checks passed"

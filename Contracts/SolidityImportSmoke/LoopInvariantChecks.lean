import Compiler.SolidityImport.LoopInvariants

namespace SolidityImportSmoke.LoopInvariantChecks
open Compiler.CompilationModel Compiler.CompilationModel.Denote

def fields : List Field := [{ name := "stored", ty := .uint256 }]
def invariant (_ : Nat) (state : DenoteState) : Prop := (state.world.storage 0).val ≤ 1

/-- A concrete storage-writing loop, for every dynamically evaluated bound.
Early exits are forbidden by the postcondition rather than discarded. -/
theorem write_loop_preserves (oracle : DenoteOracle) (state : DenoteState)
    (count : Expr) (bound : Nat)
    (evaluated : evalExpr oracle fields state count = some bound)
    (initial : invariant 0 state) :
    LoopOutcomePost (invariant bound) (fun _ => False)
      (execStmt oracle fields state
        (.forEach "i" count [.setStorage "stored" (.literal 1)])) := by
  apply forEach_invariant oracle fields "i" count _ invariant (fun _ => False)
    state bound evaluated initial
  intro index before _
  change (1 : Nat) ≤ 1
  decide

/-- A revert exits on the first iteration and retains its exact payload. -/
theorem loop_panic_bytes (oracle : DenoteOracle) (state : DenoteState)
    (remaining index : Nat) :
    execForEachLoop "i"
      (fun before => execStmtList oracle fields before [.panicCode (.literal 1)])
      state index (remaining + 1) = .revertWithData (panicBytes 1) := by
  rfl

end SolidityImportSmoke.LoopInvariantChecks

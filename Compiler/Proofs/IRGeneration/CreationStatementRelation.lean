import Compiler.Proofs.IRGeneration.CreationMemoryWhole
import Compiler.Proofs.IRGeneration.CreationMemoryLayout
import Verity.Core.Model.DenoteCreationStatement

namespace Compiler.Proofs.IRGeneration.CreationStatementRelation
open Compiler.CompilationModel Compiler.CompilationModel.Denote
open Verity.Core.Model CreationMemoryFrames CreationMemoryOperation

/-- Observation erases only caller memory. Every interpreter outcome, binding,
revert byte and execution-context field is retained. This is not execution input. -/
def eraseState (state : DenoteState) : DenoteState :=
  { state with world := eraseMemory state.world }

def eraseOutcome : StmtOutcome → StmtOutcome
  | .continue state => .continue (eraseState state)
  | .stop state => .stop (eraseState state)
  | .return value state => .return value (eraseState state)
  | .exceptional state => .exceptional (eraseState state)
  | .revert => .revert
  | .revertWithData data => .revertWithData data
  | .interpretationError message => .interpretationError message

/-- Restore actual interpreter state from the computed operation, without
substituting the seed's world, bindings or context into that computation. -/
def finish (seed : DenoteState) (destination : String) : Except String Create2Operation.Result → StmtOutcome
  | .error message => .interpretationError message
  | .ok (.exceptional frame) => .exceptional
      { seed with
        world := frame.world
        executionContext := some { opcode := frame.context, warm := frame.warm } }
  | .ok (.continued value frame) => .continue
      { seed with
        world := frame.world
        executionContext := some { opcode := frame.context, warm := frame.warm }
        bindings := bindValue seed.bindings destination value.val }

theorem execCreation_finish (oracle : DenoteOracle) (fields : List Field)
    (seed : DenoteState) (context : ExecutionContext) (destination : String)
    (offset size salt : Expr) (o n s : Nat)
    (resolved : evalExprList oracle fields seed [offset, size, salt] = some [o,n,s])
    (actual : seed.executionContext = some context) :
    execCreation oracle fields seed destination offset size salt =
      finish seed destination (Create2Operation.run ⟨seed.world, context.opcode, context.warm⟩
        (Verity.Core.Uint256.ofNat o) (Verity.Core.Uint256.ofNat n) (Verity.Core.Uint256.ofNat s)) := by
  simp only [execCreation, resolved, actual]
  cases executed : Create2Operation.run ⟨seed.world, context.opcode, context.warm⟩
      (Verity.Core.Uint256.ofNat o) (Verity.Core.Uint256.ofNat n) (Verity.Core.Uint256.ofNat s) with
  | error message => rfl
  | ok result => cases result <;> rfl

/-- All caller bindings and every nonmemory field survive this abstraction. -/
theorem finish_erase (seed : DenoteState) (destination : String)
    (computed : Except String Create2Operation.Result) :
    eraseOutcome (finish seed destination computed) =
      finish (eraseState seed) destination (computed.map eraseResult) := by
  cases computed with
  | error message => rfl
  | ok result =>
    cases result <;> simp only [finish, eraseOutcome, eraseState, Except.map, eraseResult, eraseFrame]

/-- Transport an actual creation result between independent interpreter states.
The premise is operation equivalence, never a selected final world or result. -/
theorem statement_of_operation (oracle : DenoteOracle) (fields : List Field)
    (left right : DenoteState) (context : ExecutionContext) (destination : String)
    (loffset roffset size salt : Expr) (lo ro n s : Nat)
    (lresolved : evalExprList oracle fields left [loffset, size, salt] = some [lo,n,s])
    (rresolved : evalExprList oracle fields right [roffset, size, salt] = some [ro,n,s])
    (lactual : left.executionContext = some context) (ractual : right.executionContext = some context)
    (same : eraseState left = eraseState right)
    (operation :
      (Create2Operation.run ⟨left.world, context.opcode, context.warm⟩
        (Verity.Core.Uint256.ofNat lo) (Verity.Core.Uint256.ofNat n) (Verity.Core.Uint256.ofNat s)).map eraseResult =
      (Create2Operation.run ⟨right.world, context.opcode, context.warm⟩
        (Verity.Core.Uint256.ofNat ro) (Verity.Core.Uint256.ofNat n) (Verity.Core.Uint256.ofNat s)).map eraseResult) :
    eraseOutcome (execStmt oracle fields left (.create2 destination loffset size salt)) =
      eraseOutcome (execStmt oracle fields right (.create2 destination roffset size salt)) := by
  rw [execStmt_create2, execStmt_create2,
    execCreation_finish oracle fields left context destination loffset size salt lo n s lresolved lactual,
    execCreation_finish oracle fields right context destination roffset size salt ro n s rresolved ractual,
    finish_erase, finish_erase, same, operation]

/-- Full actual CREATE2 statement transport from independently computed prefix
states, with all outcomes/bindings/context retained and only memory abstracted. -/
theorem statement_equivalence (oracle : DenoteOracle) (fields : List Field)
    (left right : DenoteState) (context : ExecutionContext) (destination : String)
    (offset size salt : Expr) (o n s : Nat)
    (lresolved : evalExprList oracle fields left [offset, size, salt] = some [o,n,s])
    (rresolved : evalExprList oracle fields right [offset, size, salt] = some [o,n,s])
    (lactual : left.executionContext = some context) (ractual : right.executionContext = some context)
    (same : eraseState left = eraseState right)
    (extent : left.world.byteMemory.size = right.world.byteMemory.size)
    (slice : ∀ index < (Verity.Core.Uint256.ofNat n).val,
      left.world.physicalByte ((Verity.Core.Uint256.ofNat o).val + index) =
      right.world.physicalByte ((Verity.Core.Uint256.ofNat o).val + index)) :
    eraseOutcome (execStmt oracle fields left (.create2 destination offset size salt)) =
      eraseOutcome (execStmt oracle fields right (.create2 destination offset size salt)) := by
  have related : Related left.world right.world := by
    have projected := congrArg (fun state : DenoteState => state.world) same
    change eraseMemory left.world = eraseMemory right.world
    simpa only [eraseState] using projected
  have operation := operation_equivalence left.world right.world context.opcode context.warm
    (Verity.Core.Uint256.ofNat o) (Verity.Core.Uint256.ofNat n) (Verity.Core.Uint256.ofNat s)
    related extent slice
  exact statement_of_operation oracle fields left right context destination offset offset size salt
    o o n s lresolved rresolved lactual ractual same operation

/-- Different allocated buffer layouts can also use the real statement bridge.
The caller supplies actual prepare equations; gas is derived from coverage. -/
theorem statement_layout_equivalence (oracle : DenoteOracle) (fields : List Field)
    (left right : DenoteState) (context : ExecutionContext) (destination : String)
    (loffset roffset size salt : Expr) (lo ro n s : Nat)
    (lchild rchild : Create2Entry.Forwarded)
    (lresolved : evalExprList oracle fields left [loffset, size, salt] = some [lo,n,s])
    (rresolved : evalExprList oracle fields right [roffset, size, salt] = some [ro,n,s])
    (lactual : left.executionContext = some context) (ractual : right.executionContext = some context)
    (same : eraseState left = eraseState right)
    (lprep : Create2Entry.prepare left.world.byteMemory context.opcode
      (Verity.Core.Uint256.ofNat lo).val (Verity.Core.Uint256.ofNat n).val = .ok (.forwarded lchild))
    (rprep : Create2Entry.prepare right.world.byteMemory context.opcode
      (Verity.Core.Uint256.ofNat ro).val (Verity.Core.Uint256.ofNat n).val = .ok (.forwarded rchild))
    (legal : (left.world.creationAccounts left.world.thisAddress.val).nonce < Create2NonceEntry.maxCreatorNonce)
    (lcovered : (Verity.Core.Uint256.ofNat lo).val + (Verity.Core.Uint256.ofNat n).val ≤ left.world.byteMemory.size)
    (rcovered : (Verity.Core.Uint256.ofNat ro).val + (Verity.Core.Uint256.ofNat n).val ≤ right.world.byteMemory.size)
    (code : Create2.physicalInitcodeBytes left.world (Verity.Core.Uint256.ofNat lo).val (Verity.Core.Uint256.ofNat n).val =
      Create2.physicalInitcodeBytes right.world (Verity.Core.Uint256.ofNat ro).val (Verity.Core.Uint256.ofNat n).val) :
    eraseOutcome (execStmt oracle fields left (.create2 destination loffset size salt)) =
      eraseOutcome (execStmt oracle fields right (.create2 destination roffset size salt)) := by
  have related : Related left.world right.world := by
    have projected := congrArg (fun state : DenoteState => state.world) same
    change eraseMemory left.world = eraseMemory right.world
    simpa only [eraseState] using projected
  have operation := CreationLayoutOperation.covered_layout_equivalence left.world right.world
    context.opcode context.warm (Verity.Core.Uint256.ofNat lo) (Verity.Core.Uint256.ofNat ro)
    (Verity.Core.Uint256.ofNat n) (Verity.Core.Uint256.ofNat s) lchild rchild lprep rprep
    related legal lcovered rcovered code
  exact statement_of_operation oracle fields left right context destination loffset roffset size salt
    lo ro n s lresolved rresolved lactual ractual same operation

end Compiler.Proofs.IRGeneration.CreationStatementRelation

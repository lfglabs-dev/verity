import Compiler.Proofs.IRGeneration.GuardedSpec
import Verity.Core.Model.NonReentrantGuard

/-!
# Guarded source semantics and its bridge to the compiled guard

The source semantics of an annotated function, defined via the existing
`interpretFunction`: a locked entry reverts; a free entry is the plain
interpretation from the lock-acquired world.  `SourceContractResult` does not
observe transient storage, so the release is invisible on both sides — the
free case therefore reuses the whole existing correspondence stack verbatim
at the acquired world, and only record-commutation glue is new.
-/
namespace Compiler.Proofs.IRGeneration

open Compiler.Yul
open Compiler.CompilationModel
open Verity.Core.NonReentrantGuard
open Compiler.Proofs.IRGeneration.Function

/-- Source semantics of a `nonreentrant`-annotated function. -/
def interpretGuardedFunction (spec : CompilationModel) (lockSlot : Nat)
    (fn : FunctionSpec) (tx : IRTransaction)
    (initialWorld : Verity.ContractState) : SourceSemantics.SourceContractResult :=
  if (initialWorld.transientStorage lockSlot).val = 1 then
    SourceSemantics.revertedResult spec
      (SourceSemantics.withTransactionContext initialWorld tx)
  else
    SourceSemantics.interpretFunction spec fn tx
      (setLock lockSlot 1 initialWorld)

/-- Acquiring the lock commutes with installing the transaction context. -/
theorem withTransactionContext_setLock (world : Verity.ContractState)
    (tx : IRTransaction) (slot : Nat) (v : Verity.Uint256) :
    SourceSemantics.withTransactionContext (setLock slot v world) tx =
      setLock slot v (SourceSemantics.withTransactionContext world tx) := rfl

/-- The dynamic-array scan never reads transient storage. -/
theorem findDynamicArrayElementAtSlot_go_setLock
    (world : Verity.ContractState) (targetSlot lockSlot : Nat)
    (v : Verity.Uint256) :
    ∀ (remaining : List Field) (idx : Nat),
      SourceSemantics.findDynamicArrayElementAtSlot.go
          (setLock lockSlot v world) targetSlot remaining idx =
        SourceSemantics.findDynamicArrayElementAtSlot.go
          world targetSlot remaining idx
  | [], _ => rfl
  | field :: rest, idx => by
      simp only [SourceSemantics.findDynamicArrayElementAtSlot.go]
      rw [show (setLock lockSlot v world).storageArray = world.storageArray
        from rfl,
        findDynamicArrayElementAtSlot_go_setLock world targetSlot lockSlot v
          rest (idx + 1)]

/-- `encodeStorageAt` never reads transient storage. -/
theorem encodeStorageAt_setLock (fields : List Field)
    (world : Verity.ContractState) (lockSlot : Nat) (v : Verity.Uint256)
    (slot : Nat) :
    SourceSemantics.encodeStorageAt fields (setLock lockSlot v world) slot =
      SourceSemantics.encodeStorageAt fields world slot := by
  unfold SourceSemantics.encodeStorageAt
  rw [show SourceSemantics.findDynamicArrayElementAtSlot fields
      (setLock lockSlot v world) slot =
    SourceSemantics.findDynamicArrayElementAtSlot fields world slot from
    findDynamicArrayElementAtSlot_go_setLock world slot lockSlot v fields 0]
  cases SourceSemantics.findResolvedFieldAtSlot fields slot <;> rfl

/-- The initial IR state of the lock-acquired world is the lock overlay of
the initial IR state. -/
theorem initialIRStateForTx_setLock (spec : CompilationModel)
    (tx : IRTransaction) (world : Verity.ContractState) (slot : Nat) :
    FunctionBody.initialIRStateForTx spec tx (setLock slot 1 world) =
      { FunctionBody.initialIRStateForTx spec tx world with
        transientStorage := fun o =>
          if o = slot then 1 else (world.transientStorage o).val } := by
  simp only [FunctionBody.initialIRStateForTx]
  congr 1
  all_goals first
    | rfl
    | (funext o
       exact congrArg IRStorageWord.ofNat
         (encodeStorageAt_setLock _ world slot 1 o.toNat))
    | (funext o
       by_cases h : o = slot <;> simp [setLock, h])

/-- The revert projection ignores transient storage: overlaying the lock on
the rollback state does not change it. -/
theorem execResultToIRResult_lock_overlay (spec : CompilationModel)
    (tx : IRTransaction) (world : Verity.ContractState) (slot : Nat)
    (r : IRExecResult) :
    execResultToIRResult
        (FunctionBody.initialIRStateForTx spec tx (setLock slot 1 world)) r =
      execResultToIRResult
        (FunctionBody.initialIRStateForTx spec tx world) r := by
  rw [initialIRStateForTx_setLock]
  cases r <;> rfl

/-- Locked entry: the source revert matches the IR revert projection. -/
theorem revertedResult_matches_revert_projection (spec : CompilationModel)
    (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (s : IRState) :
    FunctionBody.sourceResultMatchesIRResult
      (SourceSemantics.revertedResult spec
        (SourceSemantics.withTransactionContext initialWorld tx))
      (execResultToIRResult
        (FunctionBody.initialIRStateForTx spec tx initialWorld) (.revert s)) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · funext x
    simp [SourceSemantics.revertedResult, execResultToIRResult,
      FunctionBody.initialIRStateForTx,
      SourceSemantics.encodeStorage_withTransactionContext]
  · simp [SourceSemantics.revertedResult, execResultToIRResult,
      FunctionBody.initialIRStateForTx,
      FunctionBody.encodeEvents_withTransactionContext]

/-- The guarded gluing theorem: given the base correspondence at the
lock-acquired world (exactly what the existing per-function machinery
produces there) and the compiled guard's dispatch behavior (from the family
root, at whatever fuel the consumer chose), the guarded source semantics
matches the compiled guarded function. -/
theorem interpretGuardedFunction_matches (spec : CompilationModel)
    (lockSlot : Nat) (fn : FunctionSpec) (tx : IRTransaction)
    (initialWorld : Verity.ContractState) (guardedFn : IRFunction)
    (tailIR : IRExecResult)
    (hlocked_ir :
      (initialWorld.transientStorage lockSlot).val = 1 →
      execIRFunction guardedFn tx.args
          (FunctionBody.initialIRStateForTx spec tx initialWorld) =
        execResultToIRResult
          (FunctionBody.initialIRStateForTx spec tx initialWorld)
          (.revert (FunctionBody.initialIRStateForTx spec tx initialWorld)))
    (hfree_ir :
      (initialWorld.transientStorage lockSlot).val ≠ 1 →
      execIRFunction guardedFn tx.args
          (FunctionBody.initialIRStateForTx spec tx initialWorld) =
        execResultToIRResult
          (FunctionBody.initialIRStateForTx spec tx
            (setLock lockSlot 1 initialWorld)) tailIR)
    (hfree_base :
      (initialWorld.transientStorage lockSlot).val ≠ 1 →
      FunctionBody.sourceResultMatchesIRResult
        (SourceSemantics.interpretFunction spec fn tx
          (setLock lockSlot 1 initialWorld))
        (execResultToIRResult
          (FunctionBody.initialIRStateForTx spec tx
            (setLock lockSlot 1 initialWorld)) tailIR)) :
    FunctionBody.sourceResultMatchesIRResult
      (interpretGuardedFunction spec lockSlot fn tx initialWorld)
      (execIRFunction guardedFn tx.args
        (FunctionBody.initialIRStateForTx spec tx initialWorld)) := by
  unfold interpretGuardedFunction
  by_cases hlock : (initialWorld.transientStorage lockSlot).val = 1
  · rw [if_pos hlock, hlocked_ir hlock]
    exact revertedResult_matches_revert_projection spec tx initialWorld _
  · rw [if_neg hlock, hfree_ir hlock]
    exact hfree_base hlock

end Compiler.Proofs.IRGeneration

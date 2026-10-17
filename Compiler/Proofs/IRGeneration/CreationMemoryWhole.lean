import Compiler.Proofs.IRGeneration.CreationMemoryOperation

namespace Compiler.Proofs.IRGeneration.CreationMemoryOperation
open Verity.Core.Model
open Compiler.CompilationModel.DenoteMemory
open CreationMemoryFrames CreationMemoryInputs CreationMemoryExpansion

/-- Transport only independently expanded memory; kind and gas remain unchanged. -/
def rehome (memory : Memory) (offset size : Nat) : Create2Entry.Preparation → Create2Entry.Preparation
  | .exceptional => .exceptional
  | .depthFailure _ gas => .depthFailure (MidnightInitcode.returnMemory memory offset size) gas
  | .forwarded child => .forwarded { child with memory := MidnightInitcode.returnMemory memory offset size }

theorem preparation_transport (left right : Memory) (context : Create2Entry.Context)
    (offset size : Nat) (extent : left.size = right.size) :
    Create2Entry.prepare right context offset size =
      (Create2Entry.prepare left context offset size).map (rehome right offset size) := by
  unfold Create2Entry.prepare
  rw [entry_cost left right offset size extent]
  by_cases invalid : Create2Entry.maxGas < context.gas
  · simp only [invalid, if_true, Except.map]
  · simp only [invalid, if_false]
    by_cases exceptional : (context.isStatic || decide (49152 < size)) = true
    · simp only [exceptional, if_true, Except.map, rehome]
    · simp only [exceptional, Bool.false_eq_true, if_false]
      by_cases exhausted : context.gas < Create2Entry.entryCost right offset size
      · simp only [exhausted, if_true, Except.map, rehome]
      · simp only [exhausted, if_false]
        by_cases depth : 1024 ≤ context.depth
        <;> simp only [depth, if_true, if_false, Except.map, rehome]

/-- Returndata clearing commutes with the complete nonmemory observation. -/
theorem erase_cleared (world : Verity.ContractState) (memory : Memory) :
    eraseMemory { world.installPhysicalMemory memory with returndata := [] } =
      { eraseMemory world with returndata := [] } := rfl

/-- Includes out-of-range account projections and EIP-2681 nonce failure. -/
theorem forwarded_all_nonces (left right : Verity.ContractState)
    (context : Create2Entry.Context) (warm : Create2Access.WarmAccounts)
    (offset size salt : Verity.Core.Uint256) (lchild rchild : Create2Entry.Forwarded)
    (lprep : Create2Entry.prepare left.byteMemory context offset.val size.val = .ok (.forwarded lchild))
    (rprep : Create2Entry.prepare right.byteMemory context offset.val size.val = .ok (.forwarded rchild))
    (same : Related left right) (extent : left.byteMemory.size = right.byteMemory.size)
    (slice : ∀ index < size.val, left.physicalByte (offset.val + index) =
      right.physicalByte (offset.val + index)) :
    (Create2Operation.run ⟨left, context, warm⟩ offset size salt).map eraseResult =
      (Create2Operation.run ⟨right, context, warm⟩ offset size salt).map eraseResult := by
  have accounts := related_accounts left right same
  have creator := related_creator left right same
  by_cases high : Create2NonceEntry.maxCreatorNonce < (left.creationAccounts left.thisAddress.val).nonce
  · simp only [Create2Operation.run, lprep, rprep, Bind.bind, Except.bind,
      Verity.ContractState.installPhysicalMemory, ← accounts, ← creator, high, if_true]
  · by_cases maximum : (left.creationAccounts left.thisAddress.val).nonce = Create2NonceEntry.maxCreatorNonce
    · have rmax : (right.creationAccounts right.thisAddress.val).nonce = Create2NonceEntry.maxCreatorNonce := by
        rw [← accounts, ← creator]; exact maximum
      rw [Create2Operation.run_nonce_overflow _ _ _ _ _ lprep maximum,
        Create2Operation.run_nonce_overflow _ _ _ _ _ rprep rmax]
      have gas := forwarded_gas left.byteMemory right.byteMemory context offset.val size.val
        extent lchild rchild lprep rprep
      change eraseMemory left = eraseMemory right at same
      simp only [Except.map, eraseResult, eraseFrame, erase_cleared, Create2Entry.completeGas,
        gas.1, gas.2, same]
    · exact forwarded_equivalence left right context warm offset size salt lchild rchild
        lprep rprep same extent (by omega) slice

/-- Complete value-zero operation equivalence across arbitrary scratch memory.
Covers every prepare result and every creator nonce; exact unsupported errors are retained. -/
theorem operation_equivalence (left right : Verity.ContractState)
    (context : Create2Entry.Context) (warm : Create2Access.WarmAccounts)
    (offset size salt : Verity.Core.Uint256)
    (same : Related left right) (extent : left.byteMemory.size = right.byteMemory.size)
    (slice : ∀ index < size.val, left.physicalByte (offset.val + index) =
      right.physicalByte (offset.val + index)) :
    (Create2Operation.run ⟨left, context, warm⟩ offset size salt).map eraseResult =
      (Create2Operation.run ⟨right, context, warm⟩ offset size salt).map eraseResult := by
  have transported := preparation_transport left.byteMemory right.byteMemory context offset.val size.val extent
  cases prepared : Create2Entry.prepare left.byteMemory context offset.val size.val with
  | error message =>
    rw [prepared] at transported
    simp only [Except.map] at transported
    simp only [Create2Operation.run, prepared, transported, Bind.bind, Except.bind, Except.map]
  | ok result =>
    rw [prepared] at transported
    simp only [Except.map] at transported
    cases result with
    | forwarded child =>
      exact forwarded_all_nonces left right context warm offset size salt child _
        prepared transported same extent slice
    | exceptional =>
      rw [Create2Operation.run_exceptional _ _ _ _ prepared,
        Create2Operation.run_exceptional _ _ _ _ transported]
      change eraseMemory left = eraseMemory right at same
      simp only [Except.map, eraseResult, eraseFrame, same]
    | depthFailure memory gas =>
      rw [Create2Operation.run_depth_failure _ _ _ _ _ _ prepared,
        Create2Operation.run_depth_failure _ _ _ _ _ _ transported]
      change eraseMemory left = eraseMemory right at same
      simp only [Except.map, eraseResult, eraseFrame, erase_cleared, same]

end Compiler.Proofs.IRGeneration.CreationMemoryOperation

import Compiler.Proofs.IRGeneration.CreationMemoryWhole

namespace Compiler.Proofs.IRGeneration.CreationLayoutOperation
open Verity.Core.Model
open Compiler.CompilationModel.DenoteMemory
open CreationMemoryFrames CreationMemoryInputs CreationMemoryExpansion CreationMemoryOperation

/-- Actual gas preparation may agree even when source and compiled allocations differ. -/
theorem preparation_gas_cost (left right : Memory) (context : Create2Entry.Context)
    (loffset roffset size : Nat)
    (cost : Create2Entry.entryCost left loffset size = Create2Entry.entryCost right roffset size) :
    (Create2Entry.prepare left context loffset size).map preparationGas =
      (Create2Entry.prepare right context roffset size).map preparationGas := by
  unfold Create2Entry.prepare
  rw [cost]
  by_cases invalid : Create2Entry.maxGas < context.gas
  · simp only [invalid, if_true, Except.map]
  · simp only [invalid, if_false]
    by_cases exceptional : (context.isStatic || decide (49152 < size)) = true
    · simp only [exceptional, if_true, Except.map]
    · simp only [exceptional, Bool.false_eq_true, if_false]
      by_cases exhausted : context.gas < Create2Entry.entryCost right roffset size
      · simp only [exhausted, if_true, Except.map]
      · simp only [exhausted, if_false]
        by_cases depth : 1024 ≤ context.depth
        <;> simp only [depth, if_true, if_false, Except.map, preparationGas]


/-- Layout-independent complete forwarded observation congruence. -/
theorem forwarded_layout_congr (left right : Verity.ContractState)
    (context : Create2Entry.Context) (warm : Create2Access.WarmAccounts)
    (loffset roffset size salt : Verity.Core.Uint256) (lchild rchild : Create2Entry.Forwarded)
    (lprep : Create2Entry.prepare left.byteMemory context loffset.val size.val = .ok (.forwarded lchild))
    (rprep : Create2Entry.prepare right.byteMemory context roffset.val size.val = .ok (.forwarded rchild))
    (same : Related left right)
    (legal : (left.creationAccounts left.thisAddress.val).nonce < Create2NonceEntry.maxCreatorNonce)
    (gas : lchild.childGas = rchild.childGas) (retained : lchild.retainedGas = rchild.retainedGas)
    (code : Create2.physicalInitcodeBytes (left.installPhysicalMemory lchild.memory) loffset.val size.val =
      Create2.physicalInitcodeBytes (right.installPhysicalMemory rchild.memory) roffset.val size.val) :
    (Create2Operation.run ⟨left, context, warm⟩ loffset size salt).map eraseResult =
      (Create2Operation.run ⟨right, context, warm⟩ roffset size salt).map eraseResult := by
  have accounts := related_accounts left right same
  have creator := related_creator left right same
  have rlegal : (right.creationAccounts right.thisAddress.val).nonce < Create2NonceEntry.maxCreatorNonce := by
    rw [← accounts, ← creator]; exact legal
  rw [forwarded_projection _ _ _ _ _ lprep legal, forwarded_projection _ _ _ _ _ rprep rlegal]
  have target : Create2.create2AddressFromPhysicalMemory (left.installPhysicalMemory lchild.memory)
      loffset size salt left.thisAddress =
      Create2.create2AddressFromPhysicalMemory (right.installPhysicalMemory rchild.memory)
      roffset size salt right.thisAddress := by
    unfold Create2.create2AddressFromPhysicalMemory
    rw [code, creator]
  change eraseMemory left = eraseMemory right at same
  simp only [Verity.ContractState.installPhysicalMemory] at code target ⊢
  rw [target, code, accounts, creator, gas, same]
  simp only [Create2Entry.completeGas, retained]


/-- Different allocation layouts need no equal pointer or extent assumption
when both exact initcode buffers are already within their active memories. -/
theorem covered_layout_equivalence (left right : Verity.ContractState)
    (context : Create2Entry.Context) (warm : Create2Access.WarmAccounts)
    (loffset roffset size salt : Verity.Core.Uint256) (lchild rchild : Create2Entry.Forwarded)
    (lprep : Create2Entry.prepare left.byteMemory context loffset.val size.val = .ok (.forwarded lchild))
    (rprep : Create2Entry.prepare right.byteMemory context roffset.val size.val = .ok (.forwarded rchild))
    (same : Related left right)
    (legal : (left.creationAccounts left.thisAddress.val).nonce < Create2NonceEntry.maxCreatorNonce)
    (lcovered : loffset.val + size.val ≤ left.byteMemory.size)
    (rcovered : roffset.val + size.val ≤ right.byteMemory.size)
    (code : Create2.physicalInitcodeBytes left loffset.val size.val =
      Create2.physicalInitcodeBytes right roffset.val size.val) :
    (Create2Operation.run ⟨left, context, warm⟩ loffset size salt).map eraseResult =
      (Create2Operation.run ⟨right, context, warm⟩ roffset size salt).map eraseResult := by
  have cost : Create2Entry.entryCost left.byteMemory loffset.val size.val =
      Create2Entry.entryCost right.byteMemory roffset.val size.val := by
    rw [Create2Entry.entryCost_covered _ _ _ lcovered, Create2Entry.entryCost_covered _ _ _ rcovered]
  have gas := preparation_gas_cost left.byteMemory right.byteMemory context
    loffset.val roffset.val size.val cost
  rw [lprep, rprep] at gas
  have pair := Prod.mk.inj (Option.some.inj (Except.ok.inj gas))
  apply forwarded_layout_congr left right context warm loffset roffset size salt lchild rchild
    lprep rprep same legal pair.2 pair.1
  rw [forwarded_memory _ _ _ _ _ lprep, forwarded_memory _ _ _ _ _ rprep, return_code, return_code]
  exact code

end Compiler.Proofs.IRGeneration.CreationLayoutOperation

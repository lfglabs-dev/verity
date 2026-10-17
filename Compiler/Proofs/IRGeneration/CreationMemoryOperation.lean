import Compiler.Proofs.IRGeneration.CreationMemoryFrames
import Compiler.Proofs.IRGeneration.CreationMemoryInputs
import Compiler.Proofs.IRGeneration.CreationMemoryExpansion

namespace Compiler.Proofs.IRGeneration.CreationMemoryOperation
open Verity.Core.Model
open Compiler.CompilationModel.DenoteMemory
open CreationMemoryFrames CreationMemoryInputs CreationMemoryExpansion

/-- Erase only caller memory, preserving result kind, value, all nonmemory world,
gas/depth/static context and warm accounts. This is a relation, never execution input. -/
def eraseFrame (frame : Create2Operation.Frame) : Create2Operation.Frame :=
  { frame with world := eraseMemory frame.world }

def eraseResult : Create2Operation.Result → Create2Operation.Result
  | .exceptional frame => .exceptional (eraseFrame frame)
  | .continued value frame => .continued value (eraseFrame frame)

/-- Keep preparation kind and all gas, abstracting only caller scratch bytes. -/
def preparationGas : Create2Entry.Preparation → Option (Nat × Nat)
  | .forwarded frame => some (frame.retainedGas, frame.childGas)
  | _ => none

/-- Equal active extents force identical forwarded gas from actual preparation. -/
theorem preparation_gas (left right : Memory) (context : Create2Entry.Context)
    (offset size : Nat) (extent : left.size = right.size) :
    (Create2Entry.prepare left context offset size).map preparationGas =
      (Create2Entry.prepare right context offset size).map preparationGas := by
  unfold Create2Entry.prepare
  rw [entry_cost left right offset size extent]
  by_cases invalid : Create2Entry.maxGas < context.gas
  · simp only [invalid, if_true, Except.map]
  · simp only [invalid, if_false]
    by_cases exceptional : (context.isStatic || decide (49152 < size)) = true
    · simp only [exceptional, if_true, Except.map]
    · simp only [exceptional, Bool.false_eq_true, if_false]
      by_cases exhausted : context.gas < Create2Entry.entryCost right offset size
      · simp only [exhausted, if_true, Except.map]
      · simp only [exhausted, if_false]
        by_cases depth : 1024 ≤ context.depth
        <;> simp only [depth, if_true, if_false, Except.map, preparationGas]

/-- This derives both forwarded gas inputs; they need not be supplied as oracles. -/
theorem forwarded_gas (left right : Memory) (context : Create2Entry.Context)
    (offset size : Nat) (extent : left.size = right.size)
    (lchild rchild : Create2Entry.Forwarded)
    (lprep : Create2Entry.prepare left context offset size = .ok (.forwarded lchild))
    (rprep : Create2Entry.prepare right context offset size = .ok (.forwarded rchild)) :
    lchild.retainedGas = rchild.retainedGas ∧ lchild.childGas = rchild.childGas := by
  have same := preparation_gas left right context offset size extent
  rw [lprep, rprep] at same
  exact Prod.mk.inj (Option.some.inj (Except.ok.inj same))

/-- The complete forwarding branch, retaining every error and constructor outcome.
Preparation must be the actual prepare equation, not a supplied poststate. -/
theorem forwarded_projection (before : Create2Operation.Frame)
    (offset size salt : Verity.Core.Uint256) (child : Create2Entry.Forwarded)
    (prepared : Create2Entry.prepare before.world.byteMemory before.context offset.val size.val =
      .ok (.forwarded child))
    (legal : (before.world.creationAccounts before.world.thisAddress.val).nonce <
      Create2NonceEntry.maxCreatorNonce) :
    (Create2Operation.run before offset size salt).map eraseResult =
      (do
        let world := before.world.installPhysicalMemory child.memory
        let target := (Create2.create2AddressFromPhysicalMemory world offset size salt world.thisAddress).val
        let result ← Create2Operation.enterCode world.creationAccounts world.thisAddress.val target
          (Create2.physicalInitcodeBytes world offset.val size.val) child.childGas
        let committed ← CreationStorage.commit (eraseMemory before.world) result.outcome
        pure (.continued (Create2Operation.outcomeValue result.outcome)
          { world := committed
            context := { before.context with gas := Create2Entry.completeGas child result.gasLeft }
            warm := Create2Access.warm before.warm target })) := by
  have noInvalid : ¬ Create2NonceEntry.maxCreatorNonce <
      (before.world.creationAccounts before.world.thisAddress.val).nonce := by omega
  have notMaximum := Nat.ne_of_lt legal
  simp only [Create2Operation.run, prepared, Bind.bind, Except.bind,
    Verity.ContractState.installPhysicalMemory, noInvalid, notMaximum, if_false]
  cases entered : Create2Operation.enterCode before.world.creationAccounts before.world.thisAddress.val
      (Create2.create2AddressFromPhysicalMemory (before.world.installPhysicalMemory child.memory)
        offset size salt before.world.thisAddress).val
      (Create2.physicalInitcodeBytes (before.world.installPhysicalMemory child.memory) offset.val size.val)
      child.childGas with
  | error message =>
    simp only [Verity.ContractState.installPhysicalMemory] at entered
    rw [entered]
    rfl
  | ok result =>
    simp only [Verity.ContractState.installPhysicalMemory] at entered
    rw [entered]
    dsimp only
    have commutes := commit_frame (before.world.installPhysicalMemory child.memory) result.outcome
    rw [install_frame] at commutes
    simp only [Verity.ContractState.installPhysicalMemory] at commutes
    rw [← commutes]
    cases committed : CreationStorage.commit (before.world.installPhysicalMemory child.memory) result.outcome
    <;> simp only [Verity.ContractState.installPhysicalMemory] at committed
    <;> rw [committed]
    <;> rfl


/-- Equal real opcode inputs give equal complete nonmemory outcomes, including
errors. Neither execution receives the other's scratch bytes or postworld. -/
theorem forwarded_congr (left right : Verity.ContractState)
    (context : Create2Entry.Context) (warm : Create2Access.WarmAccounts)
    (offset size salt : Verity.Core.Uint256) (lchild rchild : Create2Entry.Forwarded)
    (lprep : Create2Entry.prepare left.byteMemory context offset.val size.val = .ok (.forwarded lchild))
    (rprep : Create2Entry.prepare right.byteMemory context offset.val size.val = .ok (.forwarded rchild))
    (same : Related left right)
    (legal : (left.creationAccounts left.thisAddress.val).nonce < Create2NonceEntry.maxCreatorNonce)
    (gas : lchild.childGas = rchild.childGas) (retained : lchild.retainedGas = rchild.retainedGas)
    (code : Create2.physicalInitcodeBytes (left.installPhysicalMemory lchild.memory) offset.val size.val =
      Create2.physicalInitcodeBytes (right.installPhysicalMemory rchild.memory) offset.val size.val) :
    (Create2Operation.run ⟨left, context, warm⟩ offset size salt).map eraseResult =
      (Create2Operation.run ⟨right, context, warm⟩ offset size salt).map eraseResult := by
  have accounts := related_accounts left right same
  have creator := related_creator left right same
  have rlegal : (right.creationAccounts right.thisAddress.val).nonce < Create2NonceEntry.maxCreatorNonce := by
    rw [← accounts, ← creator]; exact legal
  rw [forwarded_projection _ _ _ _ _ lprep legal, forwarded_projection _ _ _ _ _ rprep rlegal]
  have target : Create2.create2AddressFromPhysicalMemory (left.installPhysicalMemory lchild.memory)
      offset size salt left.thisAddress =
      Create2.create2AddressFromPhysicalMemory (right.installPhysicalMemory rchild.memory)
      offset size salt right.thisAddress := by
    unfold Create2.create2AddressFromPhysicalMemory
    rw [code, creator]
  change eraseMemory left = eraseMemory right at same
  simp only [Verity.ContractState.installPhysicalMemory] at code target ⊢
  rw [target, code, accounts, creator, gas, same]
  simp only [Create2Entry.completeGas, retained]

/-- The forwarded memory is computed by preparation, never externally installed. -/
theorem forwarded_memory (memory : Memory) (context : Create2Entry.Context)
    (offset size : Nat) (child : Create2Entry.Forwarded)
    (prepared : Create2Entry.prepare memory context offset size = .ok (.forwarded child)) :
    child.memory = MidnightInitcode.returnMemory memory offset size := by
  dsimp only [Create2Entry.prepare] at prepared
  split at prepared
  · contradiction
  · split at prepared
    · cases prepared
    · split at prepared
      · cases prepared
      · split at prepared
        · cases prepared
        · cases prepared; rfl

/-- Actual forwarding from equal nonmemory worlds, exact slices and extents
preserves every nonmemory observation, value, gas, warm account and error.
Each execution retains its own memory. No whole imported-prefix claim is made. -/
theorem forwarded_equivalence (left right : Verity.ContractState)
    (context : Create2Entry.Context) (warm : Create2Access.WarmAccounts)
    (offset size salt : Verity.Core.Uint256) (lchild rchild : Create2Entry.Forwarded)
    (lprep : Create2Entry.prepare left.byteMemory context offset.val size.val = .ok (.forwarded lchild))
    (rprep : Create2Entry.prepare right.byteMemory context offset.val size.val = .ok (.forwarded rchild))
    (same : Related left right) (extent : left.byteMemory.size = right.byteMemory.size)
    (legal : (left.creationAccounts left.thisAddress.val).nonce < Create2NonceEntry.maxCreatorNonce)
    (slice : ∀ index < size.val, left.physicalByte (offset.val + index) =
      right.physicalByte (offset.val + index)) :
    (Create2Operation.run ⟨left, context, warm⟩ offset size salt).map eraseResult =
      (Create2Operation.run ⟨right, context, warm⟩ offset size salt).map eraseResult := by
  have gas := forwarded_gas left.byteMemory right.byteMemory context offset.val size.val
    extent lchild rchild lprep rprep
  apply forwarded_congr left right context warm offset size salt lchild rchild
    lprep rprep same legal gas.2 gas.1
  rw [forwarded_memory _ _ _ _ _ lprep, forwarded_memory _ _ _ _ _ rprep,
    return_code, return_code]
  exact code_slice left right offset.val size.val slice


end Compiler.Proofs.IRGeneration.CreationMemoryOperation

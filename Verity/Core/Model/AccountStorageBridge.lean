import Verity.Core.Model.DenoteCreate2

/-! Exact flat persistent self-storage/account relation. Imported mappings and
packed fields already use flat, word-normalized Solidity slots. Legacy shadow
keys and transient storage are not falsely collapsed into persistent storage.
Canonical flat persistent writes synchronize account storage without altering
code, balance or transient/legacy shadow channels. -/
namespace Compiler.CompilationModel.AccountStorageBridge

open Verity.Core

def SelfCoherent (world : Verity.ContractState) : Prop :=
  ∀ slot, world.storageWords (.slot slot) = (world.accountWorld world.thisAddress).storageAt slot

/-- Commit a physical persistent self slot through both representations. -/
def writeSelfSlot (world : Verity.ContractState) (slot value : Uint256) : Verity.ContractState :=
  world.writePhysicalSlot slot.val value

theorem writeSelfSlot_account_same (world : Verity.ContractState) (slot value : Uint256) :
    ((writeSelfSlot world slot value).accountWorld world.thisAddress).storageAt slot.val = value := by
  simp [writeSelfSlot, Verity.ContractState.writePhysicalSlot, AccountWorld.write]

theorem writeSelfSlot_account_other (world : Verity.ContractState) (slot value : Uint256)
    (address : Address) (different : address ≠ world.thisAddress) :
    (writeSelfSlot world slot value).accountWorld address = world.accountWorld address := by
  simp [writeSelfSlot, Verity.ContractState.writePhysicalSlot, AccountWorld.write, different]

theorem writeSelfSlot_word_same (world : Verity.ContractState) (slot value : Uint256) :
    (writeSelfSlot world slot value).storageWords (.slot slot.val) = value := by
  simp [writeSelfSlot, Verity.ContractState.writePhysicalSlot]

theorem writeSelfSlot_preserves_coherent (world : Verity.ContractState) (slot value : Uint256)
    (coherent : SelfCoherent world) : SelfCoherent (writeSelfSlot world slot value) := by
  intro query
  by_cases same : query = slot.val
  · subst query
    simp [writeSelfSlot, Verity.ContractState.writePhysicalSlot,
          AccountWorld.write]
  · simp [writeSelfSlot, Verity.ContractState.writePhysicalSlot,
          AccountWorld.write, AccountState.storageAt_writeStorage, same, coherent query]

theorem writePhysicalSlots_preserves_coherent (world : Verity.ContractState) (targets : List Nat)
    (value : Uint256) (coherent : SelfCoherent world) :
    SelfCoherent (world.writePhysicalSlots targets value) := by
  intro query
  simp [Verity.ContractState.writePhysicalSlots, AccountWorld.write,
        AccountState.storageAt_writeStorageValues, coherent query]

theorem modifyPhysicalSlots_preserves_coherent (world : Verity.ContractState) (targets : List Nat)
    (f : Uint256 → Uint256) (coherent : SelfCoherent world) :
    SelfCoherent (world.modifyPhysicalSlots targets f) := by
  intro query
  simp [Verity.ContractState.modifyPhysicalSlots, AccountWorld.write,
        AccountState.storageAt_writeStorageValues, coherent query]

theorem writeSelfSlot_balance_view_frame (world : Verity.ContractState) (slot value : Uint256) :
    (writeSelfSlot world slot value).selfBalance = world.selfBalance := rfl

theorem writeSelfSlot_code_view_frame (world : Verity.ContractState) (slot value : Uint256) :
    (writeSelfSlot world slot value).codeSize = world.codeSize := rfl

theorem commitRuntime_preserves_coherent (world : Verity.ContractState) (creator target : Address)
    (value : Uint256) (runtime : List DenoteMemory.Byte) (coherent : SelfCoherent world)
    (self : creator = world.thisAddress) (other : target ≠ world.thisAddress) :
    SelfCoherent (DenoteCreate2.commitRuntime world creator target value runtime) := by
  intro query
  subst creator
  simpa [DenoteCreate2.commitRuntime, Verity.ContractState.writeAccount,
         AccountWorld.write, Ne.symm other, AccountState.storageAt] using coherent query

end Compiler.CompilationModel.AccountStorageBridge

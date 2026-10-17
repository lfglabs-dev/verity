import Verity.Core.Model.Create2Operation

namespace Compiler.Proofs.IRGeneration.CreationMemoryFrames
open Verity.Core.Model
open Compiler.CompilationModel.DenoteMemory

/-- Preserve every nonmemory field, including all accounts/storage/events. -/
def eraseMemory (world : Verity.ContractState) : Verity.ContractState :=
  world.installPhysicalMemory Memory.empty

def Related (left right : Verity.ContractState) : Prop :=
  eraseMemory left = eraseMemory right

theorem related_accounts (left right : Verity.ContractState) (same : Related left right) :
    left.creationAccounts = right.creationAccounts :=
by
  change eraseMemory left = eraseMemory right at same
  have projected := congrArg (fun world : Verity.ContractState => world.creationAccounts) same
  simpa only [eraseMemory, Verity.ContractState.installPhysicalMemory] using projected

theorem related_creator (left right : Verity.ContractState) (same : Related left right) :
    left.thisAddress = right.thisAddress :=
by
  change eraseMemory left = eraseMemory right at same
  have projected := congrArg (fun world : Verity.ContractState => world.thisAddress) same
  simpa only [eraseMemory, Verity.ContractState.installPhysicalMemory] using projected

theorem install_frame (world : Verity.ContractState) (memory : Memory) :
    eraseMemory (world.installPhysicalMemory memory) = eraseMemory world := rfl

/-- Successful or failed account commit commutes with erasure of caller memory.
No source account or storage is supplied from an observed native poststate. -/
theorem commit_frame (world : Verity.ContractState) (result : Create2Runtime.Outcome) :
    (CreationStorage.commit world result).map eraseMemory =
      CreationStorage.commit (eraseMemory world) result := by
  cases result with
  | created target accounts => rfl
  | failed accounts data =>
    simp only [CreationStorage.commit, CreationStorage.clearOnSuccess, CreationCommit.commit]
    split <;> rfl

/-- Both independent worlds commit the identical computed account outcome while
retaining their own memory; every remaining field agrees. -/
theorem commit_related (left right : Verity.ContractState) (result : Create2Runtime.Outcome)
    (same : Related left right) :
    (CreationStorage.commit left result).map eraseMemory =
      (CreationStorage.commit right result).map eraseMemory := by
  rw [commit_frame, commit_frame, same]

/-- Allocation and gas depend on active extent, while caller bytes are retained. -/
theorem expanded_extent (left right : Memory) (offset size : Nat)
    (same : left.size = right.size) :
    (MidnightInitcode.returnMemory left offset size).size =
      (MidnightInitcode.returnMemory right offset size).size := by
  unfold MidnightInitcode.returnMemory
  simp only [same]
  split
  · exact same
  · simpa only [Memory.expand] using congrArg (fun n => max n (expandedLength (offset + size))) same

end Compiler.Proofs.IRGeneration.CreationMemoryFrames

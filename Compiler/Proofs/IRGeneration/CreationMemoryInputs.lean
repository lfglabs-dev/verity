import Verity.Core.Model.Create2Operation

/-! CREATE2 reads its initcode slice and charges memory expansion by extent.
Dead compiler hash scratch need not equal source-model memory. These laws do
not replace either memory or establish a whole-prefix/full-operation relation. -/
namespace Compiler.Proofs.IRGeneration.CreationMemoryInputs
open Verity.Core.Model
open Compiler.CompilationModel.DenoteMemory

/-- Scratch bytes outside the requested window do not enter the physical code. -/
theorem code_slice (left right : Verity.ContractState) (offset size : Nat)
    (same : ∀ index < size, left.physicalByte (offset + index) =
      right.physicalByte (offset + index)) :
    Create2.physicalInitcodeBytes left offset size =
      Create2.physicalInitcodeBytes right offset size := by
  apply congrArg (fun values : List UInt8 => (⟨values.toArray⟩ : ByteArray))
  apply List.map_congr_left
  intro index belongs
  exact congrArg (fun byte : Byte => UInt8.ofNat byte.val)
    (same index (List.mem_range.mp belongs))

/-- The two hashes see the exact same code and EIP-1014 preimage. -/
theorem address_slice (left right : Verity.ContractState)
    (offset size salt : Verity.Core.Uint256) (deployer : Verity.Core.Address)
    (same : ∀ index < size.val, left.physicalByte (offset.val + index) =
      right.physicalByte (offset.val + index)) :
    Create2.create2AddressFromPhysicalMemory left offset size salt deployer =
      Create2.create2AddressFromPhysicalMemory right offset size salt deployer := by
  unfold Create2.create2AddressFromPhysicalMemory
  rw [code_slice left right offset.val size.val same]

/-- Expansion charges depend on extent, never on unrelated scratch contents. -/
theorem entry_cost (left right : Memory) (offset size : Nat)
    (extent : left.size = right.size) :
    Create2Entry.entryCost left offset size = Create2Entry.entryCost right offset size := by
  simp only [Create2Entry.entryCost, MidnightInitcode.expansionCost, extent]

/-- A shared exact initcode feeds the identical nonce/collision/callee computation. -/
theorem enter_code (accounts : Create2Accounts.Accounts) (creator target gas : Nat)
    (left right : Verity.ContractState) (offset size : Nat)
    (same : ∀ index < size, left.physicalByte (offset + index) =
      right.physicalByte (offset + index)) :
    Create2Operation.enterCode accounts creator target
        (Create2.physicalInitcodeBytes left offset size) gas =
      Create2Operation.enterCode accounts creator target
        (Create2.physicalInitcodeBytes right offset size) gas := by
  rw [code_slice left right offset size same]

end Compiler.Proofs.IRGeneration.CreationMemoryInputs

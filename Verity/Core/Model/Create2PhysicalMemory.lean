import Verity.Core.Model.CodeData
import Verity.Core.Model.ByteMemoryInverse

namespace Verity.Core.Model.Create2
open Compiler.CompilationModel.PhysicalMemory
open Compiler.CompilationModel.DenoteMemory

/-- Complete requested physical initcode slice; no word-grid alignment assumed. -/
def physicalInitcodeBytes (world : Verity.ContractState) (offset size : Nat) : ByteArray :=
  ⟨((List.range size).map fun index => UInt8.ofNat (world.physicalByte (offset + index)).val).toArray⟩

/-- Every word-view byte agrees with the physical carrier, even at an unaligned
initial offset or after crossing several 32-byte windows. -/
theorem memoryByteAt_eq_physicalByte (world : Verity.ContractState)
    (coherent : Coherent world) (offset index : Nat) :
    memoryByteAt world.memory offset index =
      UInt8.ofNat (world.physicalByte (offset + index)).val := by
  have byte : valueWord (world.memory (offset + 32 * (index / 32)))
      ⟨index % 32, Nat.mod_lt _ (by decide)⟩ = world.physicalByte (offset + index) := by
    rw [coherent _, valueWord_wordValue]
    change world.byteMemory.readByte (offset + 32 * (index / 32) + index % 32) =
      world.byteMemory.readByte (offset + index)
    congr 1
    omega
  have observed := congrArg (fun value : Byte => UInt8.ofNat value.val) byte
  exact observed

/-- Entire slices agree, not just a hash or a predicted address. -/
theorem memoryBytes_eq_physicalInitcodeBytes (world : Verity.ContractState)
    (coherent : Coherent world) (offset size : Nat) :
    memoryBytes world.memory offset size = physicalInitcodeBytes world offset size := by
  apply congrArg (fun values : List UInt8 => (⟨values.toArray⟩ : ByteArray))
  apply List.map_congr_left
  intro index _
  exact memoryByteAt_eq_physicalByte world coherent offset index

/-- Physical-memory address calculation includes the initcode Keccak and the
outer EIP-1014 Keccak. This is address calculation, not deployment semantics. -/
def create2AddressFromPhysicalMemory (world : Verity.ContractState)
    (offset size salt : Uint256) (deployer : Address) : Address :=
  create2Address salt
    (Uint256.ofNat (KeccakEngine.byteArrayToNatBE
      (KeccakEngine.keccak256 (physicalInitcodeBytes world offset.val size.val)))) deployer

theorem create2AddressFromMemory_eq_physical (world : Verity.ContractState)
    (coherent : Coherent world) (offset size salt : Uint256) (deployer : Address) :
    create2AddressFromMemory world.memory offset size salt deployer =
      create2AddressFromPhysicalMemory world offset size salt deployer := by
  unfold create2AddressFromMemory create2AddressFromPhysicalMemory
  rw [memoryBytes_eq_physicalInitcodeBytes world coherent]

end Verity.Core.Model.Create2

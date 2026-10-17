import Compiler.Proofs.IRGeneration.NativeCallerAllocation

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul

/-- Every actual word-sized memory request has a representable active-word
count. The sum is natural arithmetic, so this does not assume offset+size nowrap. -/
theorem native_memory_words_nowrap (words offset count : UInt256) :
    MachineState.M words.toNat offset.toNat count.toNat < UInt256.size := by
  have old : words.toNat < UInt256.size := words.val.isLt
  have start : offset.toNat < UInt256.size := offset.val.isLt
  have length : count.toNat < UInt256.size := count.val.isLt
  have wide : 32 < UInt256.size := by decide
  cases size : count.toNat with
  | zero => exact old
  | succ n =>
    change max words.toNat ((offset.toNat + (n + 1) + 31) / 32) < UInt256.size
    apply max_lt old
    omega

/-- MCOPY's maximum source/destination address is still an actual word range. -/
theorem native_mcopy_words_nowrap (words dest source count : UInt256) :
    MachineState.M words.toNat (max dest.toNat source.toNat) count.toNat < UInt256.size := by
  have old : words.toNat < UInt256.size := words.val.isLt
  have destination : dest.toNat < UInt256.size := dest.val.isLt
  have origin : source.toNat < UInt256.size := source.val.isLt
  have length : count.toNat < UInt256.size := count.val.isLt
  have wide : 32 < UInt256.size := by decide
  cases size : count.toNat with
  | zero => exact old
  | succ n =>
    change max words.toNat ((max dest.toNat source.toNat + (n + 1) + 31) / 32) < UInt256.size
    apply max_lt old
    omega

/-- Actual native MSTORE preserves allocation without a host-padding premise. -/
theorem caller_mstore_allocated (machine : MachineState)
    (allocated : machine.memory.size ≤ machine.activeWords.toNat * 32) (offset value : UInt256) :
    (machine.mstore offset value).memory.size ≤ (machine.mstore offset value).activeWords.toNat * 32 := by
  have nowrap := native_memory_words_nowrap machine.activeWords offset (UInt256.ofNat 32)
  have conversion : (machine.mstore offset value).activeWords.toNat =
      MachineState.M machine.activeWords.toNat offset.toNat 32 := Nat.mod_eq_of_lt nowrap
  rw [conversion]
  exact native_write_extent value.toByteArray machine.memory 0 offset.toNat 32 machine.activeWords.toNat allocated

/-- Actual native MSTORE8 preserves allocation for every word-sized offset. -/
theorem caller_mstore8_allocated (machine : MachineState)
    (allocated : machine.memory.size ≤ machine.activeWords.toNat * 32) (offset value : UInt256) :
    (machine.mstore8 offset value).memory.size ≤ (machine.mstore8 offset value).activeWords.toNat * 32 := by
  have nowrap := native_memory_words_nowrap machine.activeWords offset (UInt256.ofNat 1)
  have conversion : (machine.mstore8 offset value).activeWords.toNat =
      MachineState.M machine.activeWords.toNat offset.toNat 1 := Nat.mod_eq_of_lt nowrap
  rw [conversion]
  exact native_write_extent ⟨#[UInt8.ofNat value.toNat]⟩ machine.memory 0 offset.toNat 1 machine.activeWords.toNat allocated

/-- Actual MLOAD allocation needs no independent no-wrap certificate. -/
theorem caller_mload_allocated (machine : MachineState)
    (allocated : machine.memory.size ≤ machine.activeWords.toNat * 32) (offset : UInt256) :
    (machine.mload offset).2.memory.size ≤ (machine.mload offset).2.activeWords.toNat * 32 :=
  native_mload_allocation machine allocated offset
    (native_memory_words_nowrap machine.activeWords offset (UInt256.ofNat 32))

/-- Actual calldata-copy allocation needs no independent no-wrap certificate. -/
theorem caller_calldatacopy_allocated (machine : SharedState .EVM)
    (allocated : machine.memory.size ≤ machine.activeWords.toNat * 32) (offset source count : UInt256) :
    (machine.calldatacopy offset source count).memory.size ≤
      (machine.calldatacopy offset source count).activeWords.toNat * 32 :=
  native_calldatacopy_allocation machine allocated offset source count
    (native_memory_words_nowrap machine.activeWords offset count)

/-- Actual code-copy allocation needs no independent no-wrap certificate. -/
theorem caller_codecopy_allocated (machine : SharedState .EVM)
    (allocated : machine.memory.size ≤ machine.activeWords.toNat * 32) (offset source count : UInt256) :
    (machine.codeCopy offset source count).memory.size ≤
      (machine.codeCopy offset source count).activeWords.toNat * 32 :=
  native_codecopy_allocation machine allocated offset source count
    (native_memory_words_nowrap machine.activeWords offset count)

/-- Actual return-data-copy allocation needs no independent no-wrap certificate. -/
theorem caller_returndatacopy_allocated (machine : MachineState)
    (allocated : machine.memory.size ≤ machine.activeWords.toNat * 32) (offset source count : UInt256) :
    (machine.returndatacopy offset source count).memory.size ≤
      (machine.returndatacopy offset source count).activeWords.toNat * 32 :=
  native_returndatacopy_allocation machine allocated offset source count
    (native_memory_words_nowrap machine.activeWords offset count)

/-- Actual overlapping memory-copy allocation needs no independent no-wrap certificate. -/
theorem caller_mcopy_allocated (machine : MachineState)
    (allocated : machine.memory.size ≤ machine.activeWords.toNat * 32) (offset source count : UInt256) :
    (machine.mcopy offset source count).memory.size ≤
      (machine.mcopy offset source count).activeWords.toNat * 32 :=
  native_mcopy_allocation machine allocated offset source count
    (native_mcopy_words_nowrap machine.activeWords offset source count)

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor

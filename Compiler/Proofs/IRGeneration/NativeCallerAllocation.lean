import Compiler.Proofs.IRGeneration.NativeCreate2AddressAgreement
import EvmYul.EVM.Proof.MemoryStep

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul

/-- Actual materialized memory fits in the charged active extent. -/
def CallerAllocated (state : EVM.State) : Prop :=
  state.memory.size ≤ state.activeWords.toNat * 32

private theorem native_memory_extent (words offset count : Nat) (positive : 0 < count) :
    words * 32 ≤ MachineState.M words offset count * 32 ∧
      offset + count ≤ MachineState.M words offset count * 32 := by
  cases count with
  | zero => omega
  | succ count =>
    change words * 32 ≤ max words ((offset + (count + 1) + 31) / 32) * 32 ∧
      offset + (count + 1) ≤ max words ((offset + (count + 1) + 31) / 32) * 32
    have old := Nat.le_max_left words ((offset + (count + 1) + 31) / 32)
    have fresh := Nat.le_max_right words ((offset + (count + 1) + 31) / 32)
    omega

private theorem native_copy_slice_size (source dest : ByteArray) (sourceOffset destOffset count : Nat) :
    (source.copySlice sourceOffset dest destOffset count).size ≤ max dest.size (destOffset + count) := by
  simp only [ByteArray.copySlice, ByteArray.size, Array.size_append, Array.size_extract]
  omega

private theorem native_zeroes_size (count : Nat) :
    (ffi.ByteArray.zeroes (USize.ofNat count)).size ≤ count := by
  simp only [ffi.ByteArray.zeroes, ByteArray.size, Array.size_replicate, USize.toNat_ofNat']
  exact Nat.mod_le _ _

/-- Native writes never allocate past either the old allocation or the requested
span, including source padding and host-size truncation of padding counts. -/
theorem native_write_size_bound (source dest : ByteArray) (sourceOffset destOffset count : Nat) :
    (source.write sourceOffset dest destOffset count).size ≤ max dest.size (destOffset + count) := by
  unfold ByteArray.write
  split
  · exact Nat.le_max_left _ _
  · split
    · refine (native_copy_slice_size _ dest 0 (min destOffset dest.size)
        (min count (dest.size - destOffset))).trans ?_
      omega
    · refine (native_copy_slice_size _
        (dest ++ ffi.ByteArray.zeroes (USize.ofNat (destOffset - dest.size)))
        sourceOffset destOffset _).trans ?_
      have padded := native_zeroes_size (destOffset - dest.size)
      rw [ByteArray.size_append]
      apply max_le <;> omega

/-- Any native write fits the newly charged extent, including zero-length copies. -/
theorem native_write_extent (source dest : ByteArray) (sourceOffset destOffset count words : Nat)
    (allocated : dest.size ≤ words * 32) :
    (source.write sourceOffset dest destOffset count).size ≤ MachineState.M words destOffset count * 32 := by
  by_cases empty : count = 0
  · subst count
    simpa only [ByteArray.write, if_true, MachineState.M] using allocated
  · have extent := native_memory_extent words destOffset count (by omega)
    exact (native_write_size_bound source dest sourceOffset destOffset count).trans
      (max_le (allocated.trans extent.1) extent.2)

/-- Real MSTORE post-state preserves allocation when host padding and the
native active-word conversion do not wrap. These bounds are not hidden. -/
theorem native_mstore_allocation (pre : EVM.State) (allocated : CallerAllocated pre)
    (cost : Nat) (rest : Stack UInt256) (offset value : UInt256)
    (padding : offset.toNat - pre.memory.size < 2 ^ System.Platform.numBits)
    (nowrap : MachineState.M pre.activeWords.toNat offset.toNat 32 < UInt256.size) :
    CallerAllocated (EVM.Proof.mstorePost cost pre rest offset value) := by
  unfold CallerAllocated at allocated ⊢
  rw [EVM.Proof.size_memory_step_MSTORE cost pre rest offset value padding,
    EVM.Proof.activeWords_step_MSTORE]
  have conversion : (UInt256.ofNat (MachineState.M pre.activeWords.toNat offset.toNat 32)).toNat =
      MachineState.M pre.activeWords.toNat offset.toNat 32 := Nat.mod_eq_of_lt nowrap
  rw [conversion]
  have extent := native_memory_extent pre.activeWords.toNat offset.toNat 32 (by decide)
  exact max_le (allocated.trans extent.1) extent.2

/-- The actual successful MSTORE step retains the physical-memory invariant. -/
theorem native_mstore_step_allocation (pre : EVM.State) (allocated : CallerAllocated pre)
    (fuel cost : Nat) (rest : Stack UInt256) (offset value : UInt256)
    (popped : pre.stack.pop2 = some (rest, offset, value))
    (padding : offset.toNat - pre.memory.size < 2 ^ System.Platform.numBits)
    (nowrap : MachineState.M pre.activeWords.toNat offset.toNat 32 < UInt256.size) :
    ∃ next, EVM.step (fuel + 1) cost (some (.MSTORE, none)) pre = .ok next ∧ CallerAllocated next := by
  exact ⟨EVM.Proof.mstorePost cost pre rest offset value,
    EVM.Proof.step_MSTORE fuel cost pre rest offset value popped,
    native_mstore_allocation pre allocated cost rest offset value padding nowrap⟩

/-- Actual MSTORE8 also keeps every materialized byte in the active extent. -/
theorem native_mstore8_allocation (machine : MachineState)
    (allocated : machine.memory.size ≤ machine.activeWords.toNat * 32) (offset value : UInt256)
    (padding : offset.toNat - machine.memory.size < 2 ^ System.Platform.numBits)
    (nowrap : MachineState.M machine.activeWords.toNat offset.toNat 1 < UInt256.size) :
    (machine.mstore8 offset value).memory.size ≤ (machine.mstore8 offset value).activeWords.toNat * 32 := by
  rw [MachineState.size_memory_mstore8_of_pad machine offset value padding]
  have conversion : (machine.mstore8 offset value).activeWords.toNat =
      MachineState.M machine.activeWords.toNat offset.toNat 1 := Nat.mod_eq_of_lt nowrap
  rw [conversion]
  have extent := native_memory_extent machine.activeWords.toNat offset.toNat 1 (by decide)
  exact max_le (allocated.trans extent.1) extent.2

/-- Actual MLOAD may expose more zero memory but cannot hide allocated bytes. -/
theorem native_mload_allocation (machine : MachineState)
    (allocated : machine.memory.size ≤ machine.activeWords.toNat * 32) (offset : UInt256)
    (nowrap : MachineState.M machine.activeWords.toNat offset.toNat 32 < UInt256.size) :
    (machine.mload offset).2.memory.size ≤ (machine.mload offset).2.activeWords.toNat * 32 := by
  have conversion : (machine.mload offset).2.activeWords.toNat =
      MachineState.M machine.activeWords.toNat offset.toNat 32 := Nat.mod_eq_of_lt nowrap
  rw [conversion]
  exact allocated.trans (native_memory_extent machine.activeWords.toNat offset.toNat 32 (by decide)).1

/-- Actual calldata copy preserves allocation without a source-in-bounds premise. -/
theorem native_calldatacopy_allocation (machine : SharedState .EVM)
    (allocated : machine.memory.size ≤ machine.activeWords.toNat * 32)
    (offset source count : UInt256)
    (nowrap : MachineState.M machine.activeWords.toNat offset.toNat count.toNat < UInt256.size) :
    (machine.calldatacopy offset source count).memory.size ≤
      (machine.calldatacopy offset source count).activeWords.toNat * 32 := by
  have conversion : (machine.calldatacopy offset source count).activeWords.toNat =
      MachineState.M machine.activeWords.toNat offset.toNat count.toNat := Nat.mod_eq_of_lt nowrap
  rw [conversion]
  exact native_write_extent machine.executionEnv.calldata machine.memory source.toNat offset.toNat
    count.toNat machine.activeWords.toNat allocated

/-- Actual code copy preserves allocation even when the source is zero-padded. -/
theorem native_codecopy_allocation (machine : SharedState .EVM)
    (allocated : machine.memory.size ≤ machine.activeWords.toNat * 32)
    (offset source count : UInt256)
    (nowrap : MachineState.M machine.activeWords.toNat offset.toNat count.toNat < UInt256.size) :
    (machine.codeCopy offset source count).memory.size ≤
      (machine.codeCopy offset source count).activeWords.toNat * 32 := by
  have conversion : (machine.codeCopy offset source count).activeWords.toNat =
      MachineState.M machine.activeWords.toNat offset.toNat count.toNat := Nat.mod_eq_of_lt nowrap
  rw [conversion]
  exact native_write_extent machine.executionEnv.code machine.memory source.toNat offset.toNat
    count.toNat machine.activeWords.toNat allocated

/-- Actual return-data copy preserves allocation; its access guard is separate. -/
theorem native_returndatacopy_allocation (machine : MachineState)
    (allocated : machine.memory.size ≤ machine.activeWords.toNat * 32)
    (offset source count : UInt256)
    (nowrap : MachineState.M machine.activeWords.toNat offset.toNat count.toNat < UInt256.size) :
    (machine.returndatacopy offset source count).memory.size ≤
      (machine.returndatacopy offset source count).activeWords.toNat * 32 := by
  have conversion : (machine.returndatacopy offset source count).activeWords.toNat =
      MachineState.M machine.activeWords.toNat offset.toNat count.toNat := Nat.mod_eq_of_lt nowrap
  rw [conversion]
  exact native_write_extent machine.returnData machine.memory source.toNat offset.toNat
    count.toNat machine.activeWords.toNat allocated

/-- Actual overlapping MCOPY preserves allocation, including a zero-byte copy. -/
theorem native_mcopy_allocation (machine : MachineState)
    (allocated : machine.memory.size ≤ machine.activeWords.toNat * 32)
    (offset source count : UInt256)
    (nowrap : MachineState.M machine.activeWords.toNat (max offset.toNat source.toNat) count.toNat < UInt256.size) :
    (machine.mcopy offset source count).memory.size ≤
      (machine.mcopy offset source count).activeWords.toNat * 32 := by
  have conversion : (machine.mcopy offset source count).activeWords.toNat =
      MachineState.M machine.activeWords.toNat (max offset.toNat source.toNat) count.toNat := Nat.mod_eq_of_lt nowrap
  rw [conversion]
  have written := native_write_extent machine.memory machine.memory source.toNat offset.toNat
    count.toNat machine.activeWords.toNat allocated
  have monotone : MachineState.M machine.activeWords.toNat offset.toNat count.toNat ≤
      MachineState.M machine.activeWords.toNat (max offset.toNat source.toNat) count.toNat := by
    cases size : count.toNat with
    | zero => exact Nat.le_refl _
    | succ n =>
      change max machine.activeWords.toNat ((offset.toNat + (n + 1) + 31) / 32) ≤
        max machine.activeWords.toNat ((max offset.toNat source.toNat + (n + 1) + 31) / 32)
      have position := Nat.le_max_left offset.toNat source.toNat
      omega
  exact written.trans (Nat.mul_le_mul_right 32 monotone)

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor

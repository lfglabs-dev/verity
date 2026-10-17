import Compiler.Proofs.IRGeneration.NativeSourceAddressPair

namespace Compiler.Proofs.IRGeneration.NativeSourceGrowingMemoryFrame
open EvmYul EVM EVM.Proof

theorem read_below_grows (src dest : ByteArray) (offset len start count : Nat)
    (positive : 0 < len) (source : src.size = len) (grows : dest.size ≤ offset + len)
    (pad : offset - dest.size < 2 ^ System.Platform.numBits)
    (readPositive : 0 < count) (readBound : count < 2 ^ 64)
    (inside : start + count ≤ dest.size) (below : start + count ≤ offset) :
    (ByteArray.write src 0 dest offset len).readWithPadding start count =
      dest.readWithPadding start count := by
  have size := ByteArray.size_write src dest offset len positive source pad
  rw [ByteArray.readWithPadding_eq_extract _ _ _ readPositive readBound (by omega),
    ByteArray.readWithPadding_eq_extract _ _ _ readPositive readBound inside,
    ByteArray.write_eq_of_grows src dest offset len positive source grows pad]
  have firstSize : start + count ≤ (dest.data.extract 0 offset).size := by
    simp only [Array.size_extract, ByteArray.size_data]; omega
  ext1
  simp only [ByteArray.data_extract]
  rw [Array.extract_append_of_le _ _ _ _ _ firstSize]
  simp only [Array.toList_inj.symm, Array.toList_extract, List.extract_eq_take_drop,
    List.drop_zero, List.drop_take, List.take_take, Nat.sub_zero]
  congr 1
  omega

theorem read_below (src dest : ByteArray) (offset len start count : Nat)
    (positive : 0 < len) (source : src.size = len)
    (pad : offset - dest.size < 2 ^ System.Platform.numBits)
    (readPositive : 0 < count) (readBound : count < 2 ^ 64)
    (inside : start + count ≤ dest.size) (below : start + count ≤ offset) :
    (ByteArray.write src 0 dest offset len).readWithPadding start count =
      dest.readWithPadding start count := by
  by_cases fits : offset + len ≤ dest.size
  · exact ByteArray.readWithPadding_write_of_le src dest offset len start count
      positive source fits readPositive readBound below
  · exact read_below_grows src dest offset len start count positive source (by omega)
      pad readPositive readBound inside below

theorem post_span (state : EVM.State) (offset value : UInt256) (tail : Stack UInt256)
    (pad : offset.toNat - state.memory.size < 2 ^ System.Platform.numBits) :
    offset.toNat + 32 ≤ (mstorePost 3 (NativeSourceFieldStoreChecks.expanded state) tail offset value).memory.size := by
  exact MachineState.le_size_memory_mstore (NativeSourceFieldStoreChecks.expanded state).toMachineState offset value pad

theorem first_span (pre : EVM.State) (a base : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 944)
    (pad : (base + UInt256.ofNat 32).toNat - pre.memory.size < 2 ^ System.Platform.numBits) :
    (base + UInt256.ofNat 32).toNat + 32 ≤ (NativeSourceAddressPair.first pre a base tail).memory.size := by
  exact post_span (NativeSourceMidnightDecodedStore.prepared pre a base tail) _ _ _
    (by rw [NativeSourceMidnightDecodedStore.prepared_memory pre a base tail pc]; exact pad)

theorem loan_frame (pre : EVM.State) (x a base : UInt256) (tail : Stack UInt256) (start count : Nat)
    (pad : (base + UInt256.ofNat 64).toNat - pre.memory.size < 2 ^ System.Platform.numBits)
    (positive : 0 < count) (bounded : count < 2 ^ 64)
    (inside : start + count ≤ pre.memory.size) (below : start + count ≤ (base + UInt256.ofNat 64).toNat) :
    (NativeSourceLoanDecodedStore.stored pre x a base tail).memory.readWithPadding start count =
      pre.memory.readWithPadding start count := by
  have rawFrame (state : EVM.State) (value : UInt256)
      (padding : (base + UInt256.ofNat 64).toNat - state.memory.size < 2 ^ System.Platform.numBits)
      (span : start + count ≤ state.memory.size) :
      (mstorePost 3 (NativeSourceFieldStoreChecks.expanded state)
        (x :: (base + UInt256.ofNat 64) :: a :: base :: tail)
        (base + UInt256.ofNat 64) value).memory.readWithPadding start count = state.memory.readWithPadding start count := by
    exact read_below value.toByteArray state.memory (base + UInt256.ofNat 64).toNat 32 start count
      (by decide) (UInt256.size_toByteArray value) padding positive bounded span below
  have memory := NativeSourceLoanDecodedStore.prepared_memory pre x a base tail
  exact (rawFrame (NativeSourceLoanDecodedStore.prepared pre x a base tail)
    (NativeSourceLoanDecodedStore.word pre a) (by rw [memory]; exact pad)
    (by rw [memory]; exact inside)).trans (by rw [memory])

theorem midnight_preserved (pre : EVM.State) (a base : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 944) (nonwrap : base.toNat + 64 < 2 ^ 256)
    (pad : (base + UInt256.ofNat 32).toNat - pre.memory.size < 2 ^ System.Platform.numBits) :
    (NativeSourceAddressPair.second pre a base tail).memory.readWithPadding (base + UInt256.ofNat 32).toNat 32 =
      (NativeSourceAddressPair.first pre a base tail).memory.readWithPadding (base + UInt256.ofNat 32).toNat 32 := by
  have small : (UInt256.ofNat 32).toNat = 32 := by decide
  have large : (UInt256.ofNat 64).toNat = 64 := by decide
  have low := NativeSourceAddressGeometry.add_toNat base (UInt256.ofNat 32) (by rw [small]; omega)
  have high := NativeSourceAddressGeometry.add_toNat base (UInt256.ofNat 64) (by rw [large]; exact nonwrap)
  have span := first_span pre a base tail pc pad
  have start : (base + UInt256.ofNat 64).toNat ≤ (NativeSourceAddressPair.first pre a base tail).memory.size := by
    rw [low, small] at span; rw [high, large]; omega
  exact loan_frame (NativeSourceAddressPair.first pre a base tail) _ a base tail _ 32
    (by rw [Nat.sub_eq_zero_of_le start]; positivity) (by decide) (by decide) span
    (by rw [low, high, small, large])

theorem market_readback (pre : EVM.State) (base : UInt256) (tail : Stack UInt256)
    (selector key value : Nat) (market : NativeSourceMarketCalldata.Market)
    (encoded : pre.executionEnv.calldata = Compiler.Proofs.YulGeneration.Backends.StateBridge.calldataToByteArray selector
      (NativeSourceMarketCalldata.arguments market key value))
    (midnight : market.midnight < 2 ^ 160) (loan : market.loanToken < 2 ^ 160)
    (pc : pre.pc = UInt256.ofNat 944) (nonwrap : base.toNat + 64 < 2 ^ 256)
    (pad : (base + UInt256.ofNat 32).toNat - pre.memory.size < 2 ^ System.Platform.numBits) :
    (NativeSourceAddressPair.second pre (UInt256.ofNat 96) base tail).memory.readWithPadding (base + UInt256.ofNat 32).toNat 32 =
      (UInt256.ofNat market.midnight).toByteArray ∧
    (NativeSourceAddressPair.second pre (UInt256.ofNat 96) base tail).memory.readWithPadding (base + UInt256.ofNat 64).toNat 32 =
      (UInt256.ofNat market.loanToken).toByteArray := by
  constructor
  · rw [midnight_preserved pre _ base tail pc nonwrap pad]
    exact NativeSourceMidnightDecodedStore.market_readback pre _ base tail selector key value market encoded midnight pc pad
  · have calldataAfter := congrArg (fun state : EvmYul.State .EVM => state.executionEnv.calldata)
      (NativeSourceAddressPair.first_world pre (UInt256.ofNat 96) base tail pc)
    have span := first_span pre (UInt256.ofNat 96) base tail pc pad
    have low := NativeSourceAddressGeometry.add_toNat base (UInt256.ofNat 32)
      (by change base.toNat + 32 < _; omega)
    have high := NativeSourceAddressGeometry.add_toNat base (UInt256.ofNat 64)
      (by change base.toNat + 64 < _; exact nonwrap)
    exact NativeSourceLoanDecodedStore.market_readback (NativeSourceAddressPair.first pre (UInt256.ofNat 96) base tail)
      _ base tail selector key value market (calldataAfter.trans encoded) loan
      (by have start : (base + UInt256.ofNat 64).toNat ≤ (NativeSourceAddressPair.first pre (UInt256.ofNat 96) base tail).memory.size := by
            rw [low] at span; rw [high]; change base.toNat + 64 ≤ _; change base.toNat + 32 + 32 ≤ _ at span; omega
          rw [Nat.sub_eq_zero_of_le start]; positivity)

end Compiler.Proofs.IRGeneration.NativeSourceGrowingMemoryFrame


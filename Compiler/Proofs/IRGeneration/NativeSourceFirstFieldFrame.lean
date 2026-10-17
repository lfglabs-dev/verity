import Compiler.Proofs.IRGeneration.NativeSourceStoreFrame

namespace Compiler.Proofs.IRGeneration.NativeSourceFirstFieldFrame
open EvmYul

theorem read_below (cost : Nat) (pre : EVM.State) (a b c d e f g h i : UInt256)
    (tail : Stack UInt256) (start length : Nat)
    (padding : (h + UInt256.ofNat 192).toNat - pre.memory.size < 2 ^ System.Platform.numBits)
    (positive : 0 < length) (bounded : length < 2 ^ 64)
    (inside : start + length ≤ pre.memory.size) (below : start + length ≤ (h + UInt256.ofNat 192).toNat) :
    (NativeSourceFieldStore.s4 cost pre a b c d e f g h i tail).memory.readWithPadding start length =
      pre.memory.readWithPadding start length := by
  exact NativeSourceStoreFrame.read_below
    (NativeSourceFieldStore.s3 cost pre a b c d e f g h i tail).toMachineState
    (h + UInt256.ofNat 192) a start length padding positive bounded inside below

theorem second_read_below (cost : Nat) (pre : EVM.State) (a b c d e f g h i : UInt256)
    (tail : Stack UInt256) (start length : Nat)
    (padding : (g + UInt256.ofNat 224).toNat - pre.memory.size < 2 ^ System.Platform.numBits)
    (positive : 0 < length) (bounded : length < 2 ^ 64)
    (inside : start + length ≤ pre.memory.size) (below : start + length ≤ (g + UInt256.ofNat 224).toNat) :
    (NativeSourceSecondFieldStore.s4 cost pre a b c d e f g h i tail).memory.readWithPadding start length =
      pre.memory.readWithPadding start length := by
  exact NativeSourceStoreFrame.read_below
    (NativeSourceSecondFieldStore.s3 cost pre a b c d e f g h i tail).toMachineState
    (g + UInt256.ofNat 224) a start length padding positive bounded inside below

theorem third_read_below (cost : Nat) (pre : EVM.State) (a b c d e f g h i : UInt256)
    (tail : Stack UInt256) (start length : Nat)
    (padding : (e + UInt256.ofNat 256).toNat - pre.memory.size < 2 ^ System.Platform.numBits)
    (positive : 0 < length) (bounded : length < 2 ^ 64)
    (inside : start + length ≤ pre.memory.size) (below : start + length ≤ (e + UInt256.ofNat 256).toNat) :
    (NativeSourceMaskedFieldStore.s4 cost pre a b c d e f g h i tail).memory.readWithPadding start length =
      pre.memory.readWithPadding start length := by
  exact NativeSourceStoreFrame.read_below
    (NativeSourceMaskedFieldStore.s3 cost pre a b c d e f g h i tail).toMachineState
    (e + UInt256.ofNat 256) a start length padding positive bounded inside below

theorem fourth_read_below (cost : Nat) (pre : EVM.State) (a b c d e f g h i : UInt256)
    (tail : Stack UInt256) (start length : Nat)
    (padding : (c + UInt256.ofNat 288).toNat - pre.memory.size < 2 ^ System.Platform.numBits)
    (positive : 0 < length) (bounded : length < 2 ^ 64)
    (inside : start + length ≤ pre.memory.size) (below : start + length ≤ (c + UInt256.ofNat 288).toNat) :
    (NativeSourceFourthFieldStore.s4 cost pre a b c d e f g h i tail).memory.readWithPadding start length =
      pre.memory.readWithPadding start length := by
  exact NativeSourceStoreFrame.read_below
    (NativeSourceFourthFieldStore.s3 cost pre a b c d e f g h i tail).toMachineState
    (c + UInt256.ofNat 288) a start length padding positive bounded inside below

end Compiler.Proofs.IRGeneration.NativeSourceFirstFieldFrame

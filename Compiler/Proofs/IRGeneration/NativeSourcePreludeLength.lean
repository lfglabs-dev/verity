import Compiler.Proofs.IRGeneration.NativeSourcePreludeShuffles

namespace Compiler.Proofs.IRGeneration.NativeSourcePreludeLength
open EvmYul EVM.Proof NativeSourcePreludeShuffles

theorem decode636 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 636) = some (.SWAP5, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 636).toNat = some 148 := by
    have index : (UInt256.ofNat 636).toNat = 636 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem decode637 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 637) = some (.DUP6, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 637).toNat = some 133 := by
    have index : (UInt256.ofNat 637).toNat = 637 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem decode638 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 638) = some (.SWAP4, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 638).toNat = some 147 := by
    have index : (UInt256.ofNat 638).toNat = 638 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem decode639 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 639) = some (.DUP4, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 639).toNat = some 131 := by
    have index : (UInt256.ofNat 639).toNat = 639 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem decode640 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 640) = some (.DUP6, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 640).toNat = some 133 := by
    have index : (UInt256.ofNat 640).toNat = 640 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem decode641 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 641) = some (.ADD, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 641).toNat = some 1 := by
    have index : (UInt256.ofNat 641).toNat = 641 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem decode642 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 642) = some (.SWAP8, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 642).toNat = some 151 := by
    have index : (UInt256.ofNat 642).toNat = 642 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem decode643 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 643) = some (.MLOAD, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 643).toNat = some 81 := by
    have index : (UInt256.ofNat 643).toNat = 643 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

def loaded (cost loadCost : Nat) (pre : EVM.State) (free a b c d e f g h : UInt256)
    (tail : Stack UInt256) : EVM.State :=
  NativeSourceLoadStep.loaded loadCost (result cost pre free a b c d e f g h tail) f
    (c :: e :: a :: b :: free :: d :: free :: (free + b) :: g :: h :: tail)

theorem execute (fuel cost loadCost : Nat) (pre : EVM.State) (free a b c d e f g h : UInt256)
    (tail : Stack UInt256) (stack : pre.stack = free :: a :: b :: c :: d :: e :: f :: g :: h :: tail) :
    (run fuel cost [.SWAP5, .DUP6, .SWAP4, .DUP4, .DUP6, .ADD, .SWAP8] pre >>= fun ready =>
      EVM.step (fuel + 1) loadCost (some (.MLOAD, none)) ready) =
      .ok (loaded cost loadCost pre free a b c d e f g h tail) := by
  rw [NativeSourcePreludeShuffles.execute fuel cost pre free a b c d e f g h tail stack]
  exact NativeSourceLoadStep.step fuel loadCost _ f _ (NativeSourcePreludeShuffles.stack _ _ _ _ _ _ _ _ _ _ _ _)

theorem stack (cost loadCost : Nat) (pre : EVM.State) (free a b c d e f g h : UInt256)
    (tail : Stack UInt256) :
    (loaded cost loadCost pre free a b c d e f g h tail).stack =
      (result cost pre free a b c d e f g h tail).toMachineState.lookupMemory f ::
      c :: e :: a :: b :: free :: d :: free :: (free + b) :: g :: h :: tail := by rfl

theorem memory (cost loadCost : Nat) (pre : EVM.State) (free a b c d e f g h : UInt256)
    (tail : Stack UInt256) :
    (loaded cost loadCost pre free a b c d e f g h tail).memory = pre.memory := by rfl

end Compiler.Proofs.IRGeneration.NativeSourcePreludeLength

import Compiler.Proofs.IRGeneration.NativeSourcePackingCopy
import Compiler.Proofs.IRGeneration.NativeConstructorStackSteps

namespace Compiler.Proofs.IRGeneration.NativeSourcePackingStack
open EvmYul EVM.Proof

theorem decode644 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 644) = some (.DUP1, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 644).toNat = some 128 := by
    have index : (UInt256.ofNat 644).toNat = 644 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem decode645 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 645) = some (.SWAP2, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 645).toNat = some 145 := by
    have index : (UInt256.ofNat 645).toNat = 645 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem decode646 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 646) = some (.DUP10, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 646).toNat = some 137 := by
    have index : (UInt256.ofNat 646).toNat = 646 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

/-- The exact three native shuffles immediately preceding the first MCOPY. -/
def prepared (pre : EVM.State) (cost1 cost2 cost3 : Nat)
    (length a b c d e f g dest : UInt256) (tail : Stack UInt256) : EVM.State :=
  let one := (stepPre cost1 pre).replaceStackAndIncrPC
    (length :: length :: a :: b :: c :: d :: e :: f :: g :: dest :: tail)
  let two := (stepPre cost2 one).replaceStackAndIncrPC
    (a :: length :: length :: b :: c :: d :: e :: f :: g :: dest :: tail)
  (stepPre cost3 two).replaceStackAndIncrPC
    (dest :: a :: length :: length :: b :: c :: d :: e :: f :: g :: dest :: tail)

theorem shuffle (fuel cost1 cost2 cost3 : Nat) (pre : EVM.State)
    (length a b c d e f g dest : UInt256) (tail : Stack UInt256)
    (stack : pre.stack = length :: a :: b :: c :: d :: e :: f :: g :: dest :: tail) :
    (do
      let one ← EVM.step (fuel + 1) cost1 (some (.DUP1, none)) pre
      let two ← EVM.step (fuel + 1) cost2 (some (.SWAP2, none)) one
      EVM.step (fuel + 1) cost3 (some (.DUP10, none)) two) =
      .ok (prepared pre cost1 cost2 cost3 length a b c d e f g dest tail) := by
  rw [NativeMidnightConstructor.step_DUP1 fuel cost1 pre length _ stack]
  change (do
    let two ← EvmYul.swap 2 ((stepPre cost2
      ((stepPre cost1 pre).replaceStackAndIncrPC (length :: length :: a :: b :: c :: d :: e :: f :: g :: dest :: tail))))
    EvmYul.dup 10 (stepPre cost3 two)) = _
  simp only [EvmYul.swap, EvmYul.dup, EVM.State.replaceStackAndIncrPC, stepPre, stack]
  rfl

theorem operands (pre : EVM.State) (cost1 cost2 cost3 : Nat)
    (length a b c d e f g dest : UInt256) (tail : Stack UInt256) :
    (prepared pre cost1 cost2 cost3 length a b c d e f g dest tail).stack.pop3 =
      some (length :: b :: c :: d :: e :: f :: g :: dest :: tail, dest, a, length) := by rfl

theorem memory (pre : EVM.State) (cost1 cost2 cost3 : Nat)
    (length a b c d e f g dest : UInt256) (tail : Stack UInt256) :
    (prepared pre cost1 cost2 cost3 length a b c d e f g dest tail).memory = pre.memory := by rfl

end Compiler.Proofs.IRGeneration.NativeSourcePackingStack

import Compiler.Proofs.IRGeneration.NativeSourcePackingStack

namespace Compiler.Proofs.IRGeneration.NativeSourcePackingFragment
open EvmYul EVM.Proof NativeSourcePackingStack

def first (pre : EVM.State) (cost : Nat) (length : UInt256) : EVM.State :=
  (stepPre cost pre).replaceStackAndIncrPC (length :: pre.stack)
def second (pre : EVM.State) (cost1 cost2 : Nat) (length a b c d e f g dest : UInt256)
    (tail : Stack UInt256) : EVM.State :=
  (stepPre cost2 (first pre cost1 length)).replaceStackAndIncrPC
    (a :: length :: length :: b :: c :: d :: e :: f :: g :: dest :: tail)

theorem decodes (pre : EVM.State) (cost1 cost2 : Nat) (length a b c d e f g dest : UInt256)
    (tail : Stack UInt256) (code : pre.executionEnv.code = NativeSourceAbiWrite.code)
    (pc : pre.pc = UInt256.ofNat 644) :
    decodeAt pre = (.DUP1, none) ∧
    decodeAt (first pre cost1 length) = (.SWAP2, none) ∧
    decodeAt (second pre cost1 cost2 length a b c d e f g dest tail) = (.DUP10, none) := by
  have pc1 : (first pre cost1 length).pc = UInt256.ofNat 645 := by
    change pre.pc + UInt256.ofNat 1 = _
    rw [pc]; decide
  have pc2 : (second pre cost1 cost2 length a b c d e f g dest tail).pc = UInt256.ofNat 646 := by
    change (first pre cost1 length).pc + UInt256.ofNat 1 = _
    rw [pc1]; decide
  unfold decodeAt
  change (EVM.decode pre.executionEnv.code pre.pc).getD _ = _ ∧
    (EVM.decode pre.executionEnv.code (first pre cost1 length).pc).getD _ = _ ∧
    (EVM.decode pre.executionEnv.code (second pre cost1 cost2 length a b c d e f g dest tail).pc).getD _ = _
  rw [code, pc, pc1, pc2, decode644, decode645, decode646]
  exact ⟨rfl, rfl, rfl⟩

theorem execute (fuel cost1 cost2 cost3 : Nat) (pre : EVM.State)
    (length a b c d e f g dest : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 644)
    (stack : pre.stack = length :: a :: b :: c :: d :: e :: f :: g :: dest :: tail) :
    (do
      let one ← EVM.step (fuel + 1) cost1 (some (decodeAt pre)) pre
      let two ← EVM.step (fuel + 1) cost2 (some (decodeAt one)) one
      EVM.step (fuel + 1) cost3 (some (decodeAt two)) two) =
      .ok (prepared pre cost1 cost2 cost3 length a b c d e f g dest tail) := by
  have decoded := decodes pre cost1 cost2 length a b c d e f g dest tail code pc
  have duplicate : EVM.step (fuel + 1) cost1 (some (.DUP1, none)) pre = .ok (first pre cost1 length) := by
    simpa only [first, stack, StepOk, Step] using NativeMidnightConstructor.step_DUP1 fuel cost1 pre length _ stack
  rw [decoded.1, duplicate]
  change (do
    let two ← EVM.step (fuel + 1) cost2 (some (decodeAt (first pre cost1 length))) (first pre cost1 length)
    EVM.step (fuel + 1) cost3 (some (decodeAt two)) two) = _
  rw [decoded.2.1]
  have swap : EVM.step (fuel + 1) cost2 (some (.SWAP2, none)) (first pre cost1 length) =
      .ok (second pre cost1 cost2 length a b c d e f g dest tail) := by
    change EvmYul.swap 2 _ = _
    simp only [EvmYul.swap, first, stepPre, EVM.State.replaceStackAndIncrPC, stack]
    rfl
  rw [swap]
  simp only [Bind.bind, Except.bind]
  change EVM.step (fuel + 1) cost3 (some (decodeAt (second pre cost1 cost2 length a b c d e f g dest tail)))
    (second pre cost1 cost2 length a b c d e f g dest tail) = _
  rw [decoded.2.2]
  change EvmYul.dup 10 (stepPre cost3 (second pre cost1 cost2 length a b c d e f g dest tail)) = _
  simp only [EvmYul.dup, second, first, stepPre, EVM.State.replaceStackAndIncrPC, stack]
  rfl

end Compiler.Proofs.IRGeneration.NativeSourcePackingFragment

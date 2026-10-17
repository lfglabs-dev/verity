import Compiler.Proofs.IRGeneration.NativeSourceSecondCopyHead

namespace Compiler.Proofs.IRGeneration.NativeSourceSecondCopyStore
open EvmYul EVM.Proof NativeSourcePreludeDecoded NativeSourceSecondCopyHead

theorem decode657 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 657) = some (.MSTORE, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 657).toNat = some 82 := by
    have index : (UInt256.ofNat 657).toNat = 657 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem decode658 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 658) = some (.MLOAD, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 658).toNat = some 81 := by
    have index : (UInt256.ofNat 658).toNat = 658 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

def stored (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256)
    (tail : Stack UInt256) : EVM.State :=
  let ready := s9 cost pre length b c d e f g dest x y tail
  EVM.State.replaceStackAndIncrPC
    { stepPre cost ready with
      toMachineState := (stepPre cost ready).toMachineState.mstore ((e + length) + d) x }
    (b :: ((e + length) + d) :: (e + length) :: c :: d :: e :: f :: g :: dest :: x :: y :: tail)

theorem store (fuel cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256)
    (tail : Stack UInt256) (code : pre.executionEnv.code = NativeSourceAbiWrite.code)
    (pc : pre.pc = UInt256.ofNat 648) :
    EVM.step (fuel + 1) cost (some (decodeAt (s9 cost pre length b c d e f g dest x y tail)))
      (s9 cost pre length b c d e f g dest x y tail) =
      .ok (stored cost pre length b c d e f g dest x y tail) := by
  have atPC : (s9 cost pre length b c d e f g dest x y tail).pc = UInt256.ofNat 657 := by
    change ((((((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) +
      UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1 = _
    rw [pc]; decide
  have decoded : decodeAt (s9 cost pre length b c d e f g dest x y tail) = (.MSTORE, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s9 cost pre length b c d e f g dest x y tail).pc).getD _ = _
    rw [code, atPC, decode657]
    rfl
  rw [decoded]
  exact step_MSTORE fuel cost _ _ _ x (operands cost pre length b c d e f g dest x y tail)

def loaded (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256) (tail : Stack UInt256) :=
  NativeSourceLoadStep.loaded cost (stored cost pre length b c d e f g dest x y tail) b
    (((e + length) + d) :: (e + length) :: c :: d :: e :: f :: g :: dest :: x :: y :: tail)

theorem load (fuel cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256)
    (tail : Stack UInt256) (code : pre.executionEnv.code = NativeSourceAbiWrite.code)
    (pc : pre.pc = UInt256.ofNat 648) :
    EVM.step (fuel + 1) cost (some (decodeAt (stored cost pre length b c d e f g dest x y tail)))
      (stored cost pre length b c d e f g dest x y tail) =
      .ok (loaded cost pre length b c d e f g dest x y tail) := by
  have atPC : (stored cost pre length b c d e f g dest x y tail).pc = UInt256.ofNat 658 := by
    change (((((((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) +
      UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1 = _
    rw [pc]; decide
  have decoded : decodeAt (stored cost pre length b c d e f g dest x y tail) = (.MLOAD, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (stored cost pre length b c d e f g dest x y tail).pc).getD _ = _
    rw [code, atPC, decode658]
    rfl
  rw [decoded]
  exact NativeSourceLoadStep.step fuel cost _ b _ (by rfl)

theorem execute (fuel cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256)
    (tail : Stack UInt256) (code : pre.executionEnv.code = NativeSourceAbiWrite.code)
    (pc : pre.pc = UInt256.ofNat 648)
    (stack : pre.stack = length :: b :: c :: d :: e :: f :: g :: dest :: x :: y :: tail) :
    run fuel cost 11 pre = .ok (loaded cost pre length b c d e f g dest x y tail) := by
  rw [show 11 = 9 + 2 by decide, run_add, NativeSourceSecondCopyHead.execute fuel cost pre length b c d e f g dest x y tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, store fuel cost pre length b c d e f g dest x y tail code pc]
  simp only [Bind.bind, Except.bind]
  rw [run, load fuel cost pre length b c d e f g dest x y tail code pc]
  rfl

theorem loaded_stack (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256)
    (tail : Stack UInt256) :
    (loaded cost pre length b c d e f g dest x y tail).stack =
      (stored cost pre length b c d e f g dest x y tail).toMachineState.lookupMemory b ::
      ((e + length) + d) :: (e + length) :: c :: d :: e :: f :: g :: dest :: x :: y :: tail := by
  rfl

theorem loaded_memory (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256)
    (tail : Stack UInt256) :
    (loaded cost pre length b c d e f g dest x y tail).memory =
      (stored cost pre length b c d e f g dest x y tail).memory := by
  rfl

end Compiler.Proofs.IRGeneration.NativeSourceSecondCopyStore

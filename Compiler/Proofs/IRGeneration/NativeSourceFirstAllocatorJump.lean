import Compiler.Proofs.IRGeneration.NativeSourceFirstAllocatorCall

namespace Compiler.Proofs.IRGeneration.NativeSourceFirstAllocatorJump
open EvmYul EVM.Proof NativeSourcePreludeDecoded NativeSourceFirstAllocatorCall

theorem decode631 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 631) = some (.JUMP, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 631).toNat = some 86 := by
    have index : (UInt256.ofNat 631).toNat = 631 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

def entered (cost : Nat) (pre : EVM.State) (a b c d e f g : UInt256) (tail : Stack UInt256) : EVM.State :=
  { stepPre cost (prepared cost pre a b c d e f g tail) with
    pc := UInt256.ofNat 910, stack := g :: a :: b :: c :: d :: e :: f :: g :: tail }

theorem jump (fuel cost : Nat) (pre : EVM.State) (a b c d e f g : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 627) :
    EVM.step (fuel + 1) cost (some (decodeAt (prepared cost pre a b c d e f g tail)))
      (prepared cost pre a b c d e f g tail) = .ok (entered cost pre a b c d e f g tail) := by
  have atPC : (prepared cost pre a b c d e f g tail).pc = UInt256.ofNat 631 := by
    change (pre.pc + UInt256.ofNat 1) + UInt256.ofNat 3 = _
    rw [pc]; decide
  have decoded : decodeAt (prepared cost pre a b c d e f g tail) = (.JUMP, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (prepared cost pre a b c d e f g tail).pc).getD _ = _
    rw [code, atPC, decode631]
    rfl
  rw [decoded]
  rfl

theorem execute (fuel cost : Nat) (pre : EVM.State) (a b c d e f g : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 627)
    (stack : pre.stack = a :: b :: c :: d :: e :: f :: g :: tail) :
    run fuel cost 3 pre = .ok (entered cost pre a b c d e f g tail) := by
  exact NativeSourceSizedPacking.compose fuel cost 2 1 pre _ _
    (NativeSourceFirstAllocatorCall.execute fuel cost pre a b c d e f g tail code pc stack)
    (by rw [run, jump fuel cost pre a b c d e f g tail code pc]; rfl)

theorem entry_stack (cost : Nat) (pre : EVM.State) (a b c d e f g : UInt256) (tail : Stack UInt256) :
    (entered cost pre a b c d e f g tail).stack = g :: a :: b :: c :: d :: e :: f :: g :: tail := by
  rfl

theorem entry_pc (cost : Nat) (pre : EVM.State) (a b c d e f g : UInt256) (tail : Stack UInt256) :
    (entered cost pre a b c d e f g tail).pc = UInt256.ofNat 910 := by
  rfl

end Compiler.Proofs.IRGeneration.NativeSourceFirstAllocatorJump

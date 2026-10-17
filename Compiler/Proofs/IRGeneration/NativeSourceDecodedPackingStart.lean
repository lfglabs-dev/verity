import Compiler.Proofs.IRGeneration.NativeSourceFreePointer

namespace Compiler.Proofs.IRGeneration.NativeSourceDecodedPackingStart
open EvmYul EVM.Proof NativeSourceFreePointer NativeSourcePreludeDecoded

theorem decodes (cost : Nat) (pre : EVM.State)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 632) :
    decodeAt pre = (.JUMPDEST, none) ∧
    decodeAt (jumped cost pre) = (.Push .PUSH1, some (UInt256.ofNat 64, 1)) ∧
    decodeAt (pushed cost pre) = (.MLOAD, none) := by
  have pc1 : (jumped cost pre).pc = UInt256.ofNat 633 := by
    change pre.pc + UInt256.ofNat 1 = _
    rw [pc]; decide
  have pc2 : (pushed cost pre).pc = UInt256.ofNat 635 := by
    change (jumped cost pre).pc + UInt256.ofNat 2 = _
    rw [pc1]; decide
  unfold decodeAt
  change (EVM.decode pre.executionEnv.code pre.pc).getD _ = _ ∧
    (EVM.decode pre.executionEnv.code (jumped cost pre).pc).getD _ = _ ∧
    (EVM.decode pre.executionEnv.code (pushed cost pre).pc).getD _ = _
  rw [code, pc, pc1, pc2, decode632, decode633, decode635]
  exact ⟨rfl, rfl, rfl⟩

theorem run3 (fuel cost : Nat) (pre : EVM.State)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 632) :
    run fuel cost 3 pre = .ok (loaded cost pre) := by
  have decoded := decodes cost pre code pc
  rw [run, decoded.1, step_JUMPDEST fuel cost pre]
  simp only [Bind.bind, Except.bind]
  change run fuel cost 2 (jumped cost pre) = _
  rw [run, decoded.2.1, NativeMidnightConstructor.step_PUSH1 fuel cost _ (UInt256.ofNat 64)]
  simp only [Bind.bind, Except.bind]
  change run fuel cost 1 (pushed cost pre) = _
  rw [run, decoded.2.2, NativeSourceLoadStep.step fuel cost _ (UInt256.ofNat 64) pre.stack (by rfl)]
  rfl

def free (cost : Nat) (pre : EVM.State) :=
  (pushed cost pre).toMachineState.lookupMemory (UInt256.ofNat 64)
def copied (cost : Nat) (pre : EVM.State) (a b c d e f g h : UInt256) (tail : Stack UInt256) :=
  NativeSourcePreludeCopy.copied cost cost cost cost cost cost (loaded cost pre)
    (free cost pre) a b c d e f g h tail

theorem execute (fuel cost : Nat) (pre : EVM.State) (a b c d e f g h : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 632)
    (stack : pre.stack = a :: b :: c :: d :: e :: f :: g :: h :: tail) :
    run fuel cost 15 pre = .ok (copied cost pre a b c d e f g h tail) := by
  rw [show 15 = 3 + 12 by decide, run_add, run3 fuel cost pre code pc]
  simp only [Bind.bind, Except.bind]
  apply NativeSourceDecodedFirstCopy.execute fuel cost (loaded cost pre) (free cost pre) a b c d e f g h tail
  · exact code
  · exact NativeSourceFreePointer.pc cost pre pc
  · rw [NativeSourceFreePointer.stack, stack]
    rfl

end Compiler.Proofs.IRGeneration.NativeSourceDecodedPackingStart

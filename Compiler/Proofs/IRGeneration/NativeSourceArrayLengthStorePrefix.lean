import Compiler.Proofs.IRGeneration.NativeSourceArrayLengthStoreSteps

namespace Compiler.Proofs.IRGeneration.NativeSourceArrayLengthStorePrefix
open EvmYul EVM EVM.Proof NativeSourceArrayLengthStoreSteps

def s1 (pre : EVM.State) := entered pre

def s2 (pre : EVM.State) (a n : UInt256) (tail : Stack UInt256) := lengthPost (s1 pre) a n tail

def s3 (pre : EVM.State) (a n x pointer : UInt256) (tail : Stack UInt256) :=
  pointerPost (s2 pre a n (x :: pointer :: tail)) n a x pointer tail

def expansion (pre : EVM.State) (a n x pointer : UInt256) (tail : Stack UInt256) :=
  memoryExpansionCost (s3 pre a n x pointer tail) .MSTORE

def stored (pre : EVM.State) (a n x pointer : UInt256) (tail : Stack UInt256) :=
  mstorePost 3 (NativeSourceFieldStoreChecks.expanded (s3 pre a n x pointer tail))
    (a :: n :: x :: pointer :: tail) pointer n

theorem pcs (pre : EVM.State) (a n x pointer : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 292) :
    (s1 pre).pc = UInt256.ofNat 293 ∧ (s2 pre a n (x :: pointer :: tail)).pc = UInt256.ofNat 294 ∧
    (s3 pre a n x pointer tail).pc = UInt256.ofNat 295 := by
  change pre.pc + UInt256.ofNat 1 = _ ∧ (pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1 = _ ∧
    ((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1 = _
  rw [pc]; decide

theorem gas_chain (pre : EVM.State) (a n x pointer : UInt256) (tail : Stack UInt256)
    (gas : 7 ≤ pre.gasAvailable.toNat) :
    (s1 pre).gasAvailable.toNat = pre.gasAvailable.toNat - 1 ∧
    (s2 pre a n (x :: pointer :: tail)).gasAvailable.toNat = pre.gasAvailable.toNat - 4 ∧
    (s3 pre a n x pointer tail).gasAvailable.toNat = pre.gasAvailable.toNat - 7 := by
  have g1 : (s1 pre).gasAvailable.toNat = pre.gasAvailable.toNat - 1 :=
    NativeSourceCheckedRejection.gas_sub _ 1 (by decide) (by omega)
  have g2 : (s2 pre a n (x :: pointer :: tail)).gasAvailable.toNat = (s1 pre).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g3 : (s3 pre a n x pointer tail).gasAvailable.toNat = (s2 pre a n (x :: pointer :: tail)).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  omega

theorem execute (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (a n x pointer : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 292)
    (stack : pre.stack = a :: n :: x :: pointer :: tail)
    (gas : 10 + expansion pre a n x pointer tail ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1018) :
    EVM.X (fuel + 5) jumps pre = EVM.X (fuel + 1) jumps (stored pre a n x pointer tail) := by
  obtain ⟨g1, g2, g3⟩ := gas_chain pre a n x pointer tail (by omega)
  obtain ⟨p1, p2, p3⟩ := pcs pre a n x pointer tail pc
  rw [enter_continue (fuel + 3) jumps pre code pc (by omega) (by simp only [stack, List.length_cons]; omega)]
  change EVM.X ((fuel + 2) + 2) jumps (s1 pre) = _
  rw [length_continue (fuel + 2) jumps (s1 pre) a n (x :: pointer :: tail) code p1
    (by exact stack) (by omega) (by simp only [s1, entered, stepPre, EVM.State.incrPC, stack, List.length_cons]; omega)]
  change EVM.X ((fuel + 1) + 2) jumps (s2 pre a n (x :: pointer :: tail)) = _
  rw [pointer_continue (fuel + 1) jumps (s2 pre a n (x :: pointer :: tail)) n a x pointer tail code p2
    rfl (by omega) (by simp only [s2, lengthPost, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, List.length_cons]; omega)]
  exact store_continue fuel jumps (s3 pre a n x pointer tail) pointer n (a :: n :: x :: pointer :: tail)
    code p3 rfl (by change expansion pre a n x pointer tail + 3 ≤ _; omega)
    (by simp only [List.length_cons]; omega)

theorem gas_exact (pre : EVM.State) (a n x pointer : UInt256) (tail : Stack UInt256)
    (gas : 10 + expansion pre a n x pointer tail ≤ pre.gasAvailable.toNat) :
    (stored pre a n x pointer tail).gasAvailable.toNat =
      pre.gasAvailable.toNat - expansion pre a n x pointer tail - 10 := by
  have charged := (gas_chain pre a n x pointer tail (by omega)).2.2
  have enough : memoryExpansionCost (s3 pre a n x pointer tail) .MSTORE + 3 ≤
      (s3 pre a n x pointer tail).gasAvailable.toNat := by
    change expansion pre a n x pointer tail + 3 ≤ _; omega
  have expanded := NativeSourceFieldStoreChecks.expansion_gas (s3 pre a n x pointer tail) (by omega)
  change (NativeSourceFieldStoreChecks.expanded (s3 pre a n x pointer tail)).gasAvailable.toNat =
    (s3 pre a n x pointer tail).gasAvailable.toNat - expansion pre a n x pointer tail at expanded
  have final : (stored pre a n x pointer tail).gasAvailable.toNat =
      (NativeSourceFieldStoreChecks.expanded (s3 pre a n x pointer tail)).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  omega

end Compiler.Proofs.IRGeneration.NativeSourceArrayLengthStorePrefix

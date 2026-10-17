import Compiler.Proofs.IRGeneration.NativeSourceArrayReadEntry

namespace Compiler.Proofs.IRGeneration.NativeSourceCheckedAllocatorStart
open EvmYul EVM EVM.Proof

theorem jumpdest_check (jumps : Array UInt256) (pre : EVM.State)
    (gas : 1 ≤ (pre.gasAvailable - UInt256.ofNat 0).toNat) (depth : pre.stack.length ≤ 1024) :
    Z jumps .JUMPDEST pre = .ok ({ pre with gasAvailable := pre.gasAvailable - UInt256.ofNat 0 }, 1) := by
  have cost (state : EVM.State) : C' state .JUMPDEST = 1 := by rfl
  simp only [Z, W, memoryExpansionCost, memoryExpansionCost.μᵢ', Nat.sub_self, cost]
  rw [if_neg (by omega), if_neg (by omega)]
  simp [δ, α, Operation.isCreate, show ¬1024 < pre.stack.length by omega]
  rfl

def s1 (pre : EVM.State) := (stepPre 1 pre).incrPC

def s2 (pre : EVM.State) (a b : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 (s1 pre)).replaceStackAndIncrPC (b :: a :: tail)

def s3 (pre : EVM.State) (a b : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 (s2 pre a b tail)).replaceStackAndIncrPC (UInt256.ofNat 31 :: b :: a :: tail) 2

theorem continue1 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 910)
    (gas : 1 ≤ pre.gasAvailable.toNat) (depth : pre.stack.length ≤ 1024) :
    EVM.X (fuel + 2) jumps pre = EVM.X (fuel + 1) jumps (s1 pre) := by
  have decoded : decodeAt pre = (.JUMPDEST, none) := by
    unfold decodeAt; rw [code, pc, NativeSourceAllocatorStart.decode910]; rfl
  have check := jumpdest_check jumps pre
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas) depth
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step : EVM.step (fuel + 1) 1 (some (.JUMPDEST, none)) pre = .ok (s1 pre) := by rfl
  exact X_succ_of_continue decoded check step rfl

theorem continue2 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (a b : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 910)
    (stack : pre.stack = a :: b :: tail)
    (gas : 3 ≤ (s1 pre).gasAvailable.toNat) (depth : tail.length ≤ 1021) :
    EVM.X (fuel + 2) jumps (s1 pre) = EVM.X (fuel + 1) jumps (s2 pre a b tail) := by
  have atPC : (s1 pre).pc = UInt256.ofNat 911 := by
    change pre.pc + UInt256.ofNat 1 = _; rw [pc]; decide
  have decoded : decodeAt (s1 pre) = (.SWAP1, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s1 pre).pc).getD _ = _
    rw [code, atPC, NativeSourceAllocatorStart.decode911]; rfl
  have check := NativeSourceGuardChecks.swap1 jumps (s1 pre)
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by change 2 ≤ pre.stack.length ∧ pre.stack.length ≤ 1024; simp only [stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step : EVM.step (fuel + 1) 3 (some (.SWAP1, none)) (s1 pre) = .ok (s2 pre a b tail) := by
    change EvmYul.swap 1 (stepPre 3 (s1 pre)) = _
    unfold EvmYul.swap
    simp only [s1, stepPre, EVM.State.incrPC, stack]
    rfl
  exact X_succ_of_continue decoded check step rfl

theorem continue3 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (a b : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 910)
    (gas : 3 ≤ (s2 pre a b tail).gasAvailable.toNat) (depth : tail.length ≤ 1021) :
    EVM.X (fuel + 2) jumps (s2 pre a b tail) = EVM.X (fuel + 1) jumps (s3 pre a b tail) := by
  have atPC : (s2 pre a b tail).pc = UInt256.ofNat 912 := by
    change (pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1 = _; rw [pc]; decide
  have decoded : decodeAt (s2 pre a b tail) = (.Push .PUSH1, some (UInt256.ofNat 31, 1)) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s2 pre a b tail).pc).getD _ = _
    rw [code, atPC, NativeSourceAllocatorStart.decode912]; rfl
  have check := NativeSourceGuardChecks.push1 jumps (s2 pre a b tail)
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by change 0 ≤ (b :: a :: tail).length ∧ (b :: a :: tail).length ≤ 1023; simp only [List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step : EVM.step (fuel + 1) 3 (some (.Push .PUSH1, some (UInt256.ofNat 31, 1))) (s2 pre a b tail) = .ok (s3 pre a b tail) := by rfl
  exact X_succ_of_continue decoded check step rfl

theorem gas_chain (pre : EVM.State) (a b : UInt256) (tail : Stack UInt256)
    (gas : 7 ≤ pre.gasAvailable.toNat) :
    (s1 pre).gasAvailable.toNat = pre.gasAvailable.toNat - 1 ∧
    (s2 pre a b tail).gasAvailable.toNat = pre.gasAvailable.toNat - 4 ∧
    (s3 pre a b tail).gasAvailable.toNat = pre.gasAvailable.toNat - 7 := by
  have g1 : (s1 pre).gasAvailable.toNat = pre.gasAvailable.toNat - 1 :=
    NativeSourceCheckedRejection.gas_sub _ 1 (by decide) (by omega)
  have g2 : (s2 pre a b tail).gasAvailable.toNat = (s1 pre).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g3 : (s3 pre a b tail).gasAvailable.toNat = (s2 pre a b tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  omega

theorem execute (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (a b : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 910)
    (stack : pre.stack = a :: b :: tail)
    (gas : 7 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1021) :
    EVM.X (fuel + 4) jumps pre = EVM.X (fuel + 1) jumps (s3 pre a b tail) := by
  obtain ⟨g1, g2, g3⟩ := gas_chain pre a b tail gas
  rw [continue1 (fuel + 2) jumps pre code pc (by omega) (by simp only [stack, List.length_cons]; omega)]
  rw [continue2 (fuel + 1) jumps pre a b tail code pc stack (by omega) depth]
  rw [continue3 fuel jumps pre a b tail code pc (by omega) depth]

end Compiler.Proofs.IRGeneration.NativeSourceCheckedAllocatorStart

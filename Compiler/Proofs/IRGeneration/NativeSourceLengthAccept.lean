import Compiler.Proofs.IRGeneration.NativeSourceCheckedLengthGuard

namespace Compiler.Proofs.IRGeneration.NativeSourceLengthAccept
open EvmYul EVM EVM.Proof NativeSourceCollateralLengthGuard

theorem panic_destination : UInt256.ofNat 786 ∈ EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0) := by
  rw [NativeSourceReturnMembership.scanned]
  apply NativeJumpScannerFrame.preserves
  simp [NativeSourceReturnMembership.found]

theorem zero_transition (fuel : Nat) (pre : EVM.State) (tail : Stack UInt256)
    (stack : pre.stack = UInt256.ofNat 786 :: UInt256.ofNat 0 :: tail) :
    EVM.step (fuel + 1) 10 (some (.JUMPI, none)) pre = .ok (NativeSourceCheckedReturn.fallthrough pre tail) := by
  change EvmYul.step (τ := .EVM) .JUMPI none (stepPre 10 pre) = _
  unfold EvmYul.step
  simp only [stepPre, stack]
  rfl

theorem zero_jump (fuel : Nat) (pre : EVM.State) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 272)
    (stack : pre.stack = UInt256.ofNat 786 :: UInt256.ofNat 0 :: tail)
    (gas : 10 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1022) :
    EVM.X (fuel + 2) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      EVM.X (fuel + 1) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0))
        (NativeSourceCheckedReturn.fallthrough pre tail) := by
  have decoded : decodeAt pre = (.JUMPI, none) := by
    unfold decodeAt; rw [code, pc, decode272]; rfl
  have check := NativeSourceJumpChecks.jumpi (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [stack, List.length_cons]; omega)
    (by rw [stack]; change (!(EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)).contains (UInt256.ofNat 786)) = false
        rw [NativeSourceJumpChecks.contains_of_mem _ _ panic_destination]; rfl)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  exact X_succ_of_continue decoded check (zero_transition fuel pre tail stack) rfl

theorem accept (fuel : Nat) (pre : EVM.State) (offset : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 258)
    (stack : pre.stack = offset :: tail) (valid : offset.toNat ≤ 2^64-1)
    (gas : 22 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1021) :
    EVM.X (fuel + 6) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      EVM.X (fuel + 1) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0))
        (NativeSourceCheckedReturn.fallthrough (s4 pre offset tail) (offset :: tail)) := by
  have charged := (NativeSourceCheckedLengthGuard.gas_chain pre offset tail (by omega)).2.2.2
  have shape := NativeSourceCheckedLengthGuard.prefix_frame pre offset tail pc
  rw [NativeSourceCheckedLengthGuard.execute_prefix (fuel + 1) _ pre offset tail code pc stack (by omega) depth]
  exact zero_jump fuel _ (offset :: tail) (shape.2.2.trans code) shape.1
    (by rw [shape.2.1, flag_zero offset valid]) (by omega) (by simp only [List.length_cons]; omega)

theorem accepted_gas (pre : EVM.State) (offset : UInt256) (tail : Stack UInt256)
    (gas : 22 ≤ pre.gasAvailable.toNat) :
    (NativeSourceCheckedReturn.fallthrough (s4 pre offset tail) (offset :: tail)).gasAvailable.toNat =
      pre.gasAvailable.toNat - 22 := by
  have charged := (NativeSourceCheckedLengthGuard.gas_chain pre offset tail (by omega)).2.2.2
  have final : (NativeSourceCheckedReturn.fallthrough (s4 pre offset tail) (offset :: tail)).gasAvailable.toNat =
      (s4 pre offset tail).gasAvailable.toNat - 10 :=
    NativeSourceCheckedRejection.gas_sub _ 10 (by decide) (by omega)
  omega

theorem accepted_frame (pre : EVM.State) (offset : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 258) :
    (NativeSourceCheckedReturn.fallthrough (s4 pre offset tail) (offset :: tail)).pc = UInt256.ofNat 273 ∧
      (NativeSourceCheckedReturn.fallthrough (s4 pre offset tail) (offset :: tail)).stack = offset :: tail ∧
      (NativeSourceCheckedReturn.fallthrough (s4 pre offset tail) (offset :: tail)).toState = pre.toState ∧
      (NativeSourceCheckedReturn.fallthrough (s4 pre offset tail) (offset :: tail)).memory = pre.memory := by
  refine ⟨?_, rfl, rfl, rfl⟩
  change (s4 pre offset tail).pc + UInt256.ofNat 1 = _
  rw [(NativeSourceCheckedLengthGuard.prefix_frame pre offset tail pc).1]; decide

theorem canonical_length_bound (n : Nat) (bound : n ≤ 2^64-1) :
    (UInt256.ofNat n).toNat ≤ 2^64-1 := by
  change n % UInt256.size ≤ 2^64-1
  have modulus : 2^64-1 < UInt256.size := by decide
  rw [Nat.mod_eq_of_lt (by omega)]
  exact bound

theorem market_length_accept (fuel : Nat) (pre : EVM.State) (tail : Stack UInt256)
    (n : Nat) (bound : n ≤ 2^64-1)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 258)
    (stack : pre.stack = UInt256.ofNat n :: tail)
    (gas : 22 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1021) :
    EVM.X (fuel + 6) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      EVM.X (fuel + 1) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0))
        (NativeSourceCheckedReturn.fallthrough (s4 pre (UInt256.ofNat n) tail) (UInt256.ofNat n :: tail)) := by
  exact accept fuel pre _ tail code pc stack (canonical_length_bound n bound) gas depth

end Compiler.Proofs.IRGeneration.NativeSourceLengthAccept

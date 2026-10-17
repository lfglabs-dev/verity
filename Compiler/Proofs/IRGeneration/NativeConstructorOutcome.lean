import Compiler.Proofs.IRGeneration.NativeConstructorSuccess

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul EVM.Proof NativeInitcodeFrames
open Verity.Core.Model.MidnightInitcode

private theorem stage_error (payload : ByteArray) (stage : Fin 9) (pre : EVM.State)
    (jumps : Array UInt256) (holds : DataAt payload stage pre)
    (reason : EVM.ExecutionException)
    (failed : Z jumps (stageInstruction stage).1 pre = .error reason) : reason = .OutOfGass := by
  rw [stage_checks payload stage pre jumps holds] at failed
  dsimp only at failed
  split at failed
  · exact (Except.error.inj failed).symm
  · split at failed
    · exact (Except.error.inj failed).symm
    · cases failed

private theorem outcome_from_stage (initial : Nat) (payload : ByteArray)
    (bounded : payload.size ≤ 49152) (jumps : Array UInt256)
    (fuel : Nat) (stage : Fin 9) (pre : EVM.State)
    (holds : GasAt initial payload stage pre) (enough : 10 ≤ fuel + stage.val) :
    EVM.X fuel jumps pre = .error .OutOfGass ∨
      ∃ post, EVM.X fuel jumps pre = .ok (.success post payload) := by
  induction fuel generalizing stage pre with
  | zero => omega
  | succ fuel ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have decoded := data_decode payload stage pre holds.1
      cases checked : Z jumps (stageInstruction stage).1 pre with
      | error reason =>
        have same := stage_error payload stage pre jumps holds.1 reason checked
        subst reason
        exact Or.inl (X_succ_of_Z_error decoded checked)
      | ok entry =>
        obtain ⟨mid, cost⟩ := entry
        have dataMid : DataAt payload stage mid := by rw [Z_ok_state checked]; exact holds.1
        obtain ⟨next, stepped⟩ := stage_step_success payload stage mid fuel cost dataMid
        by_cases continuing : stage.val < 8
        · let short : Fin 8 := ⟨stage.val, continuing⟩
          have nextHolds := gas_next initial payload short jumps pre mid next fuel cost
            holds bounded checked stepped
          have continued := X_succ_of_continue decoded checked stepped (stage_nonhalting short next)
          rw [continued]
          exact ih ⟨stage.val + 1, by omega⟩ next nextHolds
            (by change 10 ≤ fuel + 1 + (stage.val + 1); omega)
        · have last : stage = ⟨8, by decide⟩ := by
            apply Fin.ext
            change stage.val = 8
            omega
          subst stage
          have returned := gas_return initial payload jumps pre mid next fuel cost holds bounded checked stepped
          exact Or.inr ⟨next, X_succ_of_halt decoded checked stepped returned.2 (by decide)⟩

/-- With sufficient interpreter fuel, the actual header either runs out of EVM
gas or returns its payload. No revert, invalid opcode, stack error or other
exception is silently accepted as a constructor outcome. -/
theorem run_outcome (payload : ByteArray) (bounded : payload.size ≤ 49152)
    (jumps : Array UInt256) (pre : EVM.State) (fuel : Nat)
    (code : pre.executionEnv.code = initcode payload) (pc : pre.pc.toNat = 0)
    (stack : pre.stack = []) (fresh : pre.activeWords = UInt256.ofNat 0)
    (enough : 10 ≤ fuel) :
    EVM.X fuel jumps pre = .error .OutOfGass ∨
      ∃ post, EVM.X fuel jumps pre = .ok (.success post payload) := by
  have data : DataAt payload ⟨0, by decide⟩ pre := by
    refine ⟨code, pc, stack, ?_⟩
    intro impossible
    change 7 ≤ (0 : Nat) at impossible
    omega
  have holds : GasAt pre.gasAvailable.toNat payload ⟨0, by decide⟩ pre :=
    ⟨data, fresh, by change pre.gasAvailable.toNat + 0 = pre.gasAvailable.toNat; omega⟩
  exact outcome_from_stage pre.gasAvailable.toNat payload bounded jumps fuel
    ⟨0, by decide⟩ pre holds (by change 10 ≤ fuel + 0; omega)

/-- Low EVM gas is exactly OutOfGass, rather than an arbitrary failed outcome. -/
theorem run_out_of_gas (payload : ByteArray) (bounded : payload.size ≤ 49152)
    (jumps : Array UInt256) (pre : EVM.State) (fuel : Nat)
    (code : pre.executionEnv.code = initcode payload) (pc : pre.pc.toNat = 0)
    (stack : pre.stack = []) (fresh : pre.activeWords = UInt256.ofNat 0)
    (gas : pre.gasAvailable.toNat < prefixCost payload.size) (enough : 10 ≤ fuel) :
    EVM.X fuel jumps pre = .error .OutOfGass := by
  rcases run_outcome payload bounded jumps pre fuel code pc stack fresh enough with failed | success
  · exact failed
  · obtain ⟨post, success⟩ := success
    have charged := success_gas payload bounded jumps pre post fuel payload code pc stack fresh success
    omega

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor

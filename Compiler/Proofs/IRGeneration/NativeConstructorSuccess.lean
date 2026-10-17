import Compiler.Proofs.IRGeneration.NativeConstructorChecks

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul EVM.Proof NativeInitcodeFrames
open Verity.Core.Model.MidnightInitcode

private theorem run_from_stage (initial : Nat) (payload : ByteArray)
    (bounded : payload.size ≤ 49152) (jumps : Array UInt256)
    (total : prefixCost payload.size ≤ initial)
    (fuel : Nat) (stage : Fin 9) (pre : EVM.State)
    (holds : GasAt initial payload stage pre) (enough : 10 ≤ fuel + stage.val) :
    ∃ post, EVM.X fuel jumps pre = .ok (.success post payload) := by
  induction fuel generalizing stage pre with
  | zero => omega
  | succ fuel ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      let mid := zMid pre (stageInstruction stage).1
      have checked := checked_of_budget initial payload stage pre jumps holds bounded total
      have dataMid : DataAt payload stage mid := holds.1
      obtain ⟨next, stepped⟩ := stage_step_success payload stage mid fuel (stageCost payload.size stage) dataMid
      have decoded := data_decode payload stage pre holds.1
      by_cases continuing : stage.val < 8
      · let short : Fin 8 := ⟨stage.val, continuing⟩
        have nextHolds := gas_next initial payload short jumps pre mid next fuel
          (stageCost payload.size stage) holds bounded checked stepped
        have continues := stage_nonhalting short next
        obtain ⟨post, finished⟩ := ih ⟨stage.val + 1, by omega⟩ next nextHolds
          (by change 10 ≤ fuel + 1 + (stage.val + 1); omega)
        refine ⟨post, ?_⟩
        rw [X_succ_of_continue decoded checked stepped continues]
        exact finished
      · have last : stage = ⟨8, by decide⟩ := by
          apply Fin.ext
          change stage.val = 8
          omega
        subst stage
        have result := gas_return initial payload jumps pre mid next fuel _ holds bounded checked stepped
        refine ⟨next, ?_⟩
        exact X_succ_of_halt decoded checked stepped result.2 (by decide)

/-- Sufficient gas and interpreter fuel guarantee actual constructor success,
with exact payload, canonical remaining gas and unchanged native world. -/
theorem run_success (payload : ByteArray) (bounded : payload.size ≤ 49152)
    (jumps : Array UInt256) (pre : EVM.State) (fuel : Nat)
    (code : pre.executionEnv.code = initcode payload) (pc : pre.pc.toNat = 0)
    (stack : pre.stack = []) (fresh : pre.activeWords = UInt256.ofNat 0)
    (gas : prefixCost payload.size ≤ pre.gasAvailable.toNat) (enough : 10 ≤ fuel) :
    ∃ post, EVM.X fuel jumps pre = .ok (.success post payload) ∧
      post.gasAvailable.toNat = pre.gasAvailable.toNat - prefixCost payload.size ∧
      post.toState = pre.toState := by
  have data : DataAt payload ⟨0, by decide⟩ pre := by
    refine ⟨code, pc, stack, ?_⟩
    intro impossible
    change 7 ≤ (0 : Nat) at impossible
    omega
  have holds : GasAt pre.gasAvailable.toNat payload ⟨0, by decide⟩ pre :=
    ⟨data, fresh, by change pre.gasAvailable.toNat + 0 = pre.gasAvailable.toNat; omega⟩
  obtain ⟨post, success⟩ := run_from_stage pre.gasAvailable.toNat payload bounded jumps gas fuel
    ⟨0, by decide⟩ pre holds (by change 10 ≤ fuel + 0; omega)
  have charged := success_gas payload bounded jumps pre post fuel payload code pc stack fresh success
  refine ⟨post, success, by omega, ?_⟩
  exact success_state payload jumps pre post payload fuel ⟨code, by rw [pc]; decide⟩ success

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor

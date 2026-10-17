import Compiler.Proofs.IRGeneration.NativeConstructorOutcome
import Compiler.Proofs.IRGeneration.NativeConstructorXi

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul EVM.Proof NativeInitcodeFrames
open Verity.Core.Model.MidnightInitcode

private theorem word_eq_of_toNat (left right : UInt256) (equal : left.toNat = right.toNat) :
    left = right := by
  cases left with
  | mk left =>
    cases right with
    | mk right => exact congrArg UInt256.mk (Fin.ext equal)

/-- Exact native Ξ outcome for the constructor, for all gas values. It preserves
all supplied world channels on success and returns exact OutOfGass below the
canonical debit, with no remaining interpreter-fuel dependency. -/
theorem xi_constructor (payload : ByteArray) (bounded : payload.size ≤ 49152)
    (created : Std.TreeSet AccountAddress compare) (genesis : BlockHeader)
    (blocks : ProcessedBlocks) (accounts original : AccountMap .EVM)
    (gas : UInt256) (substate : Substate) (environment : ExecutionEnv .EVM)
    (code : environment.code = initcode payload) (fuel : Nat) (enough : 10 ≤ fuel) :
    EVM.Ξ (fuel + 1) created genesis blocks accounts original gas substate environment =
      if gas.toNat < prefixCost payload.size then .error .OutOfGass else
        .ok (.success (created, accounts, UInt256.ofNat (gas.toNat - prefixCost payload.size), substate) payload) := by
  let initial := xiInitial created genesis blocks accounts original gas substate environment
  rw [xi_run]
  by_cases low : gas.toNat < prefixCost payload.size
  · have failed := run_out_of_gas payload bounded (EVM.D_J environment.code ⟨0⟩) initial
      fuel code rfl rfl rfl low enough
    change (do
      let result ← EVM.X fuel (EVM.D_J environment.code ⟨0⟩) initial
      match result with
      | .success state output => pure (EVM.ExecutionResult.success
          (state.createdAccounts, state.accountMap, state.gasAvailable, state.substate) output)
      | .revert remaining output => pure (EVM.ExecutionResult.revert remaining output)) = _
    rw [failed, if_pos low]
    rfl
  · obtain ⟨post, success, remaining, world⟩ := run_success payload bounded
      (EVM.D_J environment.code ⟨0⟩) initial fuel code rfl rfl rfl (by change prefixCost payload.size ≤ gas.toNat; omega) enough
    have gasEq : post.gasAvailable = UInt256.ofNat (gas.toNat - prefixCost payload.size) := by
      apply word_eq_of_toNat
      rw [remaining]
      change gas.toNat - prefixCost payload.size = (gas.toNat - prefixCost payload.size) % UInt256.size
      exact (Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.sub_le _ _) gas.val.isLt)).symm
    have createdEq := congrArg (fun state : State .EVM => state.createdAccounts) world
    have accountsEq := congrArg (fun state : State .EVM => state.accountMap) world
    have substateEq := congrArg (fun state : State .EVM => state.substate) world
    change (do
      let result ← EVM.X fuel (EVM.D_J environment.code ⟨0⟩) initial
      match result with
      | .success state output => pure (EVM.ExecutionResult.success
          (state.createdAccounts, state.accountMap, state.gasAvailable, state.substate) output)
      | .revert remaining output => pure (EVM.ExecutionResult.revert remaining output)) = _
    rw [success, if_neg low]
    simp only [Bind.bind, Except.bind, Pure.pure, Except.pure, gasEq, createdEq, accountsEq, substateEq]
    rfl

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor

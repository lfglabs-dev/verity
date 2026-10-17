import Compiler.Proofs.IRGeneration.NativeConstructorDataRun

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul EVM.Proof NativeInitcodeFrames
open Verity.Core.Model.MidnightInitcode

/-- Exactly the initial state allocated by the native Ξ wrapper. -/
def xiInitial (created : Std.TreeSet AccountAddress compare) (genesis : BlockHeader)
    (blocks : ProcessedBlocks) (accounts original : AccountMap .EVM)
    (gas : UInt256) (substate : Substate) (environment : ExecutionEnv .EVM) : EVM.State :=
  { (default : EVM.State) with
    accountMap := accounts
    σ₀ := original
    executionEnv := environment
    substate := substate
    createdAccounts := created
    gasAvailable := gas
    blocks := blocks
    genesisBlockHeader := genesis }

/-- Expose Ξ's real one-unit fuel decrement without changing its semantics. -/
theorem xi_run (fuel : Nat) (created : Std.TreeSet AccountAddress compare)
    (genesis : BlockHeader) (blocks : ProcessedBlocks)
    (accounts original : AccountMap .EVM) (gas : UInt256) (substate : Substate)
    (environment : ExecutionEnv .EVM) :
    EVM.Ξ (fuel + 1) created genesis blocks accounts original gas substate environment =
      (do
        let result ← EVM.X fuel (EVM.D_J environment.code ⟨0⟩)
          (xiInitial created genesis blocks accounts original gas substate environment)
        match result with
        | .success state output => pure (.success
            (state.createdAccounts, state.accountMap, state.gasAvailable, state.substate) output)
        | .revert remaining output => pure (.revert remaining output)) := by
  rfl

/-- The actual Ξ wrapper needs one more unit than the constructor X bound. -/
theorem xi_fuel_stable (payload : ByteArray) (created : Std.TreeSet AccountAddress compare)
    (genesis : BlockHeader) (blocks : ProcessedBlocks)
    (accounts original : AccountMap .EVM) (gas : UInt256) (substate : Substate)
    (environment : ExecutionEnv .EVM) (code : environment.code = initcode payload)
    (fuelA fuelB : Nat) (enoughA : 14 ≤ fuelA) (enoughB : 14 ≤ fuelB) :
    EVM.Ξ fuelA created genesis blocks accounts original gas substate environment =
      EVM.Ξ fuelB created genesis blocks accounts original gas substate environment := by
  cases fuelA with
  | zero => omega
  | succ fuelA =>
    cases fuelB with
    | zero => omega
    | succ fuelB =>
      rw [xi_run, xi_run]
      have holds : InHeader payload
          (xiInitial created genesis blocks accounts original gas substate environment) :=
        ⟨code, by change (0 : Nat) < 11; decide⟩
      rw [fuel_stable payload _ _ holds fuelA fuelB (by omega) (by omega)]

/-- Interpreter exhaustion cannot escape Ξ for this actual constructor. -/
theorem xi_fuel_adequate (payload : ByteArray) (created : Std.TreeSet AccountAddress compare)
    (genesis : BlockHeader) (blocks : ProcessedBlocks)
    (accounts original : AccountMap .EVM) (gas : UInt256) (substate : Substate)
    (environment : ExecutionEnv .EVM) (code : environment.code = initcode payload)
    (fuel : Nat) (enough : 14 ≤ fuel) :
    EVM.Ξ fuel created genesis blocks accounts original gas substate environment ≠
      .error .OutOfFuel := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    rw [xi_run]
    have holds : InHeader payload
        (xiInitial created genesis blocks accounts original gas substate environment) :=
      ⟨code, by change (0 : Nat) < 11; decide⟩
    have adequate := fuel_adequate payload (EVM.D_J environment.code ⟨0⟩) _ holds fuel (by omega)
    cases executed : EVM.X fuel (EVM.D_J environment.code ⟨0⟩)
        (xiInitial created genesis blocks accounts original gas substate environment) with
    | error reason =>
      simp only [Bind.bind, Except.bind]
      intro equal
      have same := Except.error.inj equal
      subst reason
      exact adequate executed
    | ok result =>
      cases result <;> simp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
      all_goals intro impossible; cases impossible

/-- Successful Ξ returns the unchanged constructor world and actual payload.
The remaining gas is deliberately unconstrained here. -/
theorem xi_success (payload : ByteArray) (bounded : payload.size < 2^64)
    (created : Std.TreeSet AccountAddress compare) (genesis : BlockHeader)
    (blocks : ProcessedBlocks) (accounts original : AccountMap .EVM)
    (gas : UInt256) (substate : Substate) (environment : ExecutionEnv .EVM)
    (code : environment.code = initcode payload) (fuel : Nat)
    (created' : Std.TreeSet AccountAddress compare) (accounts' : AccountMap .EVM)
    (remaining : UInt256) (substate' : Substate) (output : ByteArray)
    (success : EVM.Ξ (fuel + 1) created genesis blocks accounts original gas substate environment =
      .ok (.success (created', accounts', remaining, substate') output)) :
    created' = created ∧ accounts' = accounts ∧ substate' = substate ∧ output = payload := by
  rw [xi_run] at success
  let initial := xiInitial created genesis blocks accounts original gas substate environment
  cases executed : EVM.X fuel (EVM.D_J environment.code ⟨0⟩) initial with
  | error reason =>
    simp only [initial, executed, Bind.bind, Except.bind] at success
    cases success
  | ok result =>
    simp only [initial, executed, Bind.bind, Except.bind] at success
    cases result with
    | revert remaining data => cases success
    | success next data =>
      have world := success_state payload (EVM.D_J environment.code ⟨0⟩) initial next data fuel
        ⟨code, by change (0 : Nat) < 11; decide⟩ executed
      have bytes := success_output payload bounded (EVM.D_J environment.code ⟨0⟩)
        initial next fuel data code rfl rfl executed
      have same := EVM.ExecutionResult.success.inj (Except.ok.inj success)
      have channels := same.1
      have createdEq := congrArg (fun x => x.1) channels
      have accountsEq := congrArg (fun x => x.2.1) channels
      have substateEq := congrArg (fun x => x.2.2.2) channels
      refine ⟨createdEq.symm.trans ?_, accountsEq.symm.trans ?_, substateEq.symm.trans ?_,
        same.2.symm.trans bytes⟩
      · exact congrArg (fun state : State .EVM => state.createdAccounts) world
      · exact congrArg (fun state : State .EVM => state.accountMap) world
      · exact congrArg (fun state : State .EVM => state.substate) world

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor

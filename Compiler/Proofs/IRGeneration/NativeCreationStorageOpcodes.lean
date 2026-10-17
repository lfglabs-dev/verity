import Compiler.Proofs.IRGeneration.NativeCreationStorageAgreement

/-! Exact storage opcode step shapes and boundary agreement. World opcodes
remain excluded from CreationCaller.run until prefix/world composition. -/
namespace Compiler.Proofs.IRGeneration.NativeCreationStorageOpcodes
open EvmYul NativeCreationWorld NativeCreationStorageAgreement

/-- Exact actual native opcode result, without replacing its state update. -/
theorem step_sstore (machine : EVM.State) (slot value : UInt256)
    (tail : Stack UInt256) (gasCost : Nat) :
    EVM.step 1 gasCost (some (.SSTORE, none)) { machine with stack := slot :: value :: tail } =
      .ok ({ machine with
        toState := machine.toState.sstore slot value
        gasAvailable := machine.gasAvailable - UInt256.ofNat gasCost,
        execLength := machine.execLength + 1 }.replaceStackAndIncrPC tail) := by
  rfl

theorem step_tstore (machine : EVM.State) (slot value : UInt256)
    (tail : Stack UInt256) (gasCost : Nat) :
    EVM.step 1 gasCost (some (.TSTORE, none)) { machine with stack := slot :: value :: tail } =
      .ok ({ machine with
        toState := machine.toState.tstore slot value
        gasAvailable := machine.gasAvailable - UInt256.ofNat gasCost,
        execLength := machine.execLength + 1 }.replaceStackAndIncrPC tail) := by
  rfl

/-- Execution counting is local bookkeeping, not an account-world effect. -/
theorem agreement_execLength (world : Verity.ContractState) (machine : EVM.State)
    (warm : Verity.Core.Model.Create2Access.WarmAccounts)
    (agrees : Agreement world machine warm) (length : Nat) :
    Agreement world { machine with execLength := length } warm :=
  { caller := agrees.caller
    source := agrees.source
    origin := agrees.origin
    value := agrees.value
    accounts := agrees.accounts
    selfBalance := agrees.selfBalance
    codeSizes := agrees.codeSizes
    persistent := agrees.persistent
    transient := agrees.transient
    parkedPersistent := agrees.parkedPersistent
    parkedTransient := agrees.parkedTransient
    accountAccess := agrees.accountAccess }

/-- Actual native SSTORE step, including charged gas and stack/PC updates,
preserves the raw boundary relation with the corresponding canonical write. -/
theorem step_sstore_agreement (world : Verity.ContractState) (machine : EVM.State)
    (warm : Verity.Core.Model.Create2Access.WarmAccounts) (entry : Account .EVM)
    (present : machine.toState.lookupAccount machine.executionEnv.codeOwner = some entry)
    (agrees : Agreement world machine warm) (slot value : UInt256)
    (tail : Stack UInt256) (gasCost : Nat) (after : EVM.State)
    (stepped : EVM.step 1 gasCost (some (.SSTORE, none))
      { machine with stack := slot :: value :: tail } = .ok after) :
    Agreement (world.writeSlot slot.toNat (Verity.Core.Uint256.ofNat value.toNat)) after warm := by
  rw [step_sstore] at stepped
  cases Except.ok.inj stepped
  let counted := { machine with execLength := machine.execLength + 1 }
  have counted_agreement := agreement_execLength world machine warm agrees (machine.execLength + 1)
  have stored := agreement_sstore world counted warm entry present counted_agreement slot value
  exact agreement_local _ _ warm stored
    (machine.gasAvailable - UInt256.ofNat gasCost) (machine.pc + UInt256.ofNat 1) tail machine.memory

/-- Actual native TSTORE step preserves the corresponding transient relation. -/
theorem step_tstore_agreement (world : Verity.ContractState) (machine : EVM.State)
    (warm : Verity.Core.Model.Create2Access.WarmAccounts) (entry : Account .EVM)
    (present : machine.toState.lookupAccount machine.executionEnv.codeOwner = some entry)
    (agrees : Agreement world machine warm) (slot value : UInt256)
    (tail : Stack UInt256) (gasCost : Nat) (after : EVM.State)
    (stepped : EVM.step 1 gasCost (some (.TSTORE, none))
      { machine with stack := slot :: value :: tail } = .ok after) :
    Agreement (world.writeTransient slot.toNat (Verity.Core.Uint256.ofNat value.toNat)) after warm := by
  rw [step_tstore] at stepped
  cases Except.ok.inj stepped
  let counted := { machine with execLength := machine.execLength + 1 }
  have counted_agreement := agreement_execLength world machine warm agrees (machine.execLength + 1)
  have stored := agreement_tstore world counted warm entry present counted_agreement slot value
  exact agreement_local _ _ warm stored
    (machine.gasAvailable - UInt256.ofNat gasCost) (machine.pc + UInt256.ofNat 1) tail machine.memory

private theorem success_after_guard (condition : Prop) [Decidable condition]
    (reason : EVM.ExecutionException) (next : Except EVM.ExecutionException EVM.State)
    (after : EVM.State)
    (success : (if condition then .error reason else next) = .ok after) :
    next = .ok after := by
  by_cases guard : condition
  · rw [if_pos guard] at success
    cases success
  · rw [if_neg guard] at success
    exact success

/-- A successful checked step is the real native step after memory charging.
No exceptional precheck is bypassed or replaced with a source-side oracle. -/
theorem checkedStep_delegates (machine after : EVM.State) (op : Operation .EVM)
    (arg : Option (UInt256 × Nat))
    (success : CreationCaller.checkedStep machine op arg = .ok after) :
    let expanded := { machine with gasAvailable := (machine.gasAvailable -
        UInt256.ofNat (EVM.memoryExpansionCost machine op)) }
    EVM.step 1 (EVM.C' expanded op) (some (op, arg)) expanded = .ok after := by
  dsimp only
  unfold CreationCaller.checkedStep at success
  dsimp only [Bind.bind, Pure.pure, throw, throwThe, MonadExceptOf.throw, Except.bind, Except.pure] at success
  repeat' first
    | exact success
    | replace success := success_after_guard _ _ _ _ success

/-- The memory charge changes only gas; raw world agreement is retained. -/
theorem agreement_memoryCharge (world : Verity.ContractState) (machine : EVM.State)
    (warm : Verity.Core.Model.Create2Access.WarmAccounts)
    (agrees : Agreement world machine warm) (op : Operation .EVM) :
    Agreement world { machine with gasAvailable := (machine.gasAvailable -
        UInt256.ofNat (EVM.memoryExpansionCost machine op)) } warm :=
  agreement_local world machine warm agrees
    (machine.gasAvailable - UInt256.ofNat (EVM.memoryExpansionCost machine op))
    machine.pc machine.stack machine.memory

/-- Successful checked SSTORE retains all raw agreement fields. Its actual
memory/instruction costs, static gate and stipend sentry remain in checkedStep. -/
theorem checked_sstore_agreement (world : Verity.ContractState) (machine : EVM.State)
    (warm : Verity.Core.Model.Create2Access.WarmAccounts) (entry : Account .EVM)
    (present : machine.toState.lookupAccount machine.executionEnv.codeOwner = some entry)
    (agrees : Agreement world machine warm) (slot value : UInt256)
    (tail : Stack UInt256) (after : EVM.State)
    (success : CreationCaller.checkedStep { machine with stack := slot :: value :: tail }
      .SSTORE none = .ok after) :
    Agreement (world.writeSlot slot.toNat (Verity.Core.Uint256.ofNat value.toNat)) after warm := by
  let stacked := { machine with stack := slot :: value :: tail }
  have stacked_agreement := agreement_local world machine warm agrees machine.gasAvailable
    machine.pc (slot :: value :: tail) machine.memory
  have charged := agreement_memoryCharge world stacked warm stacked_agreement .SSTORE
  have delegated := checkedStep_delegates stacked after .SSTORE none success
  let expanded : EVM.State := { stacked with gasAvailable := (stacked.gasAvailable -
      UInt256.ofNat (EVM.memoryExpansionCost stacked .SSTORE)) }
  exact step_sstore_agreement world expanded warm entry present charged slot value tail _ after delegated

/-- Successful checked TSTORE retains all raw agreement fields. -/
theorem checked_tstore_agreement (world : Verity.ContractState) (machine : EVM.State)
    (warm : Verity.Core.Model.Create2Access.WarmAccounts) (entry : Account .EVM)
    (present : machine.toState.lookupAccount machine.executionEnv.codeOwner = some entry)
    (agrees : Agreement world machine warm) (slot value : UInt256)
    (tail : Stack UInt256) (after : EVM.State)
    (success : CreationCaller.checkedStep { machine with stack := slot :: value :: tail }
      .TSTORE none = .ok after) :
    Agreement (world.writeTransient slot.toNat (Verity.Core.Uint256.ofNat value.toNat)) after warm := by
  let stacked := { machine with stack := slot :: value :: tail }
  have stacked_agreement := agreement_local world machine warm agrees machine.gasAvailable
    machine.pc (slot :: value :: tail) machine.memory
  have charged := agreement_memoryCharge world stacked warm stacked_agreement .TSTORE
  have delegated := checkedStep_delegates stacked after .TSTORE none success
  let expanded : EVM.State := { stacked with gasAvailable := (stacked.gasAvailable -
      UInt256.ofNat (EVM.memoryExpansionCost stacked .TSTORE)) }
  exact step_tstore_agreement world expanded warm entry present charged slot value tail _ after delegated

end Compiler.Proofs.IRGeneration.NativeCreationStorageOpcodes

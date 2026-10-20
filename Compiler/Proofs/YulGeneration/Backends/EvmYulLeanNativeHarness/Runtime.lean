import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanNativeHarness.Base

namespace Compiler.Proofs.YulGeneration.Backends.Native

open Compiler.Yul
open Compiler.Proofs.YulGeneration
open Compiler.Proofs.YulGeneration.Backends.StateBridge
open Lean Elab Tactic Meta
open Compiler.Proofs.IRGeneration
  (IRResult IRState IRStorageSlot IRStorageWord IRTransaction)

@[simp] theorem projectResult_finalMappings
    (tx : YulTransaction)
    (initialStorage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (result :
      Except EvmYul.Yul.Exception
        (EvmYul.Yul.State × List EvmYul.Yul.Ast.Literal)) :
    (projectResult tx initialStorage initialEvents result).finalMappings =
      Compiler.Proofs.storageAsMappings
        (projectResult tx initialStorage initialEvents result).finalStorage := by
  cases result with
  | ok value =>
      cases value with
      | mk state values => rfl
  | error err =>
      cases err <;> rfl

/-- Lower and execute Verity runtime Yul through EVMYulLean's native
    dispatcher. -/
def interpretRuntimeNative
    (fuel : Nat)
    (runtimeCode : List YulStmt)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (events : List (List Nat) := []) :
    Except NativeLoweringError YulResult := do
  validateGeneratedRuntimeNativeFragment runtimeCode
  let contract ← lowerRuntimeContractNative runtimeCode
  validateNativeRuntimeEnvironment runtimeCode tx
  let initial :=
    initialState contract tx storage
      (materializedStorageSlots runtimeCode observableSlots)
  let result := EvmYul.Yul.callDispatcher fuel (some contract) initial
  pure (projectResult tx storage events result)

@[simp] theorem interpretRuntimeNative_loweringError
    (fuel : Nat)
    (runtimeCode : List YulStmt)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (events : List (List Nat))
    (err : NativeLoweringError)
    (hFragment : generatedRuntimeNativeFragment runtimeCode = true)
    (hLower : lowerRuntimeContractNative runtimeCode = .error err) :
    interpretRuntimeNative fuel runtimeCode tx storage observableSlots events =
      .error err := by
  rw [interpretRuntimeNative, validateGeneratedRuntimeNativeFragment_ok runtimeCode hFragment, hLower]
  rfl

@[simp] theorem interpretRuntimeNative_generatedFragmentError
    (fuel : Nat)
    (runtimeCode : List YulStmt)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (events : List (List Nat))
    (hFragment : generatedRuntimeNativeFragment runtimeCode = false) :
    interpretRuntimeNative fuel runtimeCode tx storage observableSlots events =
      .error unsupportedGeneratedRuntimeNativeFragmentError := by
  rw [interpretRuntimeNative, validateGeneratedRuntimeNativeFragment_error runtimeCode hFragment]
  rfl

@[simp] theorem interpretRuntimeNative_eq_callDispatcher_of_lowerRuntimeContractNative
    (fuel : Nat)
    (runtimeCode : List YulStmt)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (events : List (List Nat))
    (contract : EvmYul.Yul.Ast.YulContract)
    (hFragment : generatedRuntimeNativeFragment runtimeCode = true)
    (hLower : lowerRuntimeContractNative runtimeCode = .ok contract)
    (hEnv : validateNativeRuntimeEnvironment runtimeCode tx = .ok ()) :
    interpretRuntimeNative fuel runtimeCode tx storage observableSlots events =
      .ok (projectResult tx storage events
        (EvmYul.Yul.callDispatcher fuel (some contract)
          (initialState contract tx storage
            (materializedStorageSlots runtimeCode observableSlots)))) := by
  rw [interpretRuntimeNative, validateGeneratedRuntimeNativeFragment_ok runtimeCode hFragment,
    hLower, hEnv]
  rfl

@[simp] theorem interpretRuntimeNative_succ_eq_contractDispatcherBlockResult_of_lowerRuntimeContractNative
    (fuel' : Nat)
    (runtimeCode : List YulStmt)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (events : List (List Nat))
    (contract : EvmYul.Yul.Ast.YulContract)
    (hFragment : generatedRuntimeNativeFragment runtimeCode = true)
    (hLower : lowerRuntimeContractNative runtimeCode = .ok contract)
    (hEnv : validateNativeRuntimeEnvironment runtimeCode tx = .ok ()) :
    interpretRuntimeNative (Nat.succ fuel') runtimeCode tx storage observableSlots events =
      .ok (projectResult tx storage events
        (contractDispatcherBlockResult fuel' contract
          (initialState contract tx storage
            (materializedStorageSlots runtimeCode observableSlots)))) := by
  rw [interpretRuntimeNative_eq_callDispatcher_of_lowerRuntimeContractNative
    (fuel := Nat.succ fuel') (contract := contract)
    (hFragment := hFragment) (hLower := hLower) (hEnv := hEnv)]
  rw [callDispatcher_succ_eq_callDispatcherBlockResult]
  rw [callDispatcherBlockResult_initialState_eq_contractDispatcherBlockResult]

@[simp] theorem interpretRuntimeNative_succ_eq_contractDispatcherExecResult_of_lowerRuntimeContractNative
    (fuel' : Nat)
    (runtimeCode : List YulStmt)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (events : List (List Nat))
    (contract : EvmYul.Yul.Ast.YulContract)
    (hFragment : generatedRuntimeNativeFragment runtimeCode = true)
    (hLower : lowerRuntimeContractNative runtimeCode = .ok contract)
    (hEnv : validateNativeRuntimeEnvironment runtimeCode tx = .ok ()) :
    interpretRuntimeNative (Nat.succ fuel') runtimeCode tx storage observableSlots events =
      .ok (projectResult tx storage events
        (let initial :=
          initialState contract tx storage
            (materializedStorageSlots runtimeCode observableSlots)
        let dispatcherDef :=
          EvmYul.Yul.Ast.FunctionDefinition.Def [] [] [contract.dispatcher]
        match contractDispatcherExecResult fuel' contract initial with
        | .error err => .error err
        | .ok finalState =>
            let restored := finalState.reviveJump.overwrite? initial |>.setStore initial
            .ok (restored, List.map finalState.lookup! dispatcherDef.rets))) := by
  rw [interpretRuntimeNative_succ_eq_contractDispatcherBlockResult_of_lowerRuntimeContractNative
    (contract := contract) (hFragment := hFragment) (hLower := hLower) (hEnv := hEnv)]
  rw [contractDispatcherBlockResult_eq_execResult]
  rfl

@[simp] theorem interpretRuntimeNative_environmentError
    (fuel : Nat)
    (runtimeCode : List YulStmt)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (events : List (List Nat))
    (contract : EvmYul.Yul.Ast.YulContract)
    (err : NativeLoweringError)
    (hFragment : generatedRuntimeNativeFragment runtimeCode = true)
    (hLower : lowerRuntimeContractNative runtimeCode = .ok contract)
    (hEnv : validateNativeRuntimeEnvironment runtimeCode tx = .error err) :
    interpretRuntimeNative fuel runtimeCode tx storage observableSlots events =
      .error err := by
  rw [interpretRuntimeNative, validateGeneratedRuntimeNativeFragment_ok runtimeCode hFragment,
    hLower, hEnv]
  rfl

/-- Native EVMYulLean execution target for emitted IR-contract runtime Yul.

This is the executable target that #1737 will promote into the public theorem
path once the state/result bridge lemmas are proved. It intentionally returns
`Except NativeLoweringError YulResult` today because native lowering can still fail
closed for duplicate helper definitions or unsupported runtime shapes.

The observable slot set is explicit because the public theorem compares only
those final storage (IRStorageSlot.ofNat slot)s. Native execution materializes those slots plus
literal `sload` slots derived from the emitted runtime so storage reads remain
faithful even when callers compare a smaller public projection.
-/
def interpretIRRuntimeNative
    (fuel : Nat)
    (contract : Compiler.IRContract)
    (tx : Compiler.Proofs.IRGeneration.IRTransaction)
    (state : Compiler.Proofs.IRGeneration.IRState)
    (observableSlots : List Nat) :
    Except NativeLoweringError YulResult :=
  interpretRuntimeNative fuel (Compiler.emitYul contract).runtimeCode
    (YulTransaction.ofIR tx) state.storage observableSlots state.events

@[simp] theorem interpretIRRuntimeNative_eq_interpretRuntimeNative
    (fuel : Nat)
    (contract : Compiler.IRContract)
    (tx : Compiler.Proofs.IRGeneration.IRTransaction)
    (state : Compiler.Proofs.IRGeneration.IRState)
    (observableSlots : List Nat) :
    interpretIRRuntimeNative fuel contract tx state observableSlots =
      interpretRuntimeNative fuel (Compiler.emitYul contract).runtimeCode
        (YulTransaction.ofIR tx) state.storage observableSlots state.events := by
  rfl

@[simp] theorem interpretIRRuntimeNative_loweringError
    (fuel : Nat)
    (contract : Compiler.IRContract)
    (tx : Compiler.Proofs.IRGeneration.IRTransaction)
    (state : Compiler.Proofs.IRGeneration.IRState)
    (observableSlots : List Nat)
    (err : NativeLoweringError)
    (hFragment :
      generatedRuntimeNativeFragment (Compiler.emitYul contract).runtimeCode = true)
    (hLower : lowerRuntimeContractNative (Compiler.emitYul contract).runtimeCode =
      .error err) :
    interpretIRRuntimeNative fuel contract tx state observableSlots = .error err := by
  rw [interpretIRRuntimeNative, interpretRuntimeNative,
    validateGeneratedRuntimeNativeFragment_ok (Compiler.emitYul contract).runtimeCode
      hFragment, hLower]
  rfl

@[simp] theorem interpretIRRuntimeNative_generatedFragmentError
    (fuel : Nat)
    (contract : Compiler.IRContract)
    (tx : Compiler.Proofs.IRGeneration.IRTransaction)
    (state : Compiler.Proofs.IRGeneration.IRState)
    (observableSlots : List Nat)
    (hFragment :
      generatedRuntimeNativeFragment (Compiler.emitYul contract).runtimeCode = false) :
    interpretIRRuntimeNative fuel contract tx state observableSlots =
      .error unsupportedGeneratedRuntimeNativeFragmentError := by
  rw [interpretIRRuntimeNative, interpretRuntimeNative,
    validateGeneratedRuntimeNativeFragment_error (Compiler.emitYul contract).runtimeCode
      hFragment]
  rfl

@[simp] theorem interpretIRRuntimeNative_eq_callDispatcher_of_lowerRuntimeContractNative
    (fuel : Nat)
    (irContract : Compiler.IRContract)
    (tx : Compiler.Proofs.IRGeneration.IRTransaction)
    (state : Compiler.Proofs.IRGeneration.IRState)
    (observableSlots : List Nat)
    (nativeContract : EvmYul.Yul.Ast.YulContract)
    (hFragment :
      generatedRuntimeNativeFragment (Compiler.emitYul irContract).runtimeCode = true)
    (hLower : lowerRuntimeContractNative (Compiler.emitYul irContract).runtimeCode =
      .ok nativeContract)
    (hEnv :
      validateNativeRuntimeEnvironment (Compiler.emitYul irContract).runtimeCode
        (YulTransaction.ofIR tx) = .ok ()) :
    interpretIRRuntimeNative fuel irContract tx state observableSlots =
      .ok (projectResult (YulTransaction.ofIR tx) state.storage state.events
        (EvmYul.Yul.callDispatcher fuel (some nativeContract)
          (initialState nativeContract (YulTransaction.ofIR tx) state.storage
            (materializedStorageSlots (Compiler.emitYul irContract).runtimeCode
              observableSlots)))) := by
  rw [interpretIRRuntimeNative, interpretRuntimeNative,
    validateGeneratedRuntimeNativeFragment_ok (Compiler.emitYul irContract).runtimeCode
      hFragment, hLower, hEnv]
  rfl

@[simp] theorem interpretIRRuntimeNative_succ_eq_contractDispatcherBlockResult_of_lowerRuntimeContractNative
    (fuel' : Nat)
    (irContract : Compiler.IRContract)
    (tx : Compiler.Proofs.IRGeneration.IRTransaction)
    (state : Compiler.Proofs.IRGeneration.IRState)
    (observableSlots : List Nat)
    (nativeContract : EvmYul.Yul.Ast.YulContract)
    (hFragment :
      generatedRuntimeNativeFragment (Compiler.emitYul irContract).runtimeCode = true)
    (hLower : lowerRuntimeContractNative (Compiler.emitYul irContract).runtimeCode =
      .ok nativeContract)
    (hEnv :
      validateNativeRuntimeEnvironment (Compiler.emitYul irContract).runtimeCode
        (YulTransaction.ofIR tx) = .ok ()) :
    interpretIRRuntimeNative (Nat.succ fuel') irContract tx state observableSlots =
      .ok (projectResult (YulTransaction.ofIR tx) state.storage state.events
        (contractDispatcherBlockResult fuel' nativeContract
          (initialState nativeContract (YulTransaction.ofIR tx) state.storage
            (materializedStorageSlots (Compiler.emitYul irContract).runtimeCode
              observableSlots)))) := by
  rw [interpretIRRuntimeNative, interpretRuntimeNative_succ_eq_contractDispatcherBlockResult_of_lowerRuntimeContractNative
    (contract := nativeContract) (hFragment := hFragment) (hLower := hLower)
    (hEnv := hEnv)]

@[simp] theorem interpretIRRuntimeNative_succ_eq_contractDispatcherExecResult_of_lowerRuntimeContractNative
    (fuel' : Nat)
    (irContract : Compiler.IRContract)
    (tx : Compiler.Proofs.IRGeneration.IRTransaction)
    (state : Compiler.Proofs.IRGeneration.IRState)
    (observableSlots : List Nat)
    (nativeContract : EvmYul.Yul.Ast.YulContract)
    (hFragment :
      generatedRuntimeNativeFragment (Compiler.emitYul irContract).runtimeCode = true)
    (hLower : lowerRuntimeContractNative (Compiler.emitYul irContract).runtimeCode =
      .ok nativeContract)
    (hEnv :
      validateNativeRuntimeEnvironment (Compiler.emitYul irContract).runtimeCode
        (YulTransaction.ofIR tx) = .ok ()) :
    interpretIRRuntimeNative (Nat.succ fuel') irContract tx state observableSlots =
      .ok (projectResult (YulTransaction.ofIR tx) state.storage state.events
        (let initial :=
          initialState nativeContract (YulTransaction.ofIR tx) state.storage
            (materializedStorageSlots (Compiler.emitYul irContract).runtimeCode
              observableSlots)
        let dispatcherDef :=
          EvmYul.Yul.Ast.FunctionDefinition.Def [] [] [nativeContract.dispatcher]
        match contractDispatcherExecResult fuel' nativeContract initial with
        | .error err => .error err
        | .ok finalState =>
            let restored := finalState.reviveJump.overwrite? initial |>.setStore initial
            .ok (restored, List.map finalState.lookup! dispatcherDef.rets))) := by
  rw [interpretIRRuntimeNative, interpretRuntimeNative_succ_eq_contractDispatcherExecResult_of_lowerRuntimeContractNative
    (contract := nativeContract) (hFragment := hFragment) (hLower := hLower)
    (hEnv := hEnv)]

/-- Observable result comparison surface for native EVMYulLean execution. -/
def nativeResultsMatchOn
    (observableSlots : List Nat)
    (ir : IRResult)
    (native : Except NativeLoweringError YulResult) :
    Prop :=
  match native with
  | .ok yul =>
      ir.success = yul.success ∧
      ir.returnValue = yul.returnValue ∧
      (∀ slot, slot ∈ observableSlots →
        ir.finalStorage (IRStorageSlot.ofNat slot) =
          yul.finalStorage (IRStorageSlot.ofNat slot)) ∧
      ir.events = yul.events
  | .error _ => False

/-- Variant of `exec_block_leave_ok_add_ten` that splices a
`NativePreservableStraightStmts`-derived prefix in front of `.Leave`.

If the native lowering of the prefix evaluates to `.ok mid` at the
`fuel + suffixLen + 10` budget already used by the dispatcher harness, then
appending `.Leave` to the lowered prefix runs at
`fuel + suffixLen + native.length + 10` and produces `.ok mid.setLeave`. -/
theorem exec_block_lowerStmtsNativeWithSwitchIds_with_leave_ok_eq_of_NativeBlockPreservesWord
    (fuel suffixLen : Nat)
    (native : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (initial mid : EvmYul.Yul.State)
    (hPre :
      EvmYul.Yul.exec (fuel + suffixLen + native.length + 10)
          (.Block native) codeOverride initial = .ok mid) :
    EvmYul.Yul.exec (fuel + suffixLen + native.length + 10)
        (.Block (native ++ [.Leave])) codeOverride initial =
      .ok mid.setLeave := by
  have hFuel :
      fuel + suffixLen + native.length + 10 =
        (fuel + suffixLen + 9) + native.length + 1 := by omega
  have hLeft :
      EvmYul.Yul.exec ((fuel + suffixLen + 9) + native.length + 1)
          (.Block native) codeOverride initial = .ok mid := hFuel ▸ hPre
  have hRight :
      EvmYul.Yul.exec ((fuel + suffixLen + 9) + 1) (.Block [.Leave])
          codeOverride mid = .ok mid.setLeave := by
    have hLeaveFuel :
        (fuel + suffixLen + 9) + 1 =
          Nat.succ (Nat.succ (fuel + suffixLen + 8)) := by
      omega
    rw [hLeaveFuel]
    cases mid <;> simp [EvmYul.Yul.exec, EvmYul.Yul.State.setLeave]
  rw [hFuel]
  exact exec_block_append_ok (fuel + suffixLen + 9) 1 native [.Leave]
    codeOverride initial mid mid.setLeave hLeft hRight

/-- No-leave variant: a `.Block (lower preStmts)` with per-slot preservation
exits with `.ok mid`, packaged at the standard `+ 10` fuel-padding form so
the dispatcher harness can splice it into a switch case body.

This is the trivial fuel-padded form of the prefix execution: given that the
lowered prefix already evaluates to `.ok mid`, restating the equation at the
canonical `fuel + suffixLen + native.length + 10` budget keeps the consumer
free of fuel-arithmetic plumbing. -/
theorem exec_block_lowerStmtsNativeWithSwitchIds_ok_eq_of_NativeBlockPreservesWord
    (fuel suffixLen : Nat)
    (native : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (initial mid : EvmYul.Yul.State)
    (hPre :
      EvmYul.Yul.exec (fuel + suffixLen + native.length + 10)
          (.Block native) codeOverride initial = .ok mid) :
    EvmYul.Yul.exec (fuel + suffixLen + native.length + 10)
        (.Block (native ++ [])) codeOverride initial = .ok mid := by
  simpa [List.append_nil] using hPre

end Compiler.Proofs.YulGeneration.Backends.Native

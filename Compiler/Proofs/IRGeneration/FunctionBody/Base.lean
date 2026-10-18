import Compiler.CompilationModel.ExpressionCompile
import Compiler.Proofs.IRGeneration.ParamLoading
import Compiler.Proofs.IRGeneration.SourceSemantics
import Compiler.Proofs.IRGeneration.SupportedSpec
import Compiler.Proofs.IRGeneration.ExprCore
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanBuiltinSemantics
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanPureBuiltinLemmas

set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.CompilationModel
open Compiler.Yul

namespace FunctionBody

def lookupBinding? (bindings : List (String × Nat)) (name : String) : Option Nat :=
  bindings.find? (fun entry => entry.1 == name) |>.map Prod.snd

-- exprBoundNames, exprListBoundNames are now in ExprCore.lean

def exprBoundNamesPresent (expr : Expr) (bindings : List (String × Nat)) : Prop :=
  ∀ name, name ∈ exprBoundNames expr → ∃ value, lookupBinding? bindings name = some value

theorem lookupValue_eq_of_lookupBinding?_some
    {bindings : List (String × Nat)}
    {name : String}
    {value : Nat}
    (hlookup : lookupBinding? bindings name = some value) :
    SourceSemantics.lookupValue bindings name = value := by
  unfold lookupBinding? at hlookup
  unfold SourceSemantics.lookupValue
  simp [hlookup]

def bindingsExactlyMatchIRVars
    (bindings : List (String × Nat))
    (state : IRState) : Prop :=
  ∀ name, state.getVar name = lookupBinding? bindings name

def bindingsExactlyMatchIRVarsOnScope
    (scope : List String)
    (bindings : List (String × Nat))
    (state : IRState) : Prop :=
  ∀ name, name ∈ scope → state.getVar name = lookupBinding? bindings name

def bindingsExactlyMatchIRVarsOnExpr
    (expr : Expr)
    (bindings : List (String × Nat))
    (state : IRState) : Prop :=
  ∀ name, name ∈ exprBoundNames expr → state.getVar name = lookupBinding? bindings name

def bindingsMatchIRVars
    (bindings : List (String × Nat))
    (state : IRState) : Prop :=
  ∀ name, (state.getVar name).getD 0 = SourceSemantics.lookupValue bindings name

def bindingsBounded (bindings : List (String × Nat)) : Prop :=
  ∀ name, SourceSemantics.lookupValue bindings name < Compiler.Constants.evmModulus

theorem bindingsExactlyMatchIRVars_implies_bindingsMatchIRVars
    {bindings : List (String × Nat)}
    {state : IRState}
    (hexact : bindingsExactlyMatchIRVars bindings state) :
    bindingsMatchIRVars bindings state := by
  intro name
  rw [hexact name]
  rfl

theorem bindingsExactlyMatchIRVars_implies_onScope
    {scope : List String}
    {bindings : List (String × Nat)}
    {state : IRState}
    (hexact : bindingsExactlyMatchIRVars bindings state) :
    bindingsExactlyMatchIRVarsOnScope scope bindings state := by
  intro name _
  exact hexact name

theorem bindingsExactlyMatchIRVars_implies_onExpr
    {expr : Expr}
    {bindings : List (String × Nat)}
    {state : IRState}
    (hexact : bindingsExactlyMatchIRVars bindings state) :
    bindingsExactlyMatchIRVarsOnExpr expr bindings state := by
  intro name _
  exact hexact name

theorem bindingsExactlyMatchIRVarsOnExpr_of_subset
    {expr subexpr : Expr}
    {bindings : List (String × Nat)}
    {state : IRState}
    (hexact : bindingsExactlyMatchIRVarsOnExpr expr bindings state)
    (hsubset : ∀ name, name ∈ exprBoundNames subexpr → name ∈ exprBoundNames expr) :
    bindingsExactlyMatchIRVarsOnExpr subexpr bindings state := by
  intro name hname
  exact hexact name (hsubset name hname)


def runtimeStateMatchesIR
    (fields : List Field)
    (runtime : SourceSemantics.RuntimeState)
    (state : IRState) : Prop :=
  state.storage = (fun s => Compiler.Proofs.IRGeneration.IRStorageWord.ofNat
    (SourceSemantics.encodeStorageAt fields runtime.world s.toNat)) ∧
  state.transientStorage = (fun slot => (runtime.world.transientStorage slot).val) ∧
  state.sender = runtime.world.sender.val ∧
  state.msgValue = runtime.world.msgValue.val ∧
  state.thisAddress = runtime.world.thisAddress.val ∧
  state.blockTimestamp = runtime.world.blockTimestamp.val ∧
  state.blockNumber = runtime.world.blockNumber.val ∧
  state.chainId = runtime.world.chainId.val ∧
  state.blobBaseFee = runtime.world.blobBaseFee.val ∧
  state.txOrigin = runtime.world.txOrigin.val ∧
  state.selector = runtime.selector ∧
  state.calldata = runtime.world.calldata ∧
  runtime.world.calldataSize.val = 4 + state.calldata.length * 32 ∧
  state.memory = (fun o => (runtime.world.memory o).val) ∧
  state.returnValue = none ∧
  state.events = SourceSemantics.encodeEvents runtime.world.events ∧
  state.codeSize = (fun addr => (runtime.world.codeSize addr).val) ∧
  state.returndata = runtime.world.returndata ∧
  runtime.world.byteMemory = state.byteMemory

/-- Runtime/IR alignment for constructor execution, whose calldata is not
selector-prefixed. This is the constructor-shaped analogue of
`runtimeStateMatchesIR` and is the reusable target for the deploy/initcode proof
path. -/
def constructorRuntimeStateMatchesIR
    (fields : List Field)
    (runtime : SourceSemantics.RuntimeState)
    (state : IRState) : Prop :=
  state.storage = (fun s => Compiler.Proofs.IRGeneration.IRStorageWord.ofNat
    (SourceSemantics.encodeStorageAt fields runtime.world s.toNat)) ∧
  state.transientStorage = (fun slot => (runtime.world.transientStorage slot).val) ∧
  state.sender = runtime.world.sender.val ∧
  state.msgValue = runtime.world.msgValue.val ∧
  state.thisAddress = runtime.world.thisAddress.val ∧
  state.blockTimestamp = runtime.world.blockTimestamp.val ∧
  state.blockNumber = runtime.world.blockNumber.val ∧
  state.chainId = runtime.world.chainId.val ∧
  state.blobBaseFee = runtime.world.blobBaseFee.val ∧
  state.txOrigin = runtime.world.txOrigin.val ∧
  state.selector = runtime.selector ∧
  state.calldata = runtime.world.calldata ∧
  runtime.world.calldataSize.val = state.calldata.length * 32 ∧
  state.memory = (fun o => (runtime.world.memory o).val) ∧
  state.returnValue = none ∧
  state.events = SourceSemantics.encodeEvents runtime.world.events ∧
  state.codeSize = (fun addr => (runtime.world.codeSize addr).val) ∧
  state.returndata = runtime.world.returndata ∧
  runtime.world.byteMemory = state.byteMemory

theorem runtimeStateMatchesIR_returndata
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (h : runtimeStateMatchesIR fields runtime state) :
    state.returndata = runtime.world.returndata := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h⟩ := h
  exact h.1

/-- Byte correspondence is an independent obligation: legacy word projections
alone do not constrain the physical carrier of an arbitrary input state. -/
theorem runtimeStateMatchesIR_byteMemory
    {fields : List Field} {runtime : SourceSemantics.RuntimeState} {state : IRState}
    (h : runtimeStateMatchesIR fields runtime state) :
    runtime.world.byteMemory = state.byteMemory := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hbytes⟩
  exact hbytes

def initialIRStateForTx
    (spec : CompilationModel)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState) : IRState :=
  { vars := []
    storage := fun s => Compiler.Proofs.IRGeneration.IRStorageWord.ofNat
      (SourceSemantics.encodeStorage spec initialWorld s.toNat)
    transientStorage := fun slot => (initialWorld.transientStorage slot).val
    memory := fun o => (initialWorld.memory o).val
    byteMemory := initialWorld.byteMemory
    calldata := tx.args
    returnValue := none
    sender := tx.sender
    msgValue := tx.msgValue
    thisAddress := tx.thisAddress
    blockTimestamp := tx.blockTimestamp
    blockNumber := tx.blockNumber
    chainId := tx.chainId
    blobBaseFee := tx.blobBaseFee
    txOrigin := tx.txOrigin
    selector := tx.functionSelector
    events := SourceSemantics.encodeEvents initialWorld.events
    codeSize := fun addr => (initialWorld.codeSize addr).val
    returndata := [] }

/-- EIP-211 makes the returndata buffer frame-local, so the IR frame enters
    empty: a stale buffer from the initial world's earlier execution must not
    reach `returndatasize()` reads in this transaction. This reset aligns with
    `SourceSemantics.returndata_withTransactionContext`, preserving the
    `runtimeStateMatchesIR` returndata conjunct at frame entry. -/
theorem initialIRStateForTx_returndata
    (spec : CompilationModel)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState) :
    (initialIRStateForTx spec tx initialWorld).returndata = [] := rfl

@[simp] theorem bindingsMatchIRVars_nil_initialIRStateForTx
    (spec : CompilationModel)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState) :
    bindingsMatchIRVars []
      (initialIRStateForTx spec tx initialWorld) := by
  intro name
  simp [initialIRStateForTx, IRState.getVar, SourceSemantics.lookupValue]

@[simp] theorem bindingsExactlyMatchIRVars_nil_initialIRStateForTx
    (spec : CompilationModel)
    (tx : IRTransaction)
  (initialWorld : Verity.ContractState) :
    bindingsExactlyMatchIRVars []
      (initialIRStateForTx spec tx initialWorld) := by
  intro name
  simp [lookupBinding?, initialIRStateForTx, IRState.getVar]

theorem evalIRExpr_ident_of_exact_bindings
    {bindings : List (String × Nat)}
    {state : IRState}
    (hexact : bindingsExactlyMatchIRVars bindings state)
    (name : String) :
    evalIRExpr state (YulExpr.ident name) = lookupBinding? bindings name := by
  simpa [evalIRExpr] using hexact name

theorem evalIRExpr_ident_of_scope_bindings
    {scope : List String}
    {bindings : List (String × Nat)}
    {state : IRState}
    (hexact : bindingsExactlyMatchIRVarsOnScope scope bindings state)
    {name : String}
    (hname : name ∈ scope) :
  evalIRExpr state (YulExpr.ident name) = lookupBinding? bindings name := by
  simpa [evalIRExpr] using hexact name hname

theorem evalIRExpr_caller_of_runtimeStateMatchesIR
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hmatch : runtimeStateMatchesIR fields runtime state) :
    evalIRExpr state (YulExpr.call "caller" []) =
      some (SourceSemantics.evalExpr fields runtime (.caller)) := by
  rcases hmatch with ⟨_, _, hsender, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  simp [evalIRExpr, evalIRCall, evalIRExprs, Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean, hsender]
  rfl

theorem evalIRExpr_contractAddress_of_runtimeStateMatchesIR
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hmatch : runtimeStateMatchesIR fields runtime state) :
    evalIRExpr state (YulExpr.call "address" []) =
      some (SourceSemantics.evalExpr fields runtime (.contractAddress)) := by
  rcases hmatch with ⟨_, _, _, _, hthisAddress, _, _, _, _, _, _, _, _, _, _, _⟩
  have hthisLt : runtime.world.thisAddress.val < Compiler.Constants.evmModulus := by
    have haddrLt : runtime.world.thisAddress.val < Verity.Core.Address.modulus :=
      Verity.Core.Address.val_lt_modulus runtime.world.thisAddress
    dsimp [Verity.Core.Address.modulus, Verity.Core.ADDRESS_MODULUS, Compiler.Constants.evmModulus] at haddrLt ⊢
    omega
  have hthisMod : runtime.world.thisAddress.val % Compiler.Constants.evmModulus =
      runtime.world.thisAddress.val := Nat.mod_eq_of_lt hthisLt
  simp [evalIRExpr, evalIRCall, evalIRExprs, Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean, hthisAddress, hthisMod]
  rfl

theorem evalIRExpr_msgValue_of_runtimeStateMatchesIR
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hmatch : runtimeStateMatchesIR fields runtime state) :
    evalIRExpr state (YulExpr.call "callvalue" []) =
      some (SourceSemantics.evalExpr fields runtime (.msgValue)) := by
  rcases hmatch with ⟨_, _, _, hmsgValue, _, _, _, _, _, _, _, _, _, _, _, _⟩
  have hmsgLt : runtime.world.msgValue.val < Compiler.Constants.evmModulus := by
    simpa [Compiler.Constants.evmModulus, Verity.Core.UINT256_MODULUS] using runtime.world.msgValue.isLt
  have hmsgMod : runtime.world.msgValue.val % Compiler.Constants.evmModulus =
      runtime.world.msgValue.val := Nat.mod_eq_of_lt hmsgLt
  simp [evalIRExpr, evalIRCall, evalIRExprs, Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean, hmsgValue, hmsgMod]
  rfl

theorem evalIRExpr_blockTimestamp_of_runtimeStateMatchesIR
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hmatch : runtimeStateMatchesIR fields runtime state) :
    evalIRExpr state (YulExpr.call "timestamp" []) =
      some (SourceSemantics.evalExpr fields runtime (.blockTimestamp)) := by
  rcases hmatch with ⟨_, _, _, _, _, hblockTimestamp, _, _, _, _, _, _, _, _, _, _⟩
  have htimeLt : runtime.world.blockTimestamp.val < Compiler.Constants.evmModulus := by
    simpa [Compiler.Constants.evmModulus, Verity.Core.UINT256_MODULUS] using runtime.world.blockTimestamp.isLt
  have htimeMod : runtime.world.blockTimestamp.val % Compiler.Constants.evmModulus =
      runtime.world.blockTimestamp.val := Nat.mod_eq_of_lt htimeLt
  simp [evalIRExpr, evalIRCall, evalIRExprs, Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean, hblockTimestamp, htimeMod]
  rfl

theorem evalIRExpr_blockNumber_of_runtimeStateMatchesIR
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hmatch : runtimeStateMatchesIR fields runtime state) :
    evalIRExpr state (YulExpr.call "number" []) =
      some (SourceSemantics.evalExpr fields runtime (.blockNumber)) := by
  rcases hmatch with ⟨_, _, _, _, _, _, hblockNumber, _, _, _, _, _, _, _, _, _⟩
  have hnumberLt : runtime.world.blockNumber.val < Compiler.Constants.evmModulus := by
    simpa [Compiler.Constants.evmModulus, Verity.Core.UINT256_MODULUS] using runtime.world.blockNumber.isLt
  have hnumberMod : runtime.world.blockNumber.val % Compiler.Constants.evmModulus =
      runtime.world.blockNumber.val := Nat.mod_eq_of_lt hnumberLt
  simp [evalIRExpr, evalIRCall, evalIRExprs, Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean, hblockNumber, hnumberMod]
  rfl

theorem evalIRExpr_chainid_of_runtimeStateMatchesIR
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hmatch : runtimeStateMatchesIR fields runtime state) :
    evalIRExpr state (YulExpr.call "chainid" []) =
      some (SourceSemantics.evalExpr fields runtime (.chainid)) := by
  rcases hmatch with ⟨_, _, _, _, _, _, _, hchainId, _, _, _, _, _, _, _, _⟩
  have hchainLt : runtime.world.chainId.val < Compiler.Constants.evmModulus := by
    simpa [Compiler.Constants.evmModulus, Verity.Core.UINT256_MODULUS] using runtime.world.chainId.isLt
  have hchainMod : runtime.world.chainId.val % Compiler.Constants.evmModulus =
      runtime.world.chainId.val := Nat.mod_eq_of_lt hchainLt
  simp [evalIRExpr, evalIRCall, evalIRExprs, Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean, hchainId, hchainMod]
  rfl

theorem evalIRExpr_blobbasefee_of_runtimeStateMatchesIR
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hmatch : runtimeStateMatchesIR fields runtime state) :
    evalIRExpr state (YulExpr.call "blobbasefee" []) =
      some (SourceSemantics.evalExpr fields runtime (.blobbasefee)) := by
  rcases hmatch with ⟨_, _, _, _, _, _, _, _, hblobBaseFee, _, _, _, _, _, _, _⟩
  have hblobLt : runtime.world.blobBaseFee.val < Compiler.Constants.evmModulus := by
    simpa [Compiler.Constants.evmModulus, Verity.Core.UINT256_MODULUS] using runtime.world.blobBaseFee.isLt
  have hblobMod : runtime.world.blobBaseFee.val % Compiler.Constants.evmModulus =
      runtime.world.blobBaseFee.val := Nat.mod_eq_of_lt hblobLt
  simp [evalIRExpr, evalIRCall, evalIRExprs, Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean, hblobBaseFee, hblobMod]
  rfl

theorem evalIRExpr_txOrigin_of_runtimeStateMatchesIR
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hmatch : runtimeStateMatchesIR fields runtime state) :
    evalIRExpr state (YulExpr.call "origin" []) =
      some (SourceSemantics.evalExpr fields runtime (.txOrigin)) := by
  rcases hmatch with ⟨_, _, _, _, _, _, _, _, _, htxOrigin, _, _, _, _, _, _⟩
  have htxLt : runtime.world.txOrigin.val < Compiler.Constants.evmModulus := by
    have haddrLt : runtime.world.txOrigin.val < Verity.Core.Address.modulus :=
      Verity.Core.Address.val_lt_modulus runtime.world.txOrigin
    dsimp [Verity.Core.Address.modulus, Verity.Core.ADDRESS_MODULUS, Compiler.Constants.evmModulus] at haddrLt ⊢
    omega
  have htxMod : runtime.world.txOrigin.val % Compiler.Constants.evmModulus =
      runtime.world.txOrigin.val := Nat.mod_eq_of_lt htxLt
  simp [evalIRExpr, evalIRCall, evalIRExprs, Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean, htxOrigin, htxMod]
  rfl

theorem eval_compileExpr_caller
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hmatch : runtimeStateMatchesIR fields runtime state) :
    evalIRExpr state (CompilationModel.compileExpr fields .calldata .caller |>.toOption.getD (YulExpr.lit 0)) =
      some (SourceSemantics.evalExpr fields runtime (.caller)) := by
  simp [CompilationModel.compileExpr, CompilationModel.compileExprWithInternals]
  exact evalIRExpr_caller_of_runtimeStateMatchesIR hmatch

theorem eval_compileExpr_contractAddress
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hmatch : runtimeStateMatchesIR fields runtime state) :
    evalIRExpr state (CompilationModel.compileExpr fields .calldata .contractAddress |>.toOption.getD (YulExpr.lit 0)) =
      some (SourceSemantics.evalExpr fields runtime (.contractAddress)) := by
  simp [CompilationModel.compileExpr, CompilationModel.compileExprWithInternals]
  exact evalIRExpr_contractAddress_of_runtimeStateMatchesIR hmatch

theorem eval_compileExpr_msgValue
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hmatch : runtimeStateMatchesIR fields runtime state) :
    evalIRExpr state (CompilationModel.compileExpr fields .calldata .msgValue |>.toOption.getD (YulExpr.lit 0)) =
      some (SourceSemantics.evalExpr fields runtime (.msgValue)) := by
  simp [CompilationModel.compileExpr, CompilationModel.compileExprWithInternals]
  exact evalIRExpr_msgValue_of_runtimeStateMatchesIR hmatch

theorem eval_compileExpr_blockTimestamp
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hmatch : runtimeStateMatchesIR fields runtime state) :
    evalIRExpr state (CompilationModel.compileExpr fields .calldata .blockTimestamp |>.toOption.getD (YulExpr.lit 0)) =
      some (SourceSemantics.evalExpr fields runtime (.blockTimestamp)) := by
  simp [CompilationModel.compileExpr, CompilationModel.compileExprWithInternals]
  exact evalIRExpr_blockTimestamp_of_runtimeStateMatchesIR hmatch

theorem eval_compileExpr_blockNumber
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hmatch : runtimeStateMatchesIR fields runtime state) :
    evalIRExpr state (CompilationModel.compileExpr fields .calldata .blockNumber |>.toOption.getD (YulExpr.lit 0)) =
      some (SourceSemantics.evalExpr fields runtime (.blockNumber)) := by
  simp [CompilationModel.compileExpr, CompilationModel.compileExprWithInternals]
  exact evalIRExpr_blockNumber_of_runtimeStateMatchesIR hmatch

theorem eval_compileExpr_chainid
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hmatch : runtimeStateMatchesIR fields runtime state) :
    evalIRExpr state (CompilationModel.compileExpr fields .calldata .chainid |>.toOption.getD (YulExpr.lit 0)) =
      some (SourceSemantics.evalExpr fields runtime (.chainid)) := by
  simp [CompilationModel.compileExpr, CompilationModel.compileExprWithInternals]
  exact evalIRExpr_chainid_of_runtimeStateMatchesIR hmatch

theorem eval_compileExpr_blobbasefee
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hmatch : runtimeStateMatchesIR fields runtime state) :
    evalIRExpr state (CompilationModel.compileExpr fields .calldata .blobbasefee |>.toOption.getD (YulExpr.lit 0)) =
      some (SourceSemantics.evalExpr fields runtime (.blobbasefee)) := by
  simp [CompilationModel.compileExpr, CompilationModel.compileExprWithInternals]
  exact evalIRExpr_blobbasefee_of_runtimeStateMatchesIR hmatch

theorem eval_compileExpr_txOrigin
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hmatch : runtimeStateMatchesIR fields runtime state) :
    evalIRExpr state (CompilationModel.compileExpr fields .calldata .txOrigin |>.toOption.getD (YulExpr.lit 0)) =
      some (SourceSemantics.evalExpr fields runtime (.txOrigin)) := by
  simp [CompilationModel.compileExpr, CompilationModel.compileExprWithInternals]
  exact evalIRExpr_txOrigin_of_runtimeStateMatchesIR hmatch

theorem evalIRExpr_calldatasize_of_runtimeStateMatchesIR
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hmatch : runtimeStateMatchesIR fields runtime state) :
    evalIRExpr state (YulExpr.call "calldatasize" []) =
      some (SourceSemantics.evalExpr fields runtime (.calldatasize)) := by
  rcases hmatch with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hcalldataSize, _, _, _⟩
  have heval : SourceSemantics.evalExpr fields runtime (.calldatasize) =
    some runtime.world.calldataSize.val := rfl
  have hcalldataSizeMod :
      (4 + state.calldata.length * 32) % Compiler.Constants.evmModulus =
        runtime.world.calldataSize.val := by
    rw [← hcalldataSize]
    exact Nat.mod_eq_of_lt runtime.world.calldataSize.isLt
  rw [heval]
  simp [evalIRExpr, evalIRCall, evalIRExprs,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean, hcalldataSizeMod]

theorem eval_compileExpr_calldatasize
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hmatch : runtimeStateMatchesIR fields runtime state) :
    evalIRExpr state (CompilationModel.compileExpr fields .calldata .calldatasize |>.toOption.getD (YulExpr.lit 0)) =
      some (SourceSemantics.evalExpr fields runtime (.calldatasize)) := by
  simp [CompilationModel.compileExpr, CompilationModel.compileExprWithInternals]
  exact evalIRExpr_calldatasize_of_runtimeStateMatchesIR hmatch

theorem evalIRExpr_returndataSize_of_runtimeStateMatchesIR
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hmatch : runtimeStateMatchesIR fields runtime state) :
    evalIRExpr state (YulExpr.call "returndatasize" []) =
      some (SourceSemantics.evalExpr fields runtime (.returndataSize)) := by
  have hreturndata : state.returndata = runtime.world.returndata :=
    runtimeStateMatchesIR_returndata hmatch
  have heval : SourceSemantics.evalExpr fields runtime (.returndataSize) =
      some (32 * runtime.world.returndata.length % Compiler.Constants.evmModulus) := rfl
  rw [heval]
  simp [evalIRExpr, evalIRCall, evalIRExprs, hreturndata]

theorem eval_compileExpr_returndataSize
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hmatch : runtimeStateMatchesIR fields runtime state) :
    evalIRExpr state (CompilationModel.compileExpr fields .calldata .returndataSize |>.toOption.getD (YulExpr.lit 0)) =
      some (SourceSemantics.evalExpr fields runtime (.returndataSize)) := by
  simp [CompilationModel.compileExpr, CompilationModel.compileExprWithInternals]
  exact evalIRExpr_returndataSize_of_runtimeStateMatchesIR hmatch

theorem eval_compileExpr_literal
    (fields : List Field)
    (runtime : SourceSemantics.RuntimeState)
    (state : IRState)
    (value : Nat) :
    evalIRExpr state (YulExpr.lit (value % CompilationModel.uint256Modulus)) =
      some (SourceSemantics.evalExpr fields runtime (.literal value)) := by
  simp [evalIRExpr]
  change some (value % CompilationModel.uint256Modulus) = some (SourceSemantics.wordNormalize value)
  rw [ParamLoading.wordNormalize_eq_mod]
  simp [CompilationModel.uint256Modulus, Compiler.Constants.evmModulus]

@[simp] theorem boolWord_eq_if (p : Prop) [Decidable p] :
    SourceSemantics.boolWord (decide p) = (if p then 1 else 0) := by
  by_cases hp : p <;> simp [SourceSemantics.boolWord, hp]

theorem evalIRExpr_iszero_of_lt
    {state : IRState}
    {expr : YulExpr}
    {value : Nat}
    (heval : evalIRExpr state expr = some value)
    (hvalueLt : value < Compiler.Constants.evmModulus) :
    evalIRExpr state (YulExpr.call "iszero" [expr]) =
      some (SourceSemantics.boolWord (value = 0)) := by
  by_cases hzero : value = 0
  · subst hzero
    simp [evalIRExpr, evalIRCall, evalIRExprs, heval,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean,
      SourceSemantics.boolWord]
  · have hmod : value % Compiler.Constants.evmModulus = value := Nat.mod_eq_of_lt hvalueLt
    simp [evalIRExpr, evalIRCall, evalIRExprs, heval, hmod, hzero,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean,
      SourceSemantics.boolWord]

theorem evalIRExpr_yulToBool_of_lt
    {state : IRState}
    {expr : YulExpr}
    {value : Nat}
    (heval : evalIRExpr state expr = some value)
    (hvalueLt : value < Compiler.Constants.evmModulus) :
    evalIRExpr state (CompilationModel.yulToBool expr) =
      some (SourceSemantics.boolWord (value ≠ 0)) := by
  by_cases hzero : value = 0
  · subst hzero
    simp [CompilationModel.yulToBool, evalIRExpr, evalIRCall, evalIRExprs, heval,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean,
      SourceSemantics.boolWord]
  · have hmod : value % Compiler.Constants.evmModulus = value := Nat.mod_eq_of_lt hvalueLt
    simp [CompilationModel.yulToBool, evalIRExpr, evalIRCall, evalIRExprs, heval, hmod, hzero,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean,
      SourceSemantics.boolWord]

theorem evalIRExpr_add_of_eval
    {state : IRState}
    {lhs rhs : YulExpr}
    {a b : Nat}
    (hlhs : evalIRExpr state lhs = some a)
    (hrhs : evalIRExpr state rhs = some b) :
    evalIRExpr state (YulExpr.call "add" [lhs, rhs]) =
      some ((a + b) % Compiler.Constants.evmModulus) := by
  simp [evalIRExpr, evalIRCall, evalIRExprs, hlhs, hrhs,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean]

theorem evalIRExpr_sub_of_eval
    {state : IRState}
    {lhs rhs : YulExpr}
    {a b : Nat}
    (hlhs : evalIRExpr state lhs = some a)
    (hrhs : evalIRExpr state rhs = some b) :
    evalIRExpr state (YulExpr.call "sub" [lhs, rhs]) =
      some ((Compiler.Constants.evmModulus + (a % Compiler.Constants.evmModulus) -
        (b % Compiler.Constants.evmModulus)) % Compiler.Constants.evmModulus) := by
  simp [evalIRExpr, evalIRCall, evalIRExprs, hlhs, hrhs,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean]

theorem evalIRExpr_mul_of_eval
    {state : IRState}
    {lhs rhs : YulExpr}
    {a b : Nat}
    (hlhs : evalIRExpr state lhs = some a)
    (hrhs : evalIRExpr state rhs = some b) :
    evalIRExpr state (YulExpr.call "mul" [lhs, rhs]) =
      some ((a * b) % Compiler.Constants.evmModulus) := by
  simp [evalIRExpr, evalIRCall, evalIRExprs, hlhs, hrhs,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean]

theorem evalIRExpr_exp_of_eval
    {state : IRState}
    {lhs rhs : YulExpr}
    {a b : Nat}
    (hlhs : evalIRExpr state lhs = some a)
    (hrhs : evalIRExpr state rhs = some b) :
    evalIRExpr state (YulExpr.call "exp" [lhs, rhs]) =
      some ((a % Compiler.Constants.evmModulus) ^ (b % Compiler.Constants.evmModulus)
        % Compiler.Constants.evmModulus) := by
  simp [evalIRExpr, evalIRCall, evalIRExprs, hlhs, hrhs,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean]

private theorem uint256_pow_val (a b : Nat) :
    (Verity.Core.Uint256.pow (Verity.Core.Uint256.ofNat a) (Verity.Core.Uint256.ofNat b)).val =
      (a % Compiler.Constants.evmModulus) ^ (b % Compiler.Constants.evmModulus)
        % Compiler.Constants.evmModulus := by
  simp [Verity.Core.Uint256.pow, Verity.Core.Uint256.ofNat, Compiler.Constants.evmModulus]

theorem evalIRExpr_div_of_eval
    {state : IRState}
    {lhs rhs : YulExpr}
    {a b : Nat}
    (hlhs : evalIRExpr state lhs = some a)
    (hrhs : evalIRExpr state rhs = some b) :
    evalIRExpr state (YulExpr.call "div" [lhs, rhs]) =
      some (if b % Compiler.Constants.evmModulus = 0 then 0 else
        (a % Compiler.Constants.evmModulus) / (b % Compiler.Constants.evmModulus)) := by
  by_cases hzero : b % Compiler.Constants.evmModulus = 0
  · simp [evalIRExpr, evalIRCall, evalIRExprs, hlhs, hrhs, hzero,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean]
  · simp [evalIRExpr, evalIRCall, evalIRExprs, hlhs, hrhs, hzero,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean]

theorem evalIRExpr_mod_of_eval
    {state : IRState}
    {lhs rhs : YulExpr}
    {a b : Nat}
    (hlhs : evalIRExpr state lhs = some a)
    (hrhs : evalIRExpr state rhs = some b) :
    evalIRExpr state (YulExpr.call "mod" [lhs, rhs]) =
      some (if b % Compiler.Constants.evmModulus = 0 then 0 else
        (a % Compiler.Constants.evmModulus) % (b % Compiler.Constants.evmModulus)) := by
  by_cases hzero : b % Compiler.Constants.evmModulus = 0
  · simp [evalIRExpr, evalIRCall, evalIRExprs, hlhs, hrhs, hzero,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean]
  · simp [evalIRExpr, evalIRCall, evalIRExprs, hlhs, hrhs, hzero,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean]

theorem evalIRExpr_eq_of_eval
    {state : IRState}
    {lhs rhs : YulExpr}
    {a b : Nat}
    (hlhs : evalIRExpr state lhs = some a)
    (hrhs : evalIRExpr state rhs = some b) :
    evalIRExpr state (YulExpr.call "eq" [lhs, rhs]) =
      some (SourceSemantics.boolWord (a % Compiler.Constants.evmModulus =
        b % Compiler.Constants.evmModulus)) := by
  by_cases heq : a % Compiler.Constants.evmModulus = b % Compiler.Constants.evmModulus
  · simp [evalIRExpr, evalIRCall, evalIRExprs, hlhs, hrhs, heq,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean,
      SourceSemantics.boolWord]
  · simp [evalIRExpr, evalIRCall, evalIRExprs, hlhs, hrhs, heq,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean,
      SourceSemantics.boolWord]

theorem evalIRExpr_lt_of_eval
    {state : IRState}
    {lhs rhs : YulExpr}
    {a b : Nat}
    (hlhs : evalIRExpr state lhs = some a)
    (hrhs : evalIRExpr state rhs = some b) :
    evalIRExpr state (YulExpr.call "lt" [lhs, rhs]) =
      some (SourceSemantics.boolWord (a % Compiler.Constants.evmModulus <
        b % Compiler.Constants.evmModulus)) := by
  by_cases hlt : a % Compiler.Constants.evmModulus < b % Compiler.Constants.evmModulus
  · simp [evalIRExpr, evalIRCall, evalIRExprs, hlhs, hrhs, hlt,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean,
      SourceSemantics.boolWord]
  · simp [evalIRExpr, evalIRCall, evalIRExprs, hlhs, hrhs, hlt,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean,
      SourceSemantics.boolWord]

theorem evalIRExpr_gt_of_eval
    {state : IRState}
    {lhs rhs : YulExpr}
    {a b : Nat}
    (hlhs : evalIRExpr state lhs = some a)
    (hrhs : evalIRExpr state rhs = some b) :
    evalIRExpr state (YulExpr.call "gt" [lhs, rhs]) =
      some (SourceSemantics.boolWord (b % Compiler.Constants.evmModulus <
        a % Compiler.Constants.evmModulus)) := by
  by_cases hgt : b % Compiler.Constants.evmModulus < a % Compiler.Constants.evmModulus
  · have hcmp : ¬ a % Compiler.Constants.evmModulus ≤ b % Compiler.Constants.evmModulus := by
      exact Nat.not_le_of_gt hgt
    simp [evalIRExpr, evalIRCall, evalIRExprs, hlhs, hrhs, hgt,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean,
      SourceSemantics.boolWord]
  · have hcmp : a % Compiler.Constants.evmModulus ≤ b % Compiler.Constants.evmModulus := by
      exact Nat.le_of_not_gt hgt
    simp [evalIRExpr, evalIRCall, evalIRExprs, hlhs, hrhs, hgt,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean,
      SourceSemantics.boolWord]

theorem evalIRExpr_slt_of_eval
    {state : IRState}
    {lhs rhs : YulExpr}
    {a b : Nat}
    (hlhs : evalIRExpr state lhs = some a)
    (hrhs : evalIRExpr state rhs = some b) :
    evalIRExpr state (YulExpr.call "slt" [lhs, rhs]) =
      some (SourceSemantics.boolWord (decide (
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat (a % Compiler.Constants.evmModulus)) : Int) <
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat (b % Compiler.Constants.evmModulus)) : Int)))) := by
  by_cases hslt : (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat (a % Compiler.Constants.evmModulus)) : Int) <
      (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat (b % Compiler.Constants.evmModulus)) : Int)
  · simp [evalIRExpr, evalIRCall, evalIRExprs, hlhs, hrhs, hslt,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean,
      Verity.Core.Int256.toInt,
      SourceSemantics.boolWord]
  · simp [evalIRExpr, evalIRCall, evalIRExprs, hlhs, hrhs, hslt,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean,
      Verity.Core.Int256.toInt,
      SourceSemantics.boolWord]

theorem evalIRExpr_sgt_of_eval
    {state : IRState}
    {lhs rhs : YulExpr}
    {a b : Nat}
    (hlhs : evalIRExpr state lhs = some a)
    (hrhs : evalIRExpr state rhs = some b) :
    evalIRExpr state (YulExpr.call "sgt" [lhs, rhs]) =
      some (SourceSemantics.boolWord (decide (
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat (b % Compiler.Constants.evmModulus)) : Int) <
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat (a % Compiler.Constants.evmModulus)) : Int)))) := by
  by_cases hsgt : (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat (b % Compiler.Constants.evmModulus)) : Int) <
      (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat (a % Compiler.Constants.evmModulus)) : Int)
  · simp [evalIRExpr, evalIRCall, evalIRExprs, hlhs, hrhs, hsgt,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean,
      Verity.Core.Int256.toInt,
      SourceSemantics.boolWord]
  · simp [evalIRExpr, evalIRCall, evalIRExprs, hlhs, hrhs, hsgt,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean,
      Verity.Core.Int256.toInt,
      SourceSemantics.boolWord]

theorem evalIRExpr_sdiv_of_eval
    {state : IRState}
    {lhs rhs : YulExpr}
    {a b : Nat}
    (hlhs : evalIRExpr state lhs = some a)
    (hrhs : evalIRExpr state rhs = some b) :
    evalIRExpr state (YulExpr.call "sdiv" [lhs, rhs]) =
      some (Verity.Core.Int256.div
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat (a % Compiler.Constants.evmModulus)))
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat (b % Compiler.Constants.evmModulus)))).toUint256.val := by
  simp [evalIRExpr, evalIRCall, evalIRExprs, hlhs, hrhs,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean,
    Verity.Core.Int256.toUint256]

theorem evalIRExpr_smod_of_eval
    {state : IRState}
    {lhs rhs : YulExpr}
    {a b : Nat}
    (hlhs : evalIRExpr state lhs = some a)
    (hrhs : evalIRExpr state rhs = some b) :
    evalIRExpr state (YulExpr.call "smod" [lhs, rhs]) =
      some (Verity.Core.Int256.mod
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat (a % Compiler.Constants.evmModulus)))
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat (b % Compiler.Constants.evmModulus)))).toUint256.val := by
  simp [evalIRExpr, evalIRCall, evalIRExprs, hlhs, hrhs,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean,
    Verity.Core.Int256.toUint256]

theorem evalIRExpr_sar_of_eval
    {state : IRState}
    {lhs rhs : YulExpr}
    {a b : Nat}
    (hlhs : evalIRExpr state lhs = some a)
    (hrhs : evalIRExpr state rhs = some b) :
    evalIRExpr state (YulExpr.call "sar" [lhs, rhs]) =
      some (Verity.Core.Int256.sar
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat (a % Compiler.Constants.evmModulus)))
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat (b % Compiler.Constants.evmModulus)))).toUint256.val := by
  simp [evalIRExpr, evalIRCall, evalIRExprs, hlhs, hrhs,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean,
    Verity.Core.Int256.toUint256]

theorem evalIRExpr_byte_of_eval
    {state : IRState}
    {index value : YulExpr}
    {indexVal valueVal : Nat}
    (hindex : evalIRExpr state index = some indexVal)
    (hvalue : evalIRExpr state value = some valueVal) :
    evalIRExpr state (YulExpr.call "byte" [index, value]) =
      some (Verity.Core.Uint256.byte
        (Verity.Core.Uint256.ofNat (indexVal % Compiler.Constants.evmModulus))
        (Verity.Core.Uint256.ofNat (valueVal % Compiler.Constants.evmModulus))).val := by
  simp [evalIRExpr, evalIRCall, evalIRExprs, hindex, hvalue,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean]

theorem evalIRExpr_signextend_of_eval
    {state : IRState}
    {lhs rhs : YulExpr}
    {a b : Nat}
    (hlhs : evalIRExpr state lhs = some a)
    (hrhs : evalIRExpr state rhs = some b) :
    evalIRExpr state (YulExpr.call "signextend" [lhs, rhs]) =
      some (Verity.Core.Uint256.signextend
        (Verity.Core.Uint256.ofNat (a % Compiler.Constants.evmModulus))
        (Verity.Core.Uint256.ofNat (b % Compiler.Constants.evmModulus))).val := by
  simp [evalIRExpr, evalIRCall, evalIRExprs, hlhs, hrhs,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean,
    Verity.Core.Uint256.signextend]

theorem evalIRExpr_and_of_eval
    {state : IRState}
    {lhs rhs : YulExpr}
    {a b : Nat}
    (hlhs : evalIRExpr state lhs = some a)
    (hrhs : evalIRExpr state rhs = some b) :
    evalIRExpr state (YulExpr.call "and" [lhs, rhs]) =
      some ((a % Compiler.Constants.evmModulus) &&& (b % Compiler.Constants.evmModulus)) := by
  simp [evalIRExpr, evalIRCall, evalIRExprs, hlhs, hrhs,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean]

theorem evalIRExpr_or_of_eval
    {state : IRState}
    {lhs rhs : YulExpr}
    {a b : Nat}
    (hlhs : evalIRExpr state lhs = some a)
    (hrhs : evalIRExpr state rhs = some b) :
    evalIRExpr state (YulExpr.call "or" [lhs, rhs]) =
      some ((a % Compiler.Constants.evmModulus) ||| (b % Compiler.Constants.evmModulus)) := by
  simp [evalIRExpr, evalIRCall, evalIRExprs, hlhs, hrhs,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean]

theorem evalIRExpr_xor_of_eval
    {state : IRState}
    {lhs rhs : YulExpr}
    {a b : Nat}
    (hlhs : evalIRExpr state lhs = some a)
    (hrhs : evalIRExpr state rhs = some b) :
    evalIRExpr state (YulExpr.call "xor" [lhs, rhs]) =
      some (Nat.xor (a % Compiler.Constants.evmModulus) (b % Compiler.Constants.evmModulus)) := by
  simp [evalIRExpr, evalIRCall, evalIRExprs, hlhs, hrhs,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean]

theorem evalIRExpr_not_of_eval
    {state : IRState}
    {expr : YulExpr}
    {value : Nat}
    (heval : evalIRExpr state expr = some value) :
    evalIRExpr state (YulExpr.call "not" [expr]) =
      some (Nat.xor (value % Compiler.Constants.evmModulus)
        (Compiler.Constants.evmModulus - 1)) := by
  simp [evalIRExpr, evalIRCall, evalIRExprs, heval,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean]

theorem evalIRExpr_shl_of_eval
    {state : IRState}
    {shiftExpr valueExpr : YulExpr}
    {shift value : Nat}
    (hshift : evalIRExpr state shiftExpr = some shift)
    (hvalue : evalIRExpr state valueExpr = some value) :
    evalIRExpr state (YulExpr.call "shl" [shiftExpr, valueExpr]) =
      some (if shift % Compiler.Constants.evmModulus < 256 then
        ((value % Compiler.Constants.evmModulus) *
          2 ^ (shift % Compiler.Constants.evmModulus)) % Compiler.Constants.evmModulus
      else
        0) := by
  by_cases hlt : shift % Compiler.Constants.evmModulus < 256
  · simp [evalIRExpr, evalIRCall, evalIRExprs, hshift, hvalue, hlt,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean]
  · simp [evalIRExpr, evalIRCall, evalIRExprs, hshift, hvalue, hlt,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean]

theorem evalIRExpr_shr_of_eval
    {state : IRState}
    {shiftExpr valueExpr : YulExpr}
    {shift value : Nat}
    (hshift : evalIRExpr state shiftExpr = some shift)
    (hvalue : evalIRExpr state valueExpr = some value) :
    evalIRExpr state (YulExpr.call "shr" [shiftExpr, valueExpr]) =
      some (if shift % Compiler.Constants.evmModulus < 256 then
        (value % Compiler.Constants.evmModulus) /
          2 ^ (shift % Compiler.Constants.evmModulus)
      else
        0) := by
  by_cases hlt : shift % Compiler.Constants.evmModulus < 256
  · simp [evalIRExpr, evalIRCall, evalIRExprs, hshift, hvalue, hlt,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean]
  · simp [evalIRExpr, evalIRCall, evalIRExprs, hshift, hvalue, hlt,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean]

private theorem findEntry_filter_ne_eq_findEntry
    (entries : List (String × Nat))
    (blockedName queryName : String)
    (hNe : queryName ≠ blockedName) :
    List.find? (fun entry => entry.1 == queryName)
        (entries.filter (fun entry => entry.1 != blockedName)) =
      List.find? (fun entry => entry.1 == queryName) entries := by
  induction entries with
  | nil =>
      simp
  | cons entry rest ih =>
      by_cases hBlocked : entry.1 = blockedName
      · subst hBlocked
        have hHeadNe : entry.1 ≠ queryName := by
          intro hHeadEq
          apply hNe
          simp [hHeadEq]
        simp [hHeadNe, ih]
      · by_cases hQuery : entry.1 = queryName
        · subst hQuery
          simp [hBlocked]
        · simp [hBlocked, hQuery, ih]

@[simp] theorem getVar_setVar_eq
    (state : IRState)
    (name : String)
    (value : Nat) :
    (state.setVar name value).getVar name = some value := by
  simp [IRState.getVar, IRState.setVar]

theorem getVar_setVar_ne
    (state : IRState)
    (boundName queryName : String)
    (value : Nat)
    (hNe : queryName ≠ boundName) :
    (state.setVar boundName value).getVar queryName = state.getVar queryName := by
  have hNe' : boundName ≠ queryName := by
    intro hEq
    apply hNe
    simp [hEq]
  calc
    (state.setVar boundName value).getVar queryName
        =
          Option.map Prod.snd
            (List.find? (fun entry => entry.1 == queryName)
              ((boundName, value) :: List.filter (fun entry => entry.1 != boundName) state.vars)) := by
                rfl
    _ = Option.map Prod.snd
          (List.find? (fun entry => entry.1 == queryName)
            (List.filter (fun entry => entry.1 != boundName) state.vars)) := by
              simp [hNe']
    _ = Option.map Prod.snd
          (List.find? (fun entry => entry.1 == queryName) state.vars) := by
              rw [findEntry_filter_ne_eq_findEntry state.vars boundName queryName hNe]
    _ = state.getVar queryName := by
          rfl

@[simp] theorem lookupValue_bindValue_eq
    (bindings : List (String × Nat))
    (name : String)
    (value : Nat) :
    SourceSemantics.lookupValue
      (SourceSemantics.bindValue bindings name value)
      name = value := by
  simp [SourceSemantics.lookupValue, SourceSemantics.bindValue]

theorem lookupValue_bindValue_ne
    (bindings : List (String × Nat))
    (boundName queryName : String)
    (value : Nat)
    (hNe : queryName ≠ boundName) :
    SourceSemantics.lookupValue
      (SourceSemantics.bindValue bindings boundName value)
      queryName =
    SourceSemantics.lookupValue bindings queryName := by
  have hNe' : boundName ≠ queryName := by
    intro hEq
    apply hNe
    simp [hEq]
  calc
    SourceSemantics.lookupValue
        (SourceSemantics.bindValue bindings boundName value)
        queryName
        =
          (Option.map Prod.snd
            (List.find? (fun entry => entry.1 == queryName)
              ((boundName, value) :: List.filter (fun entry => entry.1 != boundName) bindings))).getD 0 := by
                rfl
    _ = (Option.map Prod.snd
          (List.find? (fun entry => entry.1 == queryName)
            (List.filter (fun entry => entry.1 != boundName) bindings))).getD 0 := by
              simp [hNe']
    _ = (Option.map Prod.snd
          (List.find? (fun entry => entry.1 == queryName) bindings)).getD 0 := by
              rw [findEntry_filter_ne_eq_findEntry bindings boundName queryName hNe]
    _ = SourceSemantics.lookupValue bindings queryName := by
          rfl

@[simp] theorem bindingsBounded_nil :
    bindingsBounded [] := by
  intro name
  simp [SourceSemantics.lookupValue, Compiler.Constants.evmModulus]

@[simp] theorem wordNormalize_lt_evmModulus (value : Nat) :
    SourceSemantics.wordNormalize value < Compiler.Constants.evmModulus := by
  rw [ParamLoading.wordNormalize_eq_mod]
  exact Nat.mod_lt _ (by simp [Compiler.Constants.evmModulus])

private theorem maskedWordNormalize_lt_evmModulus (word mask : Nat) :
    SourceSemantics.wordNormalize word &&& mask < Compiler.Constants.evmModulus := by
  have hle : SourceSemantics.wordNormalize word &&& mask ≤ SourceSemantics.wordNormalize word := Nat.and_le_left
  exact Nat.lt_of_le_of_lt hle (wordNormalize_lt_evmModulus word)

private theorem decodeSupportedParamWord_passthrough_lt_evmModulus
    {ty : ParamType}
    {word value : Nat}
    (hpassthrough : ty = .uint256 ∨ ty = .int256 ∨ ty = .bytes32)
    (hdecode : SourceSemantics.decodeSupportedParamWord ty word = some value) :
    value < Compiler.Constants.evmModulus := by
  rcases hpassthrough with rfl | rfl | rfl
  · have hvalue : value = SourceSemantics.wordNormalize word := by
      simpa [SourceSemantics.decodeSupportedParamWord] using hdecode.symm
    cases hvalue
    exact wordNormalize_lt_evmModulus word
  · have hvalue : value = SourceSemantics.wordNormalize word := by
      simpa [SourceSemantics.decodeSupportedParamWord] using hdecode.symm
    cases hvalue
    exact wordNormalize_lt_evmModulus word
  · have hvalue : value = SourceSemantics.wordNormalize word := by
      simpa [SourceSemantics.decodeSupportedParamWord] using hdecode.symm
    cases hvalue
    exact wordNormalize_lt_evmModulus word

private theorem decodeSupportedParamWord_masked_lt_evmModulus
    {ty : ParamType}
    {word value : Nat}
    (hmasked : ty = .uint8 ∨ ty = .uint16 ∨ ty = .address)
    (hdecode : SourceSemantics.decodeSupportedParamWord ty word = some value) :
    value < Compiler.Constants.evmModulus := by
  rcases hmasked with rfl | rfl | rfl
  · have hvalue : value = SourceSemantics.wordNormalize word &&& (SourceSemantics.uint8Modulus - 1) := by
      simpa [SourceSemantics.decodeSupportedParamWord] using hdecode.symm
    cases hvalue
    exact maskedWordNormalize_lt_evmModulus word (SourceSemantics.uint8Modulus - 1)
  · have hvalue : value = SourceSemantics.wordNormalize word &&& (2^16 - 1) := by
      simpa [SourceSemantics.decodeSupportedParamWord] using hdecode.symm
    cases hvalue
    exact maskedWordNormalize_lt_evmModulus word (2^16 - 1)
  · have hvalue : value = SourceSemantics.wordNormalize word &&& Compiler.Constants.addressMask := by
      simpa [SourceSemantics.decodeSupportedParamWord] using hdecode.symm
    cases hvalue
    exact maskedWordNormalize_lt_evmModulus word Compiler.Constants.addressMask

private theorem decodeSupportedParamWord_bool_lt_evmModulus
    {word value : Nat}
    (hdecode : SourceSemantics.decodeSupportedParamWord .bool word = some value) :
    value < Compiler.Constants.evmModulus := by
  simp only [SourceSemantics.decodeSupportedParamWord, SourceSemantics.wordNormalize,
    Option.some.injEq] at hdecode
  subst value
  split <;> simp [Compiler.Constants.evmModulus]

theorem decodeSupportedParamWord_lt_evmModulus
    {ty : ParamType}
    {word value : Nat}
    (hdecode : SourceSemantics.decodeSupportedParamWord ty word = some value) :
    value < Compiler.Constants.evmModulus := by
  cases ty with
  | uint256 =>
      exact decodeSupportedParamWord_passthrough_lt_evmModulus (hpassthrough := .inl rfl) hdecode
  | int256 =>
      exact decodeSupportedParamWord_passthrough_lt_evmModulus (hpassthrough := .inr (.inl rfl)) hdecode
  | uint8 =>
      exact decodeSupportedParamWord_masked_lt_evmModulus (hmasked := .inl rfl) hdecode
  | uint16 =>
      exact decodeSupportedParamWord_masked_lt_evmModulus (hmasked := .inr (.inl rfl)) hdecode
  | uintN _ | intN _ | bytesN _ =>
      simp only [SourceSemantics.decodeSupportedParamWord, SourceSemantics.wordNormalize,
        Option.some.injEq] at hdecode
      subst value
      first
      | exact Verity.Core.Uint256.isLt _
      | rw [show Compiler.Constants.evmModulus = 2 ^ 256 by rfl, Nat.land_comm]
        exact Nat.and_lt_two_pow _ (Verity.Core.Uint256.ofNat word).isLt
  | address =>
      exact decodeSupportedParamWord_masked_lt_evmModulus (hmasked := .inr (.inr rfl)) hdecode
  | bool =>
      exact decodeSupportedParamWord_bool_lt_evmModulus hdecode
  | bytes32 =>
      exact decodeSupportedParamWord_passthrough_lt_evmModulus (hpassthrough := .inr (.inr rfl)) hdecode
  | string =>
      simp [SourceSemantics.decodeSupportedParamWord] at hdecode
  | tuple _ =>
      simp [SourceSemantics.decodeSupportedParamWord] at hdecode
  | array _ =>
      simp [SourceSemantics.decodeSupportedParamWord] at hdecode
  | fixedArray _ _ =>
      simp [SourceSemantics.decodeSupportedParamWord] at hdecode
  | adt _ _ =>
      simp [SourceSemantics.decodeSupportedParamWord] at hdecode
  | newtypeOf _ _ =>
      simp [SourceSemantics.decodeSupportedParamWord] at hdecode
  | bytes =>
      simp [SourceSemantics.decodeSupportedParamWord] at hdecode

theorem bindingsBounded_bindValue
    {bindings : List (String × Nat)}
    (hbounded : bindingsBounded bindings)
    (boundName : String)
    (value : Nat)
    (hvalueLt : value < Compiler.Constants.evmModulus) :
    bindingsBounded (SourceSemantics.bindValue bindings boundName value) := by
  intro queryName
  by_cases hEq : queryName = boundName
  · subst hEq
    simp [lookupValue_bindValue_eq, hvalueLt]
  · rw [lookupValue_bindValue_ne bindings boundName queryName value hEq]
    exact hbounded queryName

private theorem bindingsBounded_cons
    {bindings : List (String × Nat)}
    (boundName : String)
    (value : Nat)
    (hvalueLt : value < Compiler.Constants.evmModulus)
    (hbounded : bindingsBounded bindings) :
    bindingsBounded ((boundName, value) :: bindings) := by
  intro queryName
  by_cases hEq : queryName = boundName
  · subst hEq
    simp [SourceSemantics.lookupValue, hvalueLt]
  · have hlookup :
        SourceSemantics.lookupValue ((boundName, value) :: bindings) queryName =
          SourceSemantics.lookupValue bindings queryName := by
        have hEq' : boundName ≠ queryName := by
          intro hEq'
          apply hEq
          exact hEq'.symm
        unfold SourceSemantics.lookupValue
        simp [hEq']
    rw [hlookup]
    exact hbounded queryName

theorem bindingsBounded_of_bindSupportedParams
    {params : List Param}
    {args : List Nat}
    {bindings : List (String × Nat)}
    (hbind : SourceSemantics.bindSupportedParams params args = some bindings) :
    bindingsBounded bindings := by
  induction params generalizing args bindings with
  | nil =>
      simp [SourceSemantics.bindSupportedParams] at hbind
      cases hbind
      simp
  | cons param rest ih =>
      cases args with
      | nil =>
          simp [SourceSemantics.bindSupportedParams] at hbind
      | cons arg restArgs =>
          cases hdecode : SourceSemantics.decodeSupportedParamWord param.ty arg <;>
              simp [SourceSemantics.bindSupportedParams, hdecode] at hbind
          case some value =>
            cases hrest : SourceSemantics.bindSupportedParams rest restArgs <;>
                simp [hrest] at hbind
            case some restBindings =>
              cases hbind
              exact bindingsBounded_cons
                param.name value (decodeSupportedParamWord_lt_evmModulus hdecode) (ih hrest)

@[simp] theorem lookupBinding?_bindValue_eq
    (bindings : List (String × Nat))
    (name : String)
    (value : Nat) :
    lookupBinding?
      (SourceSemantics.bindValue bindings name value)
      name = some value := by
  simp [lookupBinding?, SourceSemantics.bindValue]

theorem lookupBinding?_bindValue_ne
    (bindings : List (String × Nat))
    (boundName queryName : String)
    (value : Nat)
    (hNe : queryName ≠ boundName) :
    lookupBinding?
      (SourceSemantics.bindValue bindings boundName value)
      queryName =
    lookupBinding? bindings queryName := by
  have hNe' : boundName ≠ queryName := by
    intro hEq
    apply hNe
    simp [hEq]
  calc
    lookupBinding?
        (SourceSemantics.bindValue bindings boundName value)
        queryName
        =
          Option.map Prod.snd
            (List.find? (fun entry => entry.1 == queryName)
              ((boundName, value) :: List.filter (fun entry => entry.1 != boundName) bindings)) := by
                rfl
    _ = Option.map Prod.snd
          (List.find? (fun entry => entry.1 == queryName)
            (List.filter (fun entry => entry.1 != boundName) bindings)) := by
              simp [hNe']
    _ = Option.map Prod.snd
          (List.find? (fun entry => entry.1 == queryName) bindings) := by
              rw [findEntry_filter_ne_eq_findEntry bindings boundName queryName hNe]
    _ = lookupBinding? bindings queryName := by
          rfl

theorem exprBoundNamesPresent_bindValue
    (expr : Expr)
    (bindings : List (String × Nat))
    (boundName : String)
    (value : Nat)
    (hpresent : exprBoundNamesPresent expr bindings) :
    exprBoundNamesPresent expr (SourceSemantics.bindValue bindings boundName value) := by
  intro queryName hmem
  by_cases hEq : queryName = boundName
  · subst hEq
    exact ⟨value, lookupBinding?_bindValue_eq bindings queryName value⟩
  · rcases hpresent queryName hmem with ⟨found, hfound⟩
    exact ⟨found, by rw [lookupBinding?_bindValue_ne bindings boundName queryName value hEq, hfound]⟩

private theorem lookupBinding?_cons_of_ne
    (bindings : List (String × Nat))
    {boundName queryName : String}
    (value : Nat)
    (hNe : boundName ≠ queryName) :
    lookupBinding? ((boundName, value) :: bindings) queryName =
      lookupBinding? bindings queryName := by
  simp [lookupBinding?, hNe]

private theorem bindSupportedParams_cons_eq_some
    {param : Param} {rest : List Param}
    {arg : Nat} {restArgs : List Nat}
    {bindings : List (String × Nat)}
    (hbind : SourceSemantics.bindSupportedParams (param :: rest) (arg :: restArgs) =
      some bindings) :
    ∃ value restBindings,
      SourceSemantics.bindSupportedParams rest restArgs = some restBindings ∧
        bindings = (param.name, value) :: restBindings := by
  cases hdecode : SourceSemantics.decodeSupportedParamWord param.ty arg <;>
      simp [SourceSemantics.bindSupportedParams, hdecode] at hbind
  case some value =>
    cases hrest : SourceSemantics.bindSupportedParams rest restArgs <;>
        simp [hrest] at hbind
    case some restBindings =>
      exact ⟨value, restBindings, rfl, hbind.symm⟩

theorem bindSupportedParams_lookupBinding?_some_of_mem
    {params : List Param}
    {args : List Nat}
    {bindings : List (String × Nat)}
    (hparamsNodup : (params.map Param.name).Nodup)
    (hbind : SourceSemantics.bindSupportedParams params args = some bindings)
    {queryName : String}
    (hmem : queryName ∈ params.map Param.name) :
    ∃ value, lookupBinding? bindings queryName = some value := by
  induction params generalizing args bindings with
  | nil =>
      cases hmem
  | cons param rest ih =>
      cases args with
      | nil =>
          simp [SourceSemantics.bindSupportedParams] at hbind
      | cons arg restArgs =>
          obtain ⟨value, restBindings, hrest, rfl⟩ := bindSupportedParams_cons_eq_some hbind
          simp only [List.map, List.mem_cons] at hmem
          rcases hmem with rfl | hmemRest
          · exact ⟨value, by simp [lookupBinding?]⟩
          · have hNe : param.name ≠ queryName := by
              rintro rfl
              exact (List.nodup_cons.mp hparamsNodup).1 hmemRest
            rw [lookupBinding?_cons_of_ne restBindings value hNe]
            exact ih (List.nodup_cons.mp hparamsNodup).2 hrest hmemRest

theorem exprBoundNamesPresent_of_bindSupportedParams
    {expr : Expr}
    {params : List Param}
    {args : List Nat}
    {bindings : List (String × Nat)}
    (hparamsNodup : (params.map Param.name).Nodup)
    (hbind : SourceSemantics.bindSupportedParams params args = some bindings)
    (hsubset : ∀ name, name ∈ exprBoundNames expr → name ∈ params.map Param.name) :
    exprBoundNamesPresent expr bindings := by
  intro queryName hmem
  exact bindSupportedParams_lookupBinding?_some_of_mem hparamsNodup hbind (hsubset queryName hmem)

theorem bindingsExactlyMatchIRVars_setVar_bindValue
    {bindings : List (String × Nat)}
    {state : IRState}
    (hexact : bindingsExactlyMatchIRVars bindings state)
    (boundName : String)
    (value : Nat) :
    bindingsExactlyMatchIRVars
      (SourceSemantics.bindValue bindings boundName value)
      (state.setVar boundName value) := by
  intro queryName
  by_cases hEq : queryName = boundName
  · subst hEq
    simp [lookupBinding?_bindValue_eq]
  · rw [getVar_setVar_ne state boundName queryName value hEq,
      lookupBinding?_bindValue_ne bindings boundName queryName value hEq]
    exact hexact queryName

theorem bindingsMatchIRVars_setVar_bindValue
    {bindings : List (String × Nat)}
    {state : IRState}
    (hmatch : bindingsMatchIRVars bindings state)
    (boundName : String)
    (value : Nat) :
    bindingsMatchIRVars
      (SourceSemantics.bindValue bindings boundName value)
      (state.setVar boundName value) := by
  intro queryName
  by_cases hEq : queryName = boundName
  · subst hEq
    simp
  · rw [getVar_setVar_ne state boundName queryName value hEq,
      lookupValue_bindValue_ne bindings boundName queryName value hEq]
    exact hmatch queryName

theorem bindingsExactlyMatchIRVars_applyBindingsToIRState
    {bindings0 bindings : List (String × Nat)}
    {state : IRState}
    (hexact : bindingsExactlyMatchIRVars bindings0 state) :
    bindingsExactlyMatchIRVars
      (bindings.foldl (fun acc entry => SourceSemantics.bindValue acc entry.1 entry.2) bindings0)
      (ParamLoading.applyBindingsToIRState state bindings) := by
  induction bindings generalizing bindings0 state with
  | nil =>
      simpa [ParamLoading.applyBindingsToIRState]
  | cons entry rest ih =>
      have hstep :
          bindingsExactlyMatchIRVars
            (SourceSemantics.bindValue bindings0 entry.1 entry.2)
            (state.setVar entry.1 entry.2) :=
        bindingsExactlyMatchIRVars_setVar_bindValue hexact entry.1 entry.2
      simpa [ParamLoading.applyBindingsToIRState, List.foldl] using
        ih (bindings0 := SourceSemantics.bindValue bindings0 entry.1 entry.2)
          (state := state.setVar entry.1 entry.2) hstep

theorem evalIRExpr_sload_of_runtimeStateMatchesIR
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hmatch : runtimeStateMatchesIR fields runtime state)
    (slot : Nat) :
    evalIRExpr state (YulExpr.call "sload" [YulExpr.lit slot]) =
      some (SourceSemantics.encodeStorageAt fields runtime.world (IRStorageSlot.ofNat slot).toNat
        % EvmYul.UInt256.size) := by
  rcases hmatch with ⟨hstorage, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  simp [evalIRExpr, evalIRCall, evalIRExprs,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean, hstorage]

theorem eval_compileExpr_param_of_exact_bindings
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (name : String)
    (hexact : bindingsExactlyMatchIRVars runtime.bindings state)
    (hpresent : exprBoundNamesPresent (.param name) runtime.bindings) :
    evalIRExpr state (YulExpr.ident name) =
      some (SourceSemantics.evalExpr fields runtime (.param name)) := by
  rcases hpresent name (by simp [exprBoundNames]) with ⟨value, hlookup⟩
  have hident := evalIRExpr_ident_of_exact_bindings hexact name
  rw [hlookup] at hident
  have hsource : SourceSemantics.evalExpr fields runtime (.param name) = some value := by
    change some (SourceSemantics.lookupValue runtime.bindings name) = some value
    exact congrArg some (lookupValue_eq_of_lookupBinding?_some hlookup)
  have hidentLift :=
    congrArg (fun x => x.bind fun a => some (some a)) hident
  simpa [hsource] using hidentLift

theorem eval_compileExpr_localVar_of_exact_bindings
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (name : String)
    (hexact : bindingsExactlyMatchIRVars runtime.bindings state)
    (hpresent : exprBoundNamesPresent (.localVar name) runtime.bindings) :
    evalIRExpr state (YulExpr.ident name) =
      some (SourceSemantics.evalExpr fields runtime (.localVar name)) := by
  rcases hpresent name (by simp [exprBoundNames]) with ⟨value, hlookup⟩
  have hident := evalIRExpr_ident_of_exact_bindings hexact name
  rw [hlookup] at hident
  have hsource : SourceSemantics.evalExpr fields runtime (.localVar name) = some value := by
    change some (SourceSemantics.lookupValue runtime.bindings name) = some value
    exact congrArg some (lookupValue_eq_of_lookupBinding?_some hlookup)
  have hidentLift :=
    congrArg (fun x => x.bind fun a => some (some a)) hident
  simpa [hsource] using hidentLift

theorem eval_compileExpr_param_of_expr_bindings
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (name : String)
    (hexact : bindingsExactlyMatchIRVarsOnExpr (.param name) runtime.bindings state)
    (hpresent : exprBoundNamesPresent (.param name) runtime.bindings) :
    evalIRExpr state (YulExpr.ident name) =
      some (SourceSemantics.evalExpr fields runtime (.param name)) := by
  rcases hpresent name (by simp [exprBoundNames]) with ⟨value, hlookup⟩
  have hident := hexact name (by simp [exprBoundNames])
  rw [hlookup] at hident
  have hsource : SourceSemantics.evalExpr fields runtime (.param name) = some value := by
    change some (SourceSemantics.lookupValue runtime.bindings name) = some value
    exact congrArg some (lookupValue_eq_of_lookupBinding?_some hlookup)
  have hidentLift :=
    congrArg (fun x => x.bind fun a => some (some a)) hident
  simpa [evalIRExpr, hsource] using hidentLift

theorem eval_compileExpr_localVar_of_expr_bindings
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (name : String)
    (hexact : bindingsExactlyMatchIRVarsOnExpr (.localVar name) runtime.bindings state)
    (hpresent : exprBoundNamesPresent (.localVar name) runtime.bindings) :
    evalIRExpr state (YulExpr.ident name) =
      some (SourceSemantics.evalExpr fields runtime (.localVar name)) := by
  rcases hpresent name (by simp [exprBoundNames]) with ⟨value, hlookup⟩
  have hident := hexact name (by simp [exprBoundNames])
  rw [hlookup] at hident
  have hsource : SourceSemantics.evalExpr fields runtime (.localVar name) = some value := by
    change some (SourceSemantics.lookupValue runtime.bindings name) = some value
    exact congrArg some (lookupValue_eq_of_lookupBinding?_some hlookup)
  have hidentLift :=
    congrArg (fun x => x.bind fun a => some (some a)) hident
  simpa [evalIRExpr, hsource] using hidentLift

theorem eval_compileExpr_constructorArg_of_expr_bindings
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (idx : Nat)
    (hexact : bindingsExactlyMatchIRVarsOnExpr (.constructorArg idx) runtime.bindings state)
    (hpresent : exprBoundNamesPresent (.constructorArg idx) runtime.bindings) :
    evalIRExpr state (YulExpr.ident s!"arg{idx}") =
      some (SourceSemantics.evalExpr fields runtime (.constructorArg idx)) := by
  rcases hpresent s!"arg{idx}" (by simp [exprBoundNames]) with ⟨value, hlookup⟩
  have hident := hexact s!"arg{idx}" (by simp [exprBoundNames])
  rw [hlookup] at hident
  have hsource : SourceSemantics.evalExpr fields runtime (.constructorArg idx) = some value := by
    change SourceSemantics.lookupBinding? runtime.bindings s!"arg{idx}" = some value
    simpa [lookupBinding?, SourceSemantics.lookupBinding?] using hlookup
  have hidentLift :=
    congrArg (fun x => x.bind fun a => some (some a)) hident
  simpa [evalIRExpr, hsource] using hidentLift

@[simp] theorem boolWord_lt_evmModulus (b : Bool) :
    SourceSemantics.boolWord b < Compiler.Constants.evmModulus := by
  cases b <;> norm_num [SourceSemantics.boolWord, Compiler.Constants.evmModulus]

@[simp] theorem boolWord_and
    (a b : Bool) :
    (SourceSemantics.boolWord a &&& SourceSemantics.boolWord b) =
      SourceSemantics.boolWord (a && b) := by
  cases a <;> cases b <;>
    simp [SourceSemantics.boolWord]

@[simp] theorem boolWord_or
    (a b : Bool) :
    (SourceSemantics.boolWord a ||| SourceSemantics.boolWord b) =
      SourceSemantics.boolWord (a || b) := by
  cases a <;> cases b <;>
    simp [SourceSemantics.boolWord]

theorem boolWord_iszero_iszero
    {v : Nat} :
    SourceSemantics.boolWord (SourceSemantics.boolWord (v = 0) = 0) =
      SourceSemantics.boolWord (v ≠ 0) := by
  by_cases hzero : v = 0 <;> simp [hzero, SourceSemantics.boolWord]

private theorem boolWord_iszero_lt_eq_ge
    (a b : Nat)
    (ha : a < Compiler.Constants.evmModulus)
    (hb : b < Compiler.Constants.evmModulus) :
    SourceSemantics.boolWord
      (SourceSemantics.boolWord (a % Compiler.Constants.evmModulus < b % Compiler.Constants.evmModulus) = 0) =
      SourceSemantics.boolWord (decide (b ≤ a)) := by
  by_cases hlt : a < b
  · have hnotle : ¬ b ≤ a := Nat.not_le_of_gt hlt
    simp [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, hlt, hnotle, SourceSemantics.boolWord]
  · have hle : b ≤ a := Nat.le_of_not_gt hlt
    simp [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, hlt, hle, SourceSemantics.boolWord]

private theorem boolWord_iszero_gt_eq_le
    (a b : Nat)
    (ha : a < Compiler.Constants.evmModulus)
    (hb : b < Compiler.Constants.evmModulus) :
    SourceSemantics.boolWord
      (SourceSemantics.boolWord (b % Compiler.Constants.evmModulus < a % Compiler.Constants.evmModulus) = 0) =
      SourceSemantics.boolWord (decide (a ≤ b)) := by
  by_cases hgt : b < a
  · have hnotle : ¬ a ≤ b := Nat.not_le_of_gt hgt
    simp [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, hgt, hnotle, SourceSemantics.boolWord]
  · have hle : a ≤ b := Nat.le_of_not_gt hgt
    simp [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, hgt, hle, SourceSemantics.boolWord]

private theorem eval_compileExpr_ge_raw
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhsCompile : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhsCompile : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR)
    (hlhsEval : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs))
    (hrhsEval : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs)) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata (.ge lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
        some (SourceSemantics.boolWord
          (SourceSemantics.boolWord
            (((SourceSemantics.evalExpr fields runtime lhs).getD 0) % Compiler.Constants.evmModulus <
              ((SourceSemantics.evalExpr fields runtime rhs).getD 0) % Compiler.Constants.evmModulus) = 0)) := by
  rcases hlhsSrc : SourceSemantics.evalExpr fields runtime lhs with _ | lhsVal
  · cases hEval : evalIRExpr state lhsIR <;> simp [hEval, hlhsSrc] at hlhsEval
  · rcases hrhsSrc : SourceSemantics.evalExpr fields runtime rhs with _ | rhsVal
    · cases hEval : evalIRExpr state rhsIR <;> simp [hEval, hrhsSrc] at hrhsEval
    · have hlhsEval' : evalIRExpr state lhsIR = some lhsVal := by
        cases hEval : evalIRExpr state lhsIR with
        | none =>
            simp [hEval, hlhsSrc] at hlhsEval
        | some val =>
            simp [hEval, hlhsSrc] at hlhsEval
            simpa [hlhsEval] using hEval
      have hrhsEval' : evalIRExpr state rhsIR = some rhsVal := by
        cases hEval : evalIRExpr state rhsIR with
        | none =>
            simp [hEval, hrhsSrc] at hrhsEval
        | some val =>
            simp [hEval, hrhsSrc] at hrhsEval
            simpa [hrhsEval] using hEval
      have hcompile :
          (CompilationModel.compileExpr fields .calldata (.ge lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
            YulExpr.call "iszero" [YulExpr.call "lt" [lhsIR, rhsIR]] := by
        rw [← CompilationModel.compileExprWithInternals_nil_eq] at hlhsCompile hrhsCompile
        rw [CompilationModel.compileExpr, CompilationModel.compileExprWithInternals, hlhsCompile, hrhsCompile]
        rfl
      rw [hcompile]
      simpa [hlhsSrc, hrhsSrc] using
        (evalIRExpr_iszero_of_lt
          (heval := evalIRExpr_lt_of_eval hlhsEval' hrhsEval')
          (hvalueLt := boolWord_lt_evmModulus _))

private theorem eval_compileExpr_le_raw
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhsCompile : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhsCompile : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR)
    (hlhsEval : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs))
    (hrhsEval : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs)) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata (.le lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
        some (SourceSemantics.boolWord
          (SourceSemantics.boolWord
            (((SourceSemantics.evalExpr fields runtime rhs).getD 0) % Compiler.Constants.evmModulus <
              ((SourceSemantics.evalExpr fields runtime lhs).getD 0) % Compiler.Constants.evmModulus) = 0)) := by
  rcases hlhsSrc : SourceSemantics.evalExpr fields runtime lhs with _ | lhsVal
  · cases hEval : evalIRExpr state lhsIR <;> simp [hEval, hlhsSrc] at hlhsEval
  · rcases hrhsSrc : SourceSemantics.evalExpr fields runtime rhs with _ | rhsVal
    · cases hEval : evalIRExpr state rhsIR <;> simp [hEval, hrhsSrc] at hrhsEval
    · have hlhsEval' : evalIRExpr state lhsIR = some lhsVal := by
        cases hEval : evalIRExpr state lhsIR with
        | none =>
            simp [hEval, hlhsSrc] at hlhsEval
        | some val =>
            simp [hEval, hlhsSrc] at hlhsEval
            simpa [hlhsEval] using hEval
      have hrhsEval' : evalIRExpr state rhsIR = some rhsVal := by
        cases hEval : evalIRExpr state rhsIR with
        | none =>
            simp [hEval, hrhsSrc] at hrhsEval
        | some val =>
            simp [hEval, hrhsSrc] at hrhsEval
            simpa [hrhsEval] using hEval
      have hcompile :
          (CompilationModel.compileExpr fields .calldata (.le lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
            YulExpr.call "iszero" [YulExpr.call "gt" [lhsIR, rhsIR]] := by
        rw [← CompilationModel.compileExprWithInternals_nil_eq] at hlhsCompile hrhsCompile
        rw [CompilationModel.compileExpr, CompilationModel.compileExprWithInternals, hlhsCompile, hrhsCompile]
        rfl
      rw [hcompile]
      simpa [hlhsSrc, hrhsSrc] using
        (evalIRExpr_iszero_of_lt
          (heval := evalIRExpr_gt_of_eval hlhsEval' hrhsEval')
          (hvalueLt := boolWord_lt_evmModulus _))

theorem compileExpr_eq_ok
    {fields : List Field}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhs : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhs : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR) :
    CompilationModel.compileExpr fields .calldata (.eq lhs rhs) =
      Except.ok (YulExpr.call "eq" [lhsIR, rhsIR]) := by
  rw [← CompilationModel.compileExprWithInternals_nil_eq] at hlhs hrhs
  rw [CompilationModel.compileExpr, CompilationModel.compileExprWithInternals, hlhs, hrhs]
  rfl

theorem compileExpr_lt_ok
    {fields : List Field}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhs : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhs : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR) :
    CompilationModel.compileExpr fields .calldata (.lt lhs rhs) =
      Except.ok (YulExpr.call "lt" [lhsIR, rhsIR]) := by
  rw [← CompilationModel.compileExprWithInternals_nil_eq] at hlhs hrhs
  rw [CompilationModel.compileExpr, CompilationModel.compileExprWithInternals, hlhs, hrhs]
  rfl

theorem compileExpr_slt_ok
    {fields : List Field}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhs : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhs : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR) :
    CompilationModel.compileExpr fields .calldata (.slt lhs rhs) =
      Except.ok (YulExpr.call "slt" [lhsIR, rhsIR]) := by
  rw [← CompilationModel.compileExprWithInternals_nil_eq] at hlhs hrhs
  rw [CompilationModel.compileExpr, CompilationModel.compileExprWithInternals, hlhs, hrhs]
  rfl

theorem compileExpr_sgt_ok
    {fields : List Field}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhs : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhs : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR) :
    CompilationModel.compileExpr fields .calldata (.sgt lhs rhs) =
      Except.ok (YulExpr.call "sgt" [lhsIR, rhsIR]) := by
  rw [← CompilationModel.compileExprWithInternals_nil_eq] at hlhs hrhs
  rw [CompilationModel.compileExpr, CompilationModel.compileExprWithInternals, hlhs, hrhs]
  rfl

theorem compileExpr_sdiv_ok
    {fields : List Field}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhs : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhs : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR) :
    CompilationModel.compileExpr fields .calldata (.sdiv lhs rhs) =
      Except.ok (YulExpr.call "sdiv" [lhsIR, rhsIR]) := by
  rw [← CompilationModel.compileExprWithInternals_nil_eq] at hlhs hrhs
  rw [CompilationModel.compileExpr, CompilationModel.compileExprWithInternals, hlhs, hrhs]
  rfl

theorem compileExpr_smod_ok
    {fields : List Field}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhs : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhs : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR) :
    CompilationModel.compileExpr fields .calldata (.smod lhs rhs) =
      Except.ok (YulExpr.call "smod" [lhsIR, rhsIR]) := by
  rw [← CompilationModel.compileExprWithInternals_nil_eq] at hlhs hrhs
  rw [CompilationModel.compileExpr, CompilationModel.compileExprWithInternals, hlhs, hrhs]
  rfl

theorem compileExpr_sar_ok
    {fields : List Field}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhs : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhs : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR) :
    CompilationModel.compileExpr fields .calldata (.sar lhs rhs) =
      Except.ok (YulExpr.call "sar" [lhsIR, rhsIR]) := by
  rw [← CompilationModel.compileExprWithInternals_nil_eq] at hlhs hrhs
  rw [CompilationModel.compileExpr, CompilationModel.compileExprWithInternals, hlhs, hrhs]
  rfl

theorem compileExpr_byte_ok
    {fields : List Field}
    {index value : Expr}
    {indexIR valueIR : YulExpr}
    (hindex : CompilationModel.compileExpr fields .calldata index = Except.ok indexIR)
    (hvalue : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    CompilationModel.compileExpr fields .calldata (.byte index value) =
      Except.ok (YulExpr.call "byte" [indexIR, valueIR]) := by
  rw [← CompilationModel.compileExprWithInternals_nil_eq] at hindex hvalue
  rw [CompilationModel.compileExpr, CompilationModel.compileExprWithInternals, hindex, hvalue]
  rfl

theorem compileExpr_signextend_ok
    {fields : List Field}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhs : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhs : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR) :
    CompilationModel.compileExpr fields .calldata (.signextend lhs rhs) =
      Except.ok (YulExpr.call "signextend" [lhsIR, rhsIR]) := by
  rw [← CompilationModel.compileExprWithInternals_nil_eq] at hlhs hrhs
  rw [CompilationModel.compileExpr, CompilationModel.compileExprWithInternals, hlhs, hrhs]
  rfl

theorem compileExpr_gt_ok
    {fields : List Field}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhs : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhs : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR) :
    CompilationModel.compileExpr fields .calldata (.gt lhs rhs) =
      Except.ok (YulExpr.call "gt" [lhsIR, rhsIR]) := by
  rw [← CompilationModel.compileExprWithInternals_nil_eq] at hlhs hrhs
  rw [CompilationModel.compileExpr, CompilationModel.compileExprWithInternals, hlhs, hrhs]
  rfl

theorem compileExpr_ge_ok
    {fields : List Field}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhs : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhs : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR) :
    CompilationModel.compileExpr fields .calldata (.ge lhs rhs) =
      Except.ok (YulExpr.call "iszero" [YulExpr.call "lt" [lhsIR, rhsIR]]) := by
  rw [← CompilationModel.compileExprWithInternals_nil_eq] at hlhs hrhs
  rw [CompilationModel.compileExpr, CompilationModel.compileExprWithInternals, hlhs, hrhs]
  rfl

theorem compileExpr_le_ok
    {fields : List Field}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhs : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhs : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR) :
    CompilationModel.compileExpr fields .calldata (.le lhs rhs) =
      Except.ok (YulExpr.call "iszero" [YulExpr.call "gt" [lhsIR, rhsIR]]) := by
  rw [← CompilationModel.compileExprWithInternals_nil_eq] at hlhs hrhs
  rw [CompilationModel.compileExpr, CompilationModel.compileExprWithInternals, hlhs, hrhs]
  rfl

theorem compileExpr_logicalNot_ok
    {fields : List Field}
    {expr : Expr}
    {exprIR : YulExpr}
    (hexpr : CompilationModel.compileExpr fields .calldata expr = Except.ok exprIR) :
    CompilationModel.compileExpr fields .calldata (.logicalNot expr) =
      Except.ok (YulExpr.call "iszero" [exprIR]) := by
  rw [← CompilationModel.compileExprWithInternals_nil_eq] at hexpr
  rw [CompilationModel.compileExpr, CompilationModel.compileExprWithInternals, hexpr]
  rfl

theorem compileExpr_logicalAnd_ok
    {fields : List Field}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhs : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhs : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR) :
    CompilationModel.compileExpr fields .calldata (.logicalAnd lhs rhs) =
      Except.ok (YulExpr.call "and"
        [CompilationModel.yulToBool lhsIR, CompilationModel.yulToBool rhsIR]) := by
  rw [← CompilationModel.compileExprWithInternals_nil_eq] at hlhs hrhs
  rw [CompilationModel.compileExpr, CompilationModel.compileExprWithInternals, hlhs, hrhs]
  rfl

theorem compileExpr_logicalOr_ok
    {fields : List Field}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhs : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhs : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR) :
    CompilationModel.compileExpr fields .calldata (.logicalOr lhs rhs) =
      Except.ok (YulExpr.call "or"
        [CompilationModel.yulToBool lhsIR, CompilationModel.yulToBool rhsIR]) := by
  rw [← CompilationModel.compileExprWithInternals_nil_eq] at hlhs hrhs
  rw [CompilationModel.compileExpr, CompilationModel.compileExprWithInternals, hlhs, hrhs]
  rfl

theorem compileExpr_bitAnd_ok
    {fields : List Field}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhs : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhs : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR) :
    CompilationModel.compileExpr fields .calldata (.bitAnd lhs rhs) =
      Except.ok (YulExpr.call "and" [lhsIR, rhsIR]) := by
  rw [← CompilationModel.compileExprWithInternals_nil_eq] at hlhs hrhs
  rw [CompilationModel.compileExpr, CompilationModel.compileExprWithInternals, hlhs, hrhs]
  rfl

theorem compileExpr_bitOr_ok
    {fields : List Field}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhs : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhs : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR) :
    CompilationModel.compileExpr fields .calldata (.bitOr lhs rhs) =
      Except.ok (YulExpr.call "or" [lhsIR, rhsIR]) := by
  rw [← CompilationModel.compileExprWithInternals_nil_eq] at hlhs hrhs
  rw [CompilationModel.compileExpr, CompilationModel.compileExprWithInternals, hlhs, hrhs]
  rfl

theorem compileExpr_bitXor_ok
    {fields : List Field}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhs : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhs : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR) :
    CompilationModel.compileExpr fields .calldata (.bitXor lhs rhs) =
      Except.ok (YulExpr.call "xor" [lhsIR, rhsIR]) := by
  rw [← CompilationModel.compileExprWithInternals_nil_eq] at hlhs hrhs
  rw [CompilationModel.compileExpr, CompilationModel.compileExprWithInternals, hlhs, hrhs]
  rfl

theorem compileExpr_bitNot_ok
    {fields : List Field}
    {expr : Expr}
    {exprIR : YulExpr}
    (hexpr : CompilationModel.compileExpr fields .calldata expr = Except.ok exprIR) :
    CompilationModel.compileExpr fields .calldata (.bitNot expr) =
      Except.ok (YulExpr.call "not" [exprIR]) := by
  rw [← CompilationModel.compileExprWithInternals_nil_eq] at hexpr
  rw [CompilationModel.compileExpr, CompilationModel.compileExprWithInternals, hexpr]
  rfl

theorem compileExpr_shl_ok
    {fields : List Field}
    {shift value : Expr}
    {shiftIR valueIR : YulExpr}
    (hshift : CompilationModel.compileExpr fields .calldata shift = Except.ok shiftIR)
    (hvalue : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    CompilationModel.compileExpr fields .calldata (.shl shift value) =
      Except.ok (YulExpr.call "shl" [shiftIR, valueIR]) := by
  rw [← CompilationModel.compileExprWithInternals_nil_eq] at hshift hvalue
  rw [CompilationModel.compileExpr, CompilationModel.compileExprWithInternals, hshift, hvalue]
  rfl

theorem compileExpr_shr_ok
    {fields : List Field}
    {shift value : Expr}
    {shiftIR valueIR : YulExpr}
    (hshift : CompilationModel.compileExpr fields .calldata shift = Except.ok shiftIR)
    (hvalue : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    CompilationModel.compileExpr fields .calldata (.shr shift value) =
      Except.ok (YulExpr.call "shr" [shiftIR, valueIR]) := by
  rw [← CompilationModel.compileExprWithInternals_nil_eq] at hshift hvalue
  rw [CompilationModel.compileExpr, CompilationModel.compileExprWithInternals, hshift, hvalue]
  rfl

theorem compileExpr_min_ok
    {fields : List Field}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhs : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhs : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR) :
    CompilationModel.compileExpr fields .calldata (.min lhs rhs) =
      Except.ok (YulExpr.call "sub" [lhsIR,
        YulExpr.call "mul" [
          YulExpr.call "sub" [lhsIR, rhsIR],
          YulExpr.call "gt" [lhsIR, rhsIR]
        ]
      ]) := by
  rw [← CompilationModel.compileExprWithInternals_nil_eq] at hlhs hrhs
  rw [CompilationModel.compileExpr, CompilationModel.compileExprWithInternals, hlhs, hrhs]
  rfl

theorem compileExpr_max_ok
    {fields : List Field}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhs : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhs : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR) :
    CompilationModel.compileExpr fields .calldata (.max lhs rhs) =
      Except.ok (YulExpr.call "add" [lhsIR,
        YulExpr.call "mul" [
          YulExpr.call "sub" [rhsIR, lhsIR],
          YulExpr.call "gt" [rhsIR, lhsIR]
        ]
      ]) := by
  rw [← CompilationModel.compileExprWithInternals_nil_eq] at hlhs hrhs
  rw [CompilationModel.compileExpr, CompilationModel.compileExprWithInternals, hlhs, hrhs]
  rfl

theorem compileExpr_wMulDown_ok
    {fields : List Field}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhs : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhs : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR) :
    CompilationModel.compileExpr fields .calldata (.wMulDown lhs rhs) =
      Except.ok (YulExpr.call "div" [
        YulExpr.call "mul" [lhsIR, rhsIR],
        YulExpr.lit 1000000000000000000
      ]) := by
  rw [← CompilationModel.compileExprWithInternals_nil_eq] at hlhs hrhs
  rw [CompilationModel.compileExpr, CompilationModel.compileExprWithInternals, hlhs, hrhs]
  rfl

theorem compileExpr_wDivUp_ok
    {fields : List Field}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhs : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhs : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR) :
    CompilationModel.compileExpr fields .calldata (.wDivUp lhs rhs) =
      Except.ok (YulExpr.call "div" [
        YulExpr.call "add" [
          YulExpr.call "mul" [lhsIR, YulExpr.lit 1000000000000000000],
          YulExpr.call "sub" [rhsIR, YulExpr.lit 1]
        ],
        rhsIR
      ]) := by
  rw [← CompilationModel.compileExprWithInternals_nil_eq] at hlhs hrhs
  rw [CompilationModel.compileExpr, CompilationModel.compileExprWithInternals, hlhs, hrhs]
  rfl

theorem compileExpr_mulDivDown_ok
    {fields : List Field}
    {a b c : Expr}
    {aIR bIR cIR : YulExpr}
    (ha : CompilationModel.compileExpr fields .calldata a = Except.ok aIR)
    (hb : CompilationModel.compileExpr fields .calldata b = Except.ok bIR)
    (hc : CompilationModel.compileExpr fields .calldata c = Except.ok cIR) :
    CompilationModel.compileExpr fields .calldata (.mulDivDown a b c) =
      Except.ok (YulExpr.call "div" [YulExpr.call "mul" [aIR, bIR], cIR]) := by
  rw [← CompilationModel.compileExprWithInternals_nil_eq] at ha hb hc
  rw [CompilationModel.compileExpr, CompilationModel.compileExprWithInternals, ha, hb, hc]
  rfl

theorem compileExpr_mulDivUp_ok
    {fields : List Field}
    {a b c : Expr}
    {aIR bIR cIR : YulExpr}
    (ha : CompilationModel.compileExpr fields .calldata a = Except.ok aIR)
    (hb : CompilationModel.compileExpr fields .calldata b = Except.ok bIR)
    (hc : CompilationModel.compileExpr fields .calldata c = Except.ok cIR) :
    CompilationModel.compileExpr fields .calldata (.mulDivUp a b c) =
      Except.ok (YulExpr.call "div" [
        YulExpr.call "add" [YulExpr.call "mul" [aIR, bIR],
          YulExpr.call "sub" [cIR, YulExpr.lit 1]],
        cIR]) := by
  rw [← CompilationModel.compileExprWithInternals_nil_eq] at ha hb hc
  rw [CompilationModel.compileExpr, CompilationModel.compileExprWithInternals, ha, hb, hc]
  rfl

theorem compileExpr_ceilDiv_ok
    {fields : List Field}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhs : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhs : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR) :
    CompilationModel.compileExpr fields .calldata (.ceilDiv lhs rhs) =
      Except.ok (YulExpr.call "mul" [
        YulExpr.call "iszero" [YulExpr.call "iszero" [lhsIR]],
        YulExpr.call "add" [
          YulExpr.call "div" [YulExpr.call "sub" [lhsIR, YulExpr.lit 1], rhsIR],
          YulExpr.lit 1
        ]
      ]) := by
  rw [← CompilationModel.compileExprWithInternals_nil_eq] at hlhs hrhs
  rw [CompilationModel.compileExpr, CompilationModel.compileExprWithInternals, hlhs, hrhs]
  rfl

theorem compileExpr_ite_ok
    {fields : List Field}
    {cond thenVal elseVal : Expr}
    {condIR thenIR elseIR : YulExpr}
    (hcond : CompilationModel.compileExpr fields .calldata cond = Except.ok condIR)
    (hthen : CompilationModel.compileExpr fields .calldata thenVal = Except.ok thenIR)
    (helse : CompilationModel.compileExpr fields .calldata elseVal = Except.ok elseIR) :
    CompilationModel.compileExpr fields .calldata (.ite cond thenVal elseVal) =
      Except.ok (YulExpr.call "add" [
        YulExpr.call "mul" [
          YulExpr.call "iszero" [YulExpr.call "iszero" [condIR]],
          thenIR
        ],
        YulExpr.call "mul" [
          YulExpr.call "iszero" [condIR],
          elseIR
        ]
      ]) := by
  rw [← CompilationModel.compileExprWithInternals_nil_eq] at hcond hthen helse
  rw [CompilationModel.compileExpr, CompilationModel.compileExprWithInternals, hcond, hthen, helse]
  rfl

theorem compileExpr_add_ok
    {fields : List Field}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhs : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhs : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR) :
    CompilationModel.compileExpr fields .calldata (.add lhs rhs) =
      Except.ok (YulExpr.call "add" [lhsIR, rhsIR]) := by
  rw [← CompilationModel.compileExprWithInternals_nil_eq] at hlhs hrhs
  rw [CompilationModel.compileExpr, CompilationModel.compileExprWithInternals, hlhs, hrhs]
  rfl

theorem compileExpr_sub_ok
    {fields : List Field}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhs : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhs : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR) :
    CompilationModel.compileExpr fields .calldata (.sub lhs rhs) =
      Except.ok (YulExpr.call "sub" [lhsIR, rhsIR]) := by
  rw [← CompilationModel.compileExprWithInternals_nil_eq] at hlhs hrhs
  rw [CompilationModel.compileExpr, CompilationModel.compileExprWithInternals, hlhs, hrhs]
  rfl

theorem compileExpr_mul_ok
    {fields : List Field}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhs : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhs : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR) :
    CompilationModel.compileExpr fields .calldata (.mul lhs rhs) =
      Except.ok (YulExpr.call "mul" [lhsIR, rhsIR]) := by
  rw [← CompilationModel.compileExprWithInternals_nil_eq] at hlhs hrhs
  rw [CompilationModel.compileExpr, CompilationModel.compileExprWithInternals, hlhs, hrhs]
  rfl

theorem compileExpr_div_ok
    {fields : List Field}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhs : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhs : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR) :
    CompilationModel.compileExpr fields .calldata (.div lhs rhs) =
      Except.ok (YulExpr.call "div" [lhsIR, rhsIR]) := by
  rw [← CompilationModel.compileExprWithInternals_nil_eq] at hlhs hrhs
  rw [CompilationModel.compileExpr, CompilationModel.compileExprWithInternals, hlhs, hrhs]
  rfl

theorem compileExpr_mod_ok
    {fields : List Field}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhs : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhs : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR) :
    CompilationModel.compileExpr fields .calldata (.mod lhs rhs) =
      Except.ok (YulExpr.call "mod" [lhsIR, rhsIR]) := by
  rw [← CompilationModel.compileExprWithInternals_nil_eq] at hlhs hrhs
  rw [CompilationModel.compileExpr, CompilationModel.compileExprWithInternals, hlhs, hrhs]
  rfl

theorem compileExpr_mload_ok
    {fields : List Field}
    {expr : Expr}
    {exprIR : YulExpr}
    (hexpr : CompilationModel.compileExpr fields .calldata expr = Except.ok exprIR) :
    CompilationModel.compileExpr fields .calldata (.mload expr) =
      Except.ok (YulExpr.call "mload" [exprIR]) := by
  rw [← CompilationModel.compileExprWithInternals_nil_eq] at hexpr
  rw [CompilationModel.compileExpr, CompilationModel.compileExprWithInternals, hexpr]
  rfl

theorem compileExpr_keccak256_ok
    {fields : List Field}
    {offset size : Expr}
    {offsetIR sizeIR : YulExpr}
    (hoffset : CompilationModel.compileExpr fields .calldata offset = Except.ok offsetIR)
    (hsize : CompilationModel.compileExpr fields .calldata size = Except.ok sizeIR) :
    CompilationModel.compileExpr fields .calldata (.keccak256 offset size) =
      Except.ok (YulExpr.call "keccak256" [offsetIR, sizeIR]) := by
  rw [← CompilationModel.compileExprWithInternals_nil_eq] at hoffset hsize
  rw [CompilationModel.compileExpr, CompilationModel.compileExprWithInternals, hoffset, hsize]
  rfl

/-- `pow`/`^` in the EDSL surfaces as `externalCall builtinExpName [base, exponent]`, but the
compiler lowers it to the pure Yul `exp` builtin rather than emitting a foreign call. -/
theorem compileExpr_builtinExp_ok
    {fields : List Field}
    {base exponent : Expr}
    {baseIR exponentIR : YulExpr}
    (hbase : CompilationModel.compileExpr fields .calldata base = Except.ok baseIR)
    (hexp : CompilationModel.compileExpr fields .calldata exponent = Except.ok exponentIR) :
    CompilationModel.compileExpr fields .calldata
        (.externalCall builtinExpName [base, exponent]) =
      Except.ok (YulExpr.call "exp" [baseIR, exponentIR]) := by
  rw [← CompilationModel.compileExprWithInternals_nil_eq] at hbase hexp
  rw [CompilationModel.compileExpr, CompilationModel.compileExprWithInternals]
  simp only [CompilationModel.compileExprListWithInternals, hbase, hexp]
  rfl

private theorem eval_compileExpr_builtinExp_of_compiled
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {base exponent : Expr}
    {baseIR exponentIR : YulExpr}
    (hbase : CompilationModel.compileExpr fields .calldata base = Except.ok baseIR)
    (hexp : CompilationModel.compileExpr fields .calldata exponent = Except.ok exponentIR)
    (hEvalBase : evalIRExpr state baseIR =
      some (SourceSemantics.evalExpr fields runtime base))
    (hEvalExp : evalIRExpr state exponentIR =
      some (SourceSemantics.evalExpr fields runtime exponent)) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata
          (.externalCall builtinExpName [base, exponent]) |>.toOption.getD (YulExpr.lit 0)) =
      some (SourceSemantics.evalExpr fields runtime
        (.externalCall builtinExpName [base, exponent])) := by
  rw [compileExpr_builtinExp_ok hbase hexp]
  simp only [Except.toOption, Option.getD]
  rcases hB : evalIRExpr state baseIR with _ | bv
  · simp [hB] at hEvalBase
  · rcases hE : evalIRExpr state exponentIR with _ | ev
    · simp [hE] at hEvalExp
    · simp only [hB] at hEvalBase
      simp only [hE] at hEvalExp
      simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some] at hEvalBase hEvalExp
      have hsrcB : SourceSemantics.evalExpr fields runtime base = some bv := by
        simpa using hEvalBase.symm
      have hsrcE : SourceSemantics.evalExpr fields runtime exponent = some ev := by
        simpa using hEvalExp.symm
      rw [evalIRExpr_exp_of_eval hB hE,
        SourceSemantics.evalExpr_externalCall_builtinExp fields runtime base exponent]
      simp [hsrcB, hsrcE, uint256_pow_val]

private theorem eval_compileExpr_keccak256_of_compiled
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {offset size : Expr}
    {offsetIR sizeIR : YulExpr}
    (hoffset : CompilationModel.compileExpr fields .calldata offset = Except.ok offsetIR)
    (hsize : CompilationModel.compileExpr fields .calldata size = Except.ok sizeIR)
    (hEvalOff : evalIRExpr state offsetIR =
      some (SourceSemantics.evalExpr fields runtime offset))
    (hEvalSize : evalIRExpr state sizeIR =
      some (SourceSemantics.evalExpr fields runtime size))
    (hruntime : runtimeStateMatchesIR fields runtime state) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata (.keccak256 offset size)
        |>.toOption.getD (YulExpr.lit 0)) =
      some (SourceSemantics.evalExpr fields runtime (.keccak256 offset size)) := by
  rw [compileExpr_keccak256_ok hoffset hsize]
  simp only [Except.toOption, Option.getD]
  rcases hruntime with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hmem, _, _⟩
  rcases hOff : evalIRExpr state offsetIR with _ | off
  · simp [hOff] at hEvalOff
  · rcases hSize : evalIRExpr state sizeIR with _ | len
    · simp [hSize] at hEvalSize
    · simp only [hOff] at hEvalOff
      simp only [hSize] at hEvalSize
      simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some] at hEvalOff hEvalSize
      have hsrcOff : SourceSemantics.evalExpr fields runtime offset = some off := by
        simpa using hEvalOff.symm
      have hsrcSize : SourceSemantics.evalExpr fields runtime size = some len := by
        simpa using hEvalSize.symm
      simp [evalIRExpr, evalIRCall, evalIRExprs, hOff, hSize, hsrcOff, hsrcSize,
        SourceSemantics.keccakMemorySlice, hmem]
      change some (abstractKeccakMemorySlice
          (fun address => (runtime.world.memory address).val) off len) =
        (do
          let resolvedOffset ← SourceSemantics.evalExpr fields runtime offset
          let resolvedSize ← SourceSemantics.evalExpr fields runtime size
          some (SourceSemantics.keccakMemorySlice runtime.world.memory
            resolvedOffset resolvedSize))
      simp [hsrcOff, hsrcSize, SourceSemantics.keccakMemorySlice]

private theorem eval_compileExpr_mload_of_compiled
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {offset : Expr}
    {offsetIR : YulExpr}
    (hoffset : CompilationModel.compileExpr fields .calldata offset = Except.ok offsetIR)
    (hEvalOff : evalIRExpr state offsetIR =
        some (SourceSemantics.evalExpr fields runtime offset))
    (hruntime : runtimeStateMatchesIR fields runtime state) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata (.mload offset)
        |>.toOption.getD (YulExpr.lit 0)) =
      some (SourceSemantics.evalExpr fields runtime (.mload offset)) := by
  rw [compileExpr_mload_ok hoffset]
  simp only [Except.toOption, Option.getD]
  rcases hruntime with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hmem, _, _⟩
  rcases hIR : evalIRExpr state offsetIR with _ | irVal
  · simp [hIR] at hEvalOff
  · simp only [hIR] at hEvalOff
    simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some] at hEvalOff
    have hsrc : SourceSemantics.evalExpr fields runtime offset = some irVal := by
      simpa using hEvalOff.symm
    have hmload_unfold : SourceSemantics.evalExpr fields runtime (.mload offset) =
        (SourceSemantics.evalExpr fields runtime offset).bind
          (fun r => some (runtime.world.memory r).val) := rfl
    rw [hmload_unfold, hsrc]
    simp only [Option.bind_some]
    simp [evalIRExpr, hIR, hmem]

theorem compileExpr_extcodesize_ok
    {fields : List Field}
    {expr : Expr}
    {exprIR : YulExpr}
    (hexpr : CompilationModel.compileExpr fields .calldata expr = Except.ok exprIR) :
    CompilationModel.compileExpr fields .calldata (.extcodesize expr) =
      Except.ok (YulExpr.call "extcodesize" [exprIR]) := by
  rw [← CompilationModel.compileExprWithInternals_nil_eq] at hexpr
  rw [CompilationModel.compileExpr, CompilationModel.compileExprWithInternals, hexpr]
  rfl

theorem compileExpr_returndataOptionalBoolAt_ok
    {fields : List Field}
    {expr : Expr}
    {exprIR : YulExpr}
    (hexpr : CompilationModel.compileExpr fields .calldata expr = Except.ok exprIR) :
    CompilationModel.compileExpr fields .calldata (.returndataOptionalBoolAt expr) =
      Except.ok (YulExpr.call "or" [
        YulExpr.call "eq" [YulExpr.call "returndatasize" [], YulExpr.lit 0],
        YulExpr.call "and" [
          YulExpr.call "eq" [YulExpr.call "returndatasize" [], YulExpr.lit 32],
          YulExpr.call "eq" [YulExpr.call "mload" [exprIR], YulExpr.lit 1]
        ]
      ]) := by
  rw [← CompilationModel.compileExprWithInternals_nil_eq] at hexpr
  rw [CompilationModel.compileExpr, CompilationModel.compileExprWithInternals, hexpr]
  rfl

set_option linter.unusedVariables false in
private theorem eval_compileExpr_extcodesize_of_compiled
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {addr : Expr}
    {addrIR : YulExpr}
    (haddr : CompilationModel.compileExpr fields .calldata addr = Except.ok addrIR)
    (hEvalAddr : evalIRExpr state addrIR =
        some (SourceSemantics.evalExpr fields runtime addr))
    (hruntime : runtimeStateMatchesIR fields runtime state)
    (hlt : SourceSemantics.evalExpr fields runtime addr <
        Compiler.Constants.evmModulus) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata (.extcodesize addr)
        |>.toOption.getD (YulExpr.lit 0)) =
      some (SourceSemantics.evalExpr fields runtime (.extcodesize addr)) := by
  rw [compileExpr_extcodesize_ok haddr]
  simp only [Except.toOption, Option.getD]
  rcases hruntime with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hcs⟩
  rcases hIR : evalIRExpr state addrIR with _ | irVal
  · simp [hIR] at hEvalAddr
  · simp only [hIR] at hEvalAddr
    simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some] at hEvalAddr
    have hsrc : SourceSemantics.evalExpr fields runtime addr = some irVal := by
      simpa using hEvalAddr.symm
    have hecs_unfold : SourceSemantics.evalExpr fields runtime (.extcodesize addr) =
        (SourceSemantics.evalExpr fields runtime addr).bind
          (fun r => some (runtime.world.codeSize (r % SourceSemantics.addressModulus)).val) := rfl
    rw [hecs_unfold, hsrc]
    simp only [Option.bind_some]
    simp [evalIRExpr, hIR, hcs]
    rfl

/-- The word the compiled optional-bool check computes,
`or(eq(returndatasize(), 0), and(eq(returndatasize(), 32), eq(mload(out), 1)))`,
is exactly `ContractState.returndataOptionalBool`. Both operands are already
reduced modulo the EVM word, so the normalization the Yul builtins apply is the
identity and the bitwise `or`/`and` degenerate to the boolean connectives. -/
private theorem optionalReturnBoolWord_eq
    (world : Verity.ContractState) (offset : Nat) :
    SourceSemantics.boolWord
        (world.returndataSize % Compiler.Constants.evmModulus
          = 0 % Compiler.Constants.evmModulus) % Compiler.Constants.evmModulus |||
      (SourceSemantics.boolWord
          (world.returndataSize % Compiler.Constants.evmModulus
            = 32 % Compiler.Constants.evmModulus) % Compiler.Constants.evmModulus &&&
        SourceSemantics.boolWord
          ((world.memory offset).val % Compiler.Constants.evmModulus
            = 1 % Compiler.Constants.evmModulus) % Compiler.Constants.evmModulus)
        % Compiler.Constants.evmModulus
      = world.returndataOptionalBool offset := by
  have hrds : world.returndataSize % Compiler.Constants.evmModulus = world.returndataSize :=
    Nat.mod_eq_of_lt ((32 * world.returndata.length : Nat) : Verity.Core.Uint256).isLt
  have hmem : (world.memory offset).val % Compiler.Constants.evmModulus
      = (world.memory offset).val :=
    Nat.mod_eq_of_lt (world.memory offset).isLt
  have h32 : (32 : Nat) % Compiler.Constants.evmModulus = 32 := by
    norm_num [Compiler.Constants.evmModulus]
  have h1 : (1 : Nat) % Compiler.Constants.evmModulus = 1 := by
    norm_num [Compiler.Constants.evmModulus]
  simp only [Verity.ContractState.returndataOptionalBool, boolWord_eq_if,
    Nat.zero_mod, hrds, hmem, h32, h1]
  by_cases hzero : world.returndataSize = 0
  · simp [hzero, h1]
  · by_cases hword : world.returndataSize = 32
    · by_cases hone : (world.memory offset).val = 1 <;> simp [hzero, hword, hone, h1]
    · simp [hzero, hword, h1]

set_option linter.unusedVariables false in
private theorem eval_compileExpr_returndataOptionalBoolAt_of_compiled
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {offset : Expr}
    {offsetIR : YulExpr}
    (hoffset : CompilationModel.compileExpr fields .calldata offset = Except.ok offsetIR)
    (hEvalOffset : evalIRExpr state offsetIR =
        some (SourceSemantics.evalExpr fields runtime offset))
    (hruntime : runtimeStateMatchesIR fields runtime state) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata (.returndataOptionalBoolAt offset)
        |>.toOption.getD (YulExpr.lit 0)) =
      some (SourceSemantics.evalExpr fields runtime (.returndataOptionalBoolAt offset)) := by
  rw [compileExpr_returndataOptionalBoolAt_ok hoffset]
  simp only [Except.toOption, Option.getD]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hmem, -, -, -, hrd, -⟩ := hruntime
  rcases hIR : evalIRExpr state offsetIR with _ | irVal
  · simp [hIR] at hEvalOffset
  · simp only [hIR] at hEvalOffset
    simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some] at hEvalOffset
    have hsrc : SourceSemantics.evalExpr fields runtime offset = some irVal := by
      simpa using hEvalOffset.symm
    rw [show SourceSemantics.evalExpr fields runtime (.returndataOptionalBoolAt offset) =
        (SourceSemantics.evalExpr fields runtime offset).bind
          (fun r => some (runtime.world.returndataOptionalBool r)) from rfl, hsrc]
    simp only [Option.bind_some]
    have hRDS : evalIRExpr state (YulExpr.call "returndatasize" []) =
        some runtime.world.returndataSize := by
      simp only [evalIRExpr_returndatasize_nil, hrd]
      rfl
    have hMload : evalIRExpr state (YulExpr.call "mload" [offsetIR]) =
        some (runtime.world.memory irVal).val := by
      simp [evalIRExpr, evalIRCall, evalIRExprs, hIR, hmem]
    have hEq0 := evalIRExpr_eq_of_eval hRDS
      (show evalIRExpr state (YulExpr.lit 0) = some 0 from by simp [evalIRExpr])
    have hEq32 := evalIRExpr_eq_of_eval hRDS
      (show evalIRExpr state (YulExpr.lit 32) = some 32 from by simp [evalIRExpr])
    have hEqM := evalIRExpr_eq_of_eval hMload
      (show evalIRExpr state (YulExpr.lit 1) = some 1 from by simp [evalIRExpr])
    rw [evalIRExpr_or_of_eval hEq0 (evalIRExpr_and_of_eval hEq32 hEqM),
      optionalReturnBoolWord_eq runtime.world irVal]
    rfl

theorem compileExpr_tload_ok
    {fields : List Field}
    {expr : Expr}
    {exprIR : YulExpr}
    (hexpr : CompilationModel.compileExpr fields .calldata expr = Except.ok exprIR) :
    CompilationModel.compileExpr fields .calldata (.tload expr) =
      Except.ok (YulExpr.call "tload" [exprIR]) := by
  rw [← CompilationModel.compileExprWithInternals_nil_eq] at hexpr
  rw [CompilationModel.compileExpr, CompilationModel.compileExprWithInternals, hexpr]
  rfl

private theorem calldataloadWord_lt_evmModulus
    (selector : Nat) (calldata : List Nat) (offset : Nat) :
    Compiler.Proofs.YulGeneration.calldataloadWord selector calldata offset <
      Compiler.Constants.evmModulus := by
  unfold Compiler.Proofs.YulGeneration.calldataloadWord
  split
  · -- offset = 0: selectorWord
    unfold Compiler.Proofs.YulGeneration.selectorWord
    have hmod : selector % Compiler.Constants.selectorModulus <
        Compiler.Constants.selectorModulus :=
      Nat.mod_lt _ (by norm_num [Compiler.Constants.selectorModulus])
    have : Compiler.Constants.selectorModulus * 2 ^ Compiler.Constants.selectorShift =
        Compiler.Constants.evmModulus := by
      norm_num [Compiler.Constants.selectorModulus,
        Compiler.Constants.selectorShift, Compiler.Constants.evmModulus]
    calc (selector % Compiler.Constants.selectorModulus) *
            2 ^ Compiler.Constants.selectorShift
        < Compiler.Constants.selectorModulus *
            2 ^ Compiler.Constants.selectorShift :=
          Nat.mul_lt_mul_of_pos_right hmod (by positivity)
      _ = Compiler.Constants.evmModulus := this
  · split
    · -- offset < 4: returns 0
      norm_num [Compiler.Constants.evmModulus]
    · -- offset ≥ 4: let binding then conditional
      dsimp only []
      split
      · -- aligned (r = 0): calldata.getD q 0 % evmModulus
        exact Nat.mod_lt _ (by norm_num [Compiler.Constants.evmModulus])
      · -- unaligned (r ≠ 0): composed hi/lo window reduced mod evmModulus
        exact Nat.mod_lt _ (by norm_num [Compiler.Constants.evmModulus])

/-- `calldatacopy` writes the same words on both sides of the runtime/IR
correspondence: the source world stores `Uint256`-wrapped calldata words while
the IR stores their `Nat` values, and every copied word is already below the EVM
modulus, so the wrapping is the identity on the copied region. -/
theorem runtimeStateMatchesIR_calldatacopyBothMemory
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hmatch : runtimeStateMatchesIR fields runtime state)
    (dst src size : Nat) :
    runtimeStateMatchesIR fields
      { runtime with
          world := {
            runtime.world with
            memory := fun o =>
              if Compiler.Proofs.YulGeneration.calldatacopyWritesAt dst size o then
                Verity.Core.Uint256.ofNat
                  (Compiler.Proofs.YulGeneration.calldataloadWord
                    runtime.selector runtime.world.calldata (src + (o - dst)))
              else runtime.world.memory o } }
      { state with
          memory := Compiler.Proofs.YulGeneration.calldatacopyMemory
            state.selector state.calldata dst src size state.memory } := by
  cases runtime
  cases state
  simp only [runtimeStateMatchesIR] at hmatch ⊢
  obtain ⟨hstor, htrans, hsender, hmsgVal, hthis, hts, hbn, hcid, hblob, htx, hsel, hcd, hcds,
    hmem, hret, hevt⟩ := hmatch
  refine ⟨?_, htrans, hsender, hmsgVal, hthis, hts, hbn, hcid, hblob, htx, hsel, hcd, hcds,
    ?_, hret, hevt⟩
  · rw [hstor]
    funext slot
    exact congrArg _ (SourceSemantics.encodeStorageAt_congr rfl rfl rfl)
  · funext o
    simp only [Compiler.Proofs.YulGeneration.calldatacopyMemory, hsel, hcd]
    by_cases hw : Compiler.Proofs.YulGeneration.calldatacopyWritesAt dst size o
    · simp only [hw, if_true, Verity.Core.Uint256.ofNat]
      exact (Nat.mod_eq_of_lt (calldataloadWord_lt_evmModulus _ _ _)).symm
    · simp only [hw, if_false]
      exact congrFun hmem o

/-- `returndatacopy` writes the same words on both sides of the runtime/IR
correspondence: the source world stores `Uint256`-wrapped buffer words while
the IR stores their `Nat` values, and every copied word is already below the
EVM modulus, so the wrapping is the identity on the copied region. The buffer
itself is pinned equal by the returndata conjunct of `runtimeStateMatchesIR`,
so both sides read the same words. -/
theorem runtimeStateMatchesIR_returndatacopyBothMemory
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hmatch : runtimeStateMatchesIR fields runtime state)
    (dst src size : Nat) :
    runtimeStateMatchesIR fields
      { runtime with
          world := {
            runtime.world with
            memory := Compiler.Proofs.IRGeneration.returndatacopyMemoryPaddedUint256
              runtime.world.returndata dst src size runtime.world.memory } }
      { state with
          memory := Compiler.Proofs.IRGeneration.returndatacopyMemoryPadded
            state.returndata dst src size state.memory } := by
  cases runtime
  cases state
  simp only [runtimeStateMatchesIR] at hmatch ⊢
  obtain ⟨hstor, htrans, hsender, hmsgVal, hthis, hts, hbn, hcid, hblob, htx, hsel, hcd, hcds,
    hmem, hret, hevt⟩ := hmatch
  have hrd := hevt.2.2.1
  refine ⟨?_, htrans, hsender, hmsgVal, hthis, hts, hbn, hcid, hblob, htx, hsel, hcd, hcds,
    ?_, hret, hevt⟩
  · rw [hstor]
    funext slot
    exact congrArg _ (SourceSemantics.encodeStorageAt_congr rfl rfl rfl)
  · funext o
    simp only [Compiler.Proofs.IRGeneration.returndatacopyMemoryPaddedUint256,
      Verity.Core.Uint256.ofNat]
    rw [hrd, hmem]
    by_cases hceil : size % 32 ≠ 0 ∧ o = dst + size / 32 * 32
    · simp [Compiler.Proofs.IRGeneration.returndatacopyMemoryPadded, hceil,
        Nat.mod_mod]
    · simp only [Compiler.Proofs.IRGeneration.returndatacopyMemoryPadded, hceil,
        if_false, Compiler.Proofs.IRGeneration.returndatacopyMemory]
      by_cases hw : Compiler.Proofs.YulGeneration.calldatacopyWritesAt dst size o
      · simp [hw, Nat.mod_eq_of_lt
          (Compiler.Proofs.IRGeneration.returndataloadWord_lt_evmModulus _ _)]
      · simp only [hw, if_false]
        exact (Nat.mod_eq_of_lt (Verity.Core.Uint256.isLt _)).symm

theorem compileExpr_calldataload_ok
    {fields : List Field}
    {expr : Expr}
    {exprIR : YulExpr}
    (hexpr : CompilationModel.compileExpr fields .calldata expr = Except.ok exprIR) :
    CompilationModel.compileExpr fields .calldata (.calldataload expr) =
      Except.ok (YulExpr.call "calldataload" [exprIR]) := by
  rw [← CompilationModel.compileExprWithInternals_nil_eq] at hexpr
  rw [CompilationModel.compileExpr, CompilationModel.compileExprWithInternals, hexpr]
  rfl

private theorem eval_compileExpr_calldataload_of_compiled
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {offset : Expr}
    {offsetIR : YulExpr}
    (hoffset : CompilationModel.compileExpr fields .calldata offset = Except.ok offsetIR)
    (hEvalOff : evalIRExpr state offsetIR =
        some (SourceSemantics.evalExpr fields runtime offset))
    (hruntime : runtimeStateMatchesIR fields runtime state) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata (.calldataload offset)
        |>.toOption.getD (YulExpr.lit 0)) =
      some (SourceSemantics.evalExpr fields runtime (.calldataload offset)) := by
  rw [compileExpr_calldataload_ok hoffset]
  simp only [Except.toOption, Option.getD]
  rcases hruntime with ⟨_, _, _, _, _, _, _, _, _, _, hsel, hcd, _, _, _⟩
  rcases hIR : evalIRExpr state offsetIR with _ | irVal
  · simp [hIR] at hEvalOff
  · simp only [hIR] at hEvalOff
    simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some] at hEvalOff
    have hsrc : SourceSemantics.evalExpr fields runtime offset = some irVal := by
      simpa using hEvalOff.symm
    have hcl_unfold : SourceSemantics.evalExpr fields runtime (.calldataload offset) =
        (SourceSemantics.evalExpr fields runtime offset).bind
          (fun r => some (Compiler.Proofs.YulGeneration.calldataloadWord runtime.selector runtime.world.calldata r)) := rfl
    rw [hcl_unfold, hsrc]
    simp only [Option.bind_some]
    simp [evalIRExpr, hIR, hsel, hcd]

set_option linter.unusedVariables false in
private theorem eval_compileExpr_tload_of_compiled
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {offset : Expr}
    {offsetIR : YulExpr}
    (hoffset : CompilationModel.compileExpr fields .calldata offset = Except.ok offsetIR)
    (hEvalOff : evalIRExpr state offsetIR =
        some (SourceSemantics.evalExpr fields runtime offset))
    (hruntime : runtimeStateMatchesIR fields runtime state)
    (hlt : SourceSemantics.evalExpr fields runtime offset <
        Compiler.Constants.evmModulus) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata (.tload offset)
        |>.toOption.getD (YulExpr.lit 0)) =
      some (SourceSemantics.evalExpr fields runtime (.tload offset)) := by
  rw [compileExpr_tload_ok hoffset]
  simp only [Except.toOption, Option.getD]
  rcases hruntime with ⟨_, htrans, _, _, _, _, _, _, _, _, _, _, _⟩
  -- hEvalOff : (do ...).bind ... = some (evalExpr ..)
  -- Case split on evalExpr result
  -- First case-split on evalIRExpr to extract concrete value
  rcases hIR : evalIRExpr state offsetIR with _ | irVal
  · -- evalIRExpr = none → hEvalOff is contradictory
    simp [hIR] at hEvalOff
  · -- evalIRExpr = some irVal
    simp only [hIR] at hEvalOff
    -- hEvalOff now has do-notation with (some irVal); simplify it fully
    simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some] at hEvalOff
    -- hEvalOff : some (some irVal) = some (evalExpr ...) or vice versa
    have hsrc : SourceSemantics.evalExpr fields runtime offset = some irVal := by
      simpa using hEvalOff.symm
    rw [hsrc] at hlt; simp at hlt
    -- Unfold RHS: evalExpr (.tload offset) → bind form → concrete value
    have htload_unfold : SourceSemantics.evalExpr fields runtime (.tload offset) =
        (SourceSemantics.evalExpr fields runtime offset).bind
          (fun r => some (runtime.world.transientStorage r).val) := rfl
    rw [htload_unfold, hsrc]
    simp only [Option.bind_some]
    -- Goal: (do ...) = some (some (world.transientStorage irVal).val)
    -- Unfold LHS using evalIRExpr, evalIRExprs, hIR
    simp [evalIRExpr, hIR, Nat.mod_eq_of_lt hlt, htrans]

private theorem evalIRExpr_of_sourceEval_some
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {expr : Expr}
    {exprIR : YulExpr}
    {value : Nat}
    (hEval : evalIRExpr state exprIR = some (SourceSemantics.evalExpr fields runtime expr))
    (hSource : SourceSemantics.evalExpr fields runtime expr = some value) :
    evalIRExpr state exprIR = some value := by
  cases hIR : evalIRExpr state exprIR with
  | none =>
      simp [hIR, hSource] at hEval
  | some actual =>
      simp [hIR, hSource] at hEval
      simpa [hEval] using hIR

/-- Extract the (bounded) value of a compiled operand whose IR evaluation matches the
source evaluation. -/
private theorem exists_source_value_of_evalIRExpr
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {expr : Expr}
    {exprIR : YulExpr}
    (hEval : evalIRExpr state exprIR = some (SourceSemantics.evalExpr fields runtime expr))
    (hLt : SourceSemantics.evalExpr fields runtime expr < Compiler.Constants.evmModulus) :
    ∃ value, SourceSemantics.evalExpr fields runtime expr = some value ∧
      evalIRExpr state exprIR = some value ∧ value < Compiler.Constants.evmModulus := by
  rcases hSource : SourceSemantics.evalExpr fields runtime expr with _ | value
  · cases hIR : evalIRExpr state exprIR <;> simp [hIR, hSource] at hEval
  · exact ⟨value, rfl, evalIRExpr_of_sourceEval_some hEval hSource, by simpa [hSource] using hLt⟩

private theorem evalExpr_eq_of_values
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {lhs rhs : Expr}
    {lhsVal rhsVal : Nat}
    (hlhs : SourceSemantics.evalExpr fields runtime lhs = some lhsVal)
    (hrhs : SourceSemantics.evalExpr fields runtime rhs = some rhsVal) :
    SourceSemantics.evalExpr fields runtime (.eq lhs rhs) =
      some (SourceSemantics.boolWord (decide (lhsVal = rhsVal))) := by
  calc
    SourceSemantics.evalExpr fields runtime (.eq lhs rhs)
        = (do
            let lhs ← SourceSemantics.evalExpr fields runtime lhs
            let rhs ← SourceSemantics.evalExpr fields runtime rhs
            pure (SourceSemantics.boolWord (decide (lhs = rhs)))) := by
              rfl
    _ = some (SourceSemantics.boolWord (decide (lhsVal = rhsVal))) := by
          simp [hlhs, hrhs]

private theorem evalExpr_lt_of_values
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {lhs rhs : Expr}
    {lhsVal rhsVal : Nat}
    (hlhs : SourceSemantics.evalExpr fields runtime lhs = some lhsVal)
    (hrhs : SourceSemantics.evalExpr fields runtime rhs = some rhsVal) :
    SourceSemantics.evalExpr fields runtime (.lt lhs rhs) =
      some (SourceSemantics.boolWord (decide (lhsVal < rhsVal))) := by
  calc
    SourceSemantics.evalExpr fields runtime (.lt lhs rhs)
        = (do
            let lhs ← SourceSemantics.evalExpr fields runtime lhs
            let rhs ← SourceSemantics.evalExpr fields runtime rhs
            pure (SourceSemantics.boolWord (decide (lhs < rhs)))) := by
              rfl
    _ = some (SourceSemantics.boolWord (decide (lhsVal < rhsVal))) := by
          simp [hlhs, hrhs]

private theorem evalExpr_slt_of_values
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {lhs rhs : Expr}
    {lhsVal rhsVal : Nat}
    (hlhs : SourceSemantics.evalExpr fields runtime lhs = some lhsVal)
    (hrhs : SourceSemantics.evalExpr fields runtime rhs = some rhsVal) :
    SourceSemantics.evalExpr fields runtime (.slt lhs rhs) =
      some (SourceSemantics.boolWord (decide (
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat lhsVal) : Int) <
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat rhsVal) : Int)))) := by
  calc
    SourceSemantics.evalExpr fields runtime (.slt lhs rhs)
        = (do
            let lhs ← SourceSemantics.evalExpr fields runtime lhs
            let rhs ← SourceSemantics.evalExpr fields runtime rhs
            pure (SourceSemantics.boolWord (decide (
              (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat lhs) : Int) <
              (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat rhs) : Int))))) := by
              rfl
    _ = some (SourceSemantics.boolWord (decide (
          (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat lhsVal) : Int) <
          (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat rhsVal) : Int)))) := by
          simp [hlhs, hrhs]

private theorem evalExpr_sgt_of_values
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {lhs rhs : Expr}
    {lhsVal rhsVal : Nat}
    (hlhs : SourceSemantics.evalExpr fields runtime lhs = some lhsVal)
    (hrhs : SourceSemantics.evalExpr fields runtime rhs = some rhsVal) :
    SourceSemantics.evalExpr fields runtime (.sgt lhs rhs) =
      some (SourceSemantics.boolWord (decide (
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat rhsVal) : Int) <
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat lhsVal) : Int)))) := by
  calc
    SourceSemantics.evalExpr fields runtime (.sgt lhs rhs)
        = (do
            let lhs ← SourceSemantics.evalExpr fields runtime lhs
            let rhs ← SourceSemantics.evalExpr fields runtime rhs
            pure (SourceSemantics.boolWord (decide (
              (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat rhs) : Int) <
              (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat lhs) : Int))))) := by
              rfl
    _ = some (SourceSemantics.boolWord (decide (
          (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat rhsVal) : Int) <
          (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat lhsVal) : Int)))) := by
          simp [hlhs, hrhs]

private theorem evalExpr_sdiv_of_values
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {lhs rhs : Expr}
    {lhsVal rhsVal : Nat}
    (hlhs : SourceSemantics.evalExpr fields runtime lhs = some lhsVal)
    (hrhs : SourceSemantics.evalExpr fields runtime rhs = some rhsVal) :
    SourceSemantics.evalExpr fields runtime (.sdiv lhs rhs) =
      some (Verity.Core.Int256.div
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat lhsVal))
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat rhsVal))).toUint256.val := by
  calc
    SourceSemantics.evalExpr fields runtime (.sdiv lhs rhs)
        = (do
            let lhs ← SourceSemantics.evalExpr fields runtime lhs
            let rhs ← SourceSemantics.evalExpr fields runtime rhs
            pure (Verity.Core.Int256.div
              (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat lhs))
              (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat rhs))).toUint256.val) := by
              rfl
    _ = some (Verity.Core.Int256.div
          (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat lhsVal))
          (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat rhsVal))).toUint256.val := by
          simp [hlhs, hrhs]

private theorem evalExpr_smod_of_values
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {lhs rhs : Expr}
    {lhsVal rhsVal : Nat}
    (hlhs : SourceSemantics.evalExpr fields runtime lhs = some lhsVal)
    (hrhs : SourceSemantics.evalExpr fields runtime rhs = some rhsVal) :
    SourceSemantics.evalExpr fields runtime (.smod lhs rhs) =
      some (Verity.Core.Int256.mod
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat lhsVal))
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat rhsVal))).toUint256.val := by
  calc
    SourceSemantics.evalExpr fields runtime (.smod lhs rhs)
        = (do
            let lhs ← SourceSemantics.evalExpr fields runtime lhs
            let rhs ← SourceSemantics.evalExpr fields runtime rhs
            pure (Verity.Core.Int256.mod
              (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat lhs))
              (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat rhs))).toUint256.val) := by
              rfl
    _ = some (Verity.Core.Int256.mod
          (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat lhsVal))
          (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat rhsVal))).toUint256.val := by
          simp [hlhs, hrhs]

private theorem evalExpr_sar_of_values
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {lhs rhs : Expr}
    {lhsVal rhsVal : Nat}
    (hlhs : SourceSemantics.evalExpr fields runtime lhs = some lhsVal)
    (hrhs : SourceSemantics.evalExpr fields runtime rhs = some rhsVal) :
    SourceSemantics.evalExpr fields runtime (.sar lhs rhs) =
      some (Verity.Core.Int256.sar
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat lhsVal))
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat rhsVal))).toUint256.val := by
  calc
    SourceSemantics.evalExpr fields runtime (.sar lhs rhs)
        = (do
            let lhs ← SourceSemantics.evalExpr fields runtime lhs
            let rhs ← SourceSemantics.evalExpr fields runtime rhs
            pure (Verity.Core.Int256.sar
              (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat lhs))
              (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat rhs))).toUint256.val) := by
              rfl
    _ = some (Verity.Core.Int256.sar
          (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat lhsVal))
          (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat rhsVal))).toUint256.val := by
          simp [hlhs, hrhs]

private theorem evalExpr_byte_of_values
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {index value : Expr}
    {indexVal valueVal : Nat}
    (hindex : SourceSemantics.evalExpr fields runtime index = some indexVal)
    (hvalue : SourceSemantics.evalExpr fields runtime value = some valueVal) :
    SourceSemantics.evalExpr fields runtime (.byte index value) =
      some (Verity.Core.Uint256.byte
        (Verity.Core.Uint256.ofNat indexVal)
        (Verity.Core.Uint256.ofNat valueVal)).val := by
  calc
    SourceSemantics.evalExpr fields runtime (.byte index value)
        = (do
            let index ← SourceSemantics.evalExpr fields runtime index
            let value ← SourceSemantics.evalExpr fields runtime value
            pure (Verity.Core.Uint256.byte
              (Verity.Core.Uint256.ofNat index)
              (Verity.Core.Uint256.ofNat value)).val) := by
              rfl
    _ = some (Verity.Core.Uint256.byte
          (Verity.Core.Uint256.ofNat indexVal)
          (Verity.Core.Uint256.ofNat valueVal)).val := by
          simp [hindex, hvalue]

private theorem evalExpr_signextend_of_values
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {lhs rhs : Expr}
    {lhsVal rhsVal : Nat}
    (hlhs : SourceSemantics.evalExpr fields runtime lhs = some lhsVal)
    (hrhs : SourceSemantics.evalExpr fields runtime rhs = some rhsVal) :
    SourceSemantics.evalExpr fields runtime (.signextend lhs rhs) =
      some (Verity.Core.Uint256.signextend
        (Verity.Core.Uint256.ofNat lhsVal)
        (Verity.Core.Uint256.ofNat rhsVal)).val := by
  calc
    SourceSemantics.evalExpr fields runtime (.signextend lhs rhs)
        = (do
            let lhs ← SourceSemantics.evalExpr fields runtime lhs
            let rhs ← SourceSemantics.evalExpr fields runtime rhs
            pure (Verity.Core.Uint256.signextend
              (Verity.Core.Uint256.ofNat lhs)
              (Verity.Core.Uint256.ofNat rhs)).val) := by
              rfl
    _ = some (Verity.Core.Uint256.signextend
          (Verity.Core.Uint256.ofNat lhsVal)
          (Verity.Core.Uint256.ofNat rhsVal)).val := by
          simp [hlhs, hrhs]

private theorem evalExpr_gt_of_values
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {lhs rhs : Expr}
    {lhsVal rhsVal : Nat}
    (hlhs : SourceSemantics.evalExpr fields runtime lhs = some lhsVal)
    (hrhs : SourceSemantics.evalExpr fields runtime rhs = some rhsVal) :
    SourceSemantics.evalExpr fields runtime (.gt lhs rhs) =
      some (SourceSemantics.boolWord (decide (rhsVal < lhsVal))) := by
  calc
    SourceSemantics.evalExpr fields runtime (.gt lhs rhs)
        = (do
            let lhs ← SourceSemantics.evalExpr fields runtime lhs
            let rhs ← SourceSemantics.evalExpr fields runtime rhs
            pure (SourceSemantics.boolWord (decide (rhs < lhs)))) := by
              rfl
    _ = some (SourceSemantics.boolWord (decide (rhsVal < lhsVal))) := by
          simp [hlhs, hrhs]

private theorem evalExpr_add_of_values
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {lhs rhs : Expr}
    {lhsVal rhsVal : Nat}
    (hlhs : SourceSemantics.evalExpr fields runtime lhs = some lhsVal)
    (hrhs : SourceSemantics.evalExpr fields runtime rhs = some rhsVal) :
    SourceSemantics.evalExpr fields runtime (.add lhs rhs) =
      some ((((lhsVal : Verity.Core.Uint256) + (rhsVal : Verity.Core.Uint256)) :
        Verity.Core.Uint256).val) := by
  calc
    SourceSemantics.evalExpr fields runtime (.add lhs rhs)
        = (do
            let lhs ← do
              let a ← SourceSemantics.evalExpr fields runtime lhs
              pure (Verity.Core.Uint256.ofNat a)
            let rhs ← do
              let a ← SourceSemantics.evalExpr fields runtime rhs
              pure (Verity.Core.Uint256.ofNat a)
            pure (lhs + rhs).val) := by
              rfl
    _ = some ((((lhsVal : Verity.Core.Uint256) + (rhsVal : Verity.Core.Uint256)) :
          Verity.Core.Uint256).val) := by
          simp [hlhs, hrhs]

private theorem evalExpr_mul_of_values
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {lhs rhs : Expr}
    {lhsVal rhsVal : Nat}
    (hlhs : SourceSemantics.evalExpr fields runtime lhs = some lhsVal)
    (hrhs : SourceSemantics.evalExpr fields runtime rhs = some rhsVal) :
    SourceSemantics.evalExpr fields runtime (.mul lhs rhs) =
      some ((((lhsVal : Verity.Core.Uint256) * (rhsVal : Verity.Core.Uint256)) :
        Verity.Core.Uint256).val) := by
  calc
    SourceSemantics.evalExpr fields runtime (.mul lhs rhs)
        = (do
            let lhs ← do
              let a ← SourceSemantics.evalExpr fields runtime lhs
              pure (Verity.Core.Uint256.ofNat a)
            let rhs ← do
              let a ← SourceSemantics.evalExpr fields runtime rhs
              pure (Verity.Core.Uint256.ofNat a)
            pure (lhs * rhs).val) := by
              rfl
    _ = some ((((lhsVal : Verity.Core.Uint256) * (rhsVal : Verity.Core.Uint256)) :
          Verity.Core.Uint256).val) := by
          simp [hlhs, hrhs]

private theorem evalExpr_div_of_values
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {lhs rhs : Expr}
    {lhsVal rhsVal : Nat}
    (hlhs : SourceSemantics.evalExpr fields runtime lhs = some lhsVal)
    (hrhs : SourceSemantics.evalExpr fields runtime rhs = some rhsVal) :
    SourceSemantics.evalExpr fields runtime (.div lhs rhs) =
      some ((((lhsVal : Verity.Core.Uint256) / (rhsVal : Verity.Core.Uint256)) :
        Verity.Core.Uint256).val) := by
  calc
    SourceSemantics.evalExpr fields runtime (.div lhs rhs)
        = (do
            let lhs ← do
              let a ← SourceSemantics.evalExpr fields runtime lhs
              pure (Verity.Core.Uint256.ofNat a)
            let rhs ← do
              let a ← SourceSemantics.evalExpr fields runtime rhs
              pure (Verity.Core.Uint256.ofNat a)
            pure (lhs / rhs).val) := by
              rfl
    _ = some ((((lhsVal : Verity.Core.Uint256) / (rhsVal : Verity.Core.Uint256)) :
          Verity.Core.Uint256).val) := by
          simp [hlhs, hrhs]

private theorem evalExpr_sub_of_values
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {lhs rhs : Expr}
    {lhsVal rhsVal : Nat}
    (hlhs : SourceSemantics.evalExpr fields runtime lhs = some lhsVal)
    (hrhs : SourceSemantics.evalExpr fields runtime rhs = some rhsVal) :
    SourceSemantics.evalExpr fields runtime (.sub lhs rhs) =
      some ((((lhsVal : Verity.Core.Uint256) - (rhsVal : Verity.Core.Uint256)) :
        Verity.Core.Uint256).val) := by
  calc
    SourceSemantics.evalExpr fields runtime (.sub lhs rhs)
        = (do
            let lhs ← do
              let a ← SourceSemantics.evalExpr fields runtime lhs
              pure (Verity.Core.Uint256.ofNat a)
            let rhs ← do
              let a ← SourceSemantics.evalExpr fields runtime rhs
              pure (Verity.Core.Uint256.ofNat a)
            pure (lhs - rhs).val) := by
              rfl
    _ = some ((((lhsVal : Verity.Core.Uint256) - (rhsVal : Verity.Core.Uint256)) :
          Verity.Core.Uint256).val) := by
          simp [hlhs, hrhs]

private theorem evalExpr_mod_of_values
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {lhs rhs : Expr}
    {lhsVal rhsVal : Nat}
    (hlhs : SourceSemantics.evalExpr fields runtime lhs = some lhsVal)
    (hrhs : SourceSemantics.evalExpr fields runtime rhs = some rhsVal) :
    SourceSemantics.evalExpr fields runtime (.mod lhs rhs) =
      some ((((lhsVal : Verity.Core.Uint256) % (rhsVal : Verity.Core.Uint256)) :
        Verity.Core.Uint256).val) := by
  calc
    SourceSemantics.evalExpr fields runtime (.mod lhs rhs)
        = (do
            let lhs ← do
              let a ← SourceSemantics.evalExpr fields runtime lhs
              pure (Verity.Core.Uint256.ofNat a)
            let rhs ← do
              let a ← SourceSemantics.evalExpr fields runtime rhs
              pure (Verity.Core.Uint256.ofNat a)
            pure (lhs % rhs).val) := by
              rfl
    _ = some ((((lhsVal : Verity.Core.Uint256) % (rhsVal : Verity.Core.Uint256)) :
          Verity.Core.Uint256).val) := by
          simp [hlhs, hrhs]

theorem eval_compileExpr_eq_of_compiled
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhsCompile : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhsCompile : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR)
    (hlhsEval : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs))
    (hrhsEval : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs))
    (hlhsLt : SourceSemantics.evalExpr fields runtime lhs < Compiler.Constants.evmModulus)
    (hrhsLt : SourceSemantics.evalExpr fields runtime rhs < Compiler.Constants.evmModulus) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata (.eq lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
        some (SourceSemantics.evalExpr fields runtime (.eq lhs rhs)) := by
  have hcompile := compileExpr_eq_ok hlhsCompile hrhsCompile
  rcases hlhsSrc : SourceSemantics.evalExpr fields runtime lhs with _ | lhsVal
  · cases hEval : evalIRExpr state lhsIR <;> simp [hEval, hlhsSrc] at hlhsEval
  · rcases hrhsSrc : SourceSemantics.evalExpr fields runtime rhs with _ | rhsVal
    · cases hEval : evalIRExpr state rhsIR <;> simp [hEval, hrhsSrc] at hrhsEval
    · have hlhsEval' := evalIRExpr_of_sourceEval_some hlhsEval hlhsSrc
      have hrhsEval' := evalIRExpr_of_sourceEval_some hrhsEval hrhsSrc
      have hlhsLt' : lhsVal < Compiler.Constants.evmModulus := by
        simpa [hlhsSrc] using hlhsLt
      have hrhsLt' : rhsVal < Compiler.Constants.evmModulus := by
        simpa [hrhsSrc] using hrhsLt
      have heval :
          evalIRExpr state
            (CompilationModel.compileExpr fields .calldata (.eq lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
              some (SourceSemantics.boolWord
                (lhsVal % Compiler.Constants.evmModulus =
                  rhsVal % Compiler.Constants.evmModulus)) := by
        simpa [hcompile, Except.toOption, Option.getD] using evalIRExpr_eq_of_eval hlhsEval' hrhsEval'
      have hsrc := evalExpr_eq_of_values hlhsSrc hrhsSrc
      rw [heval, hsrc]
      simp [Nat.mod_eq_of_lt hlhsLt', Nat.mod_eq_of_lt hrhsLt']

theorem eval_compileExpr_lt_of_compiled
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhsCompile : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhsCompile : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR)
    (hlhsEval : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs))
    (hrhsEval : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs))
    (hlhsLt : SourceSemantics.evalExpr fields runtime lhs < Compiler.Constants.evmModulus)
    (hrhsLt : SourceSemantics.evalExpr fields runtime rhs < Compiler.Constants.evmModulus) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata (.lt lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
        some (SourceSemantics.evalExpr fields runtime (.lt lhs rhs)) := by
  have hcompile := compileExpr_lt_ok hlhsCompile hrhsCompile
  rcases hlhsSrc : SourceSemantics.evalExpr fields runtime lhs with _ | lhsVal
  · cases hEval : evalIRExpr state lhsIR <;> simp [hEval, hlhsSrc] at hlhsEval
  · rcases hrhsSrc : SourceSemantics.evalExpr fields runtime rhs with _ | rhsVal
    · cases hEval : evalIRExpr state rhsIR <;> simp [hEval, hrhsSrc] at hrhsEval
    · have hlhsEval' := evalIRExpr_of_sourceEval_some hlhsEval hlhsSrc
      have hrhsEval' := evalIRExpr_of_sourceEval_some hrhsEval hrhsSrc
      have hlhsLt' : lhsVal < Compiler.Constants.evmModulus := by
        simpa [hlhsSrc] using hlhsLt
      have hrhsLt' : rhsVal < Compiler.Constants.evmModulus := by
        simpa [hrhsSrc] using hrhsLt
      have heval :
          evalIRExpr state
            (CompilationModel.compileExpr fields .calldata (.lt lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
              some (SourceSemantics.boolWord
                (lhsVal % Compiler.Constants.evmModulus < rhsVal % Compiler.Constants.evmModulus)) := by
        simpa [hcompile, Except.toOption, Option.getD] using evalIRExpr_lt_of_eval hlhsEval' hrhsEval'
      have hsrc := evalExpr_lt_of_values hlhsSrc hrhsSrc
      rw [heval, hsrc]
      simp [Nat.mod_eq_of_lt hlhsLt', Nat.mod_eq_of_lt hrhsLt']

theorem eval_compileExpr_slt_of_compiled
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhsCompile : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhsCompile : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR)
    (hlhsEval : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs))
    (hrhsEval : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs))
    (hlhsLt : SourceSemantics.evalExpr fields runtime lhs < Compiler.Constants.evmModulus)
    (hrhsLt : SourceSemantics.evalExpr fields runtime rhs < Compiler.Constants.evmModulus) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata (.slt lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
        some (SourceSemantics.evalExpr fields runtime (.slt lhs rhs)) := by
  have hcompile := compileExpr_slt_ok hlhsCompile hrhsCompile
  rcases hlhsSrc : SourceSemantics.evalExpr fields runtime lhs with _ | lhsVal
  · cases hEval : evalIRExpr state lhsIR <;> simp [hEval, hlhsSrc] at hlhsEval
  · rcases hrhsSrc : SourceSemantics.evalExpr fields runtime rhs with _ | rhsVal
    · cases hEval : evalIRExpr state rhsIR <;> simp [hEval, hrhsSrc] at hrhsEval
    · have hlhsEval' := evalIRExpr_of_sourceEval_some hlhsEval hlhsSrc
      have hrhsEval' := evalIRExpr_of_sourceEval_some hrhsEval hrhsSrc
      have hlhsLt' : lhsVal < Compiler.Constants.evmModulus := by
        simpa [hlhsSrc] using hlhsLt
      have hrhsLt' : rhsVal < Compiler.Constants.evmModulus := by
        simpa [hrhsSrc] using hrhsLt
      have heval :
          evalIRExpr state
            (CompilationModel.compileExpr fields .calldata (.slt lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
              some (SourceSemantics.boolWord (decide (
                (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat (lhsVal % Compiler.Constants.evmModulus)) : Int) <
                (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat (rhsVal % Compiler.Constants.evmModulus)) : Int)))) := by
        simpa [hcompile, Except.toOption, Option.getD] using evalIRExpr_slt_of_eval hlhsEval' hrhsEval'
      have hsrc := evalExpr_slt_of_values hlhsSrc hrhsSrc
      rw [heval, hsrc]
      simp [Nat.mod_eq_of_lt hlhsLt', Nat.mod_eq_of_lt hrhsLt']

theorem eval_compileExpr_sgt_of_compiled
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhsCompile : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhsCompile : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR)
    (hlhsEval : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs))
    (hrhsEval : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs))
    (hlhsLt : SourceSemantics.evalExpr fields runtime lhs < Compiler.Constants.evmModulus)
    (hrhsLt : SourceSemantics.evalExpr fields runtime rhs < Compiler.Constants.evmModulus) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata (.sgt lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
        some (SourceSemantics.evalExpr fields runtime (.sgt lhs rhs)) := by
  have hcompile := compileExpr_sgt_ok hlhsCompile hrhsCompile
  rcases hlhsSrc : SourceSemantics.evalExpr fields runtime lhs with _ | lhsVal
  · cases hEval : evalIRExpr state lhsIR <;> simp [hEval, hlhsSrc] at hlhsEval
  · rcases hrhsSrc : SourceSemantics.evalExpr fields runtime rhs with _ | rhsVal
    · cases hEval : evalIRExpr state rhsIR <;> simp [hEval, hrhsSrc] at hrhsEval
    · have hlhsEval' := evalIRExpr_of_sourceEval_some hlhsEval hlhsSrc
      have hrhsEval' := evalIRExpr_of_sourceEval_some hrhsEval hrhsSrc
      have hlhsLt' : lhsVal < Compiler.Constants.evmModulus := by
        simpa [hlhsSrc] using hlhsLt
      have hrhsLt' : rhsVal < Compiler.Constants.evmModulus := by
        simpa [hrhsSrc] using hrhsLt
      have heval :
          evalIRExpr state
            (CompilationModel.compileExpr fields .calldata (.sgt lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
              some (SourceSemantics.boolWord (decide (
                (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat (rhsVal % Compiler.Constants.evmModulus)) : Int) <
                (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat (lhsVal % Compiler.Constants.evmModulus)) : Int)))) := by
        simpa [hcompile, Except.toOption, Option.getD] using evalIRExpr_sgt_of_eval hlhsEval' hrhsEval'
      have hsrc := evalExpr_sgt_of_values hlhsSrc hrhsSrc
      rw [heval, hsrc]
      simp [Nat.mod_eq_of_lt hlhsLt', Nat.mod_eq_of_lt hrhsLt']

theorem eval_compileExpr_sdiv_of_compiled
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhsCompile : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhsCompile : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR)
    (hlhsEval : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs))
    (hrhsEval : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs))
    (hlhsLt : SourceSemantics.evalExpr fields runtime lhs < Compiler.Constants.evmModulus)
    (hrhsLt : SourceSemantics.evalExpr fields runtime rhs < Compiler.Constants.evmModulus) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata (.sdiv lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
        some (SourceSemantics.evalExpr fields runtime (.sdiv lhs rhs)) := by
  have hcompile := compileExpr_sdiv_ok hlhsCompile hrhsCompile
  rcases hlhsSrc : SourceSemantics.evalExpr fields runtime lhs with _ | lhsVal
  · cases hEval : evalIRExpr state lhsIR <;> simp [hEval, hlhsSrc] at hlhsEval
  · rcases hrhsSrc : SourceSemantics.evalExpr fields runtime rhs with _ | rhsVal
    · cases hEval : evalIRExpr state rhsIR <;> simp [hEval, hrhsSrc] at hrhsEval
    · have hlhsEval' := evalIRExpr_of_sourceEval_some hlhsEval hlhsSrc
      have hrhsEval' := evalIRExpr_of_sourceEval_some hrhsEval hrhsSrc
      have hlhsLt' : lhsVal < Compiler.Constants.evmModulus := by
        simpa [hlhsSrc] using hlhsLt
      have hrhsLt' : rhsVal < Compiler.Constants.evmModulus := by
        simpa [hrhsSrc] using hrhsLt
      have heval :
          evalIRExpr state
            (CompilationModel.compileExpr fields .calldata (.sdiv lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
              some (Verity.Core.Int256.div
                (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat (lhsVal % Compiler.Constants.evmModulus)))
                (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat (rhsVal % Compiler.Constants.evmModulus)))).toUint256.val := by
        simpa [hcompile, Except.toOption, Option.getD] using evalIRExpr_sdiv_of_eval hlhsEval' hrhsEval'
      have hsrc := evalExpr_sdiv_of_values hlhsSrc hrhsSrc
      rw [heval, hsrc]
      simp [Nat.mod_eq_of_lt hlhsLt', Nat.mod_eq_of_lt hrhsLt']

theorem eval_compileExpr_smod_of_compiled
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhsCompile : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhsCompile : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR)
    (hlhsEval : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs))
    (hrhsEval : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs))
    (hlhsLt : SourceSemantics.evalExpr fields runtime lhs < Compiler.Constants.evmModulus)
    (hrhsLt : SourceSemantics.evalExpr fields runtime rhs < Compiler.Constants.evmModulus) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata (.smod lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
        some (SourceSemantics.evalExpr fields runtime (.smod lhs rhs)) := by
  have hcompile := compileExpr_smod_ok hlhsCompile hrhsCompile
  rcases hlhsSrc : SourceSemantics.evalExpr fields runtime lhs with _ | lhsVal
  · cases hEval : evalIRExpr state lhsIR <;> simp [hEval, hlhsSrc] at hlhsEval
  · rcases hrhsSrc : SourceSemantics.evalExpr fields runtime rhs with _ | rhsVal
    · cases hEval : evalIRExpr state rhsIR <;> simp [hEval, hrhsSrc] at hrhsEval
    · have hlhsEval' := evalIRExpr_of_sourceEval_some hlhsEval hlhsSrc
      have hrhsEval' := evalIRExpr_of_sourceEval_some hrhsEval hrhsSrc
      have hlhsLt' : lhsVal < Compiler.Constants.evmModulus := by
        simpa [hlhsSrc] using hlhsLt
      have hrhsLt' : rhsVal < Compiler.Constants.evmModulus := by
        simpa [hrhsSrc] using hrhsLt
      have heval :
          evalIRExpr state
            (CompilationModel.compileExpr fields .calldata (.smod lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
              some (Verity.Core.Int256.mod
                (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat (lhsVal % Compiler.Constants.evmModulus)))
                (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat (rhsVal % Compiler.Constants.evmModulus)))).toUint256.val := by
        simpa [hcompile, Except.toOption, Option.getD] using evalIRExpr_smod_of_eval hlhsEval' hrhsEval'
      have hsrc := evalExpr_smod_of_values hlhsSrc hrhsSrc
      rw [heval, hsrc]
      simp [Nat.mod_eq_of_lt hlhsLt', Nat.mod_eq_of_lt hrhsLt']

theorem eval_compileExpr_sar_of_compiled
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhsCompile : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhsCompile : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR)
    (hlhsEval : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs))
    (hrhsEval : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs))
    (hlhsLt : SourceSemantics.evalExpr fields runtime lhs < Compiler.Constants.evmModulus)
    (hrhsLt : SourceSemantics.evalExpr fields runtime rhs < Compiler.Constants.evmModulus) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata (.sar lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
        some (SourceSemantics.evalExpr fields runtime (.sar lhs rhs)) := by
  have hcompile := compileExpr_sar_ok hlhsCompile hrhsCompile
  rcases hlhsSrc : SourceSemantics.evalExpr fields runtime lhs with _ | lhsVal
  · cases hEval : evalIRExpr state lhsIR <;> simp [hEval, hlhsSrc] at hlhsEval
  · rcases hrhsSrc : SourceSemantics.evalExpr fields runtime rhs with _ | rhsVal
    · cases hEval : evalIRExpr state rhsIR <;> simp [hEval, hrhsSrc] at hrhsEval
    · have hlhsEval' := evalIRExpr_of_sourceEval_some hlhsEval hlhsSrc
      have hrhsEval' := evalIRExpr_of_sourceEval_some hrhsEval hrhsSrc
      have hlhsLt' : lhsVal < Compiler.Constants.evmModulus := by
        simpa [hlhsSrc] using hlhsLt
      have hrhsLt' : rhsVal < Compiler.Constants.evmModulus := by
        simpa [hrhsSrc] using hrhsLt
      have heval :
          evalIRExpr state
            (CompilationModel.compileExpr fields .calldata (.sar lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
              some (Verity.Core.Int256.sar
                (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat (lhsVal % Compiler.Constants.evmModulus)))
                (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat (rhsVal % Compiler.Constants.evmModulus)))).toUint256.val := by
        simpa [hcompile, Except.toOption, Option.getD] using evalIRExpr_sar_of_eval hlhsEval' hrhsEval'
      have hsrc := evalExpr_sar_of_values hlhsSrc hrhsSrc
      rw [heval, hsrc]
      simp [Nat.mod_eq_of_lt hlhsLt', Nat.mod_eq_of_lt hrhsLt']

theorem eval_compileExpr_byte_of_compiled
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {index value : Expr}
    {indexIR valueIR : YulExpr}
    (hindexCompile : CompilationModel.compileExpr fields .calldata index = Except.ok indexIR)
    (hvalueCompile : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR)
    (hindexEval : evalIRExpr state indexIR = some (SourceSemantics.evalExpr fields runtime index))
    (hvalueEval : evalIRExpr state valueIR = some (SourceSemantics.evalExpr fields runtime value))
    (hindexLt : SourceSemantics.evalExpr fields runtime index < Compiler.Constants.evmModulus)
    (hvalueLt : SourceSemantics.evalExpr fields runtime value < Compiler.Constants.evmModulus) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata (.byte index value) |>.toOption.getD (YulExpr.lit 0)) =
        some (SourceSemantics.evalExpr fields runtime (.byte index value)) := by
  have hcompile := compileExpr_byte_ok hindexCompile hvalueCompile
  rcases hindexSrc : SourceSemantics.evalExpr fields runtime index with _ | indexVal
  · cases hEval : evalIRExpr state indexIR <;> simp [hEval, hindexSrc] at hindexEval
  · rcases hvalueSrc : SourceSemantics.evalExpr fields runtime value with _ | valueVal
    · cases hEval : evalIRExpr state valueIR <;> simp [hEval, hvalueSrc] at hvalueEval
    · have hindexEval' := evalIRExpr_of_sourceEval_some hindexEval hindexSrc
      have hvalueEval' := evalIRExpr_of_sourceEval_some hvalueEval hvalueSrc
      have hindexLt' : indexVal < Compiler.Constants.evmModulus := by
        simpa [hindexSrc] using hindexLt
      have hvalueLt' : valueVal < Compiler.Constants.evmModulus := by
        simpa [hvalueSrc] using hvalueLt
      have heval :
          evalIRExpr state
            (CompilationModel.compileExpr fields .calldata (.byte index value) |>.toOption.getD (YulExpr.lit 0)) =
              some (Verity.Core.Uint256.byte
                (Verity.Core.Uint256.ofNat (indexVal % Compiler.Constants.evmModulus))
                (Verity.Core.Uint256.ofNat (valueVal % Compiler.Constants.evmModulus))).val := by
        simpa [hcompile, Except.toOption, Option.getD] using evalIRExpr_byte_of_eval hindexEval' hvalueEval'
      have hsrc := evalExpr_byte_of_values hindexSrc hvalueSrc
      rw [heval, hsrc]
      simp [Nat.mod_eq_of_lt hindexLt', Nat.mod_eq_of_lt hvalueLt']

theorem eval_compileExpr_signextend_of_compiled
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhsCompile : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhsCompile : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR)
    (hlhsEval : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs))
    (hrhsEval : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs))
    (hlhsLt : SourceSemantics.evalExpr fields runtime lhs < Compiler.Constants.evmModulus)
    (hrhsLt : SourceSemantics.evalExpr fields runtime rhs < Compiler.Constants.evmModulus) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata (.signextend lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
        some (SourceSemantics.evalExpr fields runtime (.signextend lhs rhs)) := by
  have hcompile := compileExpr_signextend_ok hlhsCompile hrhsCompile
  rcases hlhsSrc : SourceSemantics.evalExpr fields runtime lhs with _ | lhsVal
  · cases hEval : evalIRExpr state lhsIR <;> simp [hEval, hlhsSrc] at hlhsEval
  · rcases hrhsSrc : SourceSemantics.evalExpr fields runtime rhs with _ | rhsVal
    · cases hEval : evalIRExpr state rhsIR <;> simp [hEval, hrhsSrc] at hrhsEval
    · have hlhsEval' := evalIRExpr_of_sourceEval_some hlhsEval hlhsSrc
      have hrhsEval' := evalIRExpr_of_sourceEval_some hrhsEval hrhsSrc
      have hlhsLt' : lhsVal < Compiler.Constants.evmModulus := by
        simpa [hlhsSrc] using hlhsLt
      have hrhsLt' : rhsVal < Compiler.Constants.evmModulus := by
        simpa [hrhsSrc] using hrhsLt
      have heval :
          evalIRExpr state
            (CompilationModel.compileExpr fields .calldata (.signextend lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
              some (Verity.Core.Uint256.signextend
                (Verity.Core.Uint256.ofNat (lhsVal % Compiler.Constants.evmModulus))
                (Verity.Core.Uint256.ofNat (rhsVal % Compiler.Constants.evmModulus))).val := by
        simpa [hcompile, Except.toOption, Option.getD] using evalIRExpr_signextend_of_eval hlhsEval' hrhsEval'
      have hsrc := evalExpr_signextend_of_values hlhsSrc hrhsSrc
      rw [heval, hsrc]
      simp [Nat.mod_eq_of_lt hlhsLt', Nat.mod_eq_of_lt hrhsLt']

theorem eval_compileExpr_gt_of_compiled
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhsCompile : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhsCompile : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR)
    (hlhsEval : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs))
    (hrhsEval : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs))
    (hlhsLt : SourceSemantics.evalExpr fields runtime lhs < Compiler.Constants.evmModulus)
    (hrhsLt : SourceSemantics.evalExpr fields runtime rhs < Compiler.Constants.evmModulus) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata (.gt lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
        some (SourceSemantics.evalExpr fields runtime (.gt lhs rhs)) := by
  have hcompile := compileExpr_gt_ok hlhsCompile hrhsCompile
  rcases hlhsSrc : SourceSemantics.evalExpr fields runtime lhs with _ | lhsVal
  · cases hEval : evalIRExpr state lhsIR <;> simp [hEval, hlhsSrc] at hlhsEval
  · rcases hrhsSrc : SourceSemantics.evalExpr fields runtime rhs with _ | rhsVal
    · cases hEval : evalIRExpr state rhsIR <;> simp [hEval, hrhsSrc] at hrhsEval
    · have hlhsEval' := evalIRExpr_of_sourceEval_some hlhsEval hlhsSrc
      have hrhsEval' := evalIRExpr_of_sourceEval_some hrhsEval hrhsSrc
      have hlhsLt' : lhsVal < Compiler.Constants.evmModulus := by
        simpa [hlhsSrc] using hlhsLt
      have hrhsLt' : rhsVal < Compiler.Constants.evmModulus := by
        simpa [hrhsSrc] using hrhsLt
      have heval :
          evalIRExpr state
            (CompilationModel.compileExpr fields .calldata (.gt lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
              some (SourceSemantics.boolWord
                (rhsVal % Compiler.Constants.evmModulus <
                  lhsVal % Compiler.Constants.evmModulus)) := by
        simpa [hcompile, Except.toOption, Option.getD] using evalIRExpr_gt_of_eval hlhsEval' hrhsEval'
      have hsrc := evalExpr_gt_of_values hlhsSrc hrhsSrc
      rw [heval, hsrc]
      simp [Nat.mod_eq_of_lt hlhsLt', Nat.mod_eq_of_lt hrhsLt']

theorem eval_compileExpr_ge_of_compiled {fields : List Field} {runtime : SourceSemantics.RuntimeState}
    {state : IRState} {lhs rhs : Expr} {lhsIR rhsIR : YulExpr}
    (hlhsCompile : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhsCompile : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR)
    (hlhsEval : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs))
    (hrhsEval : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs))
    (hlhsLt : SourceSemantics.evalExpr fields runtime lhs < Compiler.Constants.evmModulus)
    (hrhsLt : SourceSemantics.evalExpr fields runtime rhs < Compiler.Constants.evmModulus) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata (.ge lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
        some (SourceSemantics.evalExpr fields runtime (.ge lhs rhs)) := by
  rcases hlhsSrc : SourceSemantics.evalExpr fields runtime lhs with _ | lhsVal
  · cases hEval : evalIRExpr state lhsIR <;> simp [hEval, hlhsSrc] at hlhsEval
  · rcases hrhsSrc : SourceSemantics.evalExpr fields runtime rhs with _ | rhsVal
    · cases hEval : evalIRExpr state rhsIR <;> simp [hEval, hrhsSrc] at hrhsEval
    · have hlhsLt' : lhsVal < Compiler.Constants.evmModulus := by
        simpa [hlhsSrc] using hlhsLt
      have hrhsLt' : rhsVal < Compiler.Constants.evmModulus := by
        simpa [hrhsSrc] using hrhsLt
      have heval :=
        eval_compileExpr_ge_raw
          (hlhsCompile := hlhsCompile)
          (hrhsCompile := hrhsCompile)
          (hlhsEval := hlhsEval)
          (hrhsEval := hrhsEval)
      have hsrc :
          SourceSemantics.evalExpr fields runtime (.ge lhs rhs) =
            some (SourceSemantics.boolWord (decide (rhsVal ≤ lhsVal))) := by
        calc
          SourceSemantics.evalExpr fields runtime (.ge lhs rhs)
              = (do
                  let lhs ← SourceSemantics.evalExpr fields runtime lhs
                  let rhs ← SourceSemantics.evalExpr fields runtime rhs
                  pure (SourceSemantics.boolWord (decide (rhs ≤ lhs)))) := by
                    rfl
          _ = some (SourceSemantics.boolWord (decide (rhsVal ≤ lhsVal))) := by
                simp [hlhsSrc, hrhsSrc]
      rw [heval, hsrc]
      simp [hlhsSrc, hrhsSrc, Nat.mod_eq_of_lt hlhsLt', Nat.mod_eq_of_lt hrhsLt']

theorem eval_compileExpr_le_of_compiled {fields : List Field} {runtime : SourceSemantics.RuntimeState}
    {state : IRState} {lhs rhs : Expr} {lhsIR rhsIR : YulExpr}
    (hlhsCompile : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhsCompile : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR)
    (hlhsEval : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs))
    (hrhsEval : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs))
    (hlhsLt : SourceSemantics.evalExpr fields runtime lhs < Compiler.Constants.evmModulus)
    (hrhsLt : SourceSemantics.evalExpr fields runtime rhs < Compiler.Constants.evmModulus) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata (.le lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
        some (SourceSemantics.evalExpr fields runtime (.le lhs rhs)) := by
  rcases hlhsSrc : SourceSemantics.evalExpr fields runtime lhs with _ | lhsVal
  · cases hEval : evalIRExpr state lhsIR <;> simp [hEval, hlhsSrc] at hlhsEval
  · rcases hrhsSrc : SourceSemantics.evalExpr fields runtime rhs with _ | rhsVal
    · cases hEval : evalIRExpr state rhsIR <;> simp [hEval, hrhsSrc] at hrhsEval
    · have hlhsLt' : lhsVal < Compiler.Constants.evmModulus := by
        simpa [hlhsSrc] using hlhsLt
      have hrhsLt' : rhsVal < Compiler.Constants.evmModulus := by
        simpa [hrhsSrc] using hrhsLt
      have heval :=
        eval_compileExpr_le_raw
          (hlhsCompile := hlhsCompile)
          (hrhsCompile := hrhsCompile)
          (hlhsEval := hlhsEval)
          (hrhsEval := hrhsEval)
      have hsrc :
          SourceSemantics.evalExpr fields runtime (.le lhs rhs) =
            some (SourceSemantics.boolWord (decide (lhsVal ≤ rhsVal))) := by
        calc
          SourceSemantics.evalExpr fields runtime (.le lhs rhs)
              = (do
                  let lhs ← SourceSemantics.evalExpr fields runtime lhs
                  let rhs ← SourceSemantics.evalExpr fields runtime rhs
                  pure (SourceSemantics.boolWord (decide (lhs ≤ rhs)))) := by
                    rfl
          _ = some (SourceSemantics.boolWord (decide (lhsVal ≤ rhsVal))) := by
                simp [hlhsSrc, hrhsSrc]
      rw [heval, hsrc]
      rw [hlhsSrc, hrhsSrc]
      simpa using congrArg some (boolWord_iszero_gt_eq_le lhsVal rhsVal hlhsLt' hrhsLt')

theorem eval_compileExpr_logicalNot_of_compiled
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {expr : Expr}
    {exprIR : YulExpr}
    (hexprCompile : CompilationModel.compileExpr fields .calldata expr = Except.ok exprIR)
    (hexprEval : evalIRExpr state exprIR = some (SourceSemantics.evalExpr fields runtime expr))
    (hexprLt : SourceSemantics.evalExpr fields runtime expr < Compiler.Constants.evmModulus) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata (.logicalNot expr) |>.toOption.getD (YulExpr.lit 0)) =
        some (SourceSemantics.evalExpr fields runtime (.logicalNot expr)) := by
  have hcompile := compileExpr_logicalNot_ok hexprCompile
  rcases hexprSrc : SourceSemantics.evalExpr fields runtime expr with _ | exprVal
  · cases hEval : evalIRExpr state exprIR <;> simp [hEval, hexprSrc] at hexprEval
  · have hexprEval' : evalIRExpr state exprIR = some exprVal := by
      cases hEval : evalIRExpr state exprIR with
      | none =>
          simp [hEval, hexprSrc] at hexprEval
      | some val =>
          simp [hEval, hexprSrc] at hexprEval
          simpa [hexprEval] using hEval
    have hexprLt' : exprVal < Compiler.Constants.evmModulus := by
      simpa [hexprSrc] using hexprLt
    rw [hcompile]
    have hiszero :=
      evalIRExpr_iszero_of_lt (heval := hexprEval') (hvalueLt := hexprLt')
    have hsrcNot :
        SourceSemantics.evalExpr fields runtime (.logicalNot expr) =
          some (if exprVal = 0 then 1 else 0) := by
      calc
        SourceSemantics.evalExpr fields runtime (.logicalNot expr)
          = (do
              let value ← SourceSemantics.evalExpr fields runtime expr
              pure (SourceSemantics.boolWord (decide (value = 0)))) := by
                rfl
        _ = some (SourceSemantics.boolWord (decide (exprVal = 0))) := by
              simp [hexprSrc]
        _ = some (if exprVal = 0 then 1 else 0) := by
              simp [boolWord_eq_if]
    calc
      (evalIRExpr state (YulExpr.call "iszero" [exprIR])).bind (fun a => some (some a))
        = some (some (SourceSemantics.boolWord (decide (exprVal = 0)))) := by
            simp [hiszero]
      _ = some (SourceSemantics.evalExpr fields runtime (.logicalNot expr)) := by
            rw [hsrcNot]
            simp [boolWord_eq_if]

private theorem evalExpr_logicalAnd_of_values
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {lhs rhs : Expr}
    {lhsVal rhsVal : Nat}
    (hlhs : SourceSemantics.evalExpr fields runtime lhs = some lhsVal)
    (hrhs : SourceSemantics.evalExpr fields runtime rhs = some rhsVal) :
    SourceSemantics.evalExpr fields runtime (.logicalAnd lhs rhs) =
      some (SourceSemantics.boolWord (decide (lhsVal != 0) && decide (rhsVal != 0))) := by
  calc
    SourceSemantics.evalExpr fields runtime (.logicalAnd lhs rhs)
        = (do
            let lhs ← SourceSemantics.evalExpr fields runtime lhs
            let rhs ← SourceSemantics.evalExpr fields runtime rhs
            pure (SourceSemantics.boolWord (decide (lhs != 0) && decide (rhs != 0)))) := rfl
    _ = _ := by simp [hlhs, hrhs]

private theorem evalIRExpr_and_yulToBool_of_lt
    {state : IRState}
    {lhsIR rhsIR : YulExpr}
    {lhsVal rhsVal : Nat}
    (hlhs : evalIRExpr state lhsIR = some lhsVal)
    (hrhs : evalIRExpr state rhsIR = some rhsVal)
    (hlhsLt : lhsVal < Compiler.Constants.evmModulus)
    (hrhsLt : rhsVal < Compiler.Constants.evmModulus) :
    evalIRExpr state (YulExpr.call "and"
        [CompilationModel.yulToBool lhsIR, CompilationModel.yulToBool rhsIR]) =
      some ((SourceSemantics.boolWord (lhsVal ≠ 0)) &&&
        (SourceSemantics.boolWord (rhsVal ≠ 0))) := by
  have hlhsBool :
      evalIRExpr state (CompilationModel.yulToBool lhsIR) =
        some (SourceSemantics.boolWord (lhsVal ≠ 0)) := by
    simpa using evalIRExpr_yulToBool_of_lt hlhs hlhsLt
  have hrhsBool :
      evalIRExpr state (CompilationModel.yulToBool rhsIR) =
        some (SourceSemantics.boolWord (rhsVal ≠ 0)) := by
    simpa using evalIRExpr_yulToBool_of_lt hrhs hrhsLt
  simpa only
    [Nat.mod_eq_of_lt (boolWord_lt_evmModulus (decide (lhsVal ≠ 0))),
    Nat.mod_eq_of_lt (boolWord_lt_evmModulus (decide (rhsVal ≠ 0)))] using
    evalIRExpr_and_of_eval hlhsBool hrhsBool

theorem eval_compileExpr_logicalAnd_of_compiled
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhsCompile : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhsCompile : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR)
    (hlhsEval : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs))
    (hrhsEval : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs))
    (hlhsLt : SourceSemantics.evalExpr fields runtime lhs < Compiler.Constants.evmModulus)
    (hrhsLt : SourceSemantics.evalExpr fields runtime rhs < Compiler.Constants.evmModulus) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata (.logicalAnd lhs rhs) |>.toOption.getD
        (YulExpr.lit 0)) =
        some (SourceSemantics.evalExpr fields runtime (.logicalAnd lhs rhs)) := by
  obtain ⟨lhsVal, hlhsSrc, hlhsEval', hlhsLt'⟩ := exists_source_value_of_evalIRExpr hlhsEval hlhsLt
  obtain ⟨rhsVal, hrhsSrc, hrhsEval', hrhsLt'⟩ := exists_source_value_of_evalIRExpr hrhsEval hrhsLt
  have heval :
      evalIRExpr state
        (CompilationModel.compileExpr fields .calldata (.logicalAnd lhs rhs) |>.toOption.getD
          (YulExpr.lit 0)) =
        some ((SourceSemantics.boolWord (lhsVal ≠ 0)) &&&
          (SourceSemantics.boolWord (rhsVal ≠ 0))) := by
    simpa [compileExpr_logicalAnd_ok hlhsCompile hrhsCompile, Except.toOption, Option.getD] using
      evalIRExpr_and_yulToBool_of_lt hlhsEval' hrhsEval' hlhsLt' hrhsLt'
  rw [heval, evalExpr_logicalAnd_of_values hlhsSrc hrhsSrc]
  simp [boolWord_and]

private theorem evalExpr_logicalOr_of_values
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {lhs rhs : Expr}
    {lhsVal rhsVal : Nat}
    (hlhs : SourceSemantics.evalExpr fields runtime lhs = some lhsVal)
    (hrhs : SourceSemantics.evalExpr fields runtime rhs = some rhsVal) :
    SourceSemantics.evalExpr fields runtime (.logicalOr lhs rhs) =
      some (SourceSemantics.boolWord (decide (lhsVal != 0) || decide (rhsVal != 0))) := by
  calc
    SourceSemantics.evalExpr fields runtime (.logicalOr lhs rhs)
        = (do
            let lhs ← SourceSemantics.evalExpr fields runtime lhs
            let rhs ← SourceSemantics.evalExpr fields runtime rhs
            pure (SourceSemantics.boolWord (decide (lhs != 0) || decide (rhs != 0)))) := rfl
    _ = _ := by simp [hlhs, hrhs]

private theorem evalIRExpr_or_yulToBool_of_lt
    {state : IRState}
    {lhsIR rhsIR : YulExpr}
    {lhsVal rhsVal : Nat}
    (hlhs : evalIRExpr state lhsIR = some lhsVal)
    (hrhs : evalIRExpr state rhsIR = some rhsVal)
    (hlhsLt : lhsVal < Compiler.Constants.evmModulus)
    (hrhsLt : rhsVal < Compiler.Constants.evmModulus) :
    evalIRExpr state (YulExpr.call "or"
        [CompilationModel.yulToBool lhsIR, CompilationModel.yulToBool rhsIR]) =
      some ((SourceSemantics.boolWord (lhsVal ≠ 0)) |||
        (SourceSemantics.boolWord (rhsVal ≠ 0))) := by
  have hlhsBool :
      evalIRExpr state (CompilationModel.yulToBool lhsIR) =
        some (SourceSemantics.boolWord (lhsVal ≠ 0)) := by
    simpa using evalIRExpr_yulToBool_of_lt hlhs hlhsLt
  have hrhsBool :
      evalIRExpr state (CompilationModel.yulToBool rhsIR) =
        some (SourceSemantics.boolWord (rhsVal ≠ 0)) := by
    simpa using evalIRExpr_yulToBool_of_lt hrhs hrhsLt
  simpa only
    [Nat.mod_eq_of_lt (boolWord_lt_evmModulus (decide (lhsVal ≠ 0))),
    Nat.mod_eq_of_lt (boolWord_lt_evmModulus (decide (rhsVal ≠ 0)))] using
    evalIRExpr_or_of_eval hlhsBool hrhsBool

theorem eval_compileExpr_logicalOr_of_compiled
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhsCompile : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhsCompile : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR)
    (hlhsEval : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs))
    (hrhsEval : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs))
    (hlhsLt : SourceSemantics.evalExpr fields runtime lhs < Compiler.Constants.evmModulus)
    (hrhsLt : SourceSemantics.evalExpr fields runtime rhs < Compiler.Constants.evmModulus) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata (.logicalOr lhs rhs) |>.toOption.getD
        (YulExpr.lit 0)) =
        some (SourceSemantics.evalExpr fields runtime (.logicalOr lhs rhs)) := by
  obtain ⟨lhsVal, hlhsSrc, hlhsEval', hlhsLt'⟩ := exists_source_value_of_evalIRExpr hlhsEval hlhsLt
  obtain ⟨rhsVal, hrhsSrc, hrhsEval', hrhsLt'⟩ := exists_source_value_of_evalIRExpr hrhsEval hrhsLt
  have heval :
      evalIRExpr state
        (CompilationModel.compileExpr fields .calldata (.logicalOr lhs rhs) |>.toOption.getD
          (YulExpr.lit 0)) =
        some ((SourceSemantics.boolWord (lhsVal ≠ 0)) |||
          (SourceSemantics.boolWord (rhsVal ≠ 0))) := by
    simpa [compileExpr_logicalOr_ok hlhsCompile hrhsCompile, Except.toOption, Option.getD] using
      evalIRExpr_or_yulToBool_of_lt hlhsEval' hrhsEval' hlhsLt' hrhsLt'
  rw [heval, evalExpr_logicalOr_of_values hlhsSrc hrhsSrc]
  simp [boolWord_or]

theorem eval_compileExpr_add_of_compiled
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhsCompile : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhsCompile : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR)
    (hlhsEval : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs))
    (hrhsEval : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs)) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata (.add lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
        some (SourceSemantics.evalExpr fields runtime (.add lhs rhs)) := by
  have hcompile := compileExpr_add_ok hlhsCompile hrhsCompile
  rcases hlhsSrc : SourceSemantics.evalExpr fields runtime lhs with _ | lhsVal
  · cases hEval : evalIRExpr state lhsIR <;> simp [hEval, hlhsSrc] at hlhsEval
  · rcases hrhsSrc : SourceSemantics.evalExpr fields runtime rhs with _ | rhsVal
    · cases hEval : evalIRExpr state rhsIR <;> simp [hEval, hrhsSrc] at hrhsEval
    · have hlhsEval' := evalIRExpr_of_sourceEval_some hlhsEval hlhsSrc
      have hrhsEval' := evalIRExpr_of_sourceEval_some hrhsEval hrhsSrc
      have heval :
          evalIRExpr state
            (CompilationModel.compileExpr fields .calldata (.add lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
              some ((lhsVal + rhsVal) % Compiler.Constants.evmModulus) := by
        simpa [hcompile, Except.toOption, Option.getD] using evalIRExpr_add_of_eval hlhsEval' hrhsEval'
      have hsrc := evalExpr_add_of_values hlhsSrc hrhsSrc
      rw [heval, hsrc]
      simp [HAdd.hAdd, Verity.Core.Uint256.add, Verity.Core.Uint256.ofNat,
        Verity.Core.Uint256.modulus, Compiler.Constants.evmModulus,
        Verity.Core.UINT256_MODULUS]
      simpa [Add.add] using (Nat.add_mod lhsVal rhsVal Compiler.Constants.evmModulus).symm

theorem eval_compileExpr_mul_of_compiled
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhsCompile : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhsCompile : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR)
    (hlhsEval : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs))
    (hrhsEval : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs)) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata (.mul lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
        some (SourceSemantics.evalExpr fields runtime (.mul lhs rhs)) := by
  have hcompile := compileExpr_mul_ok hlhsCompile hrhsCompile
  rcases hlhsSrc : SourceSemantics.evalExpr fields runtime lhs with _ | lhsVal
  · cases hEval : evalIRExpr state lhsIR <;> simp [hEval, hlhsSrc] at hlhsEval
  · rcases hrhsSrc : SourceSemantics.evalExpr fields runtime rhs with _ | rhsVal
    · cases hEval : evalIRExpr state rhsIR <;> simp [hEval, hrhsSrc] at hrhsEval
    · have hlhsEval' := evalIRExpr_of_sourceEval_some hlhsEval hlhsSrc
      have hrhsEval' := evalIRExpr_of_sourceEval_some hrhsEval hrhsSrc
      have heval :
          evalIRExpr state
            (CompilationModel.compileExpr fields .calldata (.mul lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
              some ((lhsVal * rhsVal) % Compiler.Constants.evmModulus) := by
        simpa [hcompile, Except.toOption, Option.getD] using evalIRExpr_mul_of_eval hlhsEval' hrhsEval'
      have hsrc := evalExpr_mul_of_values hlhsSrc hrhsSrc
      rw [heval, hsrc]
      simp [HMul.hMul, Verity.Core.Uint256.mul, Verity.Core.Uint256.ofNat,
        Verity.Core.Uint256.modulus, Compiler.Constants.evmModulus,
        Verity.Core.UINT256_MODULUS]
      simpa [Mul.mul] using (Nat.mul_mod lhsVal rhsVal Compiler.Constants.evmModulus).symm
theorem uint256_val_ofNat_eq
    {n : Nat}
    (hn : n < Compiler.Constants.evmModulus) :
    ((n : Verity.Core.Uint256)).val = n := by
  rw [show ((n : Verity.Core.Uint256)).val = n % Compiler.Constants.evmModulus by rfl]
  exact Nat.mod_eq_of_lt hn

/-- Division on in-range `Nat` values agrees with `Uint256.div`. -/
theorem uint256_div_val_eq
    {a b : Nat}
    (ha : a < Compiler.Constants.evmModulus)
    (hb : b < Compiler.Constants.evmModulus) :
    (((a : Verity.Core.Uint256) / (b : Verity.Core.Uint256)) : Verity.Core.Uint256).val =
      if b = 0 then 0 else a / b := by
  by_cases hzero : b = 0
  · subst hzero
    simp [HDiv.hDiv, Verity.Core.Uint256.div, Verity.Core.Uint256.ofNat]
  · have hdivLt : a / b < Compiler.Constants.evmModulus := by
      exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha
    have hdivMod : (a / b) % Compiler.Constants.evmModulus = a / b :=
      Nat.mod_eq_of_lt hdivLt
    simpa [HDiv.hDiv, Verity.Core.Uint256.div, Verity.Core.Uint256.ofNat,
      Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, hzero] using hdivMod

/-- Subtraction on in-range `Nat` values agrees with `Uint256.sub`. -/
theorem uint256_sub_val_eq
    {a b : Nat}
    (ha : a < Compiler.Constants.evmModulus)
    (hb : b < Compiler.Constants.evmModulus) :
    (((a : Verity.Core.Uint256) - (b : Verity.Core.Uint256)) : Verity.Core.Uint256).val =
      (Compiler.Constants.evmModulus + a - b) % Compiler.Constants.evmModulus := by
  change (Verity.Core.Uint256.sub (a : Verity.Core.Uint256) (b : Verity.Core.Uint256)).val =
    (Compiler.Constants.evmModulus + a - b) % Compiler.Constants.evmModulus
  by_cases hle : b ≤ a
  · have hsubLt : a - b < Compiler.Constants.evmModulus := by
      exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) ha
    have hsum : Compiler.Constants.evmModulus + a - b =
        Compiler.Constants.evmModulus + (a - b) := by
      omega
    simp [Verity.Core.Uint256.sub, Verity.Core.Uint256.ofNat,
      Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, hle]
    rw [hsum]
    simpa [Nat.mod_eq_of_lt hsubLt] using
      Nat.add_mod_right_right (a - b) Compiler.Constants.evmModulus
  · have hgt : b > a := Nat.lt_of_not_ge hle
    have hsubLt : a - b < Compiler.Constants.evmModulus := by
      exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) ha
    have hdiffPos : 0 < b - a := Nat.sub_pos_of_lt hgt
    have hdiffLe : b - a ≤ Compiler.Constants.evmModulus := by
      exact Nat.le_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hb)
    have hdiffLt : Compiler.Constants.evmModulus - (b - a) < Compiler.Constants.evmModulus := by
      omega
    have hsum : Compiler.Constants.evmModulus + a - b =
        Compiler.Constants.evmModulus - (b - a) := by
      omega
    simp [Verity.Core.Uint256.sub, Verity.Core.Uint256.ofNat,
      Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, hle, hsum, Nat.mod_eq_of_lt hdiffLt]

/-- Modulo on in-range `Nat` values agrees with `Uint256.mod`. -/
theorem uint256_mod_val_eq
    {a b : Nat}
    (ha : a < Compiler.Constants.evmModulus)
    (hb : b < Compiler.Constants.evmModulus) :
    (((a : Verity.Core.Uint256) % (b : Verity.Core.Uint256)) : Verity.Core.Uint256).val =
      if b = 0 then 0 else a % b := by
  change (Verity.Core.Uint256.mod (a : Verity.Core.Uint256) (b : Verity.Core.Uint256)).val =
    if b = 0 then 0 else a % b
  by_cases hzero : b = 0
  · subst hzero
    simp [Verity.Core.Uint256.mod, Verity.Core.Uint256.ofNat]
  · have hbpos : 0 < b := Nat.pos_of_ne_zero hzero
    have hmodLt : a % b < Compiler.Constants.evmModulus := by
      exact Nat.lt_trans (Nat.mod_lt _ hbpos) hb
    simp [Verity.Core.Uint256.mod, Verity.Core.Uint256.ofNat]
    rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
    simp [hzero, Nat.mod_eq_of_lt hmodLt]

theorem eval_compileExpr_div_of_compiled
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhsCompile : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhsCompile : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR)
    (hlhsEval : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs))
    (hrhsEval : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs))
    (hlhsLt : SourceSemantics.evalExpr fields runtime lhs < Compiler.Constants.evmModulus)
    (hrhsLt : SourceSemantics.evalExpr fields runtime rhs < Compiler.Constants.evmModulus) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata (.div lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
        some (SourceSemantics.evalExpr fields runtime (.div lhs rhs)) := by
  have hcompile := compileExpr_div_ok hlhsCompile hrhsCompile
  rcases hlhsSrc : SourceSemantics.evalExpr fields runtime lhs with _ | lhsVal
  · cases hEval : evalIRExpr state lhsIR <;> simp [hEval, hlhsSrc] at hlhsEval
  · rcases hrhsSrc : SourceSemantics.evalExpr fields runtime rhs with _ | rhsVal
    · cases hEval : evalIRExpr state rhsIR <;> simp [hEval, hrhsSrc] at hrhsEval
    · have hlhsEval' := evalIRExpr_of_sourceEval_some hlhsEval hlhsSrc
      have hrhsEval' := evalIRExpr_of_sourceEval_some hrhsEval hrhsSrc
      have hlhsLt' : lhsVal < Compiler.Constants.evmModulus := by
        simpa [hlhsSrc] using hlhsLt
      have hrhsLt' : rhsVal < Compiler.Constants.evmModulus := by
        simpa [hrhsSrc] using hrhsLt
      have heval :
          evalIRExpr state
            (CompilationModel.compileExpr fields .calldata (.div lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
              some (if rhsVal % Compiler.Constants.evmModulus = 0 then 0 else
                (lhsVal % Compiler.Constants.evmModulus) / (rhsVal % Compiler.Constants.evmModulus)) := by
        simpa [hcompile, Except.toOption, Option.getD] using evalIRExpr_div_of_eval hlhsEval' hrhsEval'
      have hsrc := evalExpr_div_of_values hlhsSrc hrhsSrc
      rw [heval]
      rw [hsrc]
      rw [uint256_div_val_eq hlhsLt' hrhsLt']
      simp [Nat.mod_eq_of_lt hlhsLt', Nat.mod_eq_of_lt hrhsLt']

theorem eval_compileExpr_sub_of_compiled
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhsCompile : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhsCompile : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR)
    (hlhsEval : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs))
    (hrhsEval : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs))
    (hlhsLt : SourceSemantics.evalExpr fields runtime lhs < Compiler.Constants.evmModulus)
    (hrhsLt : SourceSemantics.evalExpr fields runtime rhs < Compiler.Constants.evmModulus) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata (.sub lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
        some (SourceSemantics.evalExpr fields runtime (.sub lhs rhs)) := by
  have hcompile := compileExpr_sub_ok hlhsCompile hrhsCompile
  rcases hlhsSrc : SourceSemantics.evalExpr fields runtime lhs with _ | lhsVal
  · cases hEval : evalIRExpr state lhsIR <;> simp [hEval, hlhsSrc] at hlhsEval
  · rcases hrhsSrc : SourceSemantics.evalExpr fields runtime rhs with _ | rhsVal
    · cases hEval : evalIRExpr state rhsIR <;> simp [hEval, hrhsSrc] at hrhsEval
    · have hlhsEval' := evalIRExpr_of_sourceEval_some hlhsEval hlhsSrc
      have hrhsEval' := evalIRExpr_of_sourceEval_some hrhsEval hrhsSrc
      have hlhsLt' : lhsVal < Compiler.Constants.evmModulus := by
        simpa [hlhsSrc] using hlhsLt
      have hrhsLt' : rhsVal < Compiler.Constants.evmModulus := by
        simpa [hrhsSrc] using hrhsLt
      have heval :
          evalIRExpr state
            (CompilationModel.compileExpr fields .calldata (.sub lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
              some ((Compiler.Constants.evmModulus +
                (lhsVal % Compiler.Constants.evmModulus) -
                (rhsVal % Compiler.Constants.evmModulus)) % Compiler.Constants.evmModulus) := by
        simpa [hcompile, Except.toOption, Option.getD] using evalIRExpr_sub_of_eval hlhsEval' hrhsEval'
      have hsrc := evalExpr_sub_of_values hlhsSrc hrhsSrc
      rw [heval]
      rw [hsrc]
      rw [uint256_sub_val_eq hlhsLt' hrhsLt']
      simp [Nat.mod_eq_of_lt hlhsLt', Nat.mod_eq_of_lt hrhsLt']

theorem eval_compileExpr_mod_of_compiled
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhsCompile : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhsCompile : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR)
    (hlhsEval : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs))
    (hrhsEval : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs))
    (hlhsLt : SourceSemantics.evalExpr fields runtime lhs < Compiler.Constants.evmModulus)
    (hrhsLt : SourceSemantics.evalExpr fields runtime rhs < Compiler.Constants.evmModulus) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata (.mod lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
        some (SourceSemantics.evalExpr fields runtime (.mod lhs rhs)) := by
  have hcompile := compileExpr_mod_ok hlhsCompile hrhsCompile
  rcases hlhsSrc : SourceSemantics.evalExpr fields runtime lhs with _ | lhsVal
  · cases hEval : evalIRExpr state lhsIR <;> simp [hEval, hlhsSrc] at hlhsEval
  · rcases hrhsSrc : SourceSemantics.evalExpr fields runtime rhs with _ | rhsVal
    · cases hEval : evalIRExpr state rhsIR <;> simp [hEval, hrhsSrc] at hrhsEval
    · have hlhsEval' := evalIRExpr_of_sourceEval_some hlhsEval hlhsSrc
      have hrhsEval' := evalIRExpr_of_sourceEval_some hrhsEval hrhsSrc
      have hlhsLt' : lhsVal < Compiler.Constants.evmModulus := by
        simpa [hlhsSrc] using hlhsLt
      have hrhsLt' : rhsVal < Compiler.Constants.evmModulus := by
        simpa [hrhsSrc] using hrhsLt
      have heval :
          evalIRExpr state
            (CompilationModel.compileExpr fields .calldata (.mod lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
              some (if rhsVal % Compiler.Constants.evmModulus = 0 then 0 else
                (lhsVal % Compiler.Constants.evmModulus) % (rhsVal % Compiler.Constants.evmModulus)) := by
        simpa [hcompile, Except.toOption, Option.getD] using evalIRExpr_mod_of_eval hlhsEval' hrhsEval'
      have hsrc := evalExpr_mod_of_values hlhsSrc hrhsSrc
      rw [heval]
      rw [hsrc]
      rw [uint256_mod_val_eq hlhsLt' hrhsLt']
      simp [Nat.mod_eq_of_lt hlhsLt', Nat.mod_eq_of_lt hrhsLt']

private theorem evalExpr_bitAnd_of_values
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {lhs rhs : Expr}
    {lhsVal rhsVal : Nat}
    (hlhs : SourceSemantics.evalExpr fields runtime lhs = some lhsVal)
    (hrhs : SourceSemantics.evalExpr fields runtime rhs = some rhsVal) :
    SourceSemantics.evalExpr fields runtime (.bitAnd lhs rhs) =
      some ((Verity.Core.Uint256.and (lhsVal : Verity.Core.Uint256)
        (rhsVal : Verity.Core.Uint256)).val) := by
  calc
    SourceSemantics.evalExpr fields runtime (.bitAnd lhs rhs)
        = (do
            let l ← SourceSemantics.evalExpr fields runtime lhs
            let r ← SourceSemantics.evalExpr fields runtime rhs
            pure (Verity.Core.Uint256.and l r).val) := by rfl
    _ = some ((Verity.Core.Uint256.and (lhsVal : Verity.Core.Uint256)
          (rhsVal : Verity.Core.Uint256)).val) := by simp [hlhs, hrhs]

private theorem evalExpr_bitOr_of_values
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {lhs rhs : Expr}
    {lhsVal rhsVal : Nat}
    (hlhs : SourceSemantics.evalExpr fields runtime lhs = some lhsVal)
    (hrhs : SourceSemantics.evalExpr fields runtime rhs = some rhsVal) :
    SourceSemantics.evalExpr fields runtime (.bitOr lhs rhs) =
      some ((Verity.Core.Uint256.or (lhsVal : Verity.Core.Uint256)
        (rhsVal : Verity.Core.Uint256)).val) := by
  calc
    SourceSemantics.evalExpr fields runtime (.bitOr lhs rhs)
        = (do
            let l ← SourceSemantics.evalExpr fields runtime lhs
            let r ← SourceSemantics.evalExpr fields runtime rhs
            pure (Verity.Core.Uint256.or l r).val) := by rfl
    _ = some ((Verity.Core.Uint256.or (lhsVal : Verity.Core.Uint256)
          (rhsVal : Verity.Core.Uint256)).val) := by simp [hlhs, hrhs]

private theorem evalExpr_bitXor_of_values
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {lhs rhs : Expr}
    {lhsVal rhsVal : Nat}
    (hlhs : SourceSemantics.evalExpr fields runtime lhs = some lhsVal)
    (hrhs : SourceSemantics.evalExpr fields runtime rhs = some rhsVal) :
    SourceSemantics.evalExpr fields runtime (.bitXor lhs rhs) =
      some ((Verity.Core.Uint256.xor (lhsVal : Verity.Core.Uint256)
        (rhsVal : Verity.Core.Uint256)).val) := by
  calc
    SourceSemantics.evalExpr fields runtime (.bitXor lhs rhs)
        = (do
            let l ← SourceSemantics.evalExpr fields runtime lhs
            let r ← SourceSemantics.evalExpr fields runtime rhs
            pure (Verity.Core.Uint256.xor l r).val) := by rfl
    _ = some ((Verity.Core.Uint256.xor (lhsVal : Verity.Core.Uint256)
          (rhsVal : Verity.Core.Uint256)).val) := by simp [hlhs, hrhs]

private theorem evalExpr_bitNot_of_values
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {expr : Expr}
    {val : Nat}
    (hexpr : SourceSemantics.evalExpr fields runtime expr = some val) :
    SourceSemantics.evalExpr fields runtime (.bitNot expr) =
      some ((Verity.Core.Uint256.not (val : Verity.Core.Uint256)).val) := by
  calc
    SourceSemantics.evalExpr fields runtime (.bitNot expr)
        = (do
            let v ← SourceSemantics.evalExpr fields runtime expr
            pure (Verity.Core.Uint256.not v).val) := by rfl
    _ = some ((Verity.Core.Uint256.not (val : Verity.Core.Uint256)).val) := by simp [hexpr]

private theorem evalExpr_shl_of_values
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {shift value : Expr}
    {shiftVal valueVal : Nat}
    (hshift : SourceSemantics.evalExpr fields runtime shift = some shiftVal)
    (hvalue : SourceSemantics.evalExpr fields runtime value = some valueVal) :
    SourceSemantics.evalExpr fields runtime (.shl shift value) =
      some ((Verity.Core.Uint256.shl (shiftVal : Verity.Core.Uint256)
        (valueVal : Verity.Core.Uint256)).val) := by
  calc
    SourceSemantics.evalExpr fields runtime (.shl shift value)
        = (do
            let s ← SourceSemantics.evalExpr fields runtime shift
            let v ← SourceSemantics.evalExpr fields runtime value
            pure (Verity.Core.Uint256.shl s v).val) := by rfl
    _ = some ((Verity.Core.Uint256.shl (shiftVal : Verity.Core.Uint256)
          (valueVal : Verity.Core.Uint256)).val) := by simp [hshift, hvalue]

private theorem evalExpr_shr_of_values
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {shift value : Expr}
    {shiftVal valueVal : Nat}
    (hshift : SourceSemantics.evalExpr fields runtime shift = some shiftVal)
    (hvalue : SourceSemantics.evalExpr fields runtime value = some valueVal) :
    SourceSemantics.evalExpr fields runtime (.shr shift value) =
      some ((Verity.Core.Uint256.shr (shiftVal : Verity.Core.Uint256)
        (valueVal : Verity.Core.Uint256)).val) := by
  calc
    SourceSemantics.evalExpr fields runtime (.shr shift value)
        = (do
            let s ← SourceSemantics.evalExpr fields runtime shift
            let v ← SourceSemantics.evalExpr fields runtime value
            pure (Verity.Core.Uint256.shr s v).val) := by rfl
    _ = some ((Verity.Core.Uint256.shr (shiftVal : Verity.Core.Uint256)
          (valueVal : Verity.Core.Uint256)).val) := by simp [hshift, hvalue]

private theorem evalExpr_min_of_values
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {lhs rhs : Expr}
    {lhsVal rhsVal : Nat}
    (hlhs : SourceSemantics.evalExpr fields runtime lhs = some lhsVal)
    (hrhs : SourceSemantics.evalExpr fields runtime rhs = some rhsVal) :
    SourceSemantics.evalExpr fields runtime (.min lhs rhs) =
      some (if lhsVal ≤ rhsVal then lhsVal else rhsVal) := by
  calc
    SourceSemantics.evalExpr fields runtime (.min lhs rhs)
        = (do
            let l ← SourceSemantics.evalExpr fields runtime lhs
            let r ← SourceSemantics.evalExpr fields runtime rhs
            pure (if l ≤ r then l else r)) := by rfl
    _ = some (if lhsVal ≤ rhsVal then lhsVal else rhsVal) := by simp [hlhs, hrhs]

private theorem evalExpr_max_of_values
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {lhs rhs : Expr}
    {lhsVal rhsVal : Nat}
    (hlhs : SourceSemantics.evalExpr fields runtime lhs = some lhsVal)
    (hrhs : SourceSemantics.evalExpr fields runtime rhs = some rhsVal) :
    SourceSemantics.evalExpr fields runtime (.max lhs rhs) =
      some (if rhsVal ≤ lhsVal then lhsVal else rhsVal) := by
  calc
    SourceSemantics.evalExpr fields runtime (.max lhs rhs)
        = (do
            let l ← SourceSemantics.evalExpr fields runtime lhs
            let r ← SourceSemantics.evalExpr fields runtime rhs
            pure (if r ≤ l then l else r)) := by rfl
    _ = some (if rhsVal ≤ lhsVal then lhsVal else rhsVal) := by simp [hlhs, hrhs]

theorem eval_compileExpr_bitAnd_of_compiled
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhsCompile : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhsCompile : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR)
    (hlhsEval : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs))
    (hrhsEval : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs))
    (hlhsLt : SourceSemantics.evalExpr fields runtime lhs < Compiler.Constants.evmModulus)
    (hrhsLt : SourceSemantics.evalExpr fields runtime rhs < Compiler.Constants.evmModulus) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata (.bitAnd lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
        some (SourceSemantics.evalExpr fields runtime (.bitAnd lhs rhs)) := by
  have hcompile := compileExpr_bitAnd_ok hlhsCompile hrhsCompile
  rcases hlhsSrc : SourceSemantics.evalExpr fields runtime lhs with _ | lhsVal
  · cases hEval : evalIRExpr state lhsIR <;> simp [hEval, hlhsSrc] at hlhsEval
  · rcases hrhsSrc : SourceSemantics.evalExpr fields runtime rhs with _ | rhsVal
    · cases hEval : evalIRExpr state rhsIR <;> simp [hEval, hrhsSrc] at hrhsEval
    · have hlhsEval' := evalIRExpr_of_sourceEval_some hlhsEval hlhsSrc
      have hrhsEval' := evalIRExpr_of_sourceEval_some hrhsEval hrhsSrc
      have hlhsLt' : lhsVal < Compiler.Constants.evmModulus := by simpa [hlhsSrc] using hlhsLt
      have hrhsLt' : rhsVal < Compiler.Constants.evmModulus := by simpa [hrhsSrc] using hrhsLt
      have heval :
          evalIRExpr state
            (CompilationModel.compileExpr fields .calldata (.bitAnd lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
              some ((lhsVal % Compiler.Constants.evmModulus) &&& (rhsVal % Compiler.Constants.evmModulus)) := by
        simpa [hcompile, Except.toOption, Option.getD] using evalIRExpr_and_of_eval hlhsEval' hrhsEval'
      have hsrc := evalExpr_bitAnd_of_values hlhsSrc hrhsSrc
      rw [heval, hsrc]
      simp only [Verity.Core.Uint256.and, Verity.Core.Uint256.ofNat,
        Verity.Core.Uint256.modulus, Compiler.Constants.evmModulus,
        Verity.Core.UINT256_MODULUS,
        Nat.mod_eq_of_lt hlhsLt', Nat.mod_eq_of_lt hrhsLt']
      have hresLt : Nat.land lhsVal rhsVal < 2 ^ 256 := Nat.and_lt_two_pow lhsVal
          (show rhsVal < 2 ^ 256 by rwa [show (2 : Nat) ^ 256 = Compiler.Constants.evmModulus from rfl])
      show some (some (lhsVal.land rhsVal)) = some (some (lhsVal.land rhsVal % _))
      rw [Nat.mod_eq_of_lt hresLt]

theorem eval_compileExpr_bitOr_of_compiled
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhsCompile : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhsCompile : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR)
    (hlhsEval : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs))
    (hrhsEval : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs))
    (hlhsLt : SourceSemantics.evalExpr fields runtime lhs < Compiler.Constants.evmModulus)
    (hrhsLt : SourceSemantics.evalExpr fields runtime rhs < Compiler.Constants.evmModulus) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata (.bitOr lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
        some (SourceSemantics.evalExpr fields runtime (.bitOr lhs rhs)) := by
  have hcompile := compileExpr_bitOr_ok hlhsCompile hrhsCompile
  rcases hlhsSrc : SourceSemantics.evalExpr fields runtime lhs with _ | lhsVal
  · cases hEval : evalIRExpr state lhsIR <;> simp [hEval, hlhsSrc] at hlhsEval
  · rcases hrhsSrc : SourceSemantics.evalExpr fields runtime rhs with _ | rhsVal
    · cases hEval : evalIRExpr state rhsIR <;> simp [hEval, hrhsSrc] at hrhsEval
    · have hlhsEval' := evalIRExpr_of_sourceEval_some hlhsEval hlhsSrc
      have hrhsEval' := evalIRExpr_of_sourceEval_some hrhsEval hrhsSrc
      have hlhsLt' : lhsVal < Compiler.Constants.evmModulus := by simpa [hlhsSrc] using hlhsLt
      have hrhsLt' : rhsVal < Compiler.Constants.evmModulus := by simpa [hrhsSrc] using hrhsLt
      have heval :
          evalIRExpr state
            (CompilationModel.compileExpr fields .calldata (.bitOr lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
              some ((lhsVal % Compiler.Constants.evmModulus) ||| (rhsVal % Compiler.Constants.evmModulus)) := by
        simpa [hcompile, Except.toOption, Option.getD] using evalIRExpr_or_of_eval hlhsEval' hrhsEval'
      have hsrc := evalExpr_bitOr_of_values hlhsSrc hrhsSrc
      rw [heval, hsrc]
      simp only [Verity.Core.Uint256.or, Verity.Core.Uint256.ofNat,
        Verity.Core.Uint256.modulus, Compiler.Constants.evmModulus,
        Verity.Core.UINT256_MODULUS,
        Nat.mod_eq_of_lt hlhsLt', Nat.mod_eq_of_lt hrhsLt']
      have hresLt : Nat.lor lhsVal rhsVal < 2 ^ 256 := Nat.or_lt_two_pow
          (show lhsVal < 2 ^ 256 by rwa [show (2 : Nat) ^ 256 = Compiler.Constants.evmModulus from rfl])
          (show rhsVal < 2 ^ 256 by rwa [show (2 : Nat) ^ 256 = Compiler.Constants.evmModulus from rfl])
      show some (some (lhsVal.lor rhsVal)) = some (some (lhsVal.lor rhsVal % _))
      rw [Nat.mod_eq_of_lt hresLt]

theorem eval_compileExpr_bitXor_of_compiled
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhsCompile : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhsCompile : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR)
    (hlhsEval : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs))
    (hrhsEval : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs))
    (hlhsLt : SourceSemantics.evalExpr fields runtime lhs < Compiler.Constants.evmModulus)
    (hrhsLt : SourceSemantics.evalExpr fields runtime rhs < Compiler.Constants.evmModulus) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata (.bitXor lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
        some (SourceSemantics.evalExpr fields runtime (.bitXor lhs rhs)) := by
  have hcompile := compileExpr_bitXor_ok hlhsCompile hrhsCompile
  rcases hlhsSrc : SourceSemantics.evalExpr fields runtime lhs with _ | lhsVal
  · cases hEval : evalIRExpr state lhsIR <;> simp [hEval, hlhsSrc] at hlhsEval
  · rcases hrhsSrc : SourceSemantics.evalExpr fields runtime rhs with _ | rhsVal
    · cases hEval : evalIRExpr state rhsIR <;> simp [hEval, hrhsSrc] at hrhsEval
    · have hlhsEval' := evalIRExpr_of_sourceEval_some hlhsEval hlhsSrc
      have hrhsEval' := evalIRExpr_of_sourceEval_some hrhsEval hrhsSrc
      have hlhsLt' : lhsVal < Compiler.Constants.evmModulus := by simpa [hlhsSrc] using hlhsLt
      have hrhsLt' : rhsVal < Compiler.Constants.evmModulus := by simpa [hrhsSrc] using hrhsLt
      have heval :
          evalIRExpr state
            (CompilationModel.compileExpr fields .calldata (.bitXor lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
              some (Nat.xor (lhsVal % Compiler.Constants.evmModulus) (rhsVal % Compiler.Constants.evmModulus)) := by
        simpa [hcompile, Except.toOption, Option.getD] using evalIRExpr_xor_of_eval hlhsEval' hrhsEval'
      have hsrc := evalExpr_bitXor_of_values hlhsSrc hrhsSrc
      rw [heval, hsrc]
      simp only [Verity.Core.Uint256.xor, Verity.Core.Uint256.ofNat,
        Verity.Core.Uint256.modulus, Compiler.Constants.evmModulus,
        Verity.Core.UINT256_MODULUS,
        Nat.mod_eq_of_lt hlhsLt', Nat.mod_eq_of_lt hrhsLt']
      have hresLt : Nat.xor lhsVal rhsVal < 2 ^ 256 := Nat.xor_lt_two_pow
          (show lhsVal < 2 ^ 256 by rwa [show (2 : Nat) ^ 256 = Compiler.Constants.evmModulus from rfl])
          (show rhsVal < 2 ^ 256 by rwa [show (2 : Nat) ^ 256 = Compiler.Constants.evmModulus from rfl])
      show some (some (Nat.xor lhsVal rhsVal)) = some (some (Nat.xor lhsVal rhsVal % _))
      rw [Nat.mod_eq_of_lt hresLt]

theorem eval_compileExpr_bitNot_of_compiled
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {expr : Expr}
    {exprIR : YulExpr}
    (hexprCompile : CompilationModel.compileExpr fields .calldata expr = Except.ok exprIR)
    (hexprEval : evalIRExpr state exprIR = some (SourceSemantics.evalExpr fields runtime expr))
    (hexprLt : SourceSemantics.evalExpr fields runtime expr < Compiler.Constants.evmModulus) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata (.bitNot expr) |>.toOption.getD (YulExpr.lit 0)) =
        some (SourceSemantics.evalExpr fields runtime (.bitNot expr)) := by
  have hcompile := compileExpr_bitNot_ok hexprCompile
  rcases hexprSrc : SourceSemantics.evalExpr fields runtime expr with _ | val
  · cases hEval : evalIRExpr state exprIR <;> simp [hEval, hexprSrc] at hexprEval
  · have hexprEval' := evalIRExpr_of_sourceEval_some hexprEval hexprSrc
    have hvalLt : val < Compiler.Constants.evmModulus := by simpa [hexprSrc] using hexprLt
    have heval :
        evalIRExpr state
          (CompilationModel.compileExpr fields .calldata (.bitNot expr) |>.toOption.getD (YulExpr.lit 0)) =
            some (Nat.xor (val % Compiler.Constants.evmModulus) (Compiler.Constants.evmModulus - 1)) := by
      simpa [hcompile, Except.toOption, Option.getD] using evalIRExpr_not_of_eval hexprEval'
    have hsrc := evalExpr_bitNot_of_values hexprSrc
    -- Need to equate IR result (val ^^^ (evmModulus - 1)) with source result (Uint256.not (ofNat val)).val
    have hvalLt256 : val < 2 ^ 256 := by rwa [show (2 : Nat) ^ 256 = Compiler.Constants.evmModulus from rfl]
    -- Prove the bitwise NOT identity: xor val (2^256-1) = 2^256-1-val
    have hxor_eq : Nat.xor val (2 ^ 256 - 1) = 2 ^ 256 - 1 - val := by
      have key : (BitVec.ofNat 256 val ^^^ BitVec.allOnes 256).toNat = 2 ^ 256 - 1 - val := by
        rw [BitVec.xor_allOnes]
        simp only [BitVec.toNat_not, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hvalLt256]
      have lhs_eq : Nat.xor val (2 ^ 256 - 1) =
          (BitVec.ofNat 256 val ^^^ BitVec.allOnes 256).toNat := by
        simp only [BitVec.toNat_xor, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hvalLt256,
          BitVec.toNat_allOnes]
        rfl
      rw [lhs_eq, key]
    -- Now combine: IR evaluates to xor val (evmModulus-1), source evaluates to Uint256.not
    rw [heval, hsrc]
    -- Simplify: val % evmModulus → val, unfold Uint256.not/ofNat/MAX_UINT256 on RHS
    simp only [Nat.mod_eq_of_lt hvalLt,
      Verity.Core.Uint256.not, Verity.Core.Uint256.val_ofNat,
      Verity.Core.MAX_UINT256, Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS]
    -- Goal: some (some (Nat.xor val (2^256-1))) = some (some ((2^256-1-val) % 2^256))
    rw [show Compiler.Constants.evmModulus = 2 ^ 256 from rfl, hxor_eq,
      Nat.mod_eq_of_lt (by omega : 2 ^ 256 - 1 - val < 2 ^ 256)]
    simp

theorem eval_compileExpr_shl_of_compiled
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {shift value : Expr}
    {shiftIR valueIR : YulExpr}
    (hshiftCompile : CompilationModel.compileExpr fields .calldata shift = Except.ok shiftIR)
    (hvalueCompile : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR)
    (hshiftEval : evalIRExpr state shiftIR = some (SourceSemantics.evalExpr fields runtime shift))
    (hvalueEval : evalIRExpr state valueIR = some (SourceSemantics.evalExpr fields runtime value))
    (hshiftLt : SourceSemantics.evalExpr fields runtime shift < Compiler.Constants.evmModulus)
    (hvalueLt : SourceSemantics.evalExpr fields runtime value < Compiler.Constants.evmModulus) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata (.shl shift value) |>.toOption.getD (YulExpr.lit 0)) =
        some (SourceSemantics.evalExpr fields runtime (.shl shift value)) := by
  have hcompile := compileExpr_shl_ok hshiftCompile hvalueCompile
  rcases hshiftSrc : SourceSemantics.evalExpr fields runtime shift with _ | shiftVal
  · cases hEval : evalIRExpr state shiftIR <;> simp [hEval, hshiftSrc] at hshiftEval
  · rcases hvalueSrc : SourceSemantics.evalExpr fields runtime value with _ | valueVal
    · cases hEval : evalIRExpr state valueIR <;> simp [hEval, hvalueSrc] at hvalueEval
    · have hshiftEval' := evalIRExpr_of_sourceEval_some hshiftEval hshiftSrc
      have hvalueEval' := evalIRExpr_of_sourceEval_some hvalueEval hvalueSrc
      have hshiftLt' : shiftVal < Compiler.Constants.evmModulus := by simpa [hshiftSrc] using hshiftLt
      have hvalueLt' : valueVal < Compiler.Constants.evmModulus := by simpa [hvalueSrc] using hvalueLt
      have hIR := evalIRExpr_shl_of_eval hshiftEval' hvalueEval'
      have hsrc := evalExpr_shl_of_values hshiftSrc hvalueSrc
      rw [hsrc]
      simp only [hcompile, Except.toOption, Option.getD] at hIR ⊢
      rw [hIR]
      have hevmMod : Compiler.Constants.evmModulus = 2 ^ 256 := rfl
      rw [hevmMod] at hshiftLt' hvalueLt'
      simp only [Verity.Core.Uint256.shl, Verity.Core.Uint256.val_ofNat,
        Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS, hevmMod,
        Nat.mod_eq_of_lt hshiftLt', Nat.mod_eq_of_lt hvalueLt', Nat.shiftLeft_eq]
      simp only [Bind.bind, Option.bind, Pure.pure]
      by_cases hlt : shiftVal < 256
      · simp [hlt]
      · simp only [hlt, ↓reduceIte]
        have hge : 256 ≤ shiftVal := Nat.not_lt.mp hlt
        have h2pow : 2 ^ 256 ∣ 2 ^ shiftVal := Nat.pow_dvd_pow 2 hge
        have hmz : (valueVal * 2 ^ shiftVal) % 2 ^ 256 = 0 := by
          rw [Nat.mul_mod, Nat.dvd_iff_mod_eq_zero.mp h2pow, Nat.mul_zero, Nat.zero_mod]
        rw [hmz]

theorem eval_compileExpr_shr_of_compiled
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {shift value : Expr}
    {shiftIR valueIR : YulExpr}
    (hshiftCompile : CompilationModel.compileExpr fields .calldata shift = Except.ok shiftIR)
    (hvalueCompile : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR)
    (hshiftEval : evalIRExpr state shiftIR = some (SourceSemantics.evalExpr fields runtime shift))
    (hvalueEval : evalIRExpr state valueIR = some (SourceSemantics.evalExpr fields runtime value))
    (hshiftLt : SourceSemantics.evalExpr fields runtime shift < Compiler.Constants.evmModulus)
    (hvalueLt : SourceSemantics.evalExpr fields runtime value < Compiler.Constants.evmModulus) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata (.shr shift value) |>.toOption.getD (YulExpr.lit 0)) =
        some (SourceSemantics.evalExpr fields runtime (.shr shift value)) := by
  have hcompile := compileExpr_shr_ok hshiftCompile hvalueCompile
  rcases hshiftSrc : SourceSemantics.evalExpr fields runtime shift with _ | shiftVal
  · cases hEval : evalIRExpr state shiftIR <;> simp [hEval, hshiftSrc] at hshiftEval
  · rcases hvalueSrc : SourceSemantics.evalExpr fields runtime value with _ | valueVal
    · cases hEval : evalIRExpr state valueIR <;> simp [hEval, hvalueSrc] at hvalueEval
    · have hshiftEval' := evalIRExpr_of_sourceEval_some hshiftEval hshiftSrc
      have hvalueEval' := evalIRExpr_of_sourceEval_some hvalueEval hvalueSrc
      have hshiftLt' : shiftVal < Compiler.Constants.evmModulus := by simpa [hshiftSrc] using hshiftLt
      have hvalueLt' : valueVal < Compiler.Constants.evmModulus := by simpa [hvalueSrc] using hvalueLt
      have hIR := evalIRExpr_shr_of_eval hshiftEval' hvalueEval'
      have hsrc := evalExpr_shr_of_values hshiftSrc hvalueSrc
      rw [hsrc]
      simp only [hcompile, Except.toOption, Option.getD] at hIR ⊢
      rw [hIR]
      have hevmMod : Compiler.Constants.evmModulus = 2 ^ 256 := rfl
      rw [hevmMod] at hshiftLt' hvalueLt'
      simp only [Verity.Core.Uint256.shr, Verity.Core.Uint256.val_ofNat,
        Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS, hevmMod,
        Nat.mod_eq_of_lt hshiftLt', Nat.mod_eq_of_lt hvalueLt', Nat.shiftRight_eq_div_pow,
        Bind.bind, Option.bind, Pure.pure]
      by_cases hlt : shiftVal < 256
      · simp only [hlt, ↓reduceIte]
        have : valueVal / 2 ^ shiftVal < 2 ^ 256 :=
          lt_of_le_of_lt (Nat.div_le_self _ _) hvalueLt'
        rw [Nat.mod_eq_of_lt this]
      · simp only [hlt, ↓reduceIte]
        have hge : 256 ≤ shiftVal := Nat.not_lt.mp hlt
        have hmz : (valueVal / 2 ^ shiftVal) % 2 ^ 256 = 0 := by
          rw [Nat.div_eq_of_lt (lt_of_lt_of_le hvalueLt' (Nat.pow_le_pow_right (by norm_num) hge)),
              Nat.zero_mod]
        rw [hmz]

private theorem evalExpr_ite_of_values
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {cond thenVal elseVal : Expr}
    {condVal thenV elseV : Nat}
    (hcond : SourceSemantics.evalExpr fields runtime cond = some condVal)
    (hthen : SourceSemantics.evalExpr fields runtime thenVal = some thenV)
    (helse : SourceSemantics.evalExpr fields runtime elseVal = some elseV) :
    SourceSemantics.evalExpr fields runtime (.ite cond thenVal elseVal) =
      some (if condVal ≠ 0 then thenV else elseV) := by
  calc
    SourceSemantics.evalExpr fields runtime (.ite cond thenVal elseVal)
        = (do let c ← SourceSemantics.evalExpr fields runtime cond
              if c != 0 then SourceSemantics.evalExpr fields runtime thenVal
              else SourceSemantics.evalExpr fields runtime elseVal) := by rfl
    _ = some (if condVal ≠ 0 then thenV else elseV) := by
        simp only [hcond, Option.bind_some, bne_iff_ne]
        split <;> simp_all

private theorem evm_ite_arith {c t e M : Nat} (hc : c < M) (ht : t < M) (he : e < M)
    :
    (SourceSemantics.boolWord (c ≠ 0) * t % M +
      SourceSemantics.boolWord (c = 0) * e % M) % M =
      if c ≠ 0 then t else e := by
  by_cases hzero : c = 0
  · subst hzero; simp [SourceSemantics.boolWord, Nat.mod_eq_of_lt he]
  · simp [hzero, SourceSemantics.boolWord, Nat.mod_eq_of_lt ht]

theorem eval_compileExpr_ite_of_compiled
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {cond thenVal elseVal : Expr}
    {condIR thenIR elseIR : YulExpr}
    (hcondCompile : CompilationModel.compileExpr fields .calldata cond = Except.ok condIR)
    (hthenCompile : CompilationModel.compileExpr fields .calldata thenVal = Except.ok thenIR)
    (helseCompile : CompilationModel.compileExpr fields .calldata elseVal = Except.ok elseIR)
    (hcondEval : evalIRExpr state condIR = some (SourceSemantics.evalExpr fields runtime cond))
    (hthenEval : evalIRExpr state thenIR = some (SourceSemantics.evalExpr fields runtime thenVal))
    (helseEval : evalIRExpr state elseIR = some (SourceSemantics.evalExpr fields runtime elseVal))
    (hcondLt : SourceSemantics.evalExpr fields runtime cond < Compiler.Constants.evmModulus)
    (hthenLt : SourceSemantics.evalExpr fields runtime thenVal < Compiler.Constants.evmModulus)
    (helseLt : SourceSemantics.evalExpr fields runtime elseVal < Compiler.Constants.evmModulus) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata (.ite cond thenVal elseVal) |>.toOption.getD
        (YulExpr.lit 0)) =
        some (SourceSemantics.evalExpr fields runtime (.ite cond thenVal elseVal)) := by
  have hcompile := compileExpr_ite_ok hcondCompile hthenCompile helseCompile
  rcases hcondSrc : SourceSemantics.evalExpr fields runtime cond with _ | condV
  · cases hEval : evalIRExpr state condIR <;> simp [hEval, hcondSrc] at hcondEval
  · rcases hthenSrc : SourceSemantics.evalExpr fields runtime thenVal with _ | thenV
    · cases hEval : evalIRExpr state thenIR <;> simp [hEval, hthenSrc] at hthenEval
    · rcases helseSrc : SourceSemantics.evalExpr fields runtime elseVal with _ | elseV
      · cases hEval : evalIRExpr state elseIR <;> simp [hEval, helseSrc] at helseEval
      · have hcondEval' := evalIRExpr_of_sourceEval_some hcondEval hcondSrc
        have hthenEval' := evalIRExpr_of_sourceEval_some hthenEval hthenSrc
        have helseEval' := evalIRExpr_of_sourceEval_some helseEval helseSrc
        have hcondLt' : condV < Compiler.Constants.evmModulus := by simpa [hcondSrc] using hcondLt
        have hthenLt' : thenV < Compiler.Constants.evmModulus := by simpa [hthenSrc] using hthenLt
        have helseLt' : elseV < Compiler.Constants.evmModulus := by simpa [helseSrc] using helseLt
        have hIsZero := evalIRExpr_iszero_of_lt hcondEval' hcondLt'
        have hIsZeroIsZero := evalIRExpr_iszero_of_lt hIsZero (boolWord_lt_evmModulus _)
        have hMulThen := evalIRExpr_mul_of_eval hIsZeroIsZero hthenEval'
        have hMulElse := evalIRExpr_mul_of_eval hIsZero helseEval'
        have hAdd := evalIRExpr_add_of_eval hMulThen hMulElse
        have hsrc := evalExpr_ite_of_values hcondSrc hthenSrc helseSrc
        rw [hsrc]
        simp only [hcompile, Except.toOption, Option.getD] at hAdd ⊢
        simp only [hAdd, Option.bind_some, Option.pure_def]
        by_cases hzero : condV = 0
        · simp [hzero, SourceSemantics.boolWord, Nat.mod_eq_of_lt helseLt']
        · simp [hzero, SourceSemantics.boolWord, Nat.mod_eq_of_lt hthenLt']

private theorem evm_min_arith {a b M : Nat} (ha : a < M) (hb : b < M) :
    (M + a - ((a - b) % M * SourceSemantics.boolWord (b < a) % M)) % M =
      if a ≤ b then a else b := by
  by_cases hgt : b < a
  · simp [hgt, Nat.not_le.mpr hgt, SourceSemantics.boolWord, Nat.mod_eq_of_lt (show a - b < M by omega)]
    have : M + a - (a - b) = M + b := by omega
    rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt hb]
  · simp [hgt, Nat.le_of_not_gt hgt, SourceSemantics.boolWord, Nat.mod_eq_of_lt ha]

private theorem evm_max_arith {a b M : Nat} (ha : a < M) (hb : b < M) :
    (a + (b - a) % M * SourceSemantics.boolWord (a < b) % M) % M =
      if b ≤ a then a else b := by
  by_cases hgt : a < b
  · simp [hgt, Nat.not_le.mpr hgt, SourceSemantics.boolWord, Nat.mod_eq_of_lt (show b - a < M by omega)]
    have : a + (b - a) = b := by omega
    rw [this, Nat.mod_eq_of_lt hb]
  · simp [hgt, Nat.le_of_not_gt hgt, SourceSemantics.boolWord, Nat.mod_eq_of_lt ha]

theorem eval_compileExpr_min_of_compiled
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhsCompile : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhsCompile : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR)
    (hlhsEval : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs))
    (hrhsEval : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs))
    (hlhsLt : SourceSemantics.evalExpr fields runtime lhs < Compiler.Constants.evmModulus)
    (hrhsLt : SourceSemantics.evalExpr fields runtime rhs < Compiler.Constants.evmModulus) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata (.min lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
        some (SourceSemantics.evalExpr fields runtime (.min lhs rhs)) := by
  have hcompile := compileExpr_min_ok hlhsCompile hrhsCompile
  rcases hlhsSrc : SourceSemantics.evalExpr fields runtime lhs with _ | lhsVal
  · cases hEval : evalIRExpr state lhsIR <;> simp [hEval, hlhsSrc] at hlhsEval
  · rcases hrhsSrc : SourceSemantics.evalExpr fields runtime rhs with _ | rhsVal
    · cases hEval : evalIRExpr state rhsIR <;> simp [hEval, hrhsSrc] at hrhsEval
    · have hlhsEval' := evalIRExpr_of_sourceEval_some hlhsEval hlhsSrc
      have hrhsEval' := evalIRExpr_of_sourceEval_some hrhsEval hrhsSrc
      have hlhsLt' : lhsVal < Compiler.Constants.evmModulus := by simpa [hlhsSrc] using hlhsLt
      have hrhsLt' : rhsVal < Compiler.Constants.evmModulus := by simpa [hrhsSrc] using hrhsLt
      have hGt := evalIRExpr_gt_of_eval hlhsEval' hrhsEval'
      simp only [Nat.mod_eq_of_lt hlhsLt', Nat.mod_eq_of_lt hrhsLt'] at hGt
      have hSubInner := evalIRExpr_sub_of_eval hlhsEval' hrhsEval'
      simp only [Nat.mod_eq_of_lt hlhsLt', Nat.mod_eq_of_lt hrhsLt'] at hSubInner
      have hMul := evalIRExpr_mul_of_eval hSubInner hGt
      have hSubOuter := evalIRExpr_sub_of_eval hlhsEval' hMul
      simp only [Nat.mod_eq_of_lt hlhsLt', Nat.mod_mod] at hSubOuter
      have hsrc := evalExpr_min_of_values hlhsSrc hrhsSrc
      rw [hsrc]
      simp only [hcompile, Except.toOption, Option.getD] at hSubOuter ⊢
      simp only [hSubOuter, Option.bind_some, Option.pure_def]
      by_cases hgt : rhsVal < lhsVal
      · have hSubMod : (Compiler.Constants.evmModulus + lhsVal - rhsVal) %
            Compiler.Constants.evmModulus = lhsVal - rhsVal := by
          have : Compiler.Constants.evmModulus + lhsVal - rhsVal =
              Compiler.Constants.evmModulus + (lhsVal - rhsVal) := by omega
          rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega : lhsVal - rhsVal < _)]
        simp [hgt, Nat.not_le.mpr hgt, SourceSemantics.boolWord, hSubMod,
          Nat.mod_eq_of_lt (show lhsVal - rhsVal < Compiler.Constants.evmModulus by omega)]
        have : Compiler.Constants.evmModulus + lhsVal - (lhsVal - rhsVal) =
            Compiler.Constants.evmModulus + rhsVal := by omega
        rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt hrhsLt']
      · simp [hgt, Nat.le_of_not_gt hgt, SourceSemantics.boolWord, Nat.mod_eq_of_lt hlhsLt']

theorem eval_compileExpr_max_of_compiled
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhsCompile : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhsCompile : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR)
    (hlhsEval : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs))
    (hrhsEval : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs))
    (hlhsLt : SourceSemantics.evalExpr fields runtime lhs < Compiler.Constants.evmModulus)
    (hrhsLt : SourceSemantics.evalExpr fields runtime rhs < Compiler.Constants.evmModulus) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata (.max lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
        some (SourceSemantics.evalExpr fields runtime (.max lhs rhs)) := by
  have hcompile := compileExpr_max_ok hlhsCompile hrhsCompile
  rcases hlhsSrc : SourceSemantics.evalExpr fields runtime lhs with _ | lhsVal
  · cases hEval : evalIRExpr state lhsIR <;> simp [hEval, hlhsSrc] at hlhsEval
  · rcases hrhsSrc : SourceSemantics.evalExpr fields runtime rhs with _ | rhsVal
    · cases hEval : evalIRExpr state rhsIR <;> simp [hEval, hrhsSrc] at hrhsEval
    · have hlhsEval' := evalIRExpr_of_sourceEval_some hlhsEval hlhsSrc
      have hrhsEval' := evalIRExpr_of_sourceEval_some hrhsEval hrhsSrc
      have hlhsLt' : lhsVal < Compiler.Constants.evmModulus := by simpa [hlhsSrc] using hlhsLt
      have hrhsLt' : rhsVal < Compiler.Constants.evmModulus := by simpa [hrhsSrc] using hrhsLt
      have hGt := evalIRExpr_gt_of_eval hrhsEval' hlhsEval'
      simp only [Nat.mod_eq_of_lt hlhsLt', Nat.mod_eq_of_lt hrhsLt'] at hGt
      have hSubInner := evalIRExpr_sub_of_eval hrhsEval' hlhsEval'
      simp only [Nat.mod_eq_of_lt hlhsLt', Nat.mod_eq_of_lt hrhsLt'] at hSubInner
      have hMul := evalIRExpr_mul_of_eval hSubInner hGt
      have hAddOuter := evalIRExpr_add_of_eval hlhsEval' hMul
      have hsrc := evalExpr_max_of_values hlhsSrc hrhsSrc
      rw [hsrc]
      simp only [hcompile, Except.toOption, Option.getD] at hAddOuter ⊢
      simp only [hAddOuter, Option.bind_some, Option.pure_def]
      by_cases hgt : lhsVal < rhsVal
      · have hSubMod : (Compiler.Constants.evmModulus + rhsVal - lhsVal) %
            Compiler.Constants.evmModulus = rhsVal - lhsVal := by
          have : Compiler.Constants.evmModulus + rhsVal - lhsVal =
              Compiler.Constants.evmModulus + (rhsVal - lhsVal) := by omega
          rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega : rhsVal - lhsVal < _)]
        simp [hgt, Nat.not_le.mpr hgt, SourceSemantics.boolWord, hSubMod,
          Nat.mod_eq_of_lt (show rhsVal - lhsVal < Compiler.Constants.evmModulus by omega)]
        have : lhsVal + (rhsVal - lhsVal) = rhsVal := by omega
        rw [this, Nat.mod_eq_of_lt hrhsLt']
      · simp [hgt, Nat.le_of_not_gt hgt, SourceSemantics.boolWord, Nat.mod_eq_of_lt hlhsLt']

private theorem evalExpr_wMulDown_of_values
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {lhs rhs : Expr}
    {lhsVal rhsVal : Nat}
    (hlhs : SourceSemantics.evalExpr fields runtime lhs = some lhsVal)
    (hrhs : SourceSemantics.evalExpr fields runtime rhs = some rhsVal) :
    SourceSemantics.evalExpr fields runtime (.wMulDown lhs rhs) =
      some (((Verity.Core.Uint256.ofNat lhsVal * Verity.Core.Uint256.ofNat rhsVal) /
        (1000000000000000000 : Verity.Core.Uint256)).val) := by
  calc
    SourceSemantics.evalExpr fields runtime (.wMulDown lhs rhs)
        = (do
            let lhs ← do
              let a ← SourceSemantics.evalExpr fields runtime lhs
              pure (Verity.Core.Uint256.ofNat a)
            let rhs ← do
              let a ← SourceSemantics.evalExpr fields runtime rhs
              pure (Verity.Core.Uint256.ofNat a)
            let wad : Verity.Core.Uint256 := 1000000000000000000
            pure ((lhs * rhs) / wad).val) := rfl
    _ = _ := by simp [hlhs, hrhs]

theorem eval_compileExpr_wMulDown_of_compiled
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhsCompile : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhsCompile : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR)
    (hlhsEval : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs))
    (hrhsEval : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs))
    (hlhsLt : SourceSemantics.evalExpr fields runtime lhs < Compiler.Constants.evmModulus)
    (hrhsLt : SourceSemantics.evalExpr fields runtime rhs < Compiler.Constants.evmModulus) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata (.wMulDown lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
        some (SourceSemantics.evalExpr fields runtime (.wMulDown lhs rhs)) := by
  have hcompile := compileExpr_wMulDown_ok hlhsCompile hrhsCompile
  rcases hlhsSrc : SourceSemantics.evalExpr fields runtime lhs with _ | lhsVal
  · cases hEval : evalIRExpr state lhsIR <;> simp [hEval, hlhsSrc] at hlhsEval
  · rcases hrhsSrc : SourceSemantics.evalExpr fields runtime rhs with _ | rhsVal
    · cases hEval : evalIRExpr state rhsIR <;> simp [hEval, hrhsSrc] at hrhsEval
    · have hlhsEval' := evalIRExpr_of_sourceEval_some hlhsEval hlhsSrc
      have hrhsEval' := evalIRExpr_of_sourceEval_some hrhsEval hrhsSrc
      have hlhsLt' : lhsVal < Compiler.Constants.evmModulus := by simpa [hlhsSrc] using hlhsLt
      have hrhsLt' : rhsVal < Compiler.Constants.evmModulus := by simpa [hrhsSrc] using hrhsLt
      have hMul := evalIRExpr_mul_of_eval hlhsEval' hrhsEval'
      have hWadLt : (1000000000000000000 : Nat) < Compiler.Constants.evmModulus := by decide
      have hLitWad : evalIRExpr state (YulExpr.lit 1000000000000000000) = some 1000000000000000000 := by
        simp [evalIRExpr]
      have hDiv := evalIRExpr_div_of_eval hMul hLitWad
      have hsrc := evalExpr_wMulDown_of_values hlhsSrc hrhsSrc
      -- Simplify hDiv: remove double mod and if-condition
      simp only [Nat.mod_eq_of_lt hWadLt, Nat.mod_mod,
        show (1000000000000000000 : Nat) ≠ 0 by omega, ite_false] at hDiv
      -- Compute source result val by unfolding Uint256 operations
      have hResultVal : ((Verity.Core.Uint256.ofNat lhsVal * Verity.Core.Uint256.ofNat rhsVal) /
          (1000000000000000000 : Verity.Core.Uint256)).val =
          lhsVal * rhsVal % Compiler.Constants.evmModulus / 1000000000000000000 := by
        show (Verity.Core.Uint256.div (Verity.Core.Uint256.mul _ _) _).val = _
        have hlhsLtM : lhsVal < Verity.Core.Uint256.modulus := hlhsLt'
        have hrhsLtM : rhsVal < Verity.Core.Uint256.modulus := hrhsLt'
        have hWadNe : (1000000000000000000 : Verity.Core.Uint256).val ≠ 0 := by decide
        simp only [Verity.Core.Uint256.div, hWadNe, ↓reduceIte,
          Verity.Core.Uint256.mul, Verity.Core.Uint256.ofNat,
          Nat.mod_eq_of_lt hlhsLtM, Nat.mod_eq_of_lt hrhsLtM]
        exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _)
          (Nat.mod_lt _ (show 0 < Verity.Core.Uint256.modulus by decide)))
      simp only [hcompile, Except.toOption, Option.getD] at hDiv ⊢
      rw [hsrc, hResultVal]
      simp only [hDiv, Bind.bind, Option.bind, Pure.pure]

private theorem evalIRExpr_lit_eq (state : IRState) (value : Nat) :
    evalIRExpr state (YulExpr.lit value) = some value := by
  simp [evalIRExpr]

private theorem evmModulus_add_sub_one_mod {n : Nat}
    (hn : n < Compiler.Constants.evmModulus) (hne : n ≠ 0) :
    (Compiler.Constants.evmModulus + n - 1) % Compiler.Constants.evmModulus = n - 1 := by
  rw [show Compiler.Constants.evmModulus + n - 1 = Compiler.Constants.evmModulus + (n - 1) by
      omega, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]

private theorem pred_div_add_one_lt_evmModulus {lhsVal : Nat} (rhsVal : Nat)
    (hlhsLt : lhsVal < Compiler.Constants.evmModulus) (hne : lhsVal ≠ 0) :
    (lhsVal - 1) / rhsVal + 1 < Compiler.Constants.evmModulus :=
  Nat.lt_of_le_of_lt (Nat.add_le_add_right (Nat.div_le_self _ _) 1) (by omega)

private theorem uint256_ofNat_val_of_lt {n : Nat} (h : n < Compiler.Constants.evmModulus) :
    (Verity.Core.Uint256.ofNat n).val = n :=
  Nat.mod_eq_of_lt h

private theorem uint256_ofNat_mul_ofNat_val {a b : Nat}
    (ha : a < Compiler.Constants.evmModulus) (hb : b < Compiler.Constants.evmModulus) :
    (Verity.Core.Uint256.ofNat a * Verity.Core.Uint256.ofNat b).val =
      a * b % Compiler.Constants.evmModulus := by
  show (Verity.Core.Uint256.ofNat
    ((Verity.Core.Uint256.ofNat a).val * (Verity.Core.Uint256.ofNat b).val)).val = _
  rw [uint256_ofNat_val_of_lt ha, uint256_ofNat_val_of_lt hb]
  rfl

/-- `Uint256` division by a bounded divisor, as a `Nat` quotient guarded by `d = 0`. -/
private theorem uint256_div_ofNat_val (x : Verity.Core.Uint256) {d : Nat}
    (hd : d < Compiler.Constants.evmModulus) :
    (x / Verity.Core.Uint256.ofNat d).val = if d = 0 then 0 else x.val / d := by
  show (Verity.Core.Uint256.div x (Verity.Core.Uint256.ofNat d)).val = _
  simp only [Verity.Core.Uint256.div, uint256_ofNat_val_of_lt hd]
  split
  · rfl
  · exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) x.isLt)

private theorem uint256_ofNat_sub_one_val {d : Nat}
    (hd : d < Compiler.Constants.evmModulus) (hne : d ≠ 0) :
    (Verity.Core.Uint256.ofNat d - 1).val = d - 1 := by
  have hle : (1 : Verity.Core.Uint256).val ≤ (Verity.Core.Uint256.ofNat d).val := by
    rw [Verity.Core.Uint256.val_one, uint256_ofNat_val_of_lt hd]
    omega
  have hsub := Verity.Core.Uint256.sub_eq_of_le hle
  rwa [uint256_ofNat_val_of_lt hd, Verity.Core.Uint256.val_one] at hsub

/-- `Uint256` round-up quotient `(x + (d - 1)) / d` as a `Nat` expression. -/
private theorem uint256_add_sub_one_div_val (x : Verity.Core.Uint256) {d : Nat}
    (hd : d < Compiler.Constants.evmModulus) :
    ((x + (Verity.Core.Uint256.ofNat d - 1)) / Verity.Core.Uint256.ofNat d).val =
      if d = 0 then 0 else (x.val + (d - 1)) % Compiler.Constants.evmModulus / d := by
  rw [uint256_div_ofNat_val _ hd]
  by_cases hzero : d = 0
  · simp [hzero]
  · simp only [hzero, ↓reduceIte]
    show (Verity.Core.Uint256.ofNat (x.val + (Verity.Core.Uint256.ofNat d - 1).val)).val / d = _
    rw [uint256_ofNat_sub_one_val hd hzero]
    rfl

/-- IR evaluation of the round-up quotient `div(add(num, sub(d, 1)), d)`. -/
private theorem evalIRExpr_roundUpDiv_of_eval
    {state : IRState}
    {numIR denomIR : YulExpr}
    {num denom : Nat}
    (hnum : evalIRExpr state numIR = some num)
    (hdenom : evalIRExpr state denomIR = some denom)
    (hdenomLt : denom < Compiler.Constants.evmModulus) :
    evalIRExpr state (YulExpr.call "div"
        [YulExpr.call "add" [numIR, YulExpr.call "sub" [denomIR, YulExpr.lit 1]], denomIR]) =
      some (if denom = 0 then 0 else
        (num + (denom - 1)) % Compiler.Constants.evmModulus / denom) := by
  rw [evalIRExpr_div_of_eval (evalIRExpr_add_of_eval hnum
    (evalIRExpr_sub_of_eval hdenom (evalIRExpr_lit_eq state 1))) hdenom]
  simp only [Nat.mod_eq_of_lt hdenomLt, Nat.mod_mod,
    Nat.mod_eq_of_lt (by decide : 1 < Compiler.Constants.evmModulus)]
  by_cases hzero : denom = 0
  · simp [hzero]
  · simp only [hzero, ↓reduceIte, evmModulus_add_sub_one_mod hdenomLt hzero]

/-- IR evaluation of `ceilDiv`'s lowering `mul(iszero(iszero(l)), add(div(sub(l, 1), r), 1))`. -/
private theorem evalIRExpr_ceilDiv_of_eval
    {state : IRState}
    {lhsIR rhsIR : YulExpr}
    {lhsVal rhsVal : Nat}
    (hlhs : evalIRExpr state lhsIR = some lhsVal)
    (hrhs : evalIRExpr state rhsIR = some rhsVal)
    (hlhsLt : lhsVal < Compiler.Constants.evmModulus)
    (hrhsLt : rhsVal < Compiler.Constants.evmModulus) :
    evalIRExpr state (YulExpr.call "mul" [
        YulExpr.call "iszero" [YulExpr.call "iszero" [lhsIR]],
        YulExpr.call "add" [
          YulExpr.call "div" [YulExpr.call "sub" [lhsIR, YulExpr.lit 1], rhsIR],
          YulExpr.lit 1]]) =
      some (if lhsVal = 0 then 0 else (if rhsVal = 0 then 0 else (lhsVal - 1) / rhsVal) + 1) := by
  have hLit1 := evalIRExpr_lit_eq state 1
  rw [evalIRExpr_mul_of_eval
    (evalIRExpr_iszero_of_lt (evalIRExpr_iszero_of_lt hlhs hlhsLt) (boolWord_lt_evmModulus _))
    (evalIRExpr_add_of_eval
      (evalIRExpr_div_of_eval (evalIRExpr_sub_of_eval hlhs hLit1) hrhs) hLit1)]
  by_cases hzero : lhsVal = 0
  · simp [hzero, SourceSemantics.boolWord]
  · have hpredLt : lhsVal - 1 < Compiler.Constants.evmModulus := by omega
    simp only [hzero, SourceSemantics.boolWord, Nat.mod_eq_of_lt hlhsLt, Nat.mod_eq_of_lt hrhsLt,
      Nat.mod_eq_of_lt (by decide : 1 < Compiler.Constants.evmModulus), Nat.mod_mod,
      evmModulus_add_sub_one_mod hlhsLt hzero, Nat.mod_eq_of_lt hpredLt, decide_false,
      decide_true, Bool.false_eq_true, ↓reduceIte, Nat.one_mul]
    split <;> congr 1
    exact Nat.mod_eq_of_lt (pred_div_add_one_lt_evmModulus rhsVal hlhsLt hzero)

/-- `Uint256` `ceilDiv` result as a `Nat` expression for bounded operands. -/
private theorem uint256_ceilDiv_val {lhsVal rhsVal : Nat}
    (hlhsLt : lhsVal < Compiler.Constants.evmModulus)
    (hrhsLt : rhsVal < Compiler.Constants.evmModulus) :
    (if (Verity.Core.Uint256.ofNat lhsVal) == (0 : Verity.Core.Uint256) then 0
      else ((Verity.Core.Uint256.ofNat lhsVal - 1) / Verity.Core.Uint256.ofNat rhsVal + 1).val) =
      if lhsVal = 0 then 0 else (if rhsVal = 0 then 0 else (lhsVal - 1) / rhsVal) + 1 := by
  by_cases hzero : lhsVal = 0
  · subst hzero
    simp
  · have hne : (Verity.Core.Uint256.ofNat lhsVal == (0 : Verity.Core.Uint256)) = false := by
      rw [beq_eq_false_iff_ne]
      intro h
      have hval := congrArg Verity.Core.Uint256.val h
      rw [uint256_ofNat_val_of_lt hlhsLt] at hval
      exact hzero (hval.trans Verity.Core.Uint256.val_zero)
    simp only [hne, hzero, Bool.false_eq_true, ↓reduceIte]
    show (Verity.Core.Uint256.ofNat (((Verity.Core.Uint256.ofNat lhsVal - 1) /
      Verity.Core.Uint256.ofNat rhsVal).val + (1 : Verity.Core.Uint256).val)).val = _
    rw [uint256_div_ofNat_val _ hrhsLt, uint256_ofNat_sub_one_val hlhsLt hzero,
      Verity.Core.Uint256.val_one]
    by_cases hrhsZero : rhsVal = 0
    · simp [hrhsZero]
    · simp only [hrhsZero, ↓reduceIte]
      exact uint256_ofNat_val_of_lt (pred_div_add_one_lt_evmModulus rhsVal hlhsLt hzero)

private theorem evalExpr_wDivUp_of_values
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {lhs rhs : Expr}
    {lhsVal rhsVal : Nat}
    (hlhs : SourceSemantics.evalExpr fields runtime lhs = some lhsVal)
    (hrhs : SourceSemantics.evalExpr fields runtime rhs = some rhsVal) :
    SourceSemantics.evalExpr fields runtime (.wDivUp lhs rhs) =
      some ((((Verity.Core.Uint256.ofNat lhsVal * (1000000000000000000 : Verity.Core.Uint256)) +
        (Verity.Core.Uint256.ofNat rhsVal - 1)) / Verity.Core.Uint256.ofNat rhsVal).val) := by
  calc
    SourceSemantics.evalExpr fields runtime (.wDivUp lhs rhs)
        = (do
            let lhs ← do
              let a ← SourceSemantics.evalExpr fields runtime lhs
              pure (Verity.Core.Uint256.ofNat a)
            let rhs ← do
              let a ← SourceSemantics.evalExpr fields runtime rhs
              pure (Verity.Core.Uint256.ofNat a)
            let wad : Verity.Core.Uint256 := 1000000000000000000
            pure (((lhs * wad) + (rhs - 1)) / rhs).val) := rfl
    _ = _ := by simp [hlhs, hrhs]

theorem eval_compileExpr_wDivUp_of_compiled
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhsCompile : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhsCompile : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR)
    (hlhsEval : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs))
    (hrhsEval : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs))
    (hlhsLt : SourceSemantics.evalExpr fields runtime lhs < Compiler.Constants.evmModulus)
    (hrhsLt : SourceSemantics.evalExpr fields runtime rhs < Compiler.Constants.evmModulus) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata (.wDivUp lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
        some (SourceSemantics.evalExpr fields runtime (.wDivUp lhs rhs)) := by
  obtain ⟨lhsVal, hlhsSrc, hlhsEval', hlhsLt'⟩ := exists_source_value_of_evalIRExpr hlhsEval hlhsLt
  obtain ⟨rhsVal, hrhsSrc, hrhsEval', hrhsLt'⟩ := exists_source_value_of_evalIRExpr hrhsEval hrhsLt
  have hDiv := evalIRExpr_roundUpDiv_of_eval
    (evalIRExpr_mul_of_eval hlhsEval' (evalIRExpr_lit_eq state 1000000000000000000))
    hrhsEval' hrhsLt'
  have hWad : (Verity.Core.Uint256.ofNat lhsVal *
      (1000000000000000000 : Verity.Core.Uint256)).val =
      lhsVal * 1000000000000000000 % Compiler.Constants.evmModulus :=
    uint256_ofNat_mul_ofNat_val hlhsLt' (by decide)
  simp only [compileExpr_wDivUp_ok hlhsCompile hrhsCompile, Except.toOption, Option.getD]
  rw [hDiv, evalExpr_wDivUp_of_values hlhsSrc hrhsSrc, uint256_add_sub_one_div_val _ hrhsLt',
    hWad]
  rfl

private theorem evalExpr_mulDivDown_of_values
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {a b c : Expr}
    {aVal bVal cVal : Nat}
    (ha : SourceSemantics.evalExpr fields runtime a = some aVal)
    (hb : SourceSemantics.evalExpr fields runtime b = some bVal)
    (hc : SourceSemantics.evalExpr fields runtime c = some cVal) :
    SourceSemantics.evalExpr fields runtime (.mulDivDown a b c) =
      some (((Verity.Core.Uint256.ofNat aVal * Verity.Core.Uint256.ofNat bVal) /
        Verity.Core.Uint256.ofNat cVal).val) := by
  calc
    SourceSemantics.evalExpr fields runtime (.mulDivDown a b c)
        = (do
            let lhs ← do
              let a ← SourceSemantics.evalExpr fields runtime a
              pure (Verity.Core.Uint256.ofNat a)
            let rhs ← do
              let a ← SourceSemantics.evalExpr fields runtime b
              pure (Verity.Core.Uint256.ofNat a)
            let denom ← do
              let a ← SourceSemantics.evalExpr fields runtime c
              pure (Verity.Core.Uint256.ofNat a)
            pure ((lhs * rhs) / denom).val) := rfl
    _ = _ := by simp [ha, hb, hc]

theorem eval_compileExpr_mulDivDown_of_compiled
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {a b c : Expr}
    {aIR bIR cIR : YulExpr}
    (haCompile : CompilationModel.compileExpr fields .calldata a = Except.ok aIR)
    (hbCompile : CompilationModel.compileExpr fields .calldata b = Except.ok bIR)
    (hcCompile : CompilationModel.compileExpr fields .calldata c = Except.ok cIR)
    (haEval : evalIRExpr state aIR = some (SourceSemantics.evalExpr fields runtime a))
    (hbEval : evalIRExpr state bIR = some (SourceSemantics.evalExpr fields runtime b))
    (hcEval : evalIRExpr state cIR = some (SourceSemantics.evalExpr fields runtime c))
    (haLt : SourceSemantics.evalExpr fields runtime a < Compiler.Constants.evmModulus)
    (hbLt : SourceSemantics.evalExpr fields runtime b < Compiler.Constants.evmModulus)
    (hcLt : SourceSemantics.evalExpr fields runtime c < Compiler.Constants.evmModulus) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata (.mulDivDown a b c) |>.toOption.getD (YulExpr.lit 0)) =
        some (SourceSemantics.evalExpr fields runtime (.mulDivDown a b c)) := by
  obtain ⟨aVal, haSrc, haEval', haLt'⟩ := exists_source_value_of_evalIRExpr haEval haLt
  obtain ⟨bVal, hbSrc, hbEval', hbLt'⟩ := exists_source_value_of_evalIRExpr hbEval hbLt
  obtain ⟨cVal, hcSrc, hcEval', hcLt'⟩ := exists_source_value_of_evalIRExpr hcEval hcLt
  have hDiv := evalIRExpr_div_of_eval (evalIRExpr_mul_of_eval haEval' hbEval') hcEval'
  simp only [Nat.mod_eq_of_lt hcLt', Nat.mod_mod] at hDiv
  simp only [compileExpr_mulDivDown_ok haCompile hbCompile hcCompile, Except.toOption,
    Option.getD]
  rw [hDiv, evalExpr_mulDivDown_of_values haSrc hbSrc hcSrc, uint256_div_ofNat_val _ hcLt',
    uint256_ofNat_mul_ofNat_val haLt' hbLt']
  rfl

private theorem evalExpr_mulDivUp_of_values
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {a b c : Expr}
    {aVal bVal cVal : Nat}
    (ha : SourceSemantics.evalExpr fields runtime a = some aVal)
    (hb : SourceSemantics.evalExpr fields runtime b = some bVal)
    (hc : SourceSemantics.evalExpr fields runtime c = some cVal) :
    SourceSemantics.evalExpr fields runtime (.mulDivUp a b c) =
      some ((((Verity.Core.Uint256.ofNat aVal * Verity.Core.Uint256.ofNat bVal) +
        (Verity.Core.Uint256.ofNat cVal - 1)) / Verity.Core.Uint256.ofNat cVal).val) := by
  calc
    SourceSemantics.evalExpr fields runtime (.mulDivUp a b c)
        = (do
            let lhs ← do
              let a ← SourceSemantics.evalExpr fields runtime a
              pure (Verity.Core.Uint256.ofNat a)
            let rhs ← do
              let a ← SourceSemantics.evalExpr fields runtime b
              pure (Verity.Core.Uint256.ofNat a)
            let denom ← do
              let a ← SourceSemantics.evalExpr fields runtime c
              pure (Verity.Core.Uint256.ofNat a)
            pure (((lhs * rhs) + (denom - 1)) / denom).val) := rfl
    _ = _ := by simp [ha, hb, hc]

theorem eval_compileExpr_mulDivUp_of_compiled
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {a b c : Expr}
    {aIR bIR cIR : YulExpr}
    (haCompile : CompilationModel.compileExpr fields .calldata a = Except.ok aIR)
    (hbCompile : CompilationModel.compileExpr fields .calldata b = Except.ok bIR)
    (hcCompile : CompilationModel.compileExpr fields .calldata c = Except.ok cIR)
    (haEval : evalIRExpr state aIR = some (SourceSemantics.evalExpr fields runtime a))
    (hbEval : evalIRExpr state bIR = some (SourceSemantics.evalExpr fields runtime b))
    (hcEval : evalIRExpr state cIR = some (SourceSemantics.evalExpr fields runtime c))
    (haLt : SourceSemantics.evalExpr fields runtime a < Compiler.Constants.evmModulus)
    (hbLt : SourceSemantics.evalExpr fields runtime b < Compiler.Constants.evmModulus)
    (hcLt : SourceSemantics.evalExpr fields runtime c < Compiler.Constants.evmModulus) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata (.mulDivUp a b c) |>.toOption.getD (YulExpr.lit 0)) =
        some (SourceSemantics.evalExpr fields runtime (.mulDivUp a b c)) := by
  obtain ⟨aVal, haSrc, haEval', haLt'⟩ := exists_source_value_of_evalIRExpr haEval haLt
  obtain ⟨bVal, hbSrc, hbEval', hbLt'⟩ := exists_source_value_of_evalIRExpr hbEval hbLt
  obtain ⟨cVal, hcSrc, hcEval', hcLt'⟩ := exists_source_value_of_evalIRExpr hcEval hcLt
  have hDiv := evalIRExpr_roundUpDiv_of_eval
    (evalIRExpr_mul_of_eval haEval' hbEval') hcEval' hcLt'
  simp only [compileExpr_mulDivUp_ok haCompile hbCompile hcCompile, Except.toOption,
    Option.getD]
  rw [hDiv, evalExpr_mulDivUp_of_values haSrc hbSrc hcSrc, uint256_add_sub_one_div_val _ hcLt',
    uint256_ofNat_mul_ofNat_val haLt' hbLt']
  rfl

private theorem evalExpr_ceilDiv_of_values
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {lhs rhs : Expr}
    {lhsVal rhsVal : Nat}
    (hlhs : SourceSemantics.evalExpr fields runtime lhs = some lhsVal)
    (hrhs : SourceSemantics.evalExpr fields runtime rhs = some rhsVal) :
    SourceSemantics.evalExpr fields runtime (.ceilDiv lhs rhs) =
      some (if (Verity.Core.Uint256.ofNat lhsVal) == (0 : Verity.Core.Uint256) then 0
        else ((Verity.Core.Uint256.ofNat lhsVal - 1) / Verity.Core.Uint256.ofNat rhsVal + 1).val) := by
  calc
    SourceSemantics.evalExpr fields runtime (.ceilDiv lhs rhs)
        = (do
            let lhs ← do
              let a ← SourceSemantics.evalExpr fields runtime lhs
              pure (Verity.Core.Uint256.ofNat a)
            let rhs ← do
              let a ← SourceSemantics.evalExpr fields runtime rhs
              pure (Verity.Core.Uint256.ofNat a)
            pure (if lhs == 0 then 0 else ((lhs - 1) / rhs + 1).val)) := by rfl
    _ = some (if (Verity.Core.Uint256.ofNat lhsVal) == (0 : Verity.Core.Uint256) then 0
          else ((Verity.Core.Uint256.ofNat lhsVal - 1) / Verity.Core.Uint256.ofNat rhsVal + 1).val) := by
          simp [hlhs, hrhs]

theorem eval_compileExpr_ceilDiv_of_compiled
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhsCompile : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhsCompile : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR)
    (hlhsEval : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs))
    (hrhsEval : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs))
    (hlhsLt : SourceSemantics.evalExpr fields runtime lhs < Compiler.Constants.evmModulus)
    (hrhsLt : SourceSemantics.evalExpr fields runtime rhs < Compiler.Constants.evmModulus) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata (.ceilDiv lhs rhs) |>.toOption.getD
        (YulExpr.lit 0)) =
        some (SourceSemantics.evalExpr fields runtime (.ceilDiv lhs rhs)) := by
  obtain ⟨lhsVal, hlhsSrc, hlhsEval', hlhsLt'⟩ := exists_source_value_of_evalIRExpr hlhsEval hlhsLt
  obtain ⟨rhsVal, hrhsSrc, hrhsEval', hrhsLt'⟩ := exists_source_value_of_evalIRExpr hrhsEval hrhsLt
  simp only [compileExpr_ceilDiv_ok hlhsCompile hrhsCompile, Except.toOption, Option.getD]
  rw [evalIRExpr_ceilDiv_of_eval hlhsEval' hrhsEval' hlhsLt' hrhsLt',
    evalExpr_ceilDiv_of_values hlhsSrc hrhsSrc, uint256_ceilDiv_val hlhsLt' hrhsLt']
  rfl

theorem evalExpr_literal_lt_evmModulus
    (fields : List Field)
    (state : SourceSemantics.RuntimeState)
    (value : Nat) :
    SourceSemantics.evalExpr fields state (.literal value) < Compiler.Constants.evmModulus := by
  change SourceSemantics.wordNormalize value < Compiler.Constants.evmModulus
  exact wordNormalize_lt_evmModulus value

theorem evalExpr_param_lt_evmModulus_of_bindingsBounded
    (fields : List Field)
    (state : SourceSemantics.RuntimeState)
    (name : String)
    (hbounded : bindingsBounded state.bindings) :
    SourceSemantics.evalExpr fields state (.param name) < Compiler.Constants.evmModulus := by
  change SourceSemantics.lookupValue state.bindings name < Compiler.Constants.evmModulus
  exact hbounded name

theorem evalExpr_localVar_lt_evmModulus_of_bindingsBounded
    (fields : List Field)
    (state : SourceSemantics.RuntimeState)
    (name : String)
    (hbounded : bindingsBounded state.bindings) :
    SourceSemantics.evalExpr fields state (.localVar name) < Compiler.Constants.evmModulus := by
  change SourceSemantics.lookupValue state.bindings name < Compiler.Constants.evmModulus
  exact hbounded name

theorem exprBoundNamesPresent_of_subset
    {expr subexpr : Expr}
    {bindings : List (String × Nat)}
    (hpresent : exprBoundNamesPresent expr bindings)
    (hsubset : ∀ name, name ∈ exprBoundNames subexpr → name ∈ exprBoundNames expr) :
    exprBoundNamesPresent subexpr bindings := by
  intro name hmem
  exact hpresent name (hsubset name hmem)

-- ExprCompileCore is now in ExprCore.lean

theorem compileExpr_core_ok
    {fields : List Field}
    {expr : Expr}
    (hcore : ExprCompileCore expr) :
    ∃ exprIR, CompilationModel.compileExpr fields .calldata expr = Except.ok exprIR := by
  induction hcore with
  | literal | param | constructorArg | localVar | caller | contractAddress | txOrigin
    | msgValue | blockTimestamp | blockNumber | chainid | blobbasefee | calldatasize
    | returndataSize =>
      exact ⟨_, by
        unfold CompilationModel.compileExpr CompilationModel.compileExprWithInternals
        rfl⟩
  | builtinExp _ _ ihB ihE =>
      obtain ⟨_, hB⟩ := ihB
      obtain ⟨_, hE⟩ := ihE
      exact ⟨_, compileExpr_builtinExp_ok hB hE⟩
  | _ =>
      -- Every other constructor compiles its operands and wraps them in a fixed call.
      casesm* ∃ _, _
      simp only [← CompilationModel.compileExprWithInternals_nil_eq] at *
      rw [CompilationModel.compileExprWithInternals]
      simp only [*]
      exact ⟨_, rfl⟩

private theorem option_bind_lt_evmModulus {α : Type} {o : Option α} {f : α → Option Nat}
    (h : ∀ a, f a < some Compiler.Constants.evmModulus) :
    o >>= f < some Compiler.Constants.evmModulus := by
  cases o
  · trivial
  · exact h _

private theorem option_bind_lt_evmModulus_of_lt {o : Option Nat} {f : Nat → Option Nat}
    (ho : o < some Compiler.Constants.evmModulus)
    (h : ∀ a, a < Compiler.Constants.evmModulus → f a < some Compiler.Constants.evmModulus) :
    o >>= f < some Compiler.Constants.evmModulus := by
  cases o
  · trivial
  · exact h _ ho

private theorem some_lt_evmModulus_of_lt {n : Nat} (h : n < Compiler.Constants.evmModulus) :
    some n < some Compiler.Constants.evmModulus :=
  h

/-- Restrict the per-expression binding hypotheses to a subexpression. -/
private theorem onExpr_hyps_of_subset
    {expr subexpr : Expr}
    {bindings : List (String × Nat)}
    {state : IRState}
    (hexact : bindingsExactlyMatchIRVarsOnExpr expr bindings state)
    (hpresent : exprBoundNamesPresent expr bindings)
    (hsubset : ∀ name, name ∈ exprBoundNames subexpr → name ∈ exprBoundNames expr) :
    bindingsExactlyMatchIRVarsOnExpr subexpr bindings state ∧
      exprBoundNamesPresent subexpr bindings :=
  ⟨bindingsExactlyMatchIRVarsOnExpr_of_subset hexact hsubset,
    exprBoundNamesPresent_of_subset hpresent hsubset⟩

private theorem evalExpr_constructorArg_lt_evmModulus
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    (idx : Nat)
    (hbounded : bindingsBounded runtime.bindings)
    (hpresent : exprBoundNamesPresent (.constructorArg idx) runtime.bindings) :
    SourceSemantics.evalExpr fields runtime (.constructorArg idx) <
      Compiler.Constants.evmModulus := by
  rcases hpresent s!"arg{idx}" (by simp [exprBoundNames]) with ⟨value, hlookup⟩
  have hsourceLookup :
      SourceSemantics.lookupBinding? runtime.bindings s!"arg{idx}" = some value := by
    simpa [lookupBinding?, SourceSemantics.lookupBinding?] using hlookup
  have hlt := hbounded s!"arg{idx}"
  rw [lookupValue_eq_of_lookupBinding?_some hlookup] at hlt
  change SourceSemantics.lookupBinding? runtime.bindings s!"arg{idx}" <
    Compiler.Constants.evmModulus
  rw [hsourceLookup]
  exact hlt

private theorem evalExpr_ceilDiv_lt_evmModulus
    (fields : List Field)
    (runtime : SourceSemantics.RuntimeState)
    (lhs rhs : Expr) :
    SourceSemantics.evalExpr fields runtime (.ceilDiv lhs rhs) <
      Compiler.Constants.evmModulus := by
  show (do let l ← SourceSemantics.evalExpr fields runtime lhs
           let r ← SourceSemantics.evalExpr fields runtime rhs
           pure (if (Verity.Core.Uint256.ofNat l) == (0 : Verity.Core.Uint256) then 0
             else ((Verity.Core.Uint256.ofNat l - 1) / Verity.Core.Uint256.ofNat r + 1).val)) < _
  refine option_bind_lt_evmModulus fun _ => option_bind_lt_evmModulus fun _ =>
    some_lt_evmModulus_of_lt ?_
  split
  · decide
  · exact Verity.Core.Uint256.isLt _

private theorem returndataOptionalBool_lt_evmModulus
    (world : Verity.ContractState) (offset : Nat) :
    world.returndataOptionalBool offset < Compiler.Constants.evmModulus := by
  have hle : world.returndataOptionalBool offset ≤ 1 := by
    unfold Verity.ContractState.returndataOptionalBool
    split
    · exact Nat.le_refl 1
    · split
      · exact Nat.le_refl 1
      · exact Nat.zero_le 1
  exact Nat.lt_of_le_of_lt hle (by decide)

/-- Boundedness of `evalExpr` on `expr` for every state satisfying the binding hypotheses. -/
private def EvalExprBounded (fields : List Field) (expr : Expr) : Prop :=
  ∀ (runtime : SourceSemantics.RuntimeState) (state : IRState),
    bindingsExactlyMatchIRVarsOnExpr expr runtime.bindings state →
    bindingsBounded runtime.bindings → exprBoundNamesPresent expr runtime.bindings →
    runtimeStateMatchesIR fields runtime state →
    SourceSemantics.evalExpr fields runtime expr < Compiler.Constants.evmModulus

/-- Apply an `EvalExprBounded` induction hypothesis to a subexpression of `expr`. -/
private theorem evalExpr_lt_evmModulus_of_subexpr
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {expr subexpr : Expr}
    (ih : EvalExprBounded fields subexpr)
    (hexact : bindingsExactlyMatchIRVarsOnExpr expr runtime.bindings state)
    (hbounded : bindingsBounded runtime.bindings)
    (hpresent : exprBoundNamesPresent expr runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state)
    (hsubset : ∀ name, name ∈ exprBoundNames subexpr → name ∈ exprBoundNames expr := by
      intro _ h; simp [exprBoundNames, exprListBoundNames, h]) :
    SourceSemantics.evalExpr fields runtime subexpr < Compiler.Constants.evmModulus := by
  obtain ⟨hexact', hpresent'⟩ := onExpr_hyps_of_subset hexact hpresent hsubset
  exact ih runtime state hexact' hbounded hpresent' hruntime

private theorem evalExpr_min_lt_evmModulus
    {fields : List Field} {runtime : SourceSemantics.RuntimeState} {lhs rhs : Expr}
    (hlhs : SourceSemantics.evalExpr fields runtime lhs < Compiler.Constants.evmModulus)
    (hrhs : SourceSemantics.evalExpr fields runtime rhs < Compiler.Constants.evmModulus) :
    SourceSemantics.evalExpr fields runtime (.min lhs rhs) < Compiler.Constants.evmModulus :=
  option_bind_lt_evmModulus_of_lt hlhs fun _ _ => option_bind_lt_evmModulus_of_lt hrhs fun _ _ =>
    some_lt_evmModulus_of_lt (by split <;> assumption)

private theorem evalExpr_max_lt_evmModulus
    {fields : List Field} {runtime : SourceSemantics.RuntimeState} {lhs rhs : Expr}
    (hlhs : SourceSemantics.evalExpr fields runtime lhs < Compiler.Constants.evmModulus)
    (hrhs : SourceSemantics.evalExpr fields runtime rhs < Compiler.Constants.evmModulus) :
    SourceSemantics.evalExpr fields runtime (.max lhs rhs) < Compiler.Constants.evmModulus :=
  option_bind_lt_evmModulus_of_lt hlhs fun _ _ => option_bind_lt_evmModulus_of_lt hrhs fun _ _ =>
    some_lt_evmModulus_of_lt (by split <;> assumption)

private theorem evalExpr_ite_lt_evmModulus
    {fields : List Field} {runtime : SourceSemantics.RuntimeState} {cond thenVal elseVal : Expr}
    (hthen : SourceSemantics.evalExpr fields runtime thenVal < Compiler.Constants.evmModulus)
    (helse : SourceSemantics.evalExpr fields runtime elseVal < Compiler.Constants.evmModulus) :
    SourceSemantics.evalExpr fields runtime (.ite cond thenVal elseVal) <
      Compiler.Constants.evmModulus :=
  option_bind_lt_evmModulus fun _ => by split <;> assumption

private theorem evalExprBounded_min {fields : List Field} {lhs rhs : Expr}
    (ihL : EvalExprBounded fields lhs) (ihR : EvalExprBounded fields rhs) :
    EvalExprBounded fields (.min lhs rhs) := fun _ _ hexact hbounded hpresent hruntime =>
  evalExpr_min_lt_evmModulus
    (evalExpr_lt_evmModulus_of_subexpr ihL hexact hbounded hpresent hruntime)
    (evalExpr_lt_evmModulus_of_subexpr ihR hexact hbounded hpresent hruntime)

private theorem evalExprBounded_max {fields : List Field} {lhs rhs : Expr}
    (ihL : EvalExprBounded fields lhs) (ihR : EvalExprBounded fields rhs) :
    EvalExprBounded fields (.max lhs rhs) := fun _ _ hexact hbounded hpresent hruntime =>
  evalExpr_max_lt_evmModulus
    (evalExpr_lt_evmModulus_of_subexpr ihL hexact hbounded hpresent hruntime)
    (evalExpr_lt_evmModulus_of_subexpr ihR hexact hbounded hpresent hruntime)

private theorem evalExprBounded_ite {fields : List Field} {cond thenVal elseVal : Expr}
    (ihT : EvalExprBounded fields thenVal) (ihE : EvalExprBounded fields elseVal) :
    EvalExprBounded fields (.ite cond thenVal elseVal) :=
  fun _ _ hexact hbounded hpresent hruntime =>
    evalExpr_ite_lt_evmModulus
      (evalExpr_lt_evmModulus_of_subexpr ihT hexact hbounded hpresent hruntime)
      (evalExpr_lt_evmModulus_of_subexpr ihE hexact hbounded hpresent hruntime)

private theorem evalExpr_calldataload_lt_evmModulus
    (fields : List Field) (runtime : SourceSemantics.RuntimeState) (offset : Expr) :
    SourceSemantics.evalExpr fields runtime (.calldataload offset) <
      Compiler.Constants.evmModulus :=
  option_bind_lt_evmModulus fun _ =>
    some_lt_evmModulus_of_lt (calldataloadWord_lt_evmModulus _ _ _)

private theorem evalExpr_returndataOptionalBoolAt_lt_evmModulus
    (fields : List Field) (runtime : SourceSemantics.RuntimeState) (offset : Expr) :
    SourceSemantics.evalExpr fields runtime (.returndataOptionalBoolAt offset) <
      Compiler.Constants.evmModulus :=
  option_bind_lt_evmModulus fun _ =>
    some_lt_evmModulus_of_lt (returndataOptionalBool_lt_evmModulus _ _)

private theorem evalExpr_keccak256_lt_evmModulus
    (fields : List Field) (runtime : SourceSemantics.RuntimeState) (offset size : Expr) :
    SourceSemantics.evalExpr fields runtime (.keccak256 offset size) <
      Compiler.Constants.evmModulus :=
  option_bind_lt_evmModulus fun _ => option_bind_lt_evmModulus fun _ =>
    some_lt_evmModulus_of_lt (Nat.mod_lt _ (by decide))

private theorem evalExprBounded_of_core {fields : List Field} {expr : Expr}
    (hcore : ExprCompileCore expr) : EvalExprBounded fields expr := by
  induction hcore with
  | literal value =>
      exact fun _ _ _ _ _ _ => some_lt_evmModulus_of_lt (wordNormalize_lt_evmModulus value)
  | param name | localVar name => exact fun _ _ _ hbounded _ _ => hbounded name
  | constructorArg idx =>
      exact fun _ _ _ hbounded hpresent _ =>
        evalExpr_constructorArg_lt_evmModulus idx hbounded hpresent
  | min _ _ ihL ihR => exact evalExprBounded_min ihL ihR
  | max _ _ ihL ihR => exact evalExprBounded_max ihL ihR
  | ite _ _ _ _ ihT ihE => exact evalExprBounded_ite ihT ihE
  | ceilDiv => exact fun runtime _ _ _ _ _ => evalExpr_ceilDiv_lt_evmModulus fields runtime _ _
  | calldataload => exact fun runtime _ _ _ _ _ => evalExpr_calldataload_lt_evmModulus _ runtime _
  | returndataOptionalBoolAt =>
      exact fun runtime _ _ _ _ _ => evalExpr_returndataOptionalBoolAt_lt_evmModulus _ runtime _
  | keccak256 => exact fun runtime _ _ _ _ _ => evalExpr_keccak256_lt_evmModulus _ runtime _ _
  | _ =>
      -- The remaining constructors bind their operands and return a word-sized value.
      intro _ _ _ _ _ _
      repeat' refine option_bind_lt_evmModulus fun _ => ?_
      first
        | exact some_lt_evmModulus_of_lt (Verity.Core.Uint256.isLt _)
        | exact some_lt_evmModulus_of_lt (boolWord_lt_evmModulus _)
        | exact some_lt_evmModulus_of_lt (Nat.lt_trans (Verity.Core.Address.isLt _) (by decide))

theorem evalExpr_lt_evmModulus_core_onExpr
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {expr : Expr}
    (hcore : ExprCompileCore expr)
    (hexact : bindingsExactlyMatchIRVarsOnExpr expr runtime.bindings state)
    (hbounded : bindingsBounded runtime.bindings)
    (hpresent : exprBoundNamesPresent expr runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state) :
    SourceSemantics.evalExpr fields runtime expr < Compiler.Constants.evmModulus :=
  evalExprBounded_of_core hcore runtime state hexact hbounded hpresent hruntime

/-- Soundness of `compileExpr` on `expr` for every state satisfying the binding hypotheses. -/
private def CompileExprSound (fields : List Field) (expr : Expr) : Prop :=
  ∀ (runtime : SourceSemantics.RuntimeState) (state : IRState),
    bindingsExactlyMatchIRVarsOnExpr expr runtime.bindings state →
    bindingsBounded runtime.bindings → exprBoundNamesPresent expr runtime.bindings →
    runtimeStateMatchesIR fields runtime state →
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata expr |>.toOption.getD (YulExpr.lit 0)) =
        some (SourceSemantics.evalExpr fields runtime expr)

private theorem evalIRExpr_of_compileExpr_eq_ok
    {fields : List Field}
    {state : IRState}
    {expr : Expr}
    {exprIR : YulExpr}
    {value : Option Nat}
    (hcompile : CompilationModel.compileExpr fields .calldata expr = Except.ok exprIR)
    (heval : evalIRExpr state
      (CompilationModel.compileExpr fields .calldata expr |>.toOption.getD (YulExpr.lit 0)) =
        some value) :
    evalIRExpr state exprIR = some value := by
  rw [hcompile] at heval
  simpa only [Except.toOption, Option.getD_some] using heval

/-- Compile a core subexpression of `expr` and evaluate it through its induction hypothesis. -/
private theorem compileExprSound_subexpr
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {expr subexpr : Expr}
    (hcore : ExprCompileCore subexpr)
    (ih : CompileExprSound fields subexpr)
    (hexact : bindingsExactlyMatchIRVarsOnExpr expr runtime.bindings state)
    (hbounded : bindingsBounded runtime.bindings)
    (hpresent : exprBoundNamesPresent expr runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state)
    (hsubset : ∀ name, name ∈ exprBoundNames subexpr → name ∈ exprBoundNames expr := by
      intro _ h; simp [exprBoundNames, exprListBoundNames, h]) :
    ∃ subexprIR, CompilationModel.compileExpr fields .calldata subexpr = Except.ok subexprIR ∧
      evalIRExpr state subexprIR = some (SourceSemantics.evalExpr fields runtime subexpr) ∧
      SourceSemantics.evalExpr fields runtime subexpr < Compiler.Constants.evmModulus := by
  obtain ⟨hexact', hpresent'⟩ := onExpr_hyps_of_subset hexact hpresent hsubset
  obtain ⟨subexprIR, hcompile⟩ := compileExpr_core_ok (fields := fields) hcore
  exact ⟨subexprIR, hcompile, evalIRExpr_of_compileExpr_eq_ok hcompile
      (ih runtime state hexact' hbounded hpresent' hruntime),
    evalExprBounded_of_core hcore runtime state hexact' hbounded hpresent' hruntime⟩

private theorem compileExprSound_unary
    {fields : List Field}
    {arg expr : Expr}
    (hA : ExprCompileCore arg)
    (ihA : CompileExprSound fields arg)
    (heval : ∀ {runtime : SourceSemantics.RuntimeState} {state : IRState} {argIR : YulExpr},
      CompilationModel.compileExpr fields .calldata arg = Except.ok argIR →
      evalIRExpr state argIR = some (SourceSemantics.evalExpr fields runtime arg) →
      SourceSemantics.evalExpr fields runtime arg < Compiler.Constants.evmModulus →
      runtimeStateMatchesIR fields runtime state →
      evalIRExpr state
        (CompilationModel.compileExpr fields .calldata expr |>.toOption.getD (YulExpr.lit 0)) =
          some (SourceSemantics.evalExpr fields runtime expr))
    (hsubset : ∀ name, name ∈ exprBoundNames arg → name ∈ exprBoundNames expr := by
      intro _ h; simp [exprBoundNames, h]) :
    CompileExprSound fields expr := by
  intro runtime state hexact hbounded hpresent hruntime
  obtain ⟨_, hcompile, hevalArg, hlt⟩ :=
    compileExprSound_subexpr hA ihA hexact hbounded hpresent hruntime hsubset
  exact heval hcompile hevalArg hlt hruntime

private theorem compileExprSound_binary
    {fields : List Field}
    {lhs rhs expr : Expr}
    (hL : ExprCompileCore lhs)
    (hR : ExprCompileCore rhs)
    (ihL : CompileExprSound fields lhs)
    (ihR : CompileExprSound fields rhs)
    (heval : ∀ {runtime : SourceSemantics.RuntimeState} {state : IRState} {lhsIR rhsIR : YulExpr},
      CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR →
      CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR →
      evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs) →
      evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs) →
      SourceSemantics.evalExpr fields runtime lhs < Compiler.Constants.evmModulus →
      SourceSemantics.evalExpr fields runtime rhs < Compiler.Constants.evmModulus →
      runtimeStateMatchesIR fields runtime state →
      evalIRExpr state
        (CompilationModel.compileExpr fields .calldata expr |>.toOption.getD (YulExpr.lit 0)) =
          some (SourceSemantics.evalExpr fields runtime expr))
    (hsubsetL : ∀ name, name ∈ exprBoundNames lhs → name ∈ exprBoundNames expr := by
      intro _ h; simp [exprBoundNames, exprListBoundNames, h])
    (hsubsetR : ∀ name, name ∈ exprBoundNames rhs → name ∈ exprBoundNames expr := by
      intro _ h; simp [exprBoundNames, exprListBoundNames, h]) :
    CompileExprSound fields expr := by
  intro runtime state hexact hbounded hpresent hruntime
  obtain ⟨_, hl, el, ll⟩ :=
    compileExprSound_subexpr hL ihL hexact hbounded hpresent hruntime hsubsetL
  obtain ⟨_, hr, er, lr⟩ :=
    compileExprSound_subexpr hR ihR hexact hbounded hpresent hruntime hsubsetR
  exact heval hl hr el er ll lr hruntime

private theorem compileExprSound_literal {fields : List Field} (value : Nat) :
    CompileExprSound fields (.literal value) := fun runtime state _ _ _ _ => by
  simpa [CompilationModel.compileExpr, CompilationModel.compileExprWithInternals,
    Except.toOption, Option.getD, Functor.map, Except.map, Bind.bind,
    Except.bind, Pure.pure, Except.pure] using
    eval_compileExpr_literal fields runtime state value

private theorem compileExprSound_param {fields : List Field} (name : String) :
    CompileExprSound fields (.param name) := fun _ _ hexact _ hpresent _ => by
  simpa [CompilationModel.compileExpr, CompilationModel.compileExprWithInternals,
    Except.toOption, Option.getD, Functor.map, Except.map, Bind.bind,
    Except.bind, Pure.pure, Except.pure] using
    eval_compileExpr_param_of_expr_bindings name hexact hpresent

private theorem compileExprSound_constructorArg {fields : List Field} (idx : Nat) :
    CompileExprSound fields (.constructorArg idx) := fun _ _ hexact _ hpresent _ => by
  simpa [CompilationModel.compileExpr, CompilationModel.compileExprWithInternals,
    Except.toOption, Option.getD, Functor.map, Except.map, Bind.bind,
    Except.bind, Pure.pure, Except.pure] using
    eval_compileExpr_constructorArg_of_expr_bindings idx hexact hpresent

private theorem compileExprSound_localVar {fields : List Field} (name : String) :
    CompileExprSound fields (.localVar name) := fun _ _ hexact _ hpresent _ => by
  simpa [CompilationModel.compileExpr, CompilationModel.compileExprWithInternals,
    Except.toOption, Option.getD, Functor.map, Except.map, Bind.bind,
    Except.bind, Pure.pure, Except.pure] using
    eval_compileExpr_localVar_of_expr_bindings name hexact hpresent

private theorem compileExprSound_caller {fields : List Field} :
    CompileExprSound fields .caller := fun _ _ _ _ _ hruntime =>
  eval_compileExpr_caller hruntime

private theorem compileExprSound_contractAddress {fields : List Field} :
    CompileExprSound fields .contractAddress := fun _ _ _ _ _ hruntime =>
  eval_compileExpr_contractAddress hruntime

private theorem compileExprSound_txOrigin {fields : List Field} :
    CompileExprSound fields .txOrigin := fun _ _ _ _ _ hruntime =>
  eval_compileExpr_txOrigin hruntime

private theorem compileExprSound_msgValue {fields : List Field} :
    CompileExprSound fields .msgValue := fun _ _ _ _ _ hruntime =>
  eval_compileExpr_msgValue hruntime

private theorem compileExprSound_blockTimestamp {fields : List Field} :
    CompileExprSound fields .blockTimestamp := fun _ _ _ _ _ hruntime =>
  eval_compileExpr_blockTimestamp hruntime

private theorem compileExprSound_blockNumber {fields : List Field} :
    CompileExprSound fields .blockNumber := fun _ _ _ _ _ hruntime =>
  eval_compileExpr_blockNumber hruntime

private theorem compileExprSound_chainid {fields : List Field} :
    CompileExprSound fields .chainid := fun _ _ _ _ _ hruntime =>
  eval_compileExpr_chainid hruntime

private theorem compileExprSound_blobbasefee {fields : List Field} :
    CompileExprSound fields .blobbasefee := fun _ _ _ _ _ hruntime =>
  eval_compileExpr_blobbasefee hruntime

private theorem compileExprSound_calldatasize {fields : List Field} :
    CompileExprSound fields .calldatasize := fun _ _ _ _ _ hruntime =>
  eval_compileExpr_calldatasize hruntime

private theorem compileExprSound_returndataSize {fields : List Field} :
    CompileExprSound fields .returndataSize := fun _ _ _ _ _ hruntime =>
  eval_compileExpr_returndataSize hruntime

private theorem compileExprSound_sub {fields : List Field} {lhs rhs : Expr}
    (hL : ExprCompileCore lhs) (hR : ExprCompileCore rhs)
    (ihL : CompileExprSound fields lhs) (ihR : CompileExprSound fields rhs) :
    CompileExprSound fields (.sub lhs rhs) :=
  compileExprSound_binary hL hR ihL ihR fun hl hr el er ll lr _ =>
    eval_compileExpr_sub_of_compiled hl hr el er ll lr

private theorem compileExprSound_div {fields : List Field} {lhs rhs : Expr}
    (hL : ExprCompileCore lhs) (hR : ExprCompileCore rhs)
    (ihL : CompileExprSound fields lhs) (ihR : CompileExprSound fields rhs) :
    CompileExprSound fields (.div lhs rhs) :=
  compileExprSound_binary hL hR ihL ihR fun hl hr el er ll lr _ =>
    eval_compileExpr_div_of_compiled hl hr el er ll lr

private theorem compileExprSound_mod {fields : List Field} {lhs rhs : Expr}
    (hL : ExprCompileCore lhs) (hR : ExprCompileCore rhs)
    (ihL : CompileExprSound fields lhs) (ihR : CompileExprSound fields rhs) :
    CompileExprSound fields (.mod lhs rhs) :=
  compileExprSound_binary hL hR ihL ihR fun hl hr el er ll lr _ =>
    eval_compileExpr_mod_of_compiled hl hr el er ll lr

private theorem compileExprSound_eq {fields : List Field} {lhs rhs : Expr}
    (hL : ExprCompileCore lhs) (hR : ExprCompileCore rhs)
    (ihL : CompileExprSound fields lhs) (ihR : CompileExprSound fields rhs) :
    CompileExprSound fields (.eq lhs rhs) :=
  compileExprSound_binary hL hR ihL ihR fun hl hr el er ll lr _ =>
    eval_compileExpr_eq_of_compiled hl hr el er ll lr

private theorem compileExprSound_lt {fields : List Field} {lhs rhs : Expr}
    (hL : ExprCompileCore lhs) (hR : ExprCompileCore rhs)
    (ihL : CompileExprSound fields lhs) (ihR : CompileExprSound fields rhs) :
    CompileExprSound fields (.lt lhs rhs) :=
  compileExprSound_binary hL hR ihL ihR fun hl hr el er ll lr _ =>
    eval_compileExpr_lt_of_compiled hl hr el er ll lr

private theorem compileExprSound_gt {fields : List Field} {lhs rhs : Expr}
    (hL : ExprCompileCore lhs) (hR : ExprCompileCore rhs)
    (ihL : CompileExprSound fields lhs) (ihR : CompileExprSound fields rhs) :
    CompileExprSound fields (.gt lhs rhs) :=
  compileExprSound_binary hL hR ihL ihR fun hl hr el er ll lr _ =>
    eval_compileExpr_gt_of_compiled hl hr el er ll lr

private theorem compileExprSound_ge {fields : List Field} {lhs rhs : Expr}
    (hL : ExprCompileCore lhs) (hR : ExprCompileCore rhs)
    (ihL : CompileExprSound fields lhs) (ihR : CompileExprSound fields rhs) :
    CompileExprSound fields (.ge lhs rhs) :=
  compileExprSound_binary hL hR ihL ihR fun hl hr el er ll lr _ =>
    eval_compileExpr_ge_of_compiled hl hr el er ll lr

private theorem compileExprSound_le {fields : List Field} {lhs rhs : Expr}
    (hL : ExprCompileCore lhs) (hR : ExprCompileCore rhs)
    (ihL : CompileExprSound fields lhs) (ihR : CompileExprSound fields rhs) :
    CompileExprSound fields (.le lhs rhs) :=
  compileExprSound_binary hL hR ihL ihR fun hl hr el er ll lr _ =>
    eval_compileExpr_le_of_compiled hl hr el er ll lr

private theorem compileExprSound_logicalAnd {fields : List Field} {lhs rhs : Expr}
    (hL : ExprCompileCore lhs) (hR : ExprCompileCore rhs)
    (ihL : CompileExprSound fields lhs) (ihR : CompileExprSound fields rhs) :
    CompileExprSound fields (.logicalAnd lhs rhs) :=
  compileExprSound_binary hL hR ihL ihR fun hl hr el er ll lr _ =>
    eval_compileExpr_logicalAnd_of_compiled hl hr el er ll lr

private theorem compileExprSound_logicalOr {fields : List Field} {lhs rhs : Expr}
    (hL : ExprCompileCore lhs) (hR : ExprCompileCore rhs)
    (ihL : CompileExprSound fields lhs) (ihR : CompileExprSound fields rhs) :
    CompileExprSound fields (.logicalOr lhs rhs) :=
  compileExprSound_binary hL hR ihL ihR fun hl hr el er ll lr _ =>
    eval_compileExpr_logicalOr_of_compiled hl hr el er ll lr

private theorem compileExprSound_bitAnd {fields : List Field} {lhs rhs : Expr}
    (hL : ExprCompileCore lhs) (hR : ExprCompileCore rhs)
    (ihL : CompileExprSound fields lhs) (ihR : CompileExprSound fields rhs) :
    CompileExprSound fields (.bitAnd lhs rhs) :=
  compileExprSound_binary hL hR ihL ihR fun hl hr el er ll lr _ =>
    eval_compileExpr_bitAnd_of_compiled hl hr el er ll lr

private theorem compileExprSound_bitOr {fields : List Field} {lhs rhs : Expr}
    (hL : ExprCompileCore lhs) (hR : ExprCompileCore rhs)
    (ihL : CompileExprSound fields lhs) (ihR : CompileExprSound fields rhs) :
    CompileExprSound fields (.bitOr lhs rhs) :=
  compileExprSound_binary hL hR ihL ihR fun hl hr el er ll lr _ =>
    eval_compileExpr_bitOr_of_compiled hl hr el er ll lr

private theorem compileExprSound_bitXor {fields : List Field} {lhs rhs : Expr}
    (hL : ExprCompileCore lhs) (hR : ExprCompileCore rhs)
    (ihL : CompileExprSound fields lhs) (ihR : CompileExprSound fields rhs) :
    CompileExprSound fields (.bitXor lhs rhs) :=
  compileExprSound_binary hL hR ihL ihR fun hl hr el er ll lr _ =>
    eval_compileExpr_bitXor_of_compiled hl hr el er ll lr

private theorem compileExprSound_shl {fields : List Field} {lhs rhs : Expr}
    (hL : ExprCompileCore lhs) (hR : ExprCompileCore rhs)
    (ihL : CompileExprSound fields lhs) (ihR : CompileExprSound fields rhs) :
    CompileExprSound fields (.shl lhs rhs) :=
  compileExprSound_binary hL hR ihL ihR fun hl hr el er ll lr _ =>
    eval_compileExpr_shl_of_compiled hl hr el er ll lr

private theorem compileExprSound_shr {fields : List Field} {lhs rhs : Expr}
    (hL : ExprCompileCore lhs) (hR : ExprCompileCore rhs)
    (ihL : CompileExprSound fields lhs) (ihR : CompileExprSound fields rhs) :
    CompileExprSound fields (.shr lhs rhs) :=
  compileExprSound_binary hL hR ihL ihR fun hl hr el er ll lr _ =>
    eval_compileExpr_shr_of_compiled hl hr el er ll lr

private theorem compileExprSound_min {fields : List Field} {lhs rhs : Expr}
    (hL : ExprCompileCore lhs) (hR : ExprCompileCore rhs)
    (ihL : CompileExprSound fields lhs) (ihR : CompileExprSound fields rhs) :
    CompileExprSound fields (.min lhs rhs) :=
  compileExprSound_binary hL hR ihL ihR fun hl hr el er ll lr _ =>
    eval_compileExpr_min_of_compiled hl hr el er ll lr

private theorem compileExprSound_max {fields : List Field} {lhs rhs : Expr}
    (hL : ExprCompileCore lhs) (hR : ExprCompileCore rhs)
    (ihL : CompileExprSound fields lhs) (ihR : CompileExprSound fields rhs) :
    CompileExprSound fields (.max lhs rhs) :=
  compileExprSound_binary hL hR ihL ihR fun hl hr el er ll lr _ =>
    eval_compileExpr_max_of_compiled hl hr el er ll lr

private theorem compileExprSound_ceilDiv {fields : List Field} {lhs rhs : Expr}
    (hL : ExprCompileCore lhs) (hR : ExprCompileCore rhs)
    (ihL : CompileExprSound fields lhs) (ihR : CompileExprSound fields rhs) :
    CompileExprSound fields (.ceilDiv lhs rhs) :=
  compileExprSound_binary hL hR ihL ihR fun hl hr el er ll lr _ =>
    eval_compileExpr_ceilDiv_of_compiled hl hr el er ll lr

private theorem compileExprSound_wMulDown {fields : List Field} {lhs rhs : Expr}
    (hL : ExprCompileCore lhs) (hR : ExprCompileCore rhs)
    (ihL : CompileExprSound fields lhs) (ihR : CompileExprSound fields rhs) :
    CompileExprSound fields (.wMulDown lhs rhs) :=
  compileExprSound_binary hL hR ihL ihR fun hl hr el er ll lr _ =>
    eval_compileExpr_wMulDown_of_compiled hl hr el er ll lr

private theorem compileExprSound_wDivUp {fields : List Field} {lhs rhs : Expr}
    (hL : ExprCompileCore lhs) (hR : ExprCompileCore rhs)
    (ihL : CompileExprSound fields lhs) (ihR : CompileExprSound fields rhs) :
    CompileExprSound fields (.wDivUp lhs rhs) :=
  compileExprSound_binary hL hR ihL ihR fun hl hr el er ll lr _ =>
    eval_compileExpr_wDivUp_of_compiled hl hr el er ll lr

private theorem compileExprSound_slt {fields : List Field} {lhs rhs : Expr}
    (hL : ExprCompileCore lhs) (hR : ExprCompileCore rhs)
    (ihL : CompileExprSound fields lhs) (ihR : CompileExprSound fields rhs) :
    CompileExprSound fields (.slt lhs rhs) :=
  compileExprSound_binary hL hR ihL ihR fun hl hr el er ll lr _ =>
    eval_compileExpr_slt_of_compiled hl hr el er ll lr

private theorem compileExprSound_sgt {fields : List Field} {lhs rhs : Expr}
    (hL : ExprCompileCore lhs) (hR : ExprCompileCore rhs)
    (ihL : CompileExprSound fields lhs) (ihR : CompileExprSound fields rhs) :
    CompileExprSound fields (.sgt lhs rhs) :=
  compileExprSound_binary hL hR ihL ihR fun hl hr el er ll lr _ =>
    eval_compileExpr_sgt_of_compiled hl hr el er ll lr

private theorem compileExprSound_sdiv {fields : List Field} {lhs rhs : Expr}
    (hL : ExprCompileCore lhs) (hR : ExprCompileCore rhs)
    (ihL : CompileExprSound fields lhs) (ihR : CompileExprSound fields rhs) :
    CompileExprSound fields (.sdiv lhs rhs) :=
  compileExprSound_binary hL hR ihL ihR fun hl hr el er ll lr _ =>
    eval_compileExpr_sdiv_of_compiled hl hr el er ll lr

private theorem compileExprSound_smod {fields : List Field} {lhs rhs : Expr}
    (hL : ExprCompileCore lhs) (hR : ExprCompileCore rhs)
    (ihL : CompileExprSound fields lhs) (ihR : CompileExprSound fields rhs) :
    CompileExprSound fields (.smod lhs rhs) :=
  compileExprSound_binary hL hR ihL ihR fun hl hr el er ll lr _ =>
    eval_compileExpr_smod_of_compiled hl hr el er ll lr

private theorem compileExprSound_sar {fields : List Field} {lhs rhs : Expr}
    (hL : ExprCompileCore lhs) (hR : ExprCompileCore rhs)
    (ihL : CompileExprSound fields lhs) (ihR : CompileExprSound fields rhs) :
    CompileExprSound fields (.sar lhs rhs) :=
  compileExprSound_binary hL hR ihL ihR fun hl hr el er ll lr _ =>
    eval_compileExpr_sar_of_compiled hl hr el er ll lr

private theorem compileExprSound_byte {fields : List Field} {lhs rhs : Expr}
    (hL : ExprCompileCore lhs) (hR : ExprCompileCore rhs)
    (ihL : CompileExprSound fields lhs) (ihR : CompileExprSound fields rhs) :
    CompileExprSound fields (.byte lhs rhs) :=
  compileExprSound_binary hL hR ihL ihR fun hl hr el er ll lr _ =>
    eval_compileExpr_byte_of_compiled hl hr el er ll lr

private theorem compileExprSound_signextend {fields : List Field} {lhs rhs : Expr}
    (hL : ExprCompileCore lhs) (hR : ExprCompileCore rhs)
    (ihL : CompileExprSound fields lhs) (ihR : CompileExprSound fields rhs) :
    CompileExprSound fields (.signextend lhs rhs) :=
  compileExprSound_binary hL hR ihL ihR fun hl hr el er ll lr _ =>
    eval_compileExpr_signextend_of_compiled hl hr el er ll lr

private theorem compileExprSound_add {fields : List Field} {lhs rhs : Expr}
    (hL : ExprCompileCore lhs) (hR : ExprCompileCore rhs)
    (ihL : CompileExprSound fields lhs) (ihR : CompileExprSound fields rhs) :
    CompileExprSound fields (.add lhs rhs) :=
  compileExprSound_binary hL hR ihL ihR fun hl hr el er _ _ _ =>
    eval_compileExpr_add_of_compiled hl hr el er

private theorem compileExprSound_mul {fields : List Field} {lhs rhs : Expr}
    (hL : ExprCompileCore lhs) (hR : ExprCompileCore rhs)
    (ihL : CompileExprSound fields lhs) (ihR : CompileExprSound fields rhs) :
    CompileExprSound fields (.mul lhs rhs) :=
  compileExprSound_binary hL hR ihL ihR fun hl hr el er _ _ _ =>
    eval_compileExpr_mul_of_compiled hl hr el er

private theorem compileExprSound_builtinExp {fields : List Field} {lhs rhs : Expr}
    (hL : ExprCompileCore lhs) (hR : ExprCompileCore rhs)
    (ihL : CompileExprSound fields lhs) (ihR : CompileExprSound fields rhs) :
    CompileExprSound fields (.externalCall builtinExpName [lhs, rhs]) :=
  compileExprSound_binary hL hR ihL ihR fun hl hr el er _ _ _ =>
    eval_compileExpr_builtinExp_of_compiled hl hr el er

private theorem compileExprSound_keccak256 {fields : List Field} {lhs rhs : Expr}
    (hL : ExprCompileCore lhs) (hR : ExprCompileCore rhs)
    (ihL : CompileExprSound fields lhs) (ihR : CompileExprSound fields rhs) :
    CompileExprSound fields (.keccak256 lhs rhs) :=
  compileExprSound_binary hL hR ihL ihR fun hl hr el er _ _ hruntime =>
    eval_compileExpr_keccak256_of_compiled hl hr el er hruntime

private theorem compileExprSound_logicalNot {fields : List Field} {arg : Expr}
    (hA : ExprCompileCore arg) (ihA : CompileExprSound fields arg) :
    CompileExprSound fields (.logicalNot arg) :=
  compileExprSound_unary hA ihA fun h e l _ => eval_compileExpr_logicalNot_of_compiled h e l

private theorem compileExprSound_bitNot {fields : List Field} {arg : Expr}
    (hA : ExprCompileCore arg) (ihA : CompileExprSound fields arg) :
    CompileExprSound fields (.bitNot arg) :=
  compileExprSound_unary hA ihA fun h e l _ => eval_compileExpr_bitNot_of_compiled h e l

private theorem compileExprSound_tload {fields : List Field} {arg : Expr}
    (hA : ExprCompileCore arg) (ihA : CompileExprSound fields arg) :
    CompileExprSound fields (.tload arg) :=
  compileExprSound_unary hA ihA fun h e l hruntime =>
    eval_compileExpr_tload_of_compiled h e hruntime l

private theorem compileExprSound_extcodesize {fields : List Field} {arg : Expr}
    (hA : ExprCompileCore arg) (ihA : CompileExprSound fields arg) :
    CompileExprSound fields (.extcodesize arg) :=
  compileExprSound_unary hA ihA fun h e l hruntime =>
    eval_compileExpr_extcodesize_of_compiled h e hruntime l

private theorem compileExprSound_calldataload {fields : List Field} {arg : Expr}
    (hA : ExprCompileCore arg) (ihA : CompileExprSound fields arg) :
    CompileExprSound fields (.calldataload arg) :=
  compileExprSound_unary hA ihA fun h e _ hruntime =>
    eval_compileExpr_calldataload_of_compiled h e hruntime

private theorem compileExprSound_mload {fields : List Field} {arg : Expr}
    (hA : ExprCompileCore arg) (ihA : CompileExprSound fields arg) :
    CompileExprSound fields (.mload arg) :=
  compileExprSound_unary hA ihA fun h e _ hruntime =>
    eval_compileExpr_mload_of_compiled h e hruntime

private theorem compileExprSound_returndataOptionalBoolAt {fields : List Field} {arg : Expr}
    (hA : ExprCompileCore arg) (ihA : CompileExprSound fields arg) :
    CompileExprSound fields (.returndataOptionalBoolAt arg) :=
  compileExprSound_unary hA ihA fun h e _ hruntime =>
    eval_compileExpr_returndataOptionalBoolAt_of_compiled h e hruntime

private theorem compileExprSound_ite {fields : List Field} {a b c : Expr}
    (hA : ExprCompileCore a) (hB : ExprCompileCore b) (hC : ExprCompileCore c)
    (ihA : CompileExprSound fields a) (ihB : CompileExprSound fields b)
    (ihC : CompileExprSound fields c) :
    CompileExprSound fields (.ite a b c) := by
  intro runtime state hexact hbounded hpresent hruntime
  obtain ⟨_, ha, ea, la⟩ := compileExprSound_subexpr hA ihA hexact hbounded hpresent hruntime
  obtain ⟨_, hb, eb, lb⟩ := compileExprSound_subexpr hB ihB hexact hbounded hpresent hruntime
  obtain ⟨_, hc, ec, lc⟩ := compileExprSound_subexpr hC ihC hexact hbounded hpresent hruntime
  exact eval_compileExpr_ite_of_compiled ha hb hc ea eb ec la lb lc

private theorem compileExprSound_mulDivDown {fields : List Field} {a b c : Expr}
    (hA : ExprCompileCore a) (hB : ExprCompileCore b) (hC : ExprCompileCore c)
    (ihA : CompileExprSound fields a) (ihB : CompileExprSound fields b)
    (ihC : CompileExprSound fields c) :
    CompileExprSound fields (.mulDivDown a b c) := by
  intro runtime state hexact hbounded hpresent hruntime
  obtain ⟨_, ha, ea, la⟩ := compileExprSound_subexpr hA ihA hexact hbounded hpresent hruntime
  obtain ⟨_, hb, eb, lb⟩ := compileExprSound_subexpr hB ihB hexact hbounded hpresent hruntime
  obtain ⟨_, hc, ec, lc⟩ := compileExprSound_subexpr hC ihC hexact hbounded hpresent hruntime
  exact eval_compileExpr_mulDivDown_of_compiled ha hb hc ea eb ec la lb lc

private theorem compileExprSound_mulDivUp {fields : List Field} {a b c : Expr}
    (hA : ExprCompileCore a) (hB : ExprCompileCore b) (hC : ExprCompileCore c)
    (ihA : CompileExprSound fields a) (ihB : CompileExprSound fields b)
    (ihC : CompileExprSound fields c) :
    CompileExprSound fields (.mulDivUp a b c) := by
  intro runtime state hexact hbounded hpresent hruntime
  obtain ⟨_, ha, ea, la⟩ := compileExprSound_subexpr hA ihA hexact hbounded hpresent hruntime
  obtain ⟨_, hb, eb, lb⟩ := compileExprSound_subexpr hB ihB hexact hbounded hpresent hruntime
  obtain ⟨_, hc, ec, lc⟩ := compileExprSound_subexpr hC ihC hexact hbounded hpresent hruntime
  exact eval_compileExpr_mulDivUp_of_compiled ha hb hc ea eb ec la lb lc

private theorem compileExprSound_of_core {fields : List Field} {expr : Expr}
    (hcore : ExprCompileCore expr) : CompileExprSound fields expr :=
  -- One induction step per `ExprCompileCore` constructor, in declaration order.
  ExprCompileCore.rec (motive := fun expr _ => CompileExprSound fields expr)
    compileExprSound_literal compileExprSound_param compileExprSound_constructorArg
    compileExprSound_localVar compileExprSound_caller compileExprSound_contractAddress
    compileExprSound_txOrigin compileExprSound_msgValue compileExprSound_blockTimestamp
    compileExprSound_blockNumber compileExprSound_chainid compileExprSound_blobbasefee
    compileExprSound_calldatasize compileExprSound_returndataSize compileExprSound_add
    compileExprSound_sub compileExprSound_mul compileExprSound_div compileExprSound_mod
    compileExprSound_eq compileExprSound_lt compileExprSound_gt compileExprSound_ge
    compileExprSound_le compileExprSound_logicalNot compileExprSound_logicalAnd
    compileExprSound_logicalOr compileExprSound_bitAnd compileExprSound_bitOr
    compileExprSound_bitXor compileExprSound_bitNot compileExprSound_shl compileExprSound_shr
    compileExprSound_min compileExprSound_max compileExprSound_ite compileExprSound_ceilDiv
    compileExprSound_wMulDown compileExprSound_wDivUp compileExprSound_mulDivDown
    compileExprSound_mulDivUp compileExprSound_slt compileExprSound_sgt compileExprSound_sdiv
    compileExprSound_smod compileExprSound_sar compileExprSound_byte compileExprSound_signextend
    compileExprSound_tload compileExprSound_calldataload compileExprSound_mload
    compileExprSound_extcodesize compileExprSound_returndataOptionalBoolAt
    compileExprSound_keccak256 compileExprSound_builtinExp
    hcore

theorem eval_compileExpr_core_onExpr
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {expr : Expr}
    (hcore : ExprCompileCore expr)
    (hexact : bindingsExactlyMatchIRVarsOnExpr expr runtime.bindings state)
    (hbounded : bindingsBounded runtime.bindings)
    (hpresent : exprBoundNamesPresent expr runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata expr |>.toOption.getD (YulExpr.lit 0)) =
        some (SourceSemantics.evalExpr fields runtime expr) :=
  compileExprSound_of_core hcore runtime state hexact hbounded hpresent hruntime

theorem eval_compileExpr_core
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {expr : Expr}
    (hcore : ExprCompileCore expr)
    (hexact : bindingsExactlyMatchIRVars runtime.bindings state)
    (hbounded : bindingsBounded runtime.bindings)
    (hpresent : exprBoundNamesPresent expr runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state) :
    evalIRExpr state
      (CompilationModel.compileExpr fields .calldata expr |>.toOption.getD (YulExpr.lit 0)) =
        some (SourceSemantics.evalExpr fields runtime expr) :=
  eval_compileExpr_core_onExpr hcore
    (bindingsExactlyMatchIRVars_implies_onExpr hexact) hbounded hpresent hruntime

theorem evalExpr_lt_evmModulus_core
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {expr : Expr}
    (hcore : ExprCompileCore expr)
    (hexact : bindingsExactlyMatchIRVars runtime.bindings state)
    (hbounded : bindingsBounded runtime.bindings)
    (hpresent : exprBoundNamesPresent expr runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state) :
    SourceSemantics.evalExpr fields runtime expr < Compiler.Constants.evmModulus :=
  evalExpr_lt_evmModulus_core_onExpr hcore
    (bindingsExactlyMatchIRVars_implies_onExpr hexact) hbounded hpresent hruntime


/-- Every condition other than `ge`/`le` fails exactly when its compiled value is zero. -/
private theorem compileRequireFailCond_eq_iszero_of_compileExpr
    {fields : List Field}
    {cond : Expr}
    {condIR : YulExpr}
    (hge : ∀ lhs rhs, cond ≠ .ge lhs rhs)
    (hle : ∀ lhs rhs, cond ≠ .le lhs rhs)
    (hcompile : CompilationModel.compileExpr fields .calldata cond = Except.ok condIR) :
    CompilationModel.compileRequireFailCond fields .calldata cond =
      Except.ok (YulExpr.call "iszero" [condIR]) := by
  unfold CompilationModel.compileRequireFailCond
    CompilationModel.compileRequireFailCondWithInternals
  split
  · exact absurd rfl (hge _ _)
  · exact absurd rfl (hle _ _)
  · rw [CompilationModel.compileExprWithInternals_nil_eq, hcompile]
    rfl

private theorem compileRequireFailCond_ge_eq
    {fields : List Field}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhs : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhs : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR) :
    CompilationModel.compileRequireFailCond fields .calldata (.ge lhs rhs) =
      Except.ok (YulExpr.call "lt" [lhsIR, rhsIR]) := by
  rw [CompilationModel.compileRequireFailCond]
  rw [← CompilationModel.compileExprWithInternals_nil_eq] at hlhs hrhs
  simp [CompilationModel.compileRequireFailCondWithInternals, CompilationModel.yulBinOp, hlhs,
    hrhs]
  rfl

private theorem compileRequireFailCond_le_eq
    {fields : List Field}
    {lhs rhs : Expr}
    {lhsIR rhsIR : YulExpr}
    (hlhs : CompilationModel.compileExpr fields .calldata lhs = Except.ok lhsIR)
    (hrhs : CompilationModel.compileExpr fields .calldata rhs = Except.ok rhsIR) :
    CompilationModel.compileRequireFailCond fields .calldata (.le lhs rhs) =
      Except.ok (YulExpr.call "gt" [lhsIR, rhsIR]) := by
  rw [CompilationModel.compileRequireFailCond]
  rw [← CompilationModel.compileExprWithInternals_nil_eq] at hlhs hrhs
  simp [CompilationModel.compileRequireFailCondWithInternals, CompilationModel.yulBinOp, hlhs,
    hrhs]
  rfl

theorem compileRequireFailCond_core_ok
    {fields : List Field}
    {cond : Expr}
    (hcore : ExprCompileCore cond) :
    ∃ failCond,
      CompilationModel.compileRequireFailCond fields .calldata cond = Except.ok failCond := by
  obtain ⟨_, hcond⟩ := compileExpr_core_ok (fields := fields) hcore
  cases hcore with
  | ge hL hR =>
      obtain ⟨_, hlhs⟩ := compileExpr_core_ok (fields := fields) hL
      obtain ⟨_, hrhs⟩ := compileExpr_core_ok (fields := fields) hR
      exact ⟨_, compileRequireFailCond_ge_eq hlhs hrhs⟩
  | le hL hR =>
      obtain ⟨_, hlhs⟩ := compileExpr_core_ok (fields := fields) hL
      obtain ⟨_, hrhs⟩ := compileExpr_core_ok (fields := fields) hR
      exact ⟨_, compileRequireFailCond_le_eq hlhs hrhs⟩
  | _ =>
      exact ⟨_, compileRequireFailCond_eq_iszero_of_compileExpr
        (fun _ _ h => by cases h) (fun _ _ h => by cases h) hcond⟩

/-- `iszero` of a compiled core expression evaluates the source "is zero" test. -/
private theorem evalIRExpr_iszero_of_compileExpr_core_onExpr
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {expr : Expr}
    {exprIR : YulExpr}
    (hcore : ExprCompileCore expr)
    (hexact : bindingsExactlyMatchIRVarsOnExpr expr runtime.bindings state)
    (hbounded : bindingsBounded runtime.bindings)
    (hpresent : exprBoundNamesPresent expr runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state)
    (hcompile : CompilationModel.compileExpr fields .calldata expr = Except.ok exprIR) :
    evalIRExpr state (YulExpr.call "iszero" [exprIR]) =
      some (SourceSemantics.boolWord (SourceSemantics.evalExpr fields runtime expr = some 0)) := by
  obtain ⟨value, hsrc, hIR, hlt⟩ := exists_source_value_of_evalIRExpr
    (evalIRExpr_of_compileExpr_eq_ok hcompile
      (eval_compileExpr_core_onExpr hcore hexact hbounded hpresent hruntime))
    (evalExpr_lt_evmModulus_core_onExpr hcore hexact hbounded hpresent hruntime)
  have hiszero := evalIRExpr_iszero_of_lt hIR hlt
  simp only [hsrc, Option.some.injEq] at hiszero ⊢
  exact hiszero

/-- Compile a core subexpression of `expr` and evaluate it to a bounded value. -/
private theorem exists_compiled_value_of_subexpr
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {expr subexpr : Expr}
    (hcore : ExprCompileCore subexpr)
    (hexact : bindingsExactlyMatchIRVarsOnExpr expr runtime.bindings state)
    (hbounded : bindingsBounded runtime.bindings)
    (hpresent : exprBoundNamesPresent expr runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state)
    (hsubset : ∀ name, name ∈ exprBoundNames subexpr → name ∈ exprBoundNames expr := by
      intro _ h; simp [exprBoundNames, h]) :
    ∃ subexprIR value,
      CompilationModel.compileExpr fields .calldata subexpr = Except.ok subexprIR ∧
      evalIRExpr state subexprIR = some value ∧
      SourceSemantics.evalExpr fields runtime subexpr = some value ∧
      value < Compiler.Constants.evmModulus := by
  obtain ⟨subexprIR, hcompile, heval, hlt⟩ := compileExprSound_subexpr hcore
    (compileExprSound_of_core hcore) hexact hbounded hpresent hruntime hsubset
  obtain ⟨value, hsrc, hIR, hlt'⟩ := exists_source_value_of_evalIRExpr heval hlt
  exact ⟨subexprIR, value, hcompile, hIR, hsrc, hlt'⟩

private theorem evalExpr_ge_of_values
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {lhs rhs : Expr}
    {lhsVal rhsVal : Nat}
    (hlhs : SourceSemantics.evalExpr fields runtime lhs = some lhsVal)
    (hrhs : SourceSemantics.evalExpr fields runtime rhs = some rhsVal) :
    SourceSemantics.evalExpr fields runtime (.ge lhs rhs) =
      some (SourceSemantics.boolWord (decide (rhsVal ≤ lhsVal))) := by
  change (do let l ← SourceSemantics.evalExpr fields runtime lhs
             let r ← SourceSemantics.evalExpr fields runtime rhs
             pure (SourceSemantics.boolWord (decide (r ≤ l)))) = _
  rw [hlhs, hrhs]
  rfl

private theorem evalExpr_le_of_values
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {lhs rhs : Expr}
    {lhsVal rhsVal : Nat}
    (hlhs : SourceSemantics.evalExpr fields runtime lhs = some lhsVal)
    (hrhs : SourceSemantics.evalExpr fields runtime rhs = some rhsVal) :
    SourceSemantics.evalExpr fields runtime (.le lhs rhs) =
      some (SourceSemantics.boolWord (decide (lhsVal ≤ rhsVal))) := by
  change (do let l ← SourceSemantics.evalExpr fields runtime lhs
             let r ← SourceSemantics.evalExpr fields runtime rhs
             pure (SourceSemantics.boolWord (decide (l ≤ r)))) = _
  rw [hlhs, hrhs]
  rfl

private theorem eval_compileRequireFailCond_ge
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {lhs rhs : Expr}
    (hL : ExprCompileCore lhs)
    (hR : ExprCompileCore rhs)
    (hexact : bindingsExactlyMatchIRVarsOnExpr (.ge lhs rhs) runtime.bindings state)
    (hbounded : bindingsBounded runtime.bindings)
    (hpresent : exprBoundNamesPresent (.ge lhs rhs) runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state) :
    ∃ failCond,
      CompilationModel.compileRequireFailCond fields .calldata (.ge lhs rhs) =
        Except.ok failCond ∧
      evalIRExpr state failCond = some (SourceSemantics.boolWord
        (SourceSemantics.evalExpr fields runtime (.ge lhs rhs) = some 0)) := by
  obtain ⟨_, lhsVal, hlhs, hlhsIR, hlhsSrc, hlhsLt⟩ :=
    exists_compiled_value_of_subexpr hL hexact hbounded hpresent hruntime
  obtain ⟨_, rhsVal, hrhs, hrhsIR, hrhsSrc, hrhsLt⟩ :=
    exists_compiled_value_of_subexpr hR hexact hbounded hpresent hruntime
  refine ⟨_, compileRequireFailCond_ge_eq hlhs hrhs, ?_⟩
  rw [evalIRExpr_lt_of_eval hlhsIR hrhsIR]
  simp only [Nat.mod_eq_of_lt hlhsLt, Nat.mod_eq_of_lt hrhsLt,
    evalExpr_ge_of_values hlhsSrc hrhsSrc, Option.some.injEq, boolWord_eq_if]
  by_cases hle : rhsVal ≤ lhsVal
  · simp [hle, Nat.not_lt_of_le hle]
  · simp [hle, Nat.lt_of_not_le hle]

private theorem eval_compileRequireFailCond_le
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {lhs rhs : Expr}
    (hL : ExprCompileCore lhs)
    (hR : ExprCompileCore rhs)
    (hexact : bindingsExactlyMatchIRVarsOnExpr (.le lhs rhs) runtime.bindings state)
    (hbounded : bindingsBounded runtime.bindings)
    (hpresent : exprBoundNamesPresent (.le lhs rhs) runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state) :
    ∃ failCond,
      CompilationModel.compileRequireFailCond fields .calldata (.le lhs rhs) =
        Except.ok failCond ∧
      evalIRExpr state failCond = some (SourceSemantics.boolWord
        (SourceSemantics.evalExpr fields runtime (.le lhs rhs) = some 0)) := by
  obtain ⟨_, lhsVal, hlhs, hlhsIR, hlhsSrc, hlhsLt⟩ :=
    exists_compiled_value_of_subexpr hL hexact hbounded hpresent hruntime
  obtain ⟨_, rhsVal, hrhs, hrhsIR, hrhsSrc, hrhsLt⟩ :=
    exists_compiled_value_of_subexpr hR hexact hbounded hpresent hruntime
  refine ⟨_, compileRequireFailCond_le_eq hlhs hrhs, ?_⟩
  rw [evalIRExpr_gt_of_eval hlhsIR hrhsIR]
  simp only [Nat.mod_eq_of_lt hlhsLt, Nat.mod_eq_of_lt hrhsLt,
    evalExpr_le_of_values hlhsSrc hrhsSrc, Option.some.injEq, boolWord_eq_if]
  by_cases hle : lhsVal ≤ rhsVal
  · simp [hle, Nat.not_lt_of_le hle]
  · simp [hle, Nat.lt_of_not_le hle]

theorem eval_compileRequireFailCond_core_onExpr
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {cond : Expr}
    (hcore : ExprCompileCore cond)
    (hexact : bindingsExactlyMatchIRVarsOnExpr cond runtime.bindings state)
    (hbounded : bindingsBounded runtime.bindings)
    (hpresent : exprBoundNamesPresent cond runtime.bindings)
    (hruntime : runtimeStateMatchesIR fields runtime state) :
    ∃ failCond,
      CompilationModel.compileRequireFailCond fields .calldata cond = Except.ok failCond ∧
      evalIRExpr state failCond =
        some (SourceSemantics.boolWord (SourceSemantics.evalExpr fields runtime cond = some 0)) := by
  have hcond := hcore
  cases hcore with
  | ge hL hR => exact eval_compileRequireFailCond_ge hL hR hexact hbounded hpresent hruntime
  | le hL hR => exact eval_compileRequireFailCond_le hL hR hexact hbounded hpresent hruntime
  | _ =>
      -- Every other condition compiles via `iszero` of its compiled expression.
      obtain ⟨_, hcompile⟩ := compileExpr_core_ok (fields := fields) hcond
      exact ⟨_, compileRequireFailCond_eq_iszero_of_compileExpr
          (fun _ _ h => by cases h) (fun _ _ h => by cases h) hcompile,
        evalIRExpr_iszero_of_compileExpr_core_onExpr hcond hexact hbounded hpresent hruntime
          hcompile⟩

end FunctionBody

end Compiler.Proofs.IRGeneration

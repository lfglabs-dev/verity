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
  state.codeSize = (fun addr => (runtime.world.codeSize addr).val)

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
  state.codeSize = (fun addr => (runtime.world.codeSize addr).val)

def initialIRStateForTx
    (spec : CompilationModel)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState) : IRState :=
  { vars := []
    storage := fun s => Compiler.Proofs.IRGeneration.IRStorageWord.ofNat
      (SourceSemantics.encodeStorage spec initialWorld s.toNat)
    transientStorage := fun slot => (initialWorld.transientStorage slot).val
    memory := fun o => (initialWorld.memory o).val
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
    codeSize := fun addr => (initialWorld.codeSize addr).val }

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
    (_hmatch : runtimeStateMatchesIR fields runtime state) :
    evalIRExpr state (YulExpr.call "returndatasize" []) =
      some (SourceSemantics.evalExpr fields runtime (.returndataSize)) := by
  have heval : SourceSemantics.evalExpr fields runtime (.returndataSize) = some 0 := rfl
  rw [heval]
  simp [evalIRExpr, evalIRCall, evalIRExprs,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean]

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
          have hrestNodup : (rest.map Param.name).Nodup := by
            exact (List.nodup_cons.mp hparamsNodup).2
          cases hdecode : SourceSemantics.decodeSupportedParamWord param.ty arg <;>
              simp [SourceSemantics.bindSupportedParams, hdecode] at hbind
          case some value =>
            cases hrest : SourceSemantics.bindSupportedParams rest restArgs <;>
                simp [hrest] at hbind
            case some restBindings =>
              cases hbind
              simp only [List.map, List.mem_cons] at hmem
              rcases hmem with rfl | hmemRest
              · exact ⟨value, by simp [lookupBinding?]⟩
              · have hqueryNe : queryName ≠ param.name := by
                  intro hEq
                  apply (List.nodup_cons.mp hparamsNodup).1
                  simpa [hEq] using hmemRest
                have hqueryNe' : ¬ param.name = queryName := by
                  intro hEq
                  apply hqueryNe
                  exact hEq.symm
                rcases ih hrestNodup hrest hmemRest with ⟨found, hfound⟩
                have hfindSome : ∃ entryName,
                    List.find? (fun entry => entry.1 == queryName) restBindings =
                      some (entryName, found) := by
                  unfold lookupBinding? at hfound
                  cases hfind : List.find? (fun entry => entry.1 == queryName) restBindings with
                  | none =>
                      simp [hfind] at hfound
                  | some entry =>
                      cases entry with
                      | mk entryName entryValue =>
                          simp [hfind] at hfound
                          cases hfound
                          exact ⟨entryName, rfl⟩
                rcases hfindSome with ⟨entryName, hfindSome⟩
                exact ⟨found, by
                  unfold lookupBinding?
                  simp [hqueryNe', hfindSome]⟩

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
  rcases hIR : evalIRExpr state offsetIR with _ | irVal
  · simp [hIR] at hEvalOffset
  · simp only [hIR] at hEvalOffset
    simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some] at hEvalOffset
    have hsrc : SourceSemantics.evalExpr fields runtime offset = some irVal := by
      simpa using hEvalOffset.symm
    rw [show SourceSemantics.evalExpr fields runtime (.returndataOptionalBoolAt offset) =
        (SourceSemantics.evalExpr fields runtime offset).bind (fun _ => some 1) from rfl, hsrc]
    simp only [Option.bind_some]
    have hRDS : evalIRExpr state (YulExpr.call "returndatasize" []) = some 0 := by
      simp [evalIRExpr, evalIRCall, evalIRExprs,
        Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
        Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean]
    have hMload : evalIRExpr state (YulExpr.call "mload" [offsetIR]) =
        some (state.memory irVal) := by
      simp [evalIRExpr, evalIRCall, evalIRExprs, hIR]
    have hEq0 := evalIRExpr_eq_of_eval hRDS
      (show evalIRExpr state (YulExpr.lit 0) = some 0 from by simp [evalIRExpr])
    have hEq32 := evalIRExpr_eq_of_eval hRDS
      (show evalIRExpr state (YulExpr.lit 32) = some 32 from by simp [evalIRExpr])
    have hEqM := evalIRExpr_eq_of_eval hMload
      (show evalIRExpr state (YulExpr.lit 1) = some 1 from by simp [evalIRExpr])
    rw [evalIRExpr_or_of_eval hEq0 (evalIRExpr_and_of_eval hEq32 hEqM)]
    simp only [boolWord_eq_if, Nat.zero_mod]
    norm_num [Compiler.Constants.evmModulus]

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
      (CompilationModel.compileExpr fields .calldata (.logicalAnd lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
        some (SourceSemantics.evalExpr fields runtime (.logicalAnd lhs rhs)) := by
  have hcompile := compileExpr_logicalAnd_ok hlhsCompile hrhsCompile
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
      have hlhsBool :
          evalIRExpr state (CompilationModel.yulToBool lhsIR) =
            some (SourceSemantics.boolWord (lhsVal ≠ 0)) := by
        simpa using evalIRExpr_yulToBool_of_lt hlhsEval' hlhsLt'
      have hrhsBool :
          evalIRExpr state (CompilationModel.yulToBool rhsIR) =
            some (SourceSemantics.boolWord (rhsVal ≠ 0)) := by
        simpa using evalIRExpr_yulToBool_of_lt hrhsEval' hrhsLt'
      have hcall :
          evalIRExpr state
            (YulExpr.call "and" [CompilationModel.yulToBool lhsIR, CompilationModel.yulToBool rhsIR]) =
              some ((SourceSemantics.boolWord (lhsVal ≠ 0)) &&&
                (SourceSemantics.boolWord (rhsVal ≠ 0))) := by
        simpa only
          [Nat.mod_eq_of_lt (boolWord_lt_evmModulus (decide (lhsVal ≠ 0))),
          Nat.mod_eq_of_lt (boolWord_lt_evmModulus (decide (rhsVal ≠ 0)))] using
          evalIRExpr_and_of_eval hlhsBool hrhsBool
      have heval :
          evalIRExpr state
            (CompilationModel.compileExpr fields .calldata (.logicalAnd lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
              some ((SourceSemantics.boolWord (lhsVal ≠ 0)) &&&
                (SourceSemantics.boolWord (rhsVal ≠ 0))) := by
        simpa [hcompile, Except.toOption, Option.getD] using hcall
      have hsrc :
          SourceSemantics.evalExpr fields runtime (.logicalAnd lhs rhs) =
            some (SourceSemantics.boolWord
              (decide (lhsVal != 0) && decide (rhsVal != 0))) := by
        calc
          SourceSemantics.evalExpr fields runtime (.logicalAnd lhs rhs)
              = (do
                  let lhs ← SourceSemantics.evalExpr fields runtime lhs
                  let rhs ← SourceSemantics.evalExpr fields runtime rhs
                  pure (SourceSemantics.boolWord
                    (decide (lhs != 0) && decide (rhs != 0)))) := by
                      rfl
          _ = some (SourceSemantics.boolWord
                (decide (lhsVal != 0) && decide (rhsVal != 0))) := by
                simp [hlhsSrc, hrhsSrc]
      rw [heval, hsrc]
      simp [boolWord_and]

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
      (CompilationModel.compileExpr fields .calldata (.logicalOr lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
        some (SourceSemantics.evalExpr fields runtime (.logicalOr lhs rhs)) := by
  have hcompile := compileExpr_logicalOr_ok hlhsCompile hrhsCompile
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
      have hlhsBool :
          evalIRExpr state (CompilationModel.yulToBool lhsIR) =
            some (SourceSemantics.boolWord (lhsVal ≠ 0)) := by
        simpa using evalIRExpr_yulToBool_of_lt hlhsEval' hlhsLt'
      have hrhsBool :
          evalIRExpr state (CompilationModel.yulToBool rhsIR) =
            some (SourceSemantics.boolWord (rhsVal ≠ 0)) := by
        simpa using evalIRExpr_yulToBool_of_lt hrhsEval' hrhsLt'
      have hcall :
          evalIRExpr state
            (YulExpr.call "or" [CompilationModel.yulToBool lhsIR, CompilationModel.yulToBool rhsIR]) =
              some ((SourceSemantics.boolWord (lhsVal ≠ 0)) |||
                (SourceSemantics.boolWord (rhsVal ≠ 0))) := by
        simpa only
          [Nat.mod_eq_of_lt (boolWord_lt_evmModulus (decide (lhsVal ≠ 0))),
          Nat.mod_eq_of_lt (boolWord_lt_evmModulus (decide (rhsVal ≠ 0)))] using
          evalIRExpr_or_of_eval hlhsBool hrhsBool
      have heval :
          evalIRExpr state
            (CompilationModel.compileExpr fields .calldata (.logicalOr lhs rhs) |>.toOption.getD (YulExpr.lit 0)) =
              some ((SourceSemantics.boolWord (lhsVal ≠ 0)) |||
                (SourceSemantics.boolWord (rhsVal ≠ 0))) := by
        simpa [hcompile, Except.toOption, Option.getD] using hcall
      have hsrc :
          SourceSemantics.evalExpr fields runtime (.logicalOr lhs rhs) =
            some (SourceSemantics.boolWord
              (decide (lhsVal != 0) || decide (rhsVal != 0))) := by
        calc
          SourceSemantics.evalExpr fields runtime (.logicalOr lhs rhs)
            = (do
                let lhsVal ← SourceSemantics.evalExpr fields runtime lhs
                let rhsVal ← SourceSemantics.evalExpr fields runtime rhs
                pure (SourceSemantics.boolWord
                  (decide (lhsVal != 0) || decide (rhsVal != 0)))) := by
                  rfl
          _ = some (SourceSemantics.boolWord
                (decide (lhsVal != 0) || decide (rhsVal != 0))) := by
                simp [hlhsSrc, hrhsSrc]
      rw [heval, hsrc]
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
  have hcompile := compileExpr_wDivUp_ok hlhsCompile hrhsCompile
  rcases hlhsSrc : SourceSemantics.evalExpr fields runtime lhs with _ | lhsVal
  · cases hEval : evalIRExpr state lhsIR <;> simp [hEval, hlhsSrc] at hlhsEval
  · rcases hrhsSrc : SourceSemantics.evalExpr fields runtime rhs with _ | rhsVal
    · cases hEval : evalIRExpr state rhsIR <;> simp [hEval, hrhsSrc] at hrhsEval
    · have hlhsEval' := evalIRExpr_of_sourceEval_some hlhsEval hlhsSrc
      have hrhsEval' := evalIRExpr_of_sourceEval_some hrhsEval hrhsSrc
      have hlhsLt' : lhsVal < Compiler.Constants.evmModulus := by simpa [hlhsSrc] using hlhsLt
      have hrhsLt' : rhsVal < Compiler.Constants.evmModulus := by simpa [hrhsSrc] using hrhsLt
      have hWadLt : (1000000000000000000 : Nat) < Compiler.Constants.evmModulus := by decide
      have h1Lt : (1 : Nat) < Compiler.Constants.evmModulus := by decide
      have hevmPos : 0 < Compiler.Constants.evmModulus := by decide
      have hLitWad : evalIRExpr state (YulExpr.lit 1000000000000000000) = some 1000000000000000000 := by
        simp [evalIRExpr]
      have hLit1 : evalIRExpr state (YulExpr.lit 1) = some 1 := by simp [evalIRExpr]
      have hMul := evalIRExpr_mul_of_eval hlhsEval' hLitWad
      have hSub := evalIRExpr_sub_of_eval hrhsEval' hLit1
      have hAdd := evalIRExpr_add_of_eval hMul hSub
      have hDiv := evalIRExpr_div_of_eval hAdd hrhsEval'
      have hsrc := evalExpr_wDivUp_of_values hlhsSrc hrhsSrc
      -- Simplify hDiv: remove nested mods
      simp only [Nat.mod_eq_of_lt hrhsLt', Nat.mod_eq_of_lt h1Lt, Nat.mod_mod] at hDiv
      simp only [hcompile, Except.toOption, Option.getD] at hDiv ⊢
      rw [hsrc]
      by_cases hzero : rhsVal = 0
      · -- Zero divisor: both sides return 0
        subst hzero
        simp only [show (0 : Nat) = 0 from rfl, ↓reduceIte] at hDiv
        simp [HDiv.hDiv, Verity.Core.Uint256.div, Verity.Core.Uint256.ofNat,
          hDiv, Bind.bind, Option.bind, Pure.pure]
      · -- Non-zero divisor
        have h1le : 1 ≤ rhsVal := Nat.one_le_iff_ne_zero.mpr hzero
        have hSubM1Lt : rhsVal - 1 < Compiler.Constants.evmModulus :=
          Nat.lt_of_le_of_lt (Nat.sub_le _ _) hrhsLt'
        have hSubSimp : (Compiler.Constants.evmModulus + rhsVal - 1) %
            Compiler.Constants.evmModulus = rhsVal - 1 := by
          have : Compiler.Constants.evmModulus + rhsVal - 1 =
              Compiler.Constants.evmModulus + (rhsVal - 1) := by omega
          rw [this, Nat.add_mod_left]
          exact Nat.mod_eq_of_lt hSubM1Lt
        simp only [hSubSimp, hzero, ↓reduceIte] at hDiv
        have hrhsNe : (Verity.Core.Uint256.ofNat rhsVal).val ≠ 0 := by
          simp [Verity.Core.Uint256.ofNat, Nat.mod_eq_of_lt hrhsLt']; exact hzero
        have hrhsLtM : rhsVal < Verity.Core.Uint256.modulus := hrhsLt'
        -- Unfold source Uint256 expression to Nat
        set_option maxRecDepth 1024 in
        have hResultVal : (((Verity.Core.Uint256.ofNat lhsVal *
              (1000000000000000000 : Verity.Core.Uint256)) +
              (Verity.Core.Uint256.ofNat rhsVal - 1)) /
            Verity.Core.Uint256.ofNat rhsVal).val =
            (lhsVal * 1000000000000000000 % Compiler.Constants.evmModulus +
              (rhsVal - 1)) % Compiler.Constants.evmModulus / rhsVal := by
          show (Verity.Core.Uint256.div _ _).val = _
          simp only [HDiv.hDiv, Verity.Core.Uint256.div, hrhsNe, ↓reduceIte]
          simp only [HAdd.hAdd, Verity.Core.Uint256.add, Verity.Core.Uint256.ofNat]
          simp only [HMul.hMul, Verity.Core.Uint256.mul, Verity.Core.Uint256.ofNat]
          simp only [HSub.hSub, Verity.Core.Uint256.sub, Verity.Core.Uint256.ofNat,
            Nat.mod_eq_of_lt hrhsLtM, h1le, ↓reduceIte, Verity.Core.Uint256.val_one]
          -- Unfold OfNat and val_ofNat to get % modulus terms
          simp only [OfNat.ofNat, Verity.Core.Uint256.val_ofNat]
          -- Unfold modulus to 2^256 (which equals evmModulus definitionally)
          simp only [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS]
          -- Reduce remaining % 2^256 terms
          simp only [Nat.mod_eq_of_lt hlhsLt', Nat.mod_eq_of_lt hWadLt]
          -- Reduce the (rhsVal - 1) % 2^256 term (simp can't match Sub.sub)
          conv_lhs => rw [show Sub.sub rhsVal 1 % (2 : Nat) ^ 256 = Sub.sub rhsVal 1
            from Nat.mod_eq_of_lt hSubM1Lt]
          -- Close: LHS has outermost % 2^256, RHS doesn't; both sides eq definitionally after
          exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _)
            (Nat.mod_lt _ hevmPos))
        simp only [hResultVal, hDiv, Bind.bind, Option.bind, Pure.pure]

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
  have hcompile := compileExpr_mulDivDown_ok haCompile hbCompile hcCompile
  rcases haSrc : SourceSemantics.evalExpr fields runtime a with _ | aVal
  · cases hEval : evalIRExpr state aIR <;> simp [hEval, haSrc] at haEval
  · rcases hbSrc : SourceSemantics.evalExpr fields runtime b with _ | bVal
    · cases hEval : evalIRExpr state bIR <;> simp [hEval, hbSrc] at hbEval
    · rcases hcSrc : SourceSemantics.evalExpr fields runtime c with _ | cVal
      · cases hEval : evalIRExpr state cIR <;> simp [hEval, hcSrc] at hcEval
      · have haEval' := evalIRExpr_of_sourceEval_some haEval haSrc
        have hbEval' := evalIRExpr_of_sourceEval_some hbEval hbSrc
        have hcEval' := evalIRExpr_of_sourceEval_some hcEval hcSrc
        have haLt' : aVal < Compiler.Constants.evmModulus := by simpa [haSrc] using haLt
        have hbLt' : bVal < Compiler.Constants.evmModulus := by simpa [hbSrc] using hbLt
        have hcLt' : cVal < Compiler.Constants.evmModulus := by simpa [hcSrc] using hcLt
        have hMul := evalIRExpr_mul_of_eval haEval' hbEval'
        have hDiv := evalIRExpr_div_of_eval hMul hcEval'
        have hsrc := evalExpr_mulDivDown_of_values haSrc hbSrc hcSrc
        -- Simplify hDiv: remove nested mods
        simp only [Nat.mod_eq_of_lt hcLt', Nat.mod_mod] at hDiv
        -- Compute source result val by unfolding Uint256 operations
        have hResultVal : ((Verity.Core.Uint256.ofNat aVal * Verity.Core.Uint256.ofNat bVal) /
            Verity.Core.Uint256.ofNat cVal).val =
            (if cVal = 0 then 0 else aVal * bVal % Compiler.Constants.evmModulus / cVal) := by
          show (Verity.Core.Uint256.div (Verity.Core.Uint256.mul _ _) _).val = _
          by_cases hzero : cVal = 0
          · subst hzero
            simp [Verity.Core.Uint256.div, Verity.Core.Uint256.mul, Verity.Core.Uint256.ofNat]
          · have haLtM : aVal < Verity.Core.Uint256.modulus := haLt'
            have hbLtM : bVal < Verity.Core.Uint256.modulus := hbLt'
            have hcLtM : cVal < Verity.Core.Uint256.modulus := hcLt'
            simp only [Verity.Core.Uint256.div, Verity.Core.Uint256.mul,
              Verity.Core.Uint256.ofNat, Nat.mod_eq_of_lt haLtM, Nat.mod_eq_of_lt hbLtM,
              Nat.mod_eq_of_lt hcLtM, hzero, ↓reduceIte]
            exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _)
              (Nat.mod_lt _ (show 0 < Verity.Core.Uint256.modulus by decide)))
        simp only [hcompile, Except.toOption, Option.getD] at hDiv ⊢
        rw [hsrc]; simp only [hResultVal, hDiv, Bind.bind, Option.bind, Pure.pure]

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
  have hcompile := compileExpr_mulDivUp_ok haCompile hbCompile hcCompile
  rcases haSrc : SourceSemantics.evalExpr fields runtime a with _ | aVal
  · cases hEval : evalIRExpr state aIR <;> simp [hEval, haSrc] at haEval
  · rcases hbSrc : SourceSemantics.evalExpr fields runtime b with _ | bVal
    · cases hEval : evalIRExpr state bIR <;> simp [hEval, hbSrc] at hbEval
    · rcases hcSrc : SourceSemantics.evalExpr fields runtime c with _ | cVal
      · cases hEval : evalIRExpr state cIR <;> simp [hEval, hcSrc] at hcEval
      · have haEval' := evalIRExpr_of_sourceEval_some haEval haSrc
        have hbEval' := evalIRExpr_of_sourceEval_some hbEval hbSrc
        have hcEval' := evalIRExpr_of_sourceEval_some hcEval hcSrc
        have haLt' : aVal < Compiler.Constants.evmModulus := by simpa [haSrc] using haLt
        have hbLt' : bVal < Compiler.Constants.evmModulus := by simpa [hbSrc] using hbLt
        have hcLt' : cVal < Compiler.Constants.evmModulus := by simpa [hcSrc] using hcLt
        have h1Lt : (1 : Nat) < Compiler.Constants.evmModulus := by decide
        have hevmPos : 0 < Compiler.Constants.evmModulus := by decide
        have hLit1 : evalIRExpr state (YulExpr.lit 1) = some 1 := by simp [evalIRExpr]
        have hMul := evalIRExpr_mul_of_eval haEval' hbEval'
        have hSub := evalIRExpr_sub_of_eval hcEval' hLit1
        have hAdd := evalIRExpr_add_of_eval hMul hSub
        have hDiv := evalIRExpr_div_of_eval hAdd hcEval'
        have hsrc := evalExpr_mulDivUp_of_values haSrc hbSrc hcSrc
        -- Simplify hDiv: remove nested mods
        simp only [Nat.mod_eq_of_lt hcLt', Nat.mod_eq_of_lt h1Lt, Nat.mod_mod] at hDiv
        simp only [hcompile, Except.toOption, Option.getD] at hDiv ⊢
        rw [hsrc]
        by_cases hzero : cVal = 0
        · -- Zero divisor: both sides return 0
          subst hzero
          simp only [show (0 : Nat) = 0 from rfl, ↓reduceIte] at hDiv
          simp [HDiv.hDiv, Verity.Core.Uint256.div, Verity.Core.Uint256.ofNat,
            hDiv, Bind.bind, Option.bind, Pure.pure]
        · -- Non-zero divisor
          have h1le : 1 ≤ cVal := Nat.one_le_iff_ne_zero.mpr hzero
          have hSubM1Lt : cVal - 1 < Compiler.Constants.evmModulus :=
            Nat.lt_of_le_of_lt (Nat.sub_le _ _) hcLt'
          have hSubSimp : (Compiler.Constants.evmModulus + cVal - 1) %
              Compiler.Constants.evmModulus = cVal - 1 := by
            have : Compiler.Constants.evmModulus + cVal - 1 =
                Compiler.Constants.evmModulus + (cVal - 1) := by omega
            rw [this, Nat.add_mod_left]
            exact Nat.mod_eq_of_lt hSubM1Lt
          simp only [hSubSimp, hzero, ↓reduceIte] at hDiv
          have hcNe : (Verity.Core.Uint256.ofNat cVal).val ≠ 0 := by
            simp [Verity.Core.Uint256.ofNat, Nat.mod_eq_of_lt hcLt']; exact hzero
          have hcLtM : cVal < Verity.Core.Uint256.modulus := hcLt'
          set_option maxRecDepth 1024 in
          have hResultVal : (((Verity.Core.Uint256.ofNat aVal *
                Verity.Core.Uint256.ofNat bVal) +
                (Verity.Core.Uint256.ofNat cVal - 1)) /
              Verity.Core.Uint256.ofNat cVal).val =
              (aVal * bVal % Compiler.Constants.evmModulus +
                (cVal - 1)) % Compiler.Constants.evmModulus / cVal := by
            show (Verity.Core.Uint256.div _ _).val = _
            simp only [HDiv.hDiv, Verity.Core.Uint256.div, hcNe, ↓reduceIte]
            simp only [HAdd.hAdd, Verity.Core.Uint256.add, Verity.Core.Uint256.ofNat]
            simp only [HMul.hMul, Verity.Core.Uint256.mul, Verity.Core.Uint256.ofNat]
            simp only [HSub.hSub, Verity.Core.Uint256.sub, Verity.Core.Uint256.ofNat,
              Nat.mod_eq_of_lt hcLtM, h1le, ↓reduceIte, Verity.Core.Uint256.val_one]
            -- Unfold OfNat and val_ofNat to get % modulus terms
            simp only [OfNat.ofNat, Verity.Core.Uint256.val_ofNat]
            -- Unfold modulus to 2^256 (which equals evmModulus definitionally)
            simp only [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS]
            -- Reduce % 2^256 terms using bounds
            simp only [Nat.mod_eq_of_lt haLt', Nat.mod_eq_of_lt hbLt']
            -- Reduce the (cVal - 1) % 2^256 term (simp can't match Sub.sub)
            conv_lhs => rw [show Sub.sub cVal 1 % (2 : Nat) ^ 256 = Sub.sub cVal 1
              from Nat.mod_eq_of_lt hSubM1Lt]
            -- Close: outermost % 2^256 on LHS
            exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _)
              (Nat.mod_lt _ hevmPos))
          simp only [hResultVal, hDiv, Bind.bind, Option.bind, Pure.pure]

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
  have hcompile := compileExpr_ceilDiv_ok hlhsCompile hrhsCompile
  rcases hlhsSrc : SourceSemantics.evalExpr fields runtime lhs with _ | lhsVal
  · cases hEval : evalIRExpr state lhsIR <;> simp [hEval, hlhsSrc] at hlhsEval
  · rcases hrhsSrc : SourceSemantics.evalExpr fields runtime rhs with _ | rhsVal
    · cases hEval : evalIRExpr state rhsIR <;> simp [hEval, hrhsSrc] at hrhsEval
    · have hlhsEval' := evalIRExpr_of_sourceEval_some hlhsEval hlhsSrc
      have hrhsEval' := evalIRExpr_of_sourceEval_some hrhsEval hrhsSrc
      have hlhsLt' : lhsVal < Compiler.Constants.evmModulus := by simpa [hlhsSrc] using hlhsLt
      have hrhsLt' : rhsVal < Compiler.Constants.evmModulus := by simpa [hrhsSrc] using hrhsLt
      -- Build the IR evaluation chain
      have hIsZero := evalIRExpr_iszero_of_lt hlhsEval' hlhsLt'
      have hIsZeroIsZero := evalIRExpr_iszero_of_lt hIsZero (boolWord_lt_evmModulus _)
      have hLit1 : evalIRExpr state (YulExpr.lit 1) = some 1 := by
        simp [evalIRExpr]
      have hSub := evalIRExpr_sub_of_eval hlhsEval' hLit1
      simp only [Nat.mod_eq_of_lt hlhsLt', Nat.mod_eq_of_lt (by decide : 1 < Compiler.Constants.evmModulus)] at hSub
      have hDiv := evalIRExpr_div_of_eval hSub hrhsEval'
      simp only [Nat.mod_eq_of_lt hrhsLt', Nat.mod_mod] at hDiv
      have hLit1' : evalIRExpr state (YulExpr.lit 1) = some 1 := hLit1
      have hAdd := evalIRExpr_add_of_eval hDiv hLit1'
      have hMul := evalIRExpr_mul_of_eval hIsZeroIsZero hAdd
      -- Rewrite goal
      have hsrc := evalExpr_ceilDiv_of_values hlhsSrc hrhsSrc
      rw [hsrc]
      simp only [hcompile, Except.toOption, Option.getD] at hMul ⊢
      -- Simplify boolWord/decide values in the IR chain
      -- boolWord (decide (x = 0)) where x is a Nat
      -- For zero case: boolWord true = 1, then boolWord (decide (1 = 0)) = boolWord false = 0
      -- For non-zero case: boolWord false = 0, then boolWord (decide (0 = 0)) = boolWord true = 1
      by_cases hzero : lhsVal = 0
      · -- lhsVal = 0: iszero(iszero(0)) = 0, so mul result is 0
        subst hzero
        -- Simplify boolWord to concrete values
        simp only [SourceSemantics.boolWord] at hMul
        simp at hMul
        -- hMul: ... = some 0. Now close the goal using hMul
        simp [hMul, show (Verity.Core.Uint256.ofNat 0 == (0 : Verity.Core.Uint256)) = true from by decide]
      · -- lhsVal ≠ 0: iszero(iszero(lhsVal)) = 1, so mul result is 1 * addResult
        -- First simplify boolWord in hMul
        simp only [SourceSemantics.boolWord] at hMul
        simp [hzero] at hMul
        -- hMul now: ... = some (addResult % M)
        -- Simplify the IR sub: (M + lhsVal - 1) % M = lhsVal - 1
        have hLhsPos : 0 < lhsVal := Nat.pos_of_ne_zero hzero
        have hSubSimp : (Compiler.Constants.evmModulus + lhsVal - 1) %
            Compiler.Constants.evmModulus = lhsVal - 1 := by
          have : Compiler.Constants.evmModulus + lhsVal - 1 =
              Compiler.Constants.evmModulus + (lhsVal - 1) := by omega
          rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega : lhsVal - 1 < _)]
        -- Need: ofNat lhsVal ≠ 0 for the source side
        have hOfNatNeZero : (Verity.Core.Uint256.ofNat lhsVal == (0 : Verity.Core.Uint256)) = false := by
          rw [beq_eq_false_iff_ne]
          intro h
          have := congr_arg Verity.Core.Uint256.val h
          simp [Verity.Core.Uint256.ofNat, Nat.mod_eq_of_lt hlhsLt'] at this
          exact hzero this
        -- Compute Uint256 operations on the source side
        -- (ofNat lhsVal).val = lhsVal since lhsVal < modulus
        have hLhsOfNat : (Verity.Core.Uint256.ofNat lhsVal).val = lhsVal :=
          show lhsVal % Verity.Core.UINT256_MODULUS = lhsVal from Nat.mod_eq_of_lt hlhsLt'
        have hRhsOfNat : (Verity.Core.Uint256.ofNat rhsVal).val = rhsVal :=
          show rhsVal % Verity.Core.UINT256_MODULUS = rhsVal from Nat.mod_eq_of_lt hrhsLt'
        have hOneVal : (1 : Verity.Core.Uint256).val = 1 := by decide
        -- sub: ofNat lhsVal - 1, since lhsVal ≥ 1
        have hModEq : Verity.Core.Uint256.modulus = Compiler.Constants.evmModulus := rfl
        have hSubVal : (Verity.Core.Uint256.ofNat lhsVal - 1).val = lhsVal - 1 := by
          have hle : (1 : Verity.Core.Uint256).val ≤ (Verity.Core.Uint256.ofNat lhsVal).val := by
            rw [hOneVal, hLhsOfNat]; omega
          have := Verity.Core.Uint256.sub_eq_of_le hle
          rw [hLhsOfNat, hOneVal] at this; exact this
        -- The goal after simp on hMul is:
        -- evalIRExpr state (mul ...) = some (ceilDivVal ...)
        -- which after hMul reduces to showing the IR result equals the source result.
        -- We need to show: the source side (.val of Uint256 operations) equals
        -- the IR side (Nat arithmetic modulo evmModulus).
        -- Compute the source side Uint256 result
        -- ceilDivVal (ofNat lhsVal) (ofNat rhsVal) with lhsVal ≠ 0
        -- = ((ofNat lhsVal - 1) / ofNat rhsVal + 1).val
        -- = (lhsVal - 1) / rhsVal + 1  (when both < evmModulus)
        have hDivLt : (lhsVal - 1) / rhsVal < Compiler.Constants.evmModulus :=
          Nat.lt_of_le_of_lt (Nat.div_le_self (lhsVal - 1) rhsVal) (by omega)
        have hResLt : (lhsVal - 1) / rhsVal + 1 < Compiler.Constants.evmModulus :=
          Nat.lt_of_le_of_lt (Nat.add_le_add_right (Nat.div_le_self (lhsVal - 1) rhsVal) 1)
            (by omega)
        -- Prove div result
        have hDivLtMod : (lhsVal - 1) / rhsVal < Verity.Core.Uint256.modulus := hModEq ▸ hDivLt
        have hDivSrc : ((Verity.Core.Uint256.ofNat lhsVal - 1) /
            Verity.Core.Uint256.ofNat rhsVal).val = (lhsVal - 1) / rhsVal := by
          change (Verity.Core.Uint256.div _ _).val = _
          simp only [Verity.Core.Uint256.div, hSubVal, hRhsOfNat]
          by_cases hrhsZ : rhsVal = 0
          · simp [hrhsZ, Verity.Core.Uint256.ofNat]
          · simp only [hrhsZ, ↓reduceIte, Verity.Core.Uint256.ofNat,
              Nat.mod_eq_of_lt hDivLtMod]
        -- Prove add result
        have hResLtMod : (lhsVal - 1) / rhsVal + 1 < Verity.Core.Uint256.modulus := hModEq ▸ hResLt
        have hResSrc : ((Verity.Core.Uint256.ofNat lhsVal - 1) /
            Verity.Core.Uint256.ofNat rhsVal + 1).val = (lhsVal - 1) / rhsVal + 1 := by
          -- (a + b).val = (a.val + b.val) % modulus
          show (Verity.Core.Uint256.ofNat (((Verity.Core.Uint256.ofNat lhsVal - 1) /
              Verity.Core.Uint256.ofNat rhsVal).val + (1 : Verity.Core.Uint256).val)).val = _
          rw [hDivSrc, hOneVal]
          exact Nat.mod_eq_of_lt hResLtMod
        -- Now close the goal: IR result = source result
        -- Simplify hMul: the big literal is evmModulus - 1
        -- After simp [hzero], hMul has (evmModulus - 1 + lhsVal) % evmModulus / rhsVal
        -- which we need to simplify to (lhsVal - 1) / rhsVal
        have hIRSubSimp : (115792089237316195423570985008687907853269984665640564039457584007913129639935 +
            lhsVal) % Compiler.Constants.evmModulus = lhsVal - 1 := by
          show (Compiler.Constants.evmModulus - 1 + lhsVal) % Compiler.Constants.evmModulus = lhsVal - 1
          have : Compiler.Constants.evmModulus - 1 + lhsVal =
              Compiler.Constants.evmModulus + (lhsVal - 1) := by omega
          rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega : lhsVal - 1 < _)]
        simp only [hIRSubSimp] at hMul
        -- Reduce the do-bind on the goal LHS, substitute hMul
        simp only [Bind.bind, Option.bind, Pure.pure, hMul]
        -- Now goal: some X = some (if (ofNat lhsVal == 0) = true then 0 else ...)
        -- Simplify: ofNat lhsVal ≠ 0, and source side
        simp only [hOfNatNeZero, Bool.false_eq_true, ↓reduceIte, hResSrc]
        -- Now: ((if rhsVal = 0 then 0 else (lhsVal-1)/rhsVal)+1)%M = (lhsVal-1)/rhsVal+1
        by_cases hrhsZ : rhsVal = 0
        · simp [hrhsZ, Verity.Core.Uint256.div, hSubVal]
        · simp only [hrhsZ, ↓reduceIte, Nat.mod_eq_of_lt hResLt]

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
  | literal value =>
      exact ⟨YulExpr.lit (value % CompilationModel.uint256Modulus), by
        unfold CompilationModel.compileExpr CompilationModel.compileExprWithInternals
        rfl⟩
  | param name =>
      exact ⟨YulExpr.ident name, by
        unfold CompilationModel.compileExpr CompilationModel.compileExprWithInternals
        rfl⟩
  | constructorArg idx =>
      exact ⟨YulExpr.ident s!"arg{idx}", by
        unfold CompilationModel.compileExpr CompilationModel.compileExprWithInternals
        rfl⟩
  | localVar name =>
      exact ⟨YulExpr.ident name, by
        unfold CompilationModel.compileExpr CompilationModel.compileExprWithInternals
        rfl⟩
  | caller =>
      exact ⟨YulExpr.call "caller" [], by
        unfold CompilationModel.compileExpr CompilationModel.compileExprWithInternals
        rfl⟩
  | contractAddress =>
      exact ⟨YulExpr.call "address" [], by
        unfold CompilationModel.compileExpr CompilationModel.compileExprWithInternals
        rfl⟩
  | txOrigin =>
      exact ⟨YulExpr.call "origin" [], by
        unfold CompilationModel.compileExpr CompilationModel.compileExprWithInternals
        rfl⟩
  | msgValue =>
      exact ⟨YulExpr.call "callvalue" [], by
        unfold CompilationModel.compileExpr CompilationModel.compileExprWithInternals
        rfl⟩
  | blockTimestamp =>
      exact ⟨YulExpr.call "timestamp" [], by
        unfold CompilationModel.compileExpr CompilationModel.compileExprWithInternals
        rfl⟩
  | blockNumber =>
      exact ⟨YulExpr.call "number" [], by
        unfold CompilationModel.compileExpr CompilationModel.compileExprWithInternals
        rfl⟩
  | chainid =>
      exact ⟨YulExpr.call "chainid" [], by
        unfold CompilationModel.compileExpr CompilationModel.compileExprWithInternals
        rfl⟩
  | blobbasefee =>
      exact ⟨YulExpr.call "blobbasefee" [], by
        unfold CompilationModel.compileExpr CompilationModel.compileExprWithInternals
        rfl⟩
  | calldatasize =>
      exact ⟨YulExpr.call "calldatasize" [], by
        unfold CompilationModel.compileExpr CompilationModel.compileExprWithInternals
        rfl⟩
  | returndataSize =>
      exact ⟨YulExpr.call "returndatasize" [], by
        unfold CompilationModel.compileExpr CompilationModel.compileExprWithInternals
        rfl⟩
  | add hL hR ihL ihR =>
      rename_i lhs rhs
      rcases ihL with ⟨lhsIR, hlhs⟩
      rcases ihR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "add" [lhsIR, rhsIR], compileExpr_add_ok hlhs hrhs⟩
  | sub hL hR ihL ihR =>
      rename_i lhs rhs
      rcases ihL with ⟨lhsIR, hlhs⟩
      rcases ihR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "sub" [lhsIR, rhsIR], compileExpr_sub_ok hlhs hrhs⟩
  | mul hL hR ihL ihR =>
      rename_i lhs rhs
      rcases ihL with ⟨lhsIR, hlhs⟩
      rcases ihR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "mul" [lhsIR, rhsIR], compileExpr_mul_ok hlhs hrhs⟩
  | div hL hR ihL ihR =>
      rename_i lhs rhs
      rcases ihL with ⟨lhsIR, hlhs⟩
      rcases ihR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "div" [lhsIR, rhsIR], compileExpr_div_ok hlhs hrhs⟩
  | mod hL hR ihL ihR =>
      rename_i lhs rhs
      rcases ihL with ⟨lhsIR, hlhs⟩
      rcases ihR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "mod" [lhsIR, rhsIR], compileExpr_mod_ok hlhs hrhs⟩
  | eq hL hR ihL ihR =>
      rename_i lhs rhs
      rcases ihL with ⟨lhsIR, hlhs⟩
      rcases ihR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "eq" [lhsIR, rhsIR], compileExpr_eq_ok hlhs hrhs⟩
  | lt hL hR ihL ihR =>
      rename_i lhs rhs
      rcases ihL with ⟨lhsIR, hlhs⟩
      rcases ihR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "lt" [lhsIR, rhsIR], compileExpr_lt_ok hlhs hrhs⟩
  | slt hL hR ihL ihR =>
      rename_i lhs rhs
      rcases ihL with ⟨lhsIR, hlhs⟩
      rcases ihR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "slt" [lhsIR, rhsIR], compileExpr_slt_ok hlhs hrhs⟩
  | sgt hL hR ihL ihR =>
      rename_i lhs rhs
      rcases ihL with ⟨lhsIR, hlhs⟩
      rcases ihR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "sgt" [lhsIR, rhsIR], compileExpr_sgt_ok hlhs hrhs⟩
  | sdiv hL hR ihL ihR =>
      rename_i lhs rhs
      rcases ihL with ⟨lhsIR, hlhs⟩
      rcases ihR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "sdiv" [lhsIR, rhsIR], compileExpr_sdiv_ok hlhs hrhs⟩
  | smod hL hR ihL ihR =>
      rename_i lhs rhs
      rcases ihL with ⟨lhsIR, hlhs⟩
      rcases ihR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "smod" [lhsIR, rhsIR], compileExpr_smod_ok hlhs hrhs⟩
  | sar hL hR ihL ihR =>
      rename_i lhs rhs
      rcases ihL with ⟨lhsIR, hlhs⟩
      rcases ihR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "sar" [lhsIR, rhsIR], compileExpr_sar_ok hlhs hrhs⟩
  | byte hL hR ihL ihR =>
      rename_i index value
      rcases ihL with ⟨indexIR, hindex⟩
      rcases ihR with ⟨valueIR, hvalue⟩
      exact ⟨YulExpr.call "byte" [indexIR, valueIR], compileExpr_byte_ok hindex hvalue⟩
  | signextend hL hR ihL ihR =>
      rename_i lhs rhs
      rcases ihL with ⟨lhsIR, hlhs⟩
      rcases ihR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "signextend" [lhsIR, rhsIR], compileExpr_signextend_ok hlhs hrhs⟩
  | gt hL hR ihL ihR =>
      rename_i lhs rhs
      rcases ihL with ⟨lhsIR, hlhs⟩
      rcases ihR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "gt" [lhsIR, rhsIR], compileExpr_gt_ok hlhs hrhs⟩
  | ge hL hR ihL ihR =>
      rename_i lhs rhs
      rcases ihL with ⟨lhsIR, hlhs⟩
      rcases ihR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "iszero" [YulExpr.call "lt" [lhsIR, rhsIR]], compileExpr_ge_ok hlhs hrhs⟩
  | le hL hR ihL ihR =>
      rename_i lhs rhs
      rcases ihL with ⟨lhsIR, hlhs⟩
      rcases ihR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "iszero" [YulExpr.call "gt" [lhsIR, rhsIR]], compileExpr_le_ok hlhs hrhs⟩
  | logicalNot h ih =>
      rename_i expr
      rcases ih with ⟨exprIR, hexpr⟩
      exact ⟨YulExpr.call "iszero" [exprIR], compileExpr_logicalNot_ok hexpr⟩
  | logicalAnd hL hR ihL ihR =>
      rename_i lhs rhs
      rcases ihL with ⟨lhsIR, hlhs⟩
      rcases ihR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "and"
          [CompilationModel.yulToBool lhsIR, CompilationModel.yulToBool rhsIR],
        compileExpr_logicalAnd_ok hlhs hrhs⟩
  | logicalOr hL hR ihL ihR =>
      rename_i lhs rhs
      rcases ihL with ⟨lhsIR, hlhs⟩
      rcases ihR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "or"
          [CompilationModel.yulToBool lhsIR, CompilationModel.yulToBool rhsIR],
        compileExpr_logicalOr_ok hlhs hrhs⟩
  | bitAnd hL hR ihL ihR =>
      rename_i lhs rhs
      rcases ihL with ⟨lhsIR, hlhs⟩
      rcases ihR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "and" [lhsIR, rhsIR], compileExpr_bitAnd_ok hlhs hrhs⟩
  | bitOr hL hR ihL ihR =>
      rename_i lhs rhs
      rcases ihL with ⟨lhsIR, hlhs⟩
      rcases ihR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "or" [lhsIR, rhsIR], compileExpr_bitOr_ok hlhs hrhs⟩
  | bitXor hL hR ihL ihR =>
      rename_i lhs rhs
      rcases ihL with ⟨lhsIR, hlhs⟩
      rcases ihR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "xor" [lhsIR, rhsIR], compileExpr_bitXor_ok hlhs hrhs⟩
  | bitNot h ih =>
      rename_i expr
      rcases ih with ⟨exprIR, hexpr⟩
      exact ⟨YulExpr.call "not" [exprIR], compileExpr_bitNot_ok hexpr⟩
  | shl hS hV ihS ihV =>
      rename_i shift value
      rcases ihS with ⟨shiftIR, hshift⟩
      rcases ihV with ⟨valueIR, hvalue⟩
      exact ⟨YulExpr.call "shl" [shiftIR, valueIR], compileExpr_shl_ok hshift hvalue⟩
  | shr hS hV ihS ihV =>
      rename_i shift value
      rcases ihS with ⟨shiftIR, hshift⟩
      rcases ihV with ⟨valueIR, hvalue⟩
      exact ⟨YulExpr.call "shr" [shiftIR, valueIR], compileExpr_shr_ok hshift hvalue⟩
  | min hL hR ihL ihR =>
      rename_i lhs rhs
      rcases ihL with ⟨lhsIR, hlhs⟩
      rcases ihR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "sub" [lhsIR,
        YulExpr.call "mul" [YulExpr.call "sub" [lhsIR, rhsIR],
          YulExpr.call "gt" [lhsIR, rhsIR]]],
        compileExpr_min_ok hlhs hrhs⟩
  | max hL hR ihL ihR =>
      rename_i lhs rhs
      rcases ihL with ⟨lhsIR, hlhs⟩
      rcases ihR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "add" [lhsIR,
        YulExpr.call "mul" [YulExpr.call "sub" [rhsIR, lhsIR],
          YulExpr.call "gt" [rhsIR, lhsIR]]],
        compileExpr_max_ok hlhs hrhs⟩
  | ite hC hT hE ihC ihT ihE =>
      rename_i cond thenVal elseVal
      rcases ihC with ⟨condIR, hcond⟩
      rcases ihT with ⟨thenIR, hthen⟩
      rcases ihE with ⟨elseIR, helse⟩
      exact ⟨YulExpr.call "add" [
        YulExpr.call "mul" [
          YulExpr.call "iszero" [YulExpr.call "iszero" [condIR]], thenIR],
        YulExpr.call "mul" [
          YulExpr.call "iszero" [condIR], elseIR]],
        compileExpr_ite_ok hcond hthen helse⟩
  | ceilDiv hL hR ihL ihR =>
      rename_i lhs rhs
      rcases ihL with ⟨lhsIR, hlhs⟩
      rcases ihR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "mul" [
        YulExpr.call "iszero" [YulExpr.call "iszero" [lhsIR]],
        YulExpr.call "add" [
          YulExpr.call "div" [YulExpr.call "sub" [lhsIR, YulExpr.lit 1], rhsIR],
          YulExpr.lit 1]],
        compileExpr_ceilDiv_ok hlhs hrhs⟩
  | wMulDown hL hR ihL ihR =>
      rename_i lhs rhs
      rcases ihL with ⟨lhsIR, hlhs⟩
      rcases ihR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "div" [
        YulExpr.call "mul" [lhsIR, rhsIR], YulExpr.lit 1000000000000000000],
        compileExpr_wMulDown_ok hlhs hrhs⟩
  | wDivUp hL hR ihL ihR =>
      rename_i lhs rhs
      rcases ihL with ⟨lhsIR, hlhs⟩
      rcases ihR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "div" [
        YulExpr.call "add" [
          YulExpr.call "mul" [lhsIR, YulExpr.lit 1000000000000000000],
          YulExpr.call "sub" [rhsIR, YulExpr.lit 1]],
        rhsIR],
        compileExpr_wDivUp_ok hlhs hrhs⟩
  | mulDivDown hA hB hC ihA ihB ihC =>
      rename_i a b c
      rcases ihA with ⟨aIR, ha⟩
      rcases ihB with ⟨bIR, hb⟩
      rcases ihC with ⟨cIR, hc⟩
      exact ⟨YulExpr.call "div" [YulExpr.call "mul" [aIR, bIR], cIR],
        compileExpr_mulDivDown_ok ha hb hc⟩
  | mulDivUp hA hB hC ihA ihB ihC =>
      rename_i a b c
      rcases ihA with ⟨aIR, ha⟩
      rcases ihB with ⟨bIR, hb⟩
      rcases ihC with ⟨cIR, hc⟩
      exact ⟨YulExpr.call "div" [
        YulExpr.call "add" [YulExpr.call "mul" [aIR, bIR],
          YulExpr.call "sub" [cIR, YulExpr.lit 1]],
        cIR],
        compileExpr_mulDivUp_ok ha hb hc⟩
  | tload hO ihO =>
      rename_i offset
      rcases ihO with ⟨offsetIR, hoffset⟩
      exact ⟨YulExpr.call "tload" [offsetIR], compileExpr_tload_ok hoffset⟩
  | calldataload hO ihO =>
      rename_i offset
      rcases ihO with ⟨offsetIR, hoffset⟩
      exact ⟨YulExpr.call "calldataload" [offsetIR],
        compileExpr_calldataload_ok hoffset⟩
  | mload hO ihO =>
      rename_i offset
      rcases ihO with ⟨offsetIR, hoffset⟩
      exact ⟨YulExpr.call "mload" [offsetIR], compileExpr_mload_ok hoffset⟩
  | extcodesize hA ihA =>
      rename_i addr
      rcases ihA with ⟨addrIR, haddr⟩
      exact ⟨YulExpr.call "extcodesize" [addrIR], compileExpr_extcodesize_ok haddr⟩
  | returndataOptionalBoolAt hO ihO =>
      rename_i offset
      rcases ihO with ⟨offsetIR, hoffset⟩
      exact ⟨YulExpr.call "or" [
        YulExpr.call "eq" [YulExpr.call "returndatasize" [], YulExpr.lit 0],
        YulExpr.call "and" [
          YulExpr.call "eq" [YulExpr.call "returndatasize" [], YulExpr.lit 32],
          YulExpr.call "eq" [YulExpr.call "mload" [offsetIR], YulExpr.lit 1]
        ]
      ], compileExpr_returndataOptionalBoolAt_ok hoffset⟩
  | keccak256 hO hS ihO ihS =>
      rename_i offset size
      rcases ihO with ⟨offsetIR, hoffset⟩
      rcases ihS with ⟨sizeIR, hsize⟩
      exact ⟨YulExpr.call "keccak256" [offsetIR, sizeIR],
        compileExpr_keccak256_ok hoffset hsize⟩
  | builtinExp hB hE ihB ihE =>
      rename_i base exponent
      rcases ihB with ⟨baseIR, hbase⟩
      rcases ihE with ⟨exponentIR, hexp⟩
      exact ⟨YulExpr.call "exp" [baseIR, exponentIR],
        compileExpr_builtinExp_ok hbase hexp⟩

mutual
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
        some (SourceSemantics.evalExpr fields runtime expr) := by
  induction hcore generalizing runtime state with
  | literal value =>
      simpa [CompilationModel.compileExpr, CompilationModel.compileExprWithInternals,
        Except.toOption, Option.getD, Functor.map, Except.map, Bind.bind,
        Except.bind, Pure.pure, Except.pure] using
        eval_compileExpr_literal fields runtime state value
  | param name =>
      simpa [CompilationModel.compileExpr, CompilationModel.compileExprWithInternals,
        Except.toOption, Option.getD, Functor.map, Except.map, Bind.bind,
        Except.bind, Pure.pure, Except.pure] using
        eval_compileExpr_param_of_expr_bindings name hexact hpresent
  | constructorArg idx =>
      simpa [CompilationModel.compileExpr, CompilationModel.compileExprWithInternals,
        Except.toOption, Option.getD, Functor.map, Except.map, Bind.bind,
        Except.bind, Pure.pure, Except.pure] using
        eval_compileExpr_constructorArg_of_expr_bindings idx hexact hpresent
  | localVar name =>
      simpa [CompilationModel.compileExpr, CompilationModel.compileExprWithInternals,
        Except.toOption, Option.getD, Functor.map, Except.map, Bind.bind,
        Except.bind, Pure.pure, Except.pure] using
        eval_compileExpr_localVar_of_expr_bindings name hexact hpresent
  | caller =>
      exact eval_compileExpr_caller hruntime
  | contractAddress =>
      exact eval_compileExpr_contractAddress hruntime
  | txOrigin =>
      exact eval_compileExpr_txOrigin hruntime
  | msgValue =>
      exact eval_compileExpr_msgValue hruntime
  | blockTimestamp =>
      exact eval_compileExpr_blockTimestamp hruntime
  | blockNumber =>
      exact eval_compileExpr_blockNumber hruntime
  | chainid =>
      exact eval_compileExpr_chainid hruntime
  | blobbasefee =>
      exact eval_compileExpr_blobbasefee hruntime
  | calldatasize =>
      exact eval_compileExpr_calldatasize hruntime
  | returndataSize =>
      exact eval_compileExpr_returndataSize hruntime
  | add hL hR ihL ihR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok hR with ⟨rhsIR, hrhs⟩
      have hexactL : bindingsExactlyMatchIRVarsOnExpr lhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hexactR : bindingsExactlyMatchIRVarsOnExpr rhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hpresentL := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hpresentR := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hEvalL : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs) := by
        have htmp := ihL hexactL hbounded hpresentL hruntime
        rw [hlhs] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      have hEvalR : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs) := by
        have htmp := ihR hexactR hbounded hpresentR hruntime
        rw [hrhs] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      exact eval_compileExpr_add_of_compiled hlhs hrhs
        hEvalL hEvalR
  | sub hL hR ihL ihR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok hR with ⟨rhsIR, hrhs⟩
      have hexactL : bindingsExactlyMatchIRVarsOnExpr lhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hexactR : bindingsExactlyMatchIRVarsOnExpr rhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hpresentL := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hpresentR := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hEvalL : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs) := by
        have htmp := ihL hexactL hbounded hpresentL hruntime
        rw [hlhs] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      have hEvalR : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs) := by
        have htmp := ihR hexactR hbounded hpresentR hruntime
        rw [hrhs] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      exact eval_compileExpr_sub_of_compiled hlhs hrhs
        hEvalL hEvalR
        (evalExpr_lt_evmModulus_core_onExpr hL hexactL hbounded hpresentL hruntime)
        (evalExpr_lt_evmModulus_core_onExpr hR hexactR hbounded hpresentR hruntime)
  | mul hL hR ihL ihR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok hR with ⟨rhsIR, hrhs⟩
      have hexactL : bindingsExactlyMatchIRVarsOnExpr lhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hexactR : bindingsExactlyMatchIRVarsOnExpr rhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hpresentL := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hpresentR := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hEvalL : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs) := by
        have htmp := ihL hexactL hbounded hpresentL hruntime
        rw [hlhs] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      have hEvalR : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs) := by
        have htmp := ihR hexactR hbounded hpresentR hruntime
        rw [hrhs] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      exact eval_compileExpr_mul_of_compiled hlhs hrhs
        hEvalL hEvalR
  | div hL hR ihL ihR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok hR with ⟨rhsIR, hrhs⟩
      have hexactL : bindingsExactlyMatchIRVarsOnExpr lhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hexactR : bindingsExactlyMatchIRVarsOnExpr rhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hpresentL := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hpresentR := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hEvalL : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs) := by
        have htmp := ihL hexactL hbounded hpresentL hruntime
        rw [hlhs] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      have hEvalR : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs) := by
        have htmp := ihR hexactR hbounded hpresentR hruntime
        rw [hrhs] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      exact eval_compileExpr_div_of_compiled hlhs hrhs
        hEvalL hEvalR
        (evalExpr_lt_evmModulus_core_onExpr hL hexactL hbounded hpresentL hruntime)
        (evalExpr_lt_evmModulus_core_onExpr hR hexactR hbounded hpresentR hruntime)
  | mod hL hR ihL ihR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok hR with ⟨rhsIR, hrhs⟩
      have hexactL : bindingsExactlyMatchIRVarsOnExpr lhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hexactR : bindingsExactlyMatchIRVarsOnExpr rhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hpresentL := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hpresentR := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hEvalL : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs) := by
        have htmp := ihL hexactL hbounded hpresentL hruntime
        rw [hlhs] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      have hEvalR : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs) := by
        have htmp := ihR hexactR hbounded hpresentR hruntime
        rw [hrhs] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      exact eval_compileExpr_mod_of_compiled hlhs hrhs
        hEvalL hEvalR
        (evalExpr_lt_evmModulus_core_onExpr hL hexactL hbounded hpresentL hruntime)
        (evalExpr_lt_evmModulus_core_onExpr hR hexactR hbounded hpresentR hruntime)
  | eq hL hR ihL ihR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok hR with ⟨rhsIR, hrhs⟩
      have hexactL : bindingsExactlyMatchIRVarsOnExpr lhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hexactR : bindingsExactlyMatchIRVarsOnExpr rhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hpresentL := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hpresentR := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hEvalL : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs) := by
        have htmp := ihL hexactL hbounded hpresentL hruntime
        rw [hlhs] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      have hEvalR : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs) := by
        have htmp := ihR hexactR hbounded hpresentR hruntime
        rw [hrhs] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      exact eval_compileExpr_eq_of_compiled hlhs hrhs
        hEvalL hEvalR
        (evalExpr_lt_evmModulus_core_onExpr hL hexactL hbounded hpresentL hruntime)
        (evalExpr_lt_evmModulus_core_onExpr hR hexactR hbounded hpresentR hruntime)
  | lt hL hR ihL ihR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok hR with ⟨rhsIR, hrhs⟩
      have hexactL : bindingsExactlyMatchIRVarsOnExpr lhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hexactR : bindingsExactlyMatchIRVarsOnExpr rhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hpresentL := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hpresentR := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hEvalL : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs) := by
        have htmp := ihL hexactL hbounded hpresentL hruntime
        rw [hlhs] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      have hEvalR : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs) := by
        have htmp := ihR hexactR hbounded hpresentR hruntime
        rw [hrhs] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      exact eval_compileExpr_lt_of_compiled hlhs hrhs
        hEvalL hEvalR
        (evalExpr_lt_evmModulus_core_onExpr hL hexactL hbounded hpresentL hruntime)
        (evalExpr_lt_evmModulus_core_onExpr hR hexactR hbounded hpresentR hruntime)
  | slt hL hR ihL ihR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok hR with ⟨rhsIR, hrhs⟩
      have hexactL : bindingsExactlyMatchIRVarsOnExpr lhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hexactR : bindingsExactlyMatchIRVarsOnExpr rhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hpresentL := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hpresentR := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hEvalL : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs) := by
        have htmp := ihL hexactL hbounded hpresentL hruntime
        rw [hlhs] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      have hEvalR : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs) := by
        have htmp := ihR hexactR hbounded hpresentR hruntime
        rw [hrhs] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      exact eval_compileExpr_slt_of_compiled hlhs hrhs
        hEvalL hEvalR
        (evalExpr_lt_evmModulus_core_onExpr hL hexactL hbounded hpresentL hruntime)
        (evalExpr_lt_evmModulus_core_onExpr hR hexactR hbounded hpresentR hruntime)
  | sgt hL hR ihL ihR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok hR with ⟨rhsIR, hrhs⟩
      have hexactL : bindingsExactlyMatchIRVarsOnExpr lhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hexactR : bindingsExactlyMatchIRVarsOnExpr rhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hpresentL := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hpresentR := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hEvalL : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs) := by
        have htmp := ihL hexactL hbounded hpresentL hruntime
        rw [hlhs] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      have hEvalR : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs) := by
        have htmp := ihR hexactR hbounded hpresentR hruntime
        rw [hrhs] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      exact eval_compileExpr_sgt_of_compiled hlhs hrhs
        hEvalL hEvalR
        (evalExpr_lt_evmModulus_core_onExpr hL hexactL hbounded hpresentL hruntime)
        (evalExpr_lt_evmModulus_core_onExpr hR hexactR hbounded hpresentR hruntime)
  | sdiv hL hR ihL ihR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok hR with ⟨rhsIR, hrhs⟩
      have hexactL : bindingsExactlyMatchIRVarsOnExpr lhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hexactR : bindingsExactlyMatchIRVarsOnExpr rhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hpresentL := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hpresentR := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hEvalL : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs) := by
        have htmp := ihL hexactL hbounded hpresentL hruntime
        rw [hlhs] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      have hEvalR : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs) := by
        have htmp := ihR hexactR hbounded hpresentR hruntime
        rw [hrhs] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      exact eval_compileExpr_sdiv_of_compiled hlhs hrhs
        hEvalL hEvalR
        (evalExpr_lt_evmModulus_core_onExpr hL hexactL hbounded hpresentL hruntime)
        (evalExpr_lt_evmModulus_core_onExpr hR hexactR hbounded hpresentR hruntime)
  | smod hL hR ihL ihR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok hR with ⟨rhsIR, hrhs⟩
      have hexactL : bindingsExactlyMatchIRVarsOnExpr lhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hexactR : bindingsExactlyMatchIRVarsOnExpr rhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hpresentL := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hpresentR := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hEvalL : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs) := by
        have htmp := ihL hexactL hbounded hpresentL hruntime
        rw [hlhs] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      have hEvalR : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs) := by
        have htmp := ihR hexactR hbounded hpresentR hruntime
        rw [hrhs] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      exact eval_compileExpr_smod_of_compiled hlhs hrhs
        hEvalL hEvalR
        (evalExpr_lt_evmModulus_core_onExpr hL hexactL hbounded hpresentL hruntime)
        (evalExpr_lt_evmModulus_core_onExpr hR hexactR hbounded hpresentR hruntime)
  | sar hL hR ihL ihR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok hR with ⟨rhsIR, hrhs⟩
      have hexactL : bindingsExactlyMatchIRVarsOnExpr lhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hexactR : bindingsExactlyMatchIRVarsOnExpr rhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hpresentL := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hpresentR := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hEvalL : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs) := by
        have htmp := ihL hexactL hbounded hpresentL hruntime
        rw [hlhs] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      have hEvalR : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs) := by
        have htmp := ihR hexactR hbounded hpresentR hruntime
        rw [hrhs] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      exact eval_compileExpr_sar_of_compiled hlhs hrhs
        hEvalL hEvalR
        (evalExpr_lt_evmModulus_core_onExpr hL hexactL hbounded hpresentL hruntime)
        (evalExpr_lt_evmModulus_core_onExpr hR hexactR hbounded hpresentR hruntime)
  | byte hL hR ihL ihR =>
      rename_i index value
      rcases compileExpr_core_ok hL with ⟨indexIR, hindex⟩
      rcases compileExpr_core_ok hR with ⟨valueIR, hvalue⟩
      have hexactIndex : bindingsExactlyMatchIRVarsOnExpr index runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hexactValue : bindingsExactlyMatchIRVarsOnExpr value runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hpresentIndex := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hpresentValue := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hEvalIndex : evalIRExpr state indexIR = some (SourceSemantics.evalExpr fields runtime index) := by
        have htmp := ihL hexactIndex hbounded hpresentIndex hruntime
        rw [hindex] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      have hEvalValue : evalIRExpr state valueIR = some (SourceSemantics.evalExpr fields runtime value) := by
        have htmp := ihR hexactValue hbounded hpresentValue hruntime
        rw [hvalue] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      exact eval_compileExpr_byte_of_compiled hindex hvalue
        hEvalIndex hEvalValue
        (evalExpr_lt_evmModulus_core_onExpr hL hexactIndex hbounded hpresentIndex hruntime)
        (evalExpr_lt_evmModulus_core_onExpr hR hexactValue hbounded hpresentValue hruntime)
  | signextend hL hR ihL ihR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok hR with ⟨rhsIR, hrhs⟩
      have hexactL : bindingsExactlyMatchIRVarsOnExpr lhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hexactR : bindingsExactlyMatchIRVarsOnExpr rhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hpresentL := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hpresentR := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hEvalL : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs) := by
        have htmp := ihL hexactL hbounded hpresentL hruntime
        rw [hlhs] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      have hEvalR : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs) := by
        have htmp := ihR hexactR hbounded hpresentR hruntime
        rw [hrhs] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      exact eval_compileExpr_signextend_of_compiled hlhs hrhs
        hEvalL hEvalR
        (evalExpr_lt_evmModulus_core_onExpr hL hexactL hbounded hpresentL hruntime)
        (evalExpr_lt_evmModulus_core_onExpr hR hexactR hbounded hpresentR hruntime)
  | gt hL hR ihL ihR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok hR with ⟨rhsIR, hrhs⟩
      have hexactL : bindingsExactlyMatchIRVarsOnExpr lhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hexactR : bindingsExactlyMatchIRVarsOnExpr rhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hpresentL := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hpresentR := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hEvalL : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs) := by
        have htmp := ihL hexactL hbounded hpresentL hruntime
        rw [hlhs] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      have hEvalR : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs) := by
        have htmp := ihR hexactR hbounded hpresentR hruntime
        rw [hrhs] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      exact eval_compileExpr_gt_of_compiled hlhs hrhs
        hEvalL hEvalR
        (evalExpr_lt_evmModulus_core_onExpr hL hexactL hbounded hpresentL hruntime)
        (evalExpr_lt_evmModulus_core_onExpr hR hexactR hbounded hpresentR hruntime)
  | ge hL hR ihL ihR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok hR with ⟨rhsIR, hrhs⟩
      have hexactL : bindingsExactlyMatchIRVarsOnExpr lhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hexactR : bindingsExactlyMatchIRVarsOnExpr rhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hpresentL := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hpresentR := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hEvalL : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs) := by
        have htmp := ihL hexactL hbounded hpresentL hruntime
        rw [hlhs] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      have hEvalR : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs) := by
        have htmp := ihR hexactR hbounded hpresentR hruntime
        rw [hrhs] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      exact eval_compileExpr_ge_of_compiled hlhs hrhs
        hEvalL hEvalR
        (evalExpr_lt_evmModulus_core_onExpr hL hexactL hbounded hpresentL hruntime)
        (evalExpr_lt_evmModulus_core_onExpr hR hexactR hbounded hpresentR hruntime)
  | le hL hR ihL ihR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok hR with ⟨rhsIR, hrhs⟩
      have hexactL : bindingsExactlyMatchIRVarsOnExpr lhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hexactR : bindingsExactlyMatchIRVarsOnExpr rhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hpresentL := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hpresentR := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hEvalL : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs) := by
        have htmp := ihL hexactL hbounded hpresentL hruntime
        rw [hlhs] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      have hEvalR : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs) := by
        have htmp := ihR hexactR hbounded hpresentR hruntime
        rw [hrhs] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      exact eval_compileExpr_le_of_compiled hlhs hrhs
        hEvalL hEvalR
        (evalExpr_lt_evmModulus_core_onExpr hL hexactL hbounded hpresentL hruntime)
        (evalExpr_lt_evmModulus_core_onExpr hR hexactR hbounded hpresentR hruntime)
  | logicalNot h ih =>
      rename_i expr
      rcases compileExpr_core_ok h with ⟨exprIR, hexpr⟩
      have hexact' : bindingsExactlyMatchIRVarsOnExpr expr runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using hmem)
      have hpresent' := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using hmem)
      have hEval : evalIRExpr state exprIR = some (SourceSemantics.evalExpr fields runtime expr) := by
        have htmp := ih hexact' hbounded hpresent' hruntime
        rw [hexpr] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      exact eval_compileExpr_logicalNot_of_compiled hexpr
        hEval
        (evalExpr_lt_evmModulus_core_onExpr h hexact' hbounded hpresent' hruntime)
  | logicalAnd hL hR ihL ihR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok hR with ⟨rhsIR, hrhs⟩
      have hexactL : bindingsExactlyMatchIRVarsOnExpr lhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hexactR : bindingsExactlyMatchIRVarsOnExpr rhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hpresentL := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hpresentR := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hEvalL : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs) := by
        have htmp := ihL hexactL hbounded hpresentL hruntime
        rw [hlhs] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      have hEvalR : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs) := by
        have htmp := ihR hexactR hbounded hpresentR hruntime
        rw [hrhs] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      exact eval_compileExpr_logicalAnd_of_compiled hlhs hrhs
        hEvalL hEvalR
        (evalExpr_lt_evmModulus_core_onExpr hL hexactL hbounded hpresentL hruntime)
        (evalExpr_lt_evmModulus_core_onExpr hR hexactR hbounded hpresentR hruntime)
  | logicalOr hL hR ihL ihR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok hR with ⟨rhsIR, hrhs⟩
      have hexactL : bindingsExactlyMatchIRVarsOnExpr lhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hexactR : bindingsExactlyMatchIRVarsOnExpr rhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hpresentL := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hpresentR := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hEvalL : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs) := by
        have htmp := ihL hexactL hbounded hpresentL hruntime
        rw [hlhs] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      have hEvalR : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs) := by
        have htmp := ihR hexactR hbounded hpresentR hruntime
        rw [hrhs] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      exact eval_compileExpr_logicalOr_of_compiled hlhs hrhs
        hEvalL hEvalR
        (evalExpr_lt_evmModulus_core_onExpr hL hexactL hbounded hpresentL hruntime)
        (evalExpr_lt_evmModulus_core_onExpr hR hexactR hbounded hpresentR hruntime)
  | bitAnd hL hR ihL ihR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok hR with ⟨rhsIR, hrhs⟩
      have hexactL : bindingsExactlyMatchIRVarsOnExpr lhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hexactR : bindingsExactlyMatchIRVarsOnExpr rhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hpresentL := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hpresentR := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hEvalL : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs) := by
        have htmp := ihL hexactL hbounded hpresentL hruntime
        rw [hlhs] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      have hEvalR : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs) := by
        have htmp := ihR hexactR hbounded hpresentR hruntime
        rw [hrhs] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      exact eval_compileExpr_bitAnd_of_compiled hlhs hrhs
        hEvalL hEvalR
        (evalExpr_lt_evmModulus_core_onExpr hL hexactL hbounded hpresentL hruntime)
        (evalExpr_lt_evmModulus_core_onExpr hR hexactR hbounded hpresentR hruntime)
  | bitOr hL hR ihL ihR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok hR with ⟨rhsIR, hrhs⟩
      have hexactL : bindingsExactlyMatchIRVarsOnExpr lhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hexactR : bindingsExactlyMatchIRVarsOnExpr rhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hpresentL := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hpresentR := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hEvalL : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs) := by
        have htmp := ihL hexactL hbounded hpresentL hruntime
        rw [hlhs] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      have hEvalR : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs) := by
        have htmp := ihR hexactR hbounded hpresentR hruntime
        rw [hrhs] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      exact eval_compileExpr_bitOr_of_compiled hlhs hrhs
        hEvalL hEvalR
        (evalExpr_lt_evmModulus_core_onExpr hL hexactL hbounded hpresentL hruntime)
        (evalExpr_lt_evmModulus_core_onExpr hR hexactR hbounded hpresentR hruntime)
  | bitXor hL hR ihL ihR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok hR with ⟨rhsIR, hrhs⟩
      have hexactL : bindingsExactlyMatchIRVarsOnExpr lhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hexactR : bindingsExactlyMatchIRVarsOnExpr rhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hpresentL := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hpresentR := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hEvalL : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs) := by
        have htmp := ihL hexactL hbounded hpresentL hruntime
        rw [hlhs] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      have hEvalR : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs) := by
        have htmp := ihR hexactR hbounded hpresentR hruntime
        rw [hrhs] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      exact eval_compileExpr_bitXor_of_compiled hlhs hrhs
        hEvalL hEvalR
        (evalExpr_lt_evmModulus_core_onExpr hL hexactL hbounded hpresentL hruntime)
        (evalExpr_lt_evmModulus_core_onExpr hR hexactR hbounded hpresentR hruntime)
  | bitNot h ih =>
      rename_i expr
      rcases compileExpr_core_ok h with ⟨exprIR, hexpr⟩
      have hexact' : bindingsExactlyMatchIRVarsOnExpr expr runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using hmem)
      have hpresent' := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using hmem)
      have hEval : evalIRExpr state exprIR = some (SourceSemantics.evalExpr fields runtime expr) := by
        have htmp := ih hexact' hbounded hpresent' hruntime
        rw [hexpr] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      exact eval_compileExpr_bitNot_of_compiled hexpr
        hEval
        (evalExpr_lt_evmModulus_core_onExpr h hexact' hbounded hpresent' hruntime)
  | shl hS hV ihS ihV =>
      rename_i shift value
      rcases compileExpr_core_ok hS with ⟨shiftIR, hshift⟩
      rcases compileExpr_core_ok hV with ⟨valueIR, hvalue⟩
      have hexactS : bindingsExactlyMatchIRVarsOnExpr shift runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hexactV : bindingsExactlyMatchIRVarsOnExpr value runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hpresentS := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hpresentV := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hEvalS : evalIRExpr state shiftIR = some (SourceSemantics.evalExpr fields runtime shift) := by
        have htmp := ihS hexactS hbounded hpresentS hruntime
        rw [hshift] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      have hEvalV : evalIRExpr state valueIR = some (SourceSemantics.evalExpr fields runtime value) := by
        have htmp := ihV hexactV hbounded hpresentV hruntime
        rw [hvalue] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      exact eval_compileExpr_shl_of_compiled hshift hvalue
        hEvalS hEvalV
        (evalExpr_lt_evmModulus_core_onExpr hS hexactS hbounded hpresentS hruntime)
        (evalExpr_lt_evmModulus_core_onExpr hV hexactV hbounded hpresentV hruntime)
  | shr hS hV ihS ihV =>
      rename_i shift value
      rcases compileExpr_core_ok hS with ⟨shiftIR, hshift⟩
      rcases compileExpr_core_ok hV with ⟨valueIR, hvalue⟩
      have hexactS : bindingsExactlyMatchIRVarsOnExpr shift runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hexactV : bindingsExactlyMatchIRVarsOnExpr value runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hpresentS := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hpresentV := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hEvalS : evalIRExpr state shiftIR = some (SourceSemantics.evalExpr fields runtime shift) := by
        have htmp := ihS hexactS hbounded hpresentS hruntime
        rw [hshift] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      have hEvalV : evalIRExpr state valueIR = some (SourceSemantics.evalExpr fields runtime value) := by
        have htmp := ihV hexactV hbounded hpresentV hruntime
        rw [hvalue] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      exact eval_compileExpr_shr_of_compiled hshift hvalue
        hEvalS hEvalV
        (evalExpr_lt_evmModulus_core_onExpr hS hexactS hbounded hpresentS hruntime)
        (evalExpr_lt_evmModulus_core_onExpr hV hexactV hbounded hpresentV hruntime)
  | min hL hR ihL ihR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok hR with ⟨rhsIR, hrhs⟩
      have hexactL : bindingsExactlyMatchIRVarsOnExpr lhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hexactR : bindingsExactlyMatchIRVarsOnExpr rhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hpresentL := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hpresentR := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hEvalL : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs) := by
        have htmp := ihL hexactL hbounded hpresentL hruntime
        rw [hlhs] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      have hEvalR : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs) := by
        have htmp := ihR hexactR hbounded hpresentR hruntime
        rw [hrhs] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      exact eval_compileExpr_min_of_compiled hlhs hrhs
        hEvalL hEvalR
        (evalExpr_lt_evmModulus_core_onExpr hL hexactL hbounded hpresentL hruntime)
        (evalExpr_lt_evmModulus_core_onExpr hR hexactR hbounded hpresentR hruntime)
  | max hL hR ihL ihR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok hR with ⟨rhsIR, hrhs⟩
      have hexactL : bindingsExactlyMatchIRVarsOnExpr lhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hexactR : bindingsExactlyMatchIRVarsOnExpr rhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hpresentL := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hpresentR := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hEvalL : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs) := by
        have htmp := ihL hexactL hbounded hpresentL hruntime
        rw [hlhs] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      have hEvalR : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs) := by
        have htmp := ihR hexactR hbounded hpresentR hruntime
        rw [hrhs] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      exact eval_compileExpr_max_of_compiled hlhs hrhs
        hEvalL hEvalR
        (evalExpr_lt_evmModulus_core_onExpr hL hexactL hbounded hpresentL hruntime)
        (evalExpr_lt_evmModulus_core_onExpr hR hexactR hbounded hpresentR hruntime)
  | ite hC hT hE ihC ihT ihE =>
      rename_i cond thenVal elseVal
      rcases compileExpr_core_ok hC with ⟨condIR, hcond⟩
      rcases compileExpr_core_ok hT with ⟨thenIR, hthen⟩
      rcases compileExpr_core_ok hE with ⟨elseIR, helse⟩
      have hexactC : bindingsExactlyMatchIRVarsOnExpr cond runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem; simp [exprBoundNames]; exact Or.inl hmem)
      have hexactT : bindingsExactlyMatchIRVarsOnExpr thenVal runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem; simp [exprBoundNames]; exact Or.inr (Or.inl hmem))
      have hexactE : bindingsExactlyMatchIRVarsOnExpr elseVal runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem; simp [exprBoundNames]; exact Or.inr (Or.inr hmem))
      have hpresentC := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem; simp [exprBoundNames]; exact Or.inl hmem)
      have hpresentT := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem; simp [exprBoundNames]; exact Or.inr (Or.inl hmem))
      have hpresentE := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem; simp [exprBoundNames]; exact Or.inr (Or.inr hmem))
      have hEvalC : evalIRExpr state condIR = some (SourceSemantics.evalExpr fields runtime cond) := by
        have htmp := ihC hexactC hbounded hpresentC hruntime; rw [hcond] at htmp; simpa only [Except.toOption, Option.getD_some] using htmp
      have hEvalT : evalIRExpr state thenIR = some (SourceSemantics.evalExpr fields runtime thenVal) := by
        have htmp := ihT hexactT hbounded hpresentT hruntime; rw [hthen] at htmp; simpa only [Except.toOption, Option.getD_some] using htmp
      have hEvalE : evalIRExpr state elseIR = some (SourceSemantics.evalExpr fields runtime elseVal) := by
        have htmp := ihE hexactE hbounded hpresentE hruntime; rw [helse] at htmp; simpa only [Except.toOption, Option.getD_some] using htmp
      exact eval_compileExpr_ite_of_compiled hcond hthen helse
        hEvalC hEvalT hEvalE
        (evalExpr_lt_evmModulus_core_onExpr hC hexactC hbounded hpresentC hruntime)
        (evalExpr_lt_evmModulus_core_onExpr hT hexactT hbounded hpresentT hruntime)
        (evalExpr_lt_evmModulus_core_onExpr hE hexactE hbounded hpresentE hruntime)
  | ceilDiv hL hR ihL ihR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok hR with ⟨rhsIR, hrhs⟩
      have hexactL : bindingsExactlyMatchIRVarsOnExpr lhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hexactR : bindingsExactlyMatchIRVarsOnExpr rhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hpresentL := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hpresentR := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hEvalL : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs) := by
        have htmp := ihL hexactL hbounded hpresentL hruntime
        rw [hlhs] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      have hEvalR : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs) := by
        have htmp := ihR hexactR hbounded hpresentR hruntime
        rw [hrhs] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      exact eval_compileExpr_ceilDiv_of_compiled hlhs hrhs
        hEvalL hEvalR
        (evalExpr_lt_evmModulus_core_onExpr hL hexactL hbounded hpresentL hruntime)
        (evalExpr_lt_evmModulus_core_onExpr hR hexactR hbounded hpresentR hruntime)
  | wMulDown hL hR ihL ihR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok hR with ⟨rhsIR, hrhs⟩
      have hexactL : bindingsExactlyMatchIRVarsOnExpr lhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem; simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hexactR : bindingsExactlyMatchIRVarsOnExpr rhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem; simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hpresentL := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem; simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hpresentR := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem; simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hEvalL : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs) := by
        have htmp := ihL hexactL hbounded hpresentL hruntime; rw [hlhs] at htmp; simpa only [Except.toOption, Option.getD_some] using htmp
      have hEvalR : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs) := by
        have htmp := ihR hexactR hbounded hpresentR hruntime; rw [hrhs] at htmp; simpa only [Except.toOption, Option.getD_some] using htmp
      exact eval_compileExpr_wMulDown_of_compiled hlhs hrhs
        hEvalL hEvalR
        (evalExpr_lt_evmModulus_core_onExpr hL hexactL hbounded hpresentL hruntime)
        (evalExpr_lt_evmModulus_core_onExpr hR hexactR hbounded hpresentR hruntime)
  | wDivUp hL hR ihL ihR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok hR with ⟨rhsIR, hrhs⟩
      have hexactL : bindingsExactlyMatchIRVarsOnExpr lhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem; simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hexactR : bindingsExactlyMatchIRVarsOnExpr rhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem; simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hpresentL := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem; simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hpresentR := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem; simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hEvalL : evalIRExpr state lhsIR = some (SourceSemantics.evalExpr fields runtime lhs) := by
        have htmp := ihL hexactL hbounded hpresentL hruntime; rw [hlhs] at htmp; simpa only [Except.toOption, Option.getD_some] using htmp
      have hEvalR : evalIRExpr state rhsIR = some (SourceSemantics.evalExpr fields runtime rhs) := by
        have htmp := ihR hexactR hbounded hpresentR hruntime; rw [hrhs] at htmp; simpa only [Except.toOption, Option.getD_some] using htmp
      exact eval_compileExpr_wDivUp_of_compiled hlhs hrhs
        hEvalL hEvalR
        (evalExpr_lt_evmModulus_core_onExpr hL hexactL hbounded hpresentL hruntime)
        (evalExpr_lt_evmModulus_core_onExpr hR hexactR hbounded hpresentR hruntime)
  | mulDivDown hA hB hC ihA ihB ihC =>
      rename_i a b c
      rcases compileExpr_core_ok hA with ⟨aIR, ha⟩
      rcases compileExpr_core_ok hB with ⟨bIR, hb⟩
      rcases compileExpr_core_ok hC with ⟨cIR, hc⟩
      have hexactA : bindingsExactlyMatchIRVarsOnExpr a runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem; simp [exprBoundNames]; exact Or.inl hmem)
      have hexactB : bindingsExactlyMatchIRVarsOnExpr b runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem; simp [exprBoundNames]; exact Or.inr (Or.inl hmem))
      have hexactC : bindingsExactlyMatchIRVarsOnExpr c runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem; simp [exprBoundNames]; exact Or.inr (Or.inr hmem))
      have hpresentA := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem; simp [exprBoundNames]; exact Or.inl hmem)
      have hpresentB := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem; simp [exprBoundNames]; exact Or.inr (Or.inl hmem))
      have hpresentC := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem; simp [exprBoundNames]; exact Or.inr (Or.inr hmem))
      have hEvalA : evalIRExpr state aIR = some (SourceSemantics.evalExpr fields runtime a) := by
        have htmp := ihA hexactA hbounded hpresentA hruntime; rw [ha] at htmp; simpa only [Except.toOption, Option.getD_some] using htmp
      have hEvalB : evalIRExpr state bIR = some (SourceSemantics.evalExpr fields runtime b) := by
        have htmp := ihB hexactB hbounded hpresentB hruntime; rw [hb] at htmp; simpa only [Except.toOption, Option.getD_some] using htmp
      have hEvalC : evalIRExpr state cIR = some (SourceSemantics.evalExpr fields runtime c) := by
        have htmp := ihC hexactC hbounded hpresentC hruntime; rw [hc] at htmp; simpa only [Except.toOption, Option.getD_some] using htmp
      exact eval_compileExpr_mulDivDown_of_compiled ha hb hc
        hEvalA hEvalB hEvalC
        (evalExpr_lt_evmModulus_core_onExpr hA hexactA hbounded hpresentA hruntime)
        (evalExpr_lt_evmModulus_core_onExpr hB hexactB hbounded hpresentB hruntime)
        (evalExpr_lt_evmModulus_core_onExpr hC hexactC hbounded hpresentC hruntime)
  | mulDivUp hA hB hC ihA ihB ihC =>
      rename_i a b c
      rcases compileExpr_core_ok hA with ⟨aIR, ha⟩
      rcases compileExpr_core_ok hB with ⟨bIR, hb⟩
      rcases compileExpr_core_ok hC with ⟨cIR, hc⟩
      have hexactA : bindingsExactlyMatchIRVarsOnExpr a runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem; simp [exprBoundNames]; exact Or.inl hmem)
      have hexactB : bindingsExactlyMatchIRVarsOnExpr b runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem; simp [exprBoundNames]; exact Or.inr (Or.inl hmem))
      have hexactC : bindingsExactlyMatchIRVarsOnExpr c runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem; simp [exprBoundNames]; exact Or.inr (Or.inr hmem))
      have hpresentA := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem; simp [exprBoundNames]; exact Or.inl hmem)
      have hpresentB := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem; simp [exprBoundNames]; exact Or.inr (Or.inl hmem))
      have hpresentC := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem; simp [exprBoundNames]; exact Or.inr (Or.inr hmem))
      have hEvalA : evalIRExpr state aIR = some (SourceSemantics.evalExpr fields runtime a) := by
        have htmp := ihA hexactA hbounded hpresentA hruntime; rw [ha] at htmp; simpa only [Except.toOption, Option.getD_some] using htmp
      have hEvalB : evalIRExpr state bIR = some (SourceSemantics.evalExpr fields runtime b) := by
        have htmp := ihB hexactB hbounded hpresentB hruntime; rw [hb] at htmp; simpa only [Except.toOption, Option.getD_some] using htmp
      have hEvalC : evalIRExpr state cIR = some (SourceSemantics.evalExpr fields runtime c) := by
        have htmp := ihC hexactC hbounded hpresentC hruntime; rw [hc] at htmp; simpa only [Except.toOption, Option.getD_some] using htmp
      exact eval_compileExpr_mulDivUp_of_compiled ha hb hc
        hEvalA hEvalB hEvalC
        (evalExpr_lt_evmModulus_core_onExpr hA hexactA hbounded hpresentA hruntime)
        (evalExpr_lt_evmModulus_core_onExpr hB hexactB hbounded hpresentB hruntime)
        (evalExpr_lt_evmModulus_core_onExpr hC hexactC hbounded hpresentC hruntime)
  | tload hO ihO =>
      rename_i offset
      rcases compileExpr_core_ok hO with ⟨offsetIR, hoffset⟩
      have hexact' : bindingsExactlyMatchIRVarsOnExpr offset runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using hmem)
      have hpresent' := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using hmem)
      have hEvalOff : evalIRExpr state offsetIR =
          some (SourceSemantics.evalExpr fields runtime offset) := by
        have htmp := ihO hexact' hbounded hpresent' hruntime
        rw [hoffset] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      exact eval_compileExpr_tload_of_compiled hoffset hEvalOff hruntime
        (evalExpr_lt_evmModulus_core_onExpr hO hexact' hbounded hpresent' hruntime)
  | calldataload hO ihO =>
      rename_i offset
      rcases compileExpr_core_ok hO with ⟨offsetIR, hoffset⟩
      have hexact' : bindingsExactlyMatchIRVarsOnExpr offset runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using hmem)
      have hpresent' := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using hmem)
      have hEvalOff : evalIRExpr state offsetIR =
          some (SourceSemantics.evalExpr fields runtime offset) := by
        have htmp := ihO hexact' hbounded hpresent' hruntime
        rw [hoffset] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      exact eval_compileExpr_calldataload_of_compiled hoffset hEvalOff hruntime
  | mload hO ihO =>
      rename_i offset
      rcases compileExpr_core_ok hO with ⟨offsetIR, hoffset⟩
      have hexact' : bindingsExactlyMatchIRVarsOnExpr offset runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using hmem)
      have hpresent' := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using hmem)
      have hEvalOff : evalIRExpr state offsetIR =
          some (SourceSemantics.evalExpr fields runtime offset) := by
        have htmp := ihO hexact' hbounded hpresent' hruntime
        rw [hoffset] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      exact eval_compileExpr_mload_of_compiled hoffset hEvalOff hruntime
  | extcodesize hA ihA =>
      rename_i addr
      rcases compileExpr_core_ok hA with ⟨addrIR, haddr⟩
      have hexact' : bindingsExactlyMatchIRVarsOnExpr addr runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using hmem)
      have hpresent' := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using hmem)
      have hEvalAddr : evalIRExpr state addrIR =
          some (SourceSemantics.evalExpr fields runtime addr) := by
        have htmp := ihA hexact' hbounded hpresent' hruntime
        rw [haddr] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      exact eval_compileExpr_extcodesize_of_compiled haddr hEvalAddr hruntime
        (evalExpr_lt_evmModulus_core_onExpr hA hexact' hbounded hpresent' hruntime)
  | returndataOptionalBoolAt hO ihO =>
      rename_i offset
      rcases compileExpr_core_ok hO with ⟨offsetIR, hoffset⟩
      have hexact' : bindingsExactlyMatchIRVarsOnExpr offset runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using hmem)
      have hpresent' := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using hmem)
      have hEvalOff : evalIRExpr state offsetIR =
          some (SourceSemantics.evalExpr fields runtime offset) := by
        have htmp := ihO hexact' hbounded hpresent' hruntime
        rw [hoffset] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      exact eval_compileExpr_returndataOptionalBoolAt_of_compiled hoffset hEvalOff hruntime
  | keccak256 hO hS ihO ihS =>
      rename_i offset size
      rcases compileExpr_core_ok hO with ⟨offsetIR, hoffset⟩
      rcases compileExpr_core_ok hS with ⟨sizeIR, hsize⟩
      have hexactO : bindingsExactlyMatchIRVarsOnExpr offset runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hexactS : bindingsExactlyMatchIRVarsOnExpr size runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hpresentO := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hpresentS := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hEvalOff : evalIRExpr state offsetIR =
          some (SourceSemantics.evalExpr fields runtime offset) := by
        have htmp := ihO hexactO hbounded hpresentO hruntime
        rw [hoffset] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      have hEvalSize : evalIRExpr state sizeIR =
          some (SourceSemantics.evalExpr fields runtime size) := by
        have htmp := ihS hexactS hbounded hpresentS hruntime
        rw [hsize] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      exact eval_compileExpr_keccak256_of_compiled
        hoffset hsize hEvalOff hEvalSize hruntime
  | builtinExp hB hE ihB ihE =>
      rename_i base exponent
      rcases compileExpr_core_ok hB with ⟨baseIR, hbase⟩
      rcases compileExpr_core_ok hE with ⟨exponentIR, hexp⟩
      have hexactB : bindingsExactlyMatchIRVarsOnExpr base runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames, exprListBoundNames] using
            List.mem_append.mpr (Or.inl hmem))
      have hexactE : bindingsExactlyMatchIRVarsOnExpr exponent runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem
          simpa [exprBoundNames, exprListBoundNames] using
            List.mem_append.mpr (Or.inr hmem))
      have hpresentB := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames, exprListBoundNames] using List.mem_append.mpr (Or.inl hmem))
      have hpresentE := exprBoundNamesPresent_of_subset hpresent (by
        intro name hmem
        simpa [exprBoundNames, exprListBoundNames] using List.mem_append.mpr (Or.inr hmem))
      have hEvalBase : evalIRExpr state baseIR =
          some (SourceSemantics.evalExpr fields runtime base) := by
        have htmp := ihB hexactB hbounded hpresentB hruntime
        rw [hbase] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      have hEvalExp : evalIRExpr state exponentIR =
          some (SourceSemantics.evalExpr fields runtime exponent) := by
        have htmp := ihE hexactE hbounded hpresentE hruntime
        rw [hexp] at htmp
        simpa only [Except.toOption, Option.getD_some] using htmp
      exact eval_compileExpr_builtinExp_of_compiled hbase hexp hEvalBase hEvalExp

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
    SourceSemantics.evalExpr fields runtime expr < Compiler.Constants.evmModulus := by
  induction hcore generalizing runtime state with
  | literal value =>
      change SourceSemantics.wordNormalize value < Compiler.Constants.evmModulus
      exact wordNormalize_lt_evmModulus value
  | param name =>
      change SourceSemantics.lookupValue runtime.bindings name < Compiler.Constants.evmModulus
      exact hbounded name
  | constructorArg idx =>
      rcases hpresent s!"arg{idx}" (by simp [exprBoundNames]) with ⟨value, hlookup⟩
      have hsourceLookup :
          SourceSemantics.lookupBinding? runtime.bindings s!"arg{idx}" = some value := by
        simpa [lookupBinding?, SourceSemantics.lookupBinding?] using hlookup
      have hlookupValue :
          SourceSemantics.lookupValue runtime.bindings s!"arg{idx}" = value :=
        lookupValue_eq_of_lookupBinding?_some hlookup
      have hlt := hbounded s!"arg{idx}"
      rw [hlookupValue] at hlt
      change SourceSemantics.lookupBinding? runtime.bindings s!"arg{idx}" <
        Compiler.Constants.evmModulus
      rw [hsourceLookup]
      exact hlt
  | localVar name =>
      change SourceSemantics.lookupValue runtime.bindings name < Compiler.Constants.evmModulus
      exact hbounded name
  | caller =>
      change runtime.world.sender.val < Compiler.Constants.evmModulus
      exact Nat.lt_trans runtime.world.sender.isLt (by decide)
  | contractAddress =>
      change runtime.world.thisAddress.val < Compiler.Constants.evmModulus
      exact Nat.lt_trans runtime.world.thisAddress.isLt (by decide)
  | txOrigin =>
      change runtime.world.txOrigin.val < Compiler.Constants.evmModulus
      exact Nat.lt_trans runtime.world.txOrigin.isLt (by decide)
  | msgValue =>
      change runtime.world.msgValue.val < Compiler.Constants.evmModulus
      exact runtime.world.msgValue.isLt
  | blockTimestamp =>
      change runtime.world.blockTimestamp.val < Compiler.Constants.evmModulus
      exact runtime.world.blockTimestamp.isLt
  | blockNumber =>
      change runtime.world.blockNumber.val < Compiler.Constants.evmModulus
      exact runtime.world.blockNumber.isLt
  | chainid =>
      change runtime.world.chainId.val < Compiler.Constants.evmModulus
      exact runtime.world.chainId.isLt
  | blobbasefee =>
      change runtime.world.blobBaseFee.val < Compiler.Constants.evmModulus
      exact runtime.world.blobBaseFee.isLt
  | calldatasize =>
      change runtime.world.calldataSize.val < Compiler.Constants.evmModulus
      exact runtime.world.calldataSize.isLt
  | returndataSize =>
      simp [SourceSemantics.evalExpr, Compiler.Constants.evmModulus]
  | @add lhs rhs _ _ _ _ =>
      show (do let l : Verity.Core.Uint256 := ← SourceSemantics.evalExpr fields runtime lhs
               let r : Verity.Core.Uint256 := ← SourceSemantics.evalExpr fields runtime rhs
               pure (l + r).val) < _
      rcases SourceSemantics.evalExpr fields runtime lhs with _ | lVal
      · trivial
      · rcases SourceSemantics.evalExpr fields runtime rhs with _ | rVal
        · trivial
        · exact (Verity.Core.Uint256.ofNat lVal + Verity.Core.Uint256.ofNat rVal).isLt
  | @sub lhs rhs _ _ _ _ =>
      show (do let l : Verity.Core.Uint256 := ← SourceSemantics.evalExpr fields runtime lhs
               let r : Verity.Core.Uint256 := ← SourceSemantics.evalExpr fields runtime rhs
               pure (l - r).val) < _
      rcases SourceSemantics.evalExpr fields runtime lhs with _ | lVal
      · trivial
      · rcases SourceSemantics.evalExpr fields runtime rhs with _ | rVal
        · trivial
        · exact (Verity.Core.Uint256.ofNat lVal - Verity.Core.Uint256.ofNat rVal).isLt
  | @mul lhs rhs _ _ _ _ =>
      show (do let l : Verity.Core.Uint256 := ← SourceSemantics.evalExpr fields runtime lhs
               let r : Verity.Core.Uint256 := ← SourceSemantics.evalExpr fields runtime rhs
               pure (l * r).val) < _
      rcases SourceSemantics.evalExpr fields runtime lhs with _ | lVal
      · trivial
      · rcases SourceSemantics.evalExpr fields runtime rhs with _ | rVal
        · trivial
        · exact (Verity.Core.Uint256.ofNat lVal * Verity.Core.Uint256.ofNat rVal).isLt
  | @div lhs rhs _ _ _ _ =>
      show (do let l : Verity.Core.Uint256 := ← SourceSemantics.evalExpr fields runtime lhs
               let r : Verity.Core.Uint256 := ← SourceSemantics.evalExpr fields runtime rhs
               pure (l / r).val) < _
      rcases SourceSemantics.evalExpr fields runtime lhs with _ | lVal
      · trivial
      · rcases SourceSemantics.evalExpr fields runtime rhs with _ | rVal
        · trivial
        · exact (Verity.Core.Uint256.ofNat lVal / Verity.Core.Uint256.ofNat rVal).isLt
  | @mod lhs rhs _ _ _ _ =>
      show (do let l : Verity.Core.Uint256 := ← SourceSemantics.evalExpr fields runtime lhs
               let r : Verity.Core.Uint256 := ← SourceSemantics.evalExpr fields runtime rhs
               pure (l % r).val) < _
      rcases SourceSemantics.evalExpr fields runtime lhs with _ | lVal
      · trivial
      · rcases SourceSemantics.evalExpr fields runtime rhs with _ | rVal
        · trivial
        · exact (Verity.Core.Uint256.ofNat lVal % Verity.Core.Uint256.ofNat rVal).isLt
  | @eq lhs rhs _ _ _ _ =>
      show (do let lv ← SourceSemantics.evalExpr fields runtime lhs
               let rv ← SourceSemantics.evalExpr fields runtime rhs
               pure (SourceSemantics.boolWord (decide (lv = rv)))) < _
      rcases SourceSemantics.evalExpr fields runtime lhs with _ | lVal
      · trivial
      · rcases SourceSemantics.evalExpr fields runtime rhs with _ | rVal
        · trivial
        · exact boolWord_lt_evmModulus _
  | @lt lhs rhs _ _ _ _ =>
      show (do let lv ← SourceSemantics.evalExpr fields runtime lhs
               let rv ← SourceSemantics.evalExpr fields runtime rhs
               pure (SourceSemantics.boolWord (decide (lv < rv)))) < _
      rcases SourceSemantics.evalExpr fields runtime lhs with _ | lVal
      · trivial
      · rcases SourceSemantics.evalExpr fields runtime rhs with _ | rVal
        · trivial
        · exact boolWord_lt_evmModulus _
  | @slt lhs rhs _ _ _ _ =>
      show (do let lv ← SourceSemantics.evalExpr fields runtime lhs
               let rv ← SourceSemantics.evalExpr fields runtime rhs
               pure (SourceSemantics.boolWord (decide (
                 (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat lv) : Int) <
                 (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat rv) : Int))))) < _
      rcases SourceSemantics.evalExpr fields runtime lhs with _ | lVal
      · trivial
      · rcases SourceSemantics.evalExpr fields runtime rhs with _ | rVal
        · trivial
        · exact boolWord_lt_evmModulus _
  | @sgt lhs rhs _ _ _ _ =>
      show (do let lv ← SourceSemantics.evalExpr fields runtime lhs
               let rv ← SourceSemantics.evalExpr fields runtime rhs
               pure (SourceSemantics.boolWord (decide (
                 (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat rv) : Int) <
                 (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat lv) : Int))))) < _
      rcases SourceSemantics.evalExpr fields runtime lhs with _ | lVal
      · trivial
      · rcases SourceSemantics.evalExpr fields runtime rhs with _ | rVal
        · trivial
        · exact boolWord_lt_evmModulus _
  | @sdiv lhs rhs _ _ _ _ =>
      show (do let lv ← SourceSemantics.evalExpr fields runtime lhs
               let rv ← SourceSemantics.evalExpr fields runtime rhs
               pure (Verity.Core.Int256.div
                 (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat lv))
                 (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat rv))).toUint256.val) < _
      rcases SourceSemantics.evalExpr fields runtime lhs with _ | lVal
      · trivial
      · rcases SourceSemantics.evalExpr fields runtime rhs with _ | rVal
        · trivial
        · exact (Verity.Core.Int256.div
            (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat lVal))
            (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat rVal))).toUint256.isLt
  | @smod lhs rhs _ _ _ _ =>
      show (do let lv ← SourceSemantics.evalExpr fields runtime lhs
               let rv ← SourceSemantics.evalExpr fields runtime rhs
               pure (Verity.Core.Int256.mod
                 (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat lv))
                 (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat rv))).toUint256.val) < _
      rcases SourceSemantics.evalExpr fields runtime lhs with _ | lVal
      · trivial
      · rcases SourceSemantics.evalExpr fields runtime rhs with _ | rVal
        · trivial
        · exact (Verity.Core.Int256.mod
            (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat lVal))
            (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat rVal))).toUint256.isLt
  | @sar lhs rhs _ _ _ _ =>
      show (do let lv ← SourceSemantics.evalExpr fields runtime lhs
               let rv ← SourceSemantics.evalExpr fields runtime rhs
               pure (Verity.Core.Int256.sar
                 (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat lv))
                 (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat rv))).toUint256.val) < _
      rcases SourceSemantics.evalExpr fields runtime lhs with _ | lVal
      · trivial
      · rcases SourceSemantics.evalExpr fields runtime rhs with _ | rVal
        · trivial
        · exact (Verity.Core.Int256.sar
            (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat lVal))
            (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat rVal))).toUint256.isLt
  | @byte index value _ _ _ _ =>
      show (do let indexVal ← SourceSemantics.evalExpr fields runtime index
               let valueVal ← SourceSemantics.evalExpr fields runtime value
               pure (Verity.Core.Uint256.byte
                 (Verity.Core.Uint256.ofNat indexVal)
                 (Verity.Core.Uint256.ofNat valueVal)).val) < _
      rcases SourceSemantics.evalExpr fields runtime index with _ | indexVal
      · trivial
      · rcases SourceSemantics.evalExpr fields runtime value with _ | valueVal
        · trivial
        · exact (Verity.Core.Uint256.byte
            (Verity.Core.Uint256.ofNat indexVal)
            (Verity.Core.Uint256.ofNat valueVal)).isLt
  | @signextend lhs rhs _ _ _ _ =>
      show (do let lv ← SourceSemantics.evalExpr fields runtime lhs
               let rv ← SourceSemantics.evalExpr fields runtime rhs
               pure (Verity.Core.Uint256.signextend
                 (Verity.Core.Uint256.ofNat lv)
                 (Verity.Core.Uint256.ofNat rv)).val) < _
      rcases SourceSemantics.evalExpr fields runtime lhs with _ | lVal
      · trivial
      · rcases SourceSemantics.evalExpr fields runtime rhs with _ | rVal
        · trivial
        · exact (Verity.Core.Uint256.signextend
            (Verity.Core.Uint256.ofNat lVal)
            (Verity.Core.Uint256.ofNat rVal)).isLt
  | @gt lhs rhs _ _ _ _ =>
      show (do let lv ← SourceSemantics.evalExpr fields runtime lhs
               let rv ← SourceSemantics.evalExpr fields runtime rhs
               pure (SourceSemantics.boolWord (decide (rv < lv)))) < _
      rcases SourceSemantics.evalExpr fields runtime lhs with _ | lVal
      · trivial
      · rcases SourceSemantics.evalExpr fields runtime rhs with _ | rVal
        · trivial
        · exact boolWord_lt_evmModulus _
  | @ge lhs rhs _ _ _ _ =>
      show (do let lv ← SourceSemantics.evalExpr fields runtime lhs
               let rv ← SourceSemantics.evalExpr fields runtime rhs
               pure (SourceSemantics.boolWord (decide (rv ≤ lv)))) < _
      rcases SourceSemantics.evalExpr fields runtime lhs with _ | lVal
      · trivial
      · rcases SourceSemantics.evalExpr fields runtime rhs with _ | rVal
        · trivial
        · exact boolWord_lt_evmModulus _
  | @le lhs rhs _ _ _ _ =>
      show (do let lv ← SourceSemantics.evalExpr fields runtime lhs
               let rv ← SourceSemantics.evalExpr fields runtime rhs
               pure (SourceSemantics.boolWord (decide (lv ≤ rv)))) < _
      rcases SourceSemantics.evalExpr fields runtime lhs with _ | lVal
      · trivial
      · rcases SourceSemantics.evalExpr fields runtime rhs with _ | rVal
        · trivial
        · exact boolWord_lt_evmModulus _
  | @logicalNot subexpr _ _ =>
      show (do let value ← SourceSemantics.evalExpr fields runtime subexpr
               pure (SourceSemantics.boolWord (decide (value = 0)))) < _
      rcases SourceSemantics.evalExpr fields runtime subexpr with _ | val
      · trivial
      · exact boolWord_lt_evmModulus _
  | @logicalAnd lhs rhs _ _ _ _ =>
      show (do let lv ← SourceSemantics.evalExpr fields runtime lhs
               let rv ← SourceSemantics.evalExpr fields runtime rhs
               pure (SourceSemantics.boolWord (decide (lv != 0) && decide (rv != 0)))) < _
      rcases SourceSemantics.evalExpr fields runtime lhs with _ | lVal
      · trivial
      · rcases SourceSemantics.evalExpr fields runtime rhs with _ | rVal
        · trivial
        · exact boolWord_lt_evmModulus _
  | @logicalOr lhs rhs _ _ _ _ =>
      show (do let lv ← SourceSemantics.evalExpr fields runtime lhs
               let rv ← SourceSemantics.evalExpr fields runtime rhs
               pure (SourceSemantics.boolWord (decide (lv != 0) || decide (rv != 0)))) < _
      rcases SourceSemantics.evalExpr fields runtime lhs with _ | lVal
      · trivial
      · rcases SourceSemantics.evalExpr fields runtime rhs with _ | rVal
        · trivial
        · exact boolWord_lt_evmModulus _
  | @bitAnd lhs rhs _ _ _ _ =>
      show (do let l : Verity.Core.Uint256 := ← SourceSemantics.evalExpr fields runtime lhs
               let r : Verity.Core.Uint256 := ← SourceSemantics.evalExpr fields runtime rhs
               pure (Verity.Core.Uint256.and l r).val) < _
      rcases SourceSemantics.evalExpr fields runtime lhs with _ | lVal
      · trivial
      · rcases SourceSemantics.evalExpr fields runtime rhs with _ | rVal
        · trivial
        · exact (Verity.Core.Uint256.and (Verity.Core.Uint256.ofNat lVal) (Verity.Core.Uint256.ofNat rVal)).isLt
  | @bitOr lhs rhs _ _ _ _ =>
      show (do let l : Verity.Core.Uint256 := ← SourceSemantics.evalExpr fields runtime lhs
               let r : Verity.Core.Uint256 := ← SourceSemantics.evalExpr fields runtime rhs
               pure (Verity.Core.Uint256.or l r).val) < _
      rcases SourceSemantics.evalExpr fields runtime lhs with _ | lVal
      · trivial
      · rcases SourceSemantics.evalExpr fields runtime rhs with _ | rVal
        · trivial
        · exact (Verity.Core.Uint256.or (Verity.Core.Uint256.ofNat lVal) (Verity.Core.Uint256.ofNat rVal)).isLt
  | @bitXor lhs rhs _ _ _ _ =>
      show (do let l : Verity.Core.Uint256 := ← SourceSemantics.evalExpr fields runtime lhs
               let r : Verity.Core.Uint256 := ← SourceSemantics.evalExpr fields runtime rhs
               pure (Verity.Core.Uint256.xor l r).val) < _
      rcases SourceSemantics.evalExpr fields runtime lhs with _ | lVal
      · trivial
      · rcases SourceSemantics.evalExpr fields runtime rhs with _ | rVal
        · trivial
        · exact (Verity.Core.Uint256.xor (Verity.Core.Uint256.ofNat lVal) (Verity.Core.Uint256.ofNat rVal)).isLt
  | @bitNot subexpr _ _ =>
      show (do let v : Verity.Core.Uint256 := ← SourceSemantics.evalExpr fields runtime subexpr
               pure (Verity.Core.Uint256.not v).val) < _
      rcases SourceSemantics.evalExpr fields runtime subexpr with _ | val
      · trivial
      · exact (Verity.Core.Uint256.not (Verity.Core.Uint256.ofNat val)).isLt
  | @shl shift value _ _ _ _ =>
      show (do let s : Verity.Core.Uint256 := ← SourceSemantics.evalExpr fields runtime shift
               let v : Verity.Core.Uint256 := ← SourceSemantics.evalExpr fields runtime value
               pure (Verity.Core.Uint256.shl s v).val) < _
      rcases SourceSemantics.evalExpr fields runtime shift with _ | sVal
      · trivial
      · rcases SourceSemantics.evalExpr fields runtime value with _ | vVal
        · trivial
        · exact (Verity.Core.Uint256.shl (Verity.Core.Uint256.ofNat sVal) (Verity.Core.Uint256.ofNat vVal)).isLt
  | @shr shift value _ _ _ _ =>
      show (do let s : Verity.Core.Uint256 := ← SourceSemantics.evalExpr fields runtime shift
               let v : Verity.Core.Uint256 := ← SourceSemantics.evalExpr fields runtime value
               pure (Verity.Core.Uint256.shr s v).val) < _
      rcases SourceSemantics.evalExpr fields runtime shift with _ | sVal
      · trivial
      · rcases SourceSemantics.evalExpr fields runtime value with _ | vVal
        · trivial
        · exact (Verity.Core.Uint256.shr (Verity.Core.Uint256.ofNat sVal) (Verity.Core.Uint256.ofNat vVal)).isLt
  | @min lhs rhs _ _ ihL ihR =>
      show (do let l ← SourceSemantics.evalExpr fields runtime lhs
               let r ← SourceSemantics.evalExpr fields runtime rhs
               pure (if l ≤ r then l else r)) < _
      rcases hlhsSrc : SourceSemantics.evalExpr fields runtime lhs with _ | lVal
      · trivial
      · rcases hrhsSrc : SourceSemantics.evalExpr fields runtime rhs with _ | rVal
        · trivial
        · simp only [Option.bind_some, Option.pure_def]
          have hexactL := bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
            intro name hmem; simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
          have hexactR := bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
            intro name hmem; simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
          have hpresentL := exprBoundNamesPresent_of_subset hpresent (by
            intro name hmem; simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
          have hpresentR := exprBoundNamesPresent_of_subset hpresent (by
            intro name hmem; simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
          have hlLt : lVal < Constants.evmModulus := by
            have := ihL hexactL hbounded hpresentL hruntime; rwa [hlhsSrc] at this
          have hrLt : rVal < Constants.evmModulus := by
            have := ihR hexactR hbounded hpresentR hruntime; rwa [hrhsSrc] at this
          by_cases h : lVal ≤ rVal
          · simp [h]; exact hlLt
          · simp [h]; exact hrLt
  | @max lhs rhs _ _ ihL ihR =>
      show (do let l ← SourceSemantics.evalExpr fields runtime lhs
               let r ← SourceSemantics.evalExpr fields runtime rhs
               pure (if r ≤ l then l else r)) < _
      rcases hlhsSrc : SourceSemantics.evalExpr fields runtime lhs with _ | lVal
      · trivial
      · rcases hrhsSrc : SourceSemantics.evalExpr fields runtime rhs with _ | rVal
        · trivial
        · simp only [Option.bind_some, Option.pure_def]
          have hexactL := bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
            intro name hmem; simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
          have hexactR := bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
            intro name hmem; simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
          have hpresentL := exprBoundNamesPresent_of_subset hpresent (by
            intro name hmem; simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hmem))
          have hpresentR := exprBoundNamesPresent_of_subset hpresent (by
            intro name hmem; simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hmem))
          have hlLt : lVal < Constants.evmModulus := by
            have := ihL hexactL hbounded hpresentL hruntime; rwa [hlhsSrc] at this
          have hrLt : rVal < Constants.evmModulus := by
            have := ihR hexactR hbounded hpresentR hruntime; rwa [hrhsSrc] at this
          by_cases h : rVal ≤ lVal
          · simp [h]; exact hlLt
          · simp [h]; exact hrLt
  | @ite cond thenVal elseVal _ _ _ ihC ihT ihE =>
      show (do let c ← SourceSemantics.evalExpr fields runtime cond
               if c != 0 then SourceSemantics.evalExpr fields runtime thenVal
               else SourceSemantics.evalExpr fields runtime elseVal) < _
      rcases SourceSemantics.evalExpr fields runtime cond with _ | cVal
      · trivial
      · simp only [Option.bind_some, bne_iff_ne]
        have hexactT := bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem; simp [exprBoundNames]; exact Or.inr (Or.inl hmem))
        have hexactE := bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hmem; simp [exprBoundNames]; exact Or.inr (Or.inr hmem))
        have hpresentT := exprBoundNamesPresent_of_subset hpresent (by
          intro name hmem; simp [exprBoundNames]; exact Or.inr (Or.inl hmem))
        have hpresentE := exprBoundNamesPresent_of_subset hpresent (by
          intro name hmem; simp [exprBoundNames]; exact Or.inr (Or.inr hmem))
        by_cases h : cVal ≠ 0
        · simp [h]; simpa using ihT hexactT hbounded hpresentT hruntime
        · simp only [show cVal = 0 from by omega, ite_true]
          simpa using ihE hexactE hbounded hpresentE hruntime
  | @ceilDiv lhs rhs _ _ ihL ihR =>
      -- ceilDiv unfolds to: do let l ← lhs; let r ← rhs; pure (ceilDivVal ...)
      -- Use rfl to unfold the goal (bypasses private ceilDivVal)
      show (do let l ← SourceSemantics.evalExpr fields runtime lhs
               let r ← SourceSemantics.evalExpr fields runtime rhs
               pure (if (Verity.Core.Uint256.ofNat l) == (0 : Verity.Core.Uint256) then 0
                     else ((Verity.Core.Uint256.ofNat l - 1) / Verity.Core.Uint256.ofNat r + 1).val)) < _
      rcases SourceSemantics.evalExpr fields runtime lhs with _ | lVal
      · trivial
      · rcases SourceSemantics.evalExpr fields runtime rhs with _ | rVal
        · trivial
        · -- Reduce the do-bind, then handle if
          simp only [Bind.bind, Option.bind, Pure.pure]
          by_cases h : (Verity.Core.Uint256.ofNat lVal == (0 : Verity.Core.Uint256)) = true
          · simp [h]
          · simp only [h, ↓reduceIte]
            have hModEq : Verity.Core.Uint256.modulus = Compiler.Constants.evmModulus := rfl
            exact hModEq ▸
              ((Verity.Core.Uint256.ofNat lVal - 1) / Verity.Core.Uint256.ofNat rVal + 1).isLt
  | @wMulDown lhs rhs _ _ ihL ihR =>
      show (do let l ← SourceSemantics.evalExpr fields runtime lhs
               let r ← SourceSemantics.evalExpr fields runtime rhs
               pure ((Verity.Core.Uint256.ofNat l * Verity.Core.Uint256.ofNat r) /
                 (1000000000000000000 : Verity.Core.Uint256)).val) < _
      rcases SourceSemantics.evalExpr fields runtime lhs with _ | lVal
      · trivial
      · rcases SourceSemantics.evalExpr fields runtime rhs with _ | rVal
        · trivial
        · simp only [Bind.bind, Option.bind, Pure.pure]
          have hModEq : Verity.Core.Uint256.modulus = Compiler.Constants.evmModulus := rfl
          exact hModEq ▸ ((Verity.Core.Uint256.ofNat lVal * Verity.Core.Uint256.ofNat rVal) /
            (1000000000000000000 : Verity.Core.Uint256)).isLt
  | @wDivUp lhs rhs _ _ ihL ihR =>
      show (do let l ← SourceSemantics.evalExpr fields runtime lhs
               let r ← SourceSemantics.evalExpr fields runtime rhs
               pure (((Verity.Core.Uint256.ofNat l * (1000000000000000000 : Verity.Core.Uint256)) +
                 (Verity.Core.Uint256.ofNat r - 1)) / Verity.Core.Uint256.ofNat r).val) < _
      rcases SourceSemantics.evalExpr fields runtime lhs with _ | lVal
      · trivial
      · rcases SourceSemantics.evalExpr fields runtime rhs with _ | rVal
        · trivial
        · simp only [Bind.bind, Option.bind, Pure.pure]
          have hModEq : Verity.Core.Uint256.modulus = Compiler.Constants.evmModulus := rfl
          exact hModEq ▸ (((Verity.Core.Uint256.ofNat lVal *
            (1000000000000000000 : Verity.Core.Uint256)) +
            (Verity.Core.Uint256.ofNat rVal - 1)) / Verity.Core.Uint256.ofNat rVal).isLt
  | @mulDivDown a b c _ _ _ ihA ihB ihC =>
      show (do let aV ← SourceSemantics.evalExpr fields runtime a
               let bV ← SourceSemantics.evalExpr fields runtime b
               let cV ← SourceSemantics.evalExpr fields runtime c
               pure ((Verity.Core.Uint256.ofNat aV * Verity.Core.Uint256.ofNat bV) /
                 Verity.Core.Uint256.ofNat cV).val) < _
      rcases SourceSemantics.evalExpr fields runtime a with _ | aVal
      · trivial
      · rcases SourceSemantics.evalExpr fields runtime b with _ | bVal
        · trivial
        · rcases SourceSemantics.evalExpr fields runtime c with _ | cVal
          · trivial
          · simp only [Bind.bind, Option.bind, Pure.pure]
            have hModEq : Verity.Core.Uint256.modulus = Compiler.Constants.evmModulus := rfl
            exact hModEq ▸ ((Verity.Core.Uint256.ofNat aVal * Verity.Core.Uint256.ofNat bVal) /
              Verity.Core.Uint256.ofNat cVal).isLt
  | @mulDivUp a b c _ _ _ ihA ihB ihC =>
      show (do let aV ← SourceSemantics.evalExpr fields runtime a
               let bV ← SourceSemantics.evalExpr fields runtime b
               let cV ← SourceSemantics.evalExpr fields runtime c
               pure (((Verity.Core.Uint256.ofNat aV * Verity.Core.Uint256.ofNat bV) +
                 (Verity.Core.Uint256.ofNat cV - 1)) / Verity.Core.Uint256.ofNat cV).val) < _
      rcases SourceSemantics.evalExpr fields runtime a with _ | aVal
      · trivial
      · rcases SourceSemantics.evalExpr fields runtime b with _ | bVal
        · trivial
        · rcases SourceSemantics.evalExpr fields runtime c with _ | cVal
          · trivial
          · simp only [Bind.bind, Option.bind, Pure.pure]
            have hModEq : Verity.Core.Uint256.modulus = Compiler.Constants.evmModulus := rfl
            exact hModEq ▸ (((Verity.Core.Uint256.ofNat aVal * Verity.Core.Uint256.ofNat bVal) +
              (Verity.Core.Uint256.ofNat cVal - 1)) / Verity.Core.Uint256.ofNat cVal).isLt
  | @tload offset _ ihO =>
      show (do let r ← SourceSemantics.evalExpr fields runtime offset
               some (runtime.world.transientStorage r).val) < _
      rcases SourceSemantics.evalExpr fields runtime offset with _ | offsetVal
      · trivial
      · simp only [Bind.bind, Option.bind, Pure.pure]
        have hModEq : Verity.Core.Uint256.modulus = Compiler.Constants.evmModulus := rfl
        exact hModEq ▸ (runtime.world.transientStorage offsetVal).isLt
  | @calldataload offset _ ihO =>
      show (do let r ← SourceSemantics.evalExpr fields runtime offset
               some (Compiler.Proofs.YulGeneration.calldataloadWord
                 runtime.selector runtime.world.calldata r)) < _
      rcases SourceSemantics.evalExpr fields runtime offset with _ | offsetVal
      · trivial
      · simp only [Bind.bind, Option.bind, Pure.pure]
        exact calldataloadWord_lt_evmModulus _ _ _
  | @mload offset _ ihO =>
      show (do let r ← SourceSemantics.evalExpr fields runtime offset
               some (runtime.world.memory r).val) < _
      rcases SourceSemantics.evalExpr fields runtime offset with _ | offsetVal
      · trivial
      · simp only [Bind.bind, Option.bind, Pure.pure]
        have hModEq : Verity.Core.Uint256.modulus = Compiler.Constants.evmModulus := rfl
        exact hModEq ▸ (runtime.world.memory offsetVal).isLt
  | @extcodesize addr _ ihA =>
      show (do let r ← SourceSemantics.evalExpr fields runtime addr
               some (runtime.world.codeSize (r % SourceSemantics.addressModulus)).val) < _
      rcases SourceSemantics.evalExpr fields runtime addr with _ | addrVal
      · trivial
      · simp only [Bind.bind, Option.bind, Pure.pure]
        have hModEq : Verity.Core.Uint256.modulus = Compiler.Constants.evmModulus := rfl
        exact hModEq ▸ (runtime.world.codeSize (addrVal % SourceSemantics.addressModulus)).isLt
  | @returndataOptionalBoolAt offset _ ihO =>
      show (do let _ ← SourceSemantics.evalExpr fields runtime offset
               some 1) < _
      rcases SourceSemantics.evalExpr fields runtime offset with _ | _
      · trivial
      · simp only [Bind.bind, Option.bind, Pure.pure]
        norm_num [Compiler.Constants.evmModulus]
  | @keccak256 offset size _ _ ihO ihS =>
      show (do
        let off ← SourceSemantics.evalExpr fields runtime offset
        let len ← SourceSemantics.evalExpr fields runtime size
        some (SourceSemantics.keccakMemorySlice runtime.world.memory off len)) < _
      rcases SourceSemantics.evalExpr fields runtime offset with _ | off
      · trivial
      · rcases SourceSemantics.evalExpr fields runtime size with _ | len
        · trivial
        · simp only [Bind.bind, Option.bind, Pure.pure]
          exact Nat.mod_lt _ (by norm_num [Compiler.Constants.evmModulus])
  | @builtinExp base exponent _ _ ihB ihE =>
      show (do
        let b ← SourceSemantics.evalExpr fields runtime base
        let e ← SourceSemantics.evalExpr fields runtime exponent
        some (Verity.Core.Uint256.powEff (Verity.Core.Uint256.ofNat b)
          (Verity.Core.Uint256.ofNat e)).val) < _
      rcases SourceSemantics.evalExpr fields runtime base with _ | bv
      · trivial
      · rcases SourceSemantics.evalExpr fields runtime exponent with _ | ev
        · trivial
        · simp only [Bind.bind, Option.bind, Pure.pure]
          have hModEq : Verity.Core.Uint256.modulus = Compiler.Constants.evmModulus := rfl
          exact hModEq ▸ (Verity.Core.Uint256.powEff (Verity.Core.Uint256.ofNat bv)
            (Verity.Core.Uint256.ofNat ev)).isLt
end

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


theorem compileRequireFailCond_core_ok
    {fields : List Field}
    {cond : Expr}
    (hcore : ExprCompileCore cond) :
    ∃ failCond,
      CompilationModel.compileRequireFailCond fields .calldata cond = Except.ok failCond := by
  cases hcore with
  | literal value =>
      exact ⟨YulExpr.call "iszero" [YulExpr.lit (value % CompilationModel.uint256Modulus)], by
        unfold CompilationModel.compileRequireFailCond CompilationModel.compileRequireFailCondWithInternals
        unfold CompilationModel.compileExprWithInternals
        rfl⟩
  | param name =>
      exact ⟨YulExpr.call "iszero" [YulExpr.ident name], by
        unfold CompilationModel.compileRequireFailCond CompilationModel.compileRequireFailCondWithInternals
        unfold CompilationModel.compileExprWithInternals
        rfl⟩
  | constructorArg idx =>
      exact ⟨YulExpr.call "iszero" [YulExpr.ident s!"arg{idx}"], by
        unfold CompilationModel.compileRequireFailCond CompilationModel.compileRequireFailCondWithInternals
        unfold CompilationModel.compileExprWithInternals
        rfl⟩
  | localVar name =>
      exact ⟨YulExpr.call "iszero" [YulExpr.ident name], by
        unfold CompilationModel.compileRequireFailCond CompilationModel.compileRequireFailCondWithInternals
        unfold CompilationModel.compileExprWithInternals
        rfl⟩
  | caller =>
      exact ⟨YulExpr.call "iszero" [YulExpr.call "caller" []], by
        unfold CompilationModel.compileRequireFailCond CompilationModel.compileRequireFailCondWithInternals
        unfold CompilationModel.compileExprWithInternals
        rfl⟩
  | contractAddress =>
      exact ⟨YulExpr.call "iszero" [YulExpr.call "address" []], by
        unfold CompilationModel.compileRequireFailCond CompilationModel.compileRequireFailCondWithInternals
        unfold CompilationModel.compileExprWithInternals
        rfl⟩
  | txOrigin =>
      exact ⟨YulExpr.call "iszero" [YulExpr.call "origin" []], by
        unfold CompilationModel.compileRequireFailCond CompilationModel.compileRequireFailCondWithInternals
        unfold CompilationModel.compileExprWithInternals
        rfl⟩
  | msgValue =>
      exact ⟨YulExpr.call "iszero" [YulExpr.call "callvalue" []], by
        unfold CompilationModel.compileRequireFailCond CompilationModel.compileRequireFailCondWithInternals
        unfold CompilationModel.compileExprWithInternals
        rfl⟩
  | blockTimestamp =>
      exact ⟨YulExpr.call "iszero" [YulExpr.call "timestamp" []], by
        unfold CompilationModel.compileRequireFailCond CompilationModel.compileRequireFailCondWithInternals
        unfold CompilationModel.compileExprWithInternals
        rfl⟩
  | blockNumber =>
      exact ⟨YulExpr.call "iszero" [YulExpr.call "number" []], by
        unfold CompilationModel.compileRequireFailCond CompilationModel.compileRequireFailCondWithInternals
        unfold CompilationModel.compileExprWithInternals
        rfl⟩
  | chainid =>
      exact ⟨YulExpr.call "iszero" [YulExpr.call "chainid" []], by
        unfold CompilationModel.compileRequireFailCond CompilationModel.compileRequireFailCondWithInternals
        unfold CompilationModel.compileExprWithInternals
        rfl⟩
  | blobbasefee =>
      exact ⟨YulExpr.call "iszero" [YulExpr.call "blobbasefee" []], by
        unfold CompilationModel.compileRequireFailCond CompilationModel.compileRequireFailCondWithInternals
        unfold CompilationModel.compileExprWithInternals
        rfl⟩
  | calldatasize =>
      exact ⟨YulExpr.call "iszero" [YulExpr.call "calldatasize" []], by
        unfold CompilationModel.compileRequireFailCond CompilationModel.compileRequireFailCondWithInternals
        unfold CompilationModel.compileExprWithInternals
        rfl⟩
  | returndataSize =>
      exact ⟨YulExpr.call "iszero" [YulExpr.call "returndatasize" []], by
        unfold CompilationModel.compileRequireFailCond CompilationModel.compileRequireFailCondWithInternals
        unfold CompilationModel.compileExprWithInternals
        rfl⟩
  | add hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields) hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok (fields := fields) hR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "iszero" [YulExpr.call "add" [lhsIR, rhsIR]], by
        have hcompile := compileExpr_add_ok hlhs hrhs
        rw [CompilationModel.compileRequireFailCond]
        rw [← CompilationModel.compileExprWithInternals_nil_eq] at hcompile
        simp [CompilationModel.compileRequireFailCondWithInternals, hcompile]⟩
  | sub hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields) hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok (fields := fields) hR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "iszero" [YulExpr.call "sub" [lhsIR, rhsIR]], by
        have hcompile := compileExpr_sub_ok hlhs hrhs
        rw [CompilationModel.compileRequireFailCond]
        rw [← CompilationModel.compileExprWithInternals_nil_eq] at hcompile
        simp [CompilationModel.compileRequireFailCondWithInternals, hcompile]⟩
  | mul hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields) hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok (fields := fields) hR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "iszero" [YulExpr.call "mul" [lhsIR, rhsIR]], by
        have hcompile := compileExpr_mul_ok hlhs hrhs
        rw [CompilationModel.compileRequireFailCond]
        rw [← CompilationModel.compileExprWithInternals_nil_eq] at hcompile
        simp [CompilationModel.compileRequireFailCondWithInternals, hcompile]⟩
  | div hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields) hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok (fields := fields) hR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "iszero" [YulExpr.call "div" [lhsIR, rhsIR]], by
        have hcompile := compileExpr_div_ok hlhs hrhs
        rw [CompilationModel.compileRequireFailCond]
        rw [← CompilationModel.compileExprWithInternals_nil_eq] at hcompile
        simp [CompilationModel.compileRequireFailCondWithInternals, hcompile]⟩
  | mod hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields) hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok (fields := fields) hR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "iszero" [YulExpr.call "mod" [lhsIR, rhsIR]], by
        have hcompile := compileExpr_mod_ok hlhs hrhs
        rw [CompilationModel.compileRequireFailCond]
        rw [← CompilationModel.compileExprWithInternals_nil_eq] at hcompile
        simp [CompilationModel.compileRequireFailCondWithInternals, hcompile]⟩
  | eq hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields) hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok (fields := fields) hR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "iszero" [YulExpr.call "eq" [lhsIR, rhsIR]], by
        have hcompile := compileExpr_eq_ok hlhs hrhs
        rw [CompilationModel.compileRequireFailCond]
        rw [← CompilationModel.compileExprWithInternals_nil_eq] at hcompile
        simp [CompilationModel.compileRequireFailCondWithInternals, hcompile]⟩
  | lt hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields) hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok (fields := fields) hR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "iszero" [YulExpr.call "lt" [lhsIR, rhsIR]], by
        have hcompile := compileExpr_lt_ok hlhs hrhs
        rw [CompilationModel.compileRequireFailCond]
        rw [← CompilationModel.compileExprWithInternals_nil_eq] at hcompile
        simp [CompilationModel.compileRequireFailCondWithInternals, hcompile]⟩
  | slt hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields) hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok (fields := fields) hR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "iszero" [YulExpr.call "slt" [lhsIR, rhsIR]], by
        have hcompile := compileExpr_slt_ok hlhs hrhs
        rw [CompilationModel.compileRequireFailCond]
        rw [← CompilationModel.compileExprWithInternals_nil_eq] at hcompile
        simp [CompilationModel.compileRequireFailCondWithInternals, hcompile]⟩
  | sgt hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields) hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok (fields := fields) hR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "iszero" [YulExpr.call "sgt" [lhsIR, rhsIR]], by
        have hcompile := compileExpr_sgt_ok hlhs hrhs
        rw [CompilationModel.compileRequireFailCond]
        rw [← CompilationModel.compileExprWithInternals_nil_eq] at hcompile
        simp [CompilationModel.compileRequireFailCondWithInternals, hcompile]⟩
  | sdiv hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields) hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok (fields := fields) hR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "iszero" [YulExpr.call "sdiv" [lhsIR, rhsIR]], by
        have hcompile := compileExpr_sdiv_ok hlhs hrhs
        rw [CompilationModel.compileRequireFailCond]
        rw [← CompilationModel.compileExprWithInternals_nil_eq] at hcompile
        simp [CompilationModel.compileRequireFailCondWithInternals, hcompile]⟩
  | smod hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields) hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok (fields := fields) hR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "iszero" [YulExpr.call "smod" [lhsIR, rhsIR]], by
        have hcompile := compileExpr_smod_ok hlhs hrhs
        rw [CompilationModel.compileRequireFailCond]
        rw [← CompilationModel.compileExprWithInternals_nil_eq] at hcompile
        simp [CompilationModel.compileRequireFailCondWithInternals, hcompile]⟩
  | sar hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields) hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok (fields := fields) hR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "iszero" [YulExpr.call "sar" [lhsIR, rhsIR]], by
        have hcompile := compileExpr_sar_ok hlhs hrhs
        rw [CompilationModel.compileRequireFailCond]
        rw [← CompilationModel.compileExprWithInternals_nil_eq] at hcompile
        simp [CompilationModel.compileRequireFailCondWithInternals, hcompile]⟩
  | byte hL hR =>
      rename_i index value
      rcases compileExpr_core_ok (fields := fields) hL with ⟨indexIR, hindex⟩
      rcases compileExpr_core_ok (fields := fields) hR with ⟨valueIR, hvalue⟩
      exact ⟨YulExpr.call "iszero" [YulExpr.call "byte" [indexIR, valueIR]], by
        have hcompile := compileExpr_byte_ok hindex hvalue
        rw [CompilationModel.compileRequireFailCond]
        rw [← CompilationModel.compileExprWithInternals_nil_eq] at hcompile
        simp [CompilationModel.compileRequireFailCondWithInternals, hcompile]⟩
  | signextend hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields) hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok (fields := fields) hR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "iszero" [YulExpr.call "signextend" [lhsIR, rhsIR]], by
        have hcompile := compileExpr_signextend_ok hlhs hrhs
        rw [CompilationModel.compileRequireFailCond]
        rw [← CompilationModel.compileExprWithInternals_nil_eq] at hcompile
        simp [CompilationModel.compileRequireFailCondWithInternals, hcompile]⟩
  | gt hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields) hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok (fields := fields) hR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "iszero" [YulExpr.call "gt" [lhsIR, rhsIR]], by
        have hcompile := compileExpr_gt_ok hlhs hrhs
        rw [CompilationModel.compileRequireFailCond]
        rw [← CompilationModel.compileExprWithInternals_nil_eq] at hcompile
        simp [CompilationModel.compileRequireFailCondWithInternals, hcompile]⟩
  | ge hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields) hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok (fields := fields) hR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "lt" [lhsIR, rhsIR], by
        rw [CompilationModel.compileRequireFailCond]
        rw [← CompilationModel.compileExprWithInternals_nil_eq] at hlhs hrhs
        simp [CompilationModel.compileRequireFailCondWithInternals, CompilationModel.yulBinOp, hlhs, hrhs]
        rfl⟩
  | le hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields) hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok (fields := fields) hR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "gt" [lhsIR, rhsIR], by
        rw [CompilationModel.compileRequireFailCond]
        rw [← CompilationModel.compileExprWithInternals_nil_eq] at hlhs hrhs
        simp [CompilationModel.compileRequireFailCondWithInternals, CompilationModel.yulBinOp, hlhs, hrhs]
        rfl⟩
  | logicalNot h =>
      rename_i expr
      rcases compileExpr_core_ok (fields := fields) h with ⟨exprIR, hexpr⟩
      exact ⟨YulExpr.call "iszero" [YulExpr.call "iszero" [exprIR]], by
        have hcompile := compileExpr_logicalNot_ok hexpr
        rw [CompilationModel.compileRequireFailCond]
        rw [← CompilationModel.compileExprWithInternals_nil_eq] at hcompile
        simp [CompilationModel.compileRequireFailCondWithInternals, hcompile]⟩
  | logicalAnd hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields) hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok (fields := fields) hR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "iszero"
          [YulExpr.call "and" [CompilationModel.yulToBool lhsIR, CompilationModel.yulToBool rhsIR]], by
        have hcompile := compileExpr_logicalAnd_ok hlhs hrhs
        rw [CompilationModel.compileRequireFailCond]
        rw [← CompilationModel.compileExprWithInternals_nil_eq] at hcompile
        simp [CompilationModel.compileRequireFailCondWithInternals, hcompile]⟩
  | logicalOr hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields) hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok (fields := fields) hR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "iszero"
          [YulExpr.call "or" [CompilationModel.yulToBool lhsIR, CompilationModel.yulToBool rhsIR]], by
        have hcompile := compileExpr_logicalOr_ok hlhs hrhs
        rw [CompilationModel.compileRequireFailCond]
        rw [← CompilationModel.compileExprWithInternals_nil_eq] at hcompile
        simp [CompilationModel.compileRequireFailCondWithInternals, hcompile]⟩
  | bitAnd hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields) hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok (fields := fields) hR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "iszero" [YulExpr.call "and" [lhsIR, rhsIR]], by
        have hcompile := compileExpr_bitAnd_ok hlhs hrhs
        rw [CompilationModel.compileRequireFailCond]
        rw [← CompilationModel.compileExprWithInternals_nil_eq] at hcompile
        simp [CompilationModel.compileRequireFailCondWithInternals, hcompile]⟩
  | bitOr hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields) hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok (fields := fields) hR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "iszero" [YulExpr.call "or" [lhsIR, rhsIR]], by
        have hcompile := compileExpr_bitOr_ok hlhs hrhs
        rw [CompilationModel.compileRequireFailCond]
        rw [← CompilationModel.compileExprWithInternals_nil_eq] at hcompile
        simp [CompilationModel.compileRequireFailCondWithInternals, hcompile]⟩
  | bitXor hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields) hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok (fields := fields) hR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "iszero" [YulExpr.call "xor" [lhsIR, rhsIR]], by
        have hcompile := compileExpr_bitXor_ok hlhs hrhs
        rw [CompilationModel.compileRequireFailCond]
        rw [← CompilationModel.compileExprWithInternals_nil_eq] at hcompile
        simp [CompilationModel.compileRequireFailCondWithInternals, hcompile]⟩
  | bitNot h =>
      rename_i expr
      rcases compileExpr_core_ok (fields := fields) h with ⟨exprIR, hexpr⟩
      exact ⟨YulExpr.call "iszero" [YulExpr.call "not" [exprIR]], by
        have hcompile := compileExpr_bitNot_ok hexpr
        rw [CompilationModel.compileRequireFailCond]
        rw [← CompilationModel.compileExprWithInternals_nil_eq] at hcompile
        simp [CompilationModel.compileRequireFailCondWithInternals, hcompile]⟩
  | shl hS hV =>
      rename_i shift value
      rcases compileExpr_core_ok (fields := fields) hS with ⟨shiftIR, hshift⟩
      rcases compileExpr_core_ok (fields := fields) hV with ⟨valueIR, hvalue⟩
      exact ⟨YulExpr.call "iszero" [YulExpr.call "shl" [shiftIR, valueIR]], by
        have hcompile := compileExpr_shl_ok hshift hvalue
        rw [CompilationModel.compileRequireFailCond]
        rw [← CompilationModel.compileExprWithInternals_nil_eq] at hcompile
        simp [CompilationModel.compileRequireFailCondWithInternals, hcompile]⟩
  | shr hS hV =>
      rename_i shift value
      rcases compileExpr_core_ok (fields := fields) hS with ⟨shiftIR, hshift⟩
      rcases compileExpr_core_ok (fields := fields) hV with ⟨valueIR, hvalue⟩
      exact ⟨YulExpr.call "iszero" [YulExpr.call "shr" [shiftIR, valueIR]], by
        have hcompile := compileExpr_shr_ok hshift hvalue
        rw [CompilationModel.compileRequireFailCond]
        rw [← CompilationModel.compileExprWithInternals_nil_eq] at hcompile
        simp [CompilationModel.compileRequireFailCondWithInternals, hcompile]⟩
  | min hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields) hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok (fields := fields) hR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "iszero" [YulExpr.call "sub" [lhsIR,
        YulExpr.call "mul" [YulExpr.call "sub" [lhsIR, rhsIR],
          YulExpr.call "gt" [lhsIR, rhsIR]]]], by
        have hcompile := compileExpr_min_ok hlhs hrhs
        rw [CompilationModel.compileRequireFailCond]
        rw [← CompilationModel.compileExprWithInternals_nil_eq] at hcompile
        simp [CompilationModel.compileRequireFailCondWithInternals, hcompile]⟩
  | max hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields) hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok (fields := fields) hR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "iszero" [YulExpr.call "add" [lhsIR,
        YulExpr.call "mul" [YulExpr.call "sub" [rhsIR, lhsIR],
          YulExpr.call "gt" [rhsIR, lhsIR]]]], by
        have hcompile := compileExpr_max_ok hlhs hrhs
        rw [CompilationModel.compileRequireFailCond]
        rw [← CompilationModel.compileExprWithInternals_nil_eq] at hcompile
        simp [CompilationModel.compileRequireFailCondWithInternals, hcompile]⟩
  | ite hC hT hE =>
      rename_i cond thenVal elseVal
      rcases compileExpr_core_ok (fields := fields) hC with ⟨condIR, hcond⟩
      rcases compileExpr_core_ok (fields := fields) hT with ⟨thenIR, hthen⟩
      rcases compileExpr_core_ok (fields := fields) hE with ⟨elseIR, helse⟩
      exact ⟨YulExpr.call "iszero" [YulExpr.call "add" [
        YulExpr.call "mul" [
          YulExpr.call "iszero" [YulExpr.call "iszero" [condIR]], thenIR],
        YulExpr.call "mul" [
          YulExpr.call "iszero" [condIR], elseIR]]], by
        have hcompile := compileExpr_ite_ok hcond hthen helse
        rw [CompilationModel.compileRequireFailCond]
        rw [← CompilationModel.compileExprWithInternals_nil_eq] at hcompile
        simp [CompilationModel.compileRequireFailCondWithInternals, hcompile]⟩
  | ceilDiv hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields) hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok (fields := fields) hR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "iszero" [YulExpr.call "mul" [
        YulExpr.call "iszero" [YulExpr.call "iszero" [lhsIR]],
        YulExpr.call "add" [
          YulExpr.call "div" [YulExpr.call "sub" [lhsIR, YulExpr.lit 1], rhsIR],
          YulExpr.lit 1]]], by
        have hcompile := compileExpr_ceilDiv_ok hlhs hrhs
        rw [CompilationModel.compileRequireFailCond]
        rw [← CompilationModel.compileExprWithInternals_nil_eq] at hcompile
        simp [CompilationModel.compileRequireFailCondWithInternals, hcompile]⟩
  | wMulDown hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields) hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok (fields := fields) hR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "iszero" [YulExpr.call "div" [
        YulExpr.call "mul" [lhsIR, rhsIR], YulExpr.lit 1000000000000000000]], by
        have hcompile := compileExpr_wMulDown_ok hlhs hrhs
        rw [CompilationModel.compileRequireFailCond]
        rw [← CompilationModel.compileExprWithInternals_nil_eq] at hcompile
        simp [CompilationModel.compileRequireFailCondWithInternals, hcompile]⟩
  | wDivUp hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields) hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok (fields := fields) hR with ⟨rhsIR, hrhs⟩
      exact ⟨YulExpr.call "iszero" [YulExpr.call "div" [
        YulExpr.call "add" [
          YulExpr.call "mul" [lhsIR, YulExpr.lit 1000000000000000000],
          YulExpr.call "sub" [rhsIR, YulExpr.lit 1]],
        rhsIR]], by
        have hcompile := compileExpr_wDivUp_ok hlhs hrhs
        rw [CompilationModel.compileRequireFailCond]
        rw [← CompilationModel.compileExprWithInternals_nil_eq] at hcompile
        simp [CompilationModel.compileRequireFailCondWithInternals, hcompile]⟩
  | mulDivDown hA hB hC =>
      rename_i a b c
      rcases compileExpr_core_ok (fields := fields) hA with ⟨aIR, ha⟩
      rcases compileExpr_core_ok (fields := fields) hB with ⟨bIR, hb⟩
      rcases compileExpr_core_ok (fields := fields) hC with ⟨cIR, hc⟩
      exact ⟨YulExpr.call "iszero" [YulExpr.call "div" [
        YulExpr.call "mul" [aIR, bIR], cIR]], by
        have hcompile := compileExpr_mulDivDown_ok ha hb hc
        rw [CompilationModel.compileRequireFailCond]
        rw [← CompilationModel.compileExprWithInternals_nil_eq] at hcompile
        simp [CompilationModel.compileRequireFailCondWithInternals, hcompile]⟩
  | mulDivUp hA hB hC =>
      rename_i a b c
      rcases compileExpr_core_ok (fields := fields) hA with ⟨aIR, ha⟩
      rcases compileExpr_core_ok (fields := fields) hB with ⟨bIR, hb⟩
      rcases compileExpr_core_ok (fields := fields) hC with ⟨cIR, hc⟩
      exact ⟨YulExpr.call "iszero" [YulExpr.call "div" [
        YulExpr.call "add" [YulExpr.call "mul" [aIR, bIR],
          YulExpr.call "sub" [cIR, YulExpr.lit 1]],
        cIR]], by
        have hcompile := compileExpr_mulDivUp_ok ha hb hc
        rw [CompilationModel.compileRequireFailCond]
        rw [← CompilationModel.compileExprWithInternals_nil_eq] at hcompile
        simp [CompilationModel.compileRequireFailCondWithInternals, hcompile]⟩
  | tload h =>
      rename_i expr
      rcases compileExpr_core_ok (fields := fields) h with ⟨exprIR, hexpr⟩
      exact ⟨YulExpr.call "iszero" [YulExpr.call "tload" [exprIR]], by
        have hcompile := compileExpr_tload_ok hexpr
        rw [CompilationModel.compileRequireFailCond]
        rw [← CompilationModel.compileExprWithInternals_nil_eq] at hcompile
        simp [CompilationModel.compileRequireFailCondWithInternals, hcompile]⟩
  | calldataload h =>
      rename_i expr
      rcases compileExpr_core_ok (fields := fields) h with ⟨exprIR, hexpr⟩
      exact ⟨YulExpr.call "iszero" [YulExpr.call "calldataload" [exprIR]], by
        have hcompile := compileExpr_calldataload_ok hexpr
        rw [CompilationModel.compileRequireFailCond]
        rw [← CompilationModel.compileExprWithInternals_nil_eq] at hcompile
        simp [CompilationModel.compileRequireFailCondWithInternals, hcompile]⟩
  | mload h =>
      rename_i expr
      rcases compileExpr_core_ok (fields := fields) h with ⟨exprIR, hexpr⟩
      exact ⟨YulExpr.call "iszero" [YulExpr.call "mload" [exprIR]], by
        have hcompile := compileExpr_mload_ok hexpr
        rw [CompilationModel.compileRequireFailCond]
        rw [← CompilationModel.compileExprWithInternals_nil_eq] at hcompile
        simp [CompilationModel.compileRequireFailCondWithInternals, hcompile]⟩
  | extcodesize h =>
      rename_i expr
      rcases compileExpr_core_ok (fields := fields) h with ⟨exprIR, hexpr⟩
      exact ⟨YulExpr.call "iszero" [YulExpr.call "extcodesize" [exprIR]], by
        have hcompile := compileExpr_extcodesize_ok hexpr
        rw [CompilationModel.compileRequireFailCond]
        rw [← CompilationModel.compileExprWithInternals_nil_eq] at hcompile
        simp [CompilationModel.compileRequireFailCondWithInternals, hcompile]⟩
  | returndataOptionalBoolAt h =>
      rename_i expr
      rcases compileExpr_core_ok (fields := fields) h with ⟨exprIR, hexpr⟩
      exact ⟨YulExpr.call "iszero" [YulExpr.call "or" [
        YulExpr.call "eq" [YulExpr.call "returndatasize" [], YulExpr.lit 0],
        YulExpr.call "and" [
          YulExpr.call "eq" [YulExpr.call "returndatasize" [], YulExpr.lit 32],
          YulExpr.call "eq" [YulExpr.call "mload" [exprIR], YulExpr.lit 1]
        ]
      ]], by
        have hcompile := compileExpr_returndataOptionalBoolAt_ok hexpr
        rw [CompilationModel.compileRequireFailCond]
        rw [← CompilationModel.compileExprWithInternals_nil_eq] at hcompile
        simp [CompilationModel.compileRequireFailCondWithInternals, hcompile]⟩
  | keccak256 hO hS =>
      rename_i offset size
      rcases compileExpr_core_ok (fields := fields) hO with ⟨offsetIR, hoffset⟩
      rcases compileExpr_core_ok (fields := fields) hS with ⟨sizeIR, hsize⟩
      exact ⟨YulExpr.call "iszero" [YulExpr.call "keccak256" [offsetIR, sizeIR]], by
        have hcompile := compileExpr_keccak256_ok hoffset hsize
        rw [CompilationModel.compileRequireFailCond]
        rw [← CompilationModel.compileExprWithInternals_nil_eq] at hcompile
        simp [CompilationModel.compileRequireFailCondWithInternals, hcompile]⟩
  | builtinExp hB hE =>
      rename_i base exponent
      rcases compileExpr_core_ok (fields := fields) hB with ⟨baseIR, hbase⟩
      rcases compileExpr_core_ok (fields := fields) hE with ⟨exponentIR, hexp⟩
      exact ⟨YulExpr.call "iszero" [YulExpr.call "exp" [baseIR, exponentIR]], by
        have hcompile := compileExpr_builtinExp_ok hbase hexp
        rw [CompilationModel.compileRequireFailCond]
        rw [← CompilationModel.compileExprWithInternals_nil_eq] at hcompile
        simp [CompilationModel.compileRequireFailCondWithInternals, hcompile]⟩

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
  -- Helper for the iszero cases: extract Nat from the monadic Option wrapper
  let finishIszeroEval {expr : Expr} (h : ExprCompileCore expr)
      (hexactExpr : bindingsExactlyMatchIRVarsOnExpr expr runtime.bindings state)
      (hpresentExpr : exprBoundNamesPresent expr runtime.bindings)
      {exprIR : YulExpr}
      (hexpr : CompilationModel.compileExpr fields .calldata expr = Except.ok exprIR) :
      evalIRExpr state (YulExpr.call "iszero" [exprIR]) =
        some (SourceSemantics.boolWord (SourceSemantics.evalExpr fields runtime expr = some 0)) := by
    -- eval_compileExpr_core_onExpr gives (elaborated):
    --   (do let a ← evalIRExpr state exprIR; pure (some a)) = some (evalExpr ...)
    have heval := eval_compileExpr_core_onExpr h hexactExpr hbounded hpresentExpr hruntime
    rw [hexpr] at heval
    simp [Except.toOption] at heval
    -- heval : (evalIRExpr state exprIR).bind (fun a => some (some a)) = some (evalExpr ...)
    -- Case split on evalIRExpr to extract the Nat value
    rcases hIR : evalIRExpr state exprIR with _ | val
    · simp [hIR, Option.bind] at heval
    · simp [hIR, Option.bind] at heval
      -- heval : some val = evalExpr fields runtime expr, i.e., evalExpr = some val
      have hEvalSrc : SourceSemantics.evalExpr fields runtime expr = some val := heval.symm
      -- Boundedness: evalExpr < some evmModulus
      have hlt := evalExpr_lt_evmModulus_core_onExpr h hexactExpr hbounded hpresentExpr hruntime
      rw [hEvalSrc] at hlt
      simp at hlt
      -- Apply evalIRExpr_iszero_of_lt
      have hiszero := evalIRExpr_iszero_of_lt hIR hlt
      -- hiszero : ... = some (boolWord (val = 0))
      -- goal : ... = some (boolWord (evalExpr ... = some 0))
      -- Since evalExpr = some val, (evalExpr = some 0) ↔ (val = 0)
      -- Use simp to handle the Decidable-dependent rewrite
      simp only [hEvalSrc, Option.some.injEq] at hiszero ⊢
      exact hiszero
  cases hcore with
  | literal value =>
      rcases compileExpr_core_ok (fields := fields)
          (show ExprCompileCore (.literal value) from ExprCompileCore.literal value) with ⟨exprIR, hexpr⟩
      refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
      · rw [← CompilationModel.compileExprWithInternals_nil_eq] at hexpr
        simp [CompilationModel.compileRequireFailCond, CompilationModel.compileRequireFailCondWithInternals, hexpr]
      · simpa using finishIszeroEval (expr := .literal value)
          (show ExprCompileCore (.literal value) from ExprCompileCore.literal value) hexact hpresent hexpr
  | param name =>
      rcases compileExpr_core_ok (fields := fields)
          (show ExprCompileCore (.param name) from ExprCompileCore.param name) with ⟨exprIR, hexpr⟩
      refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
      · rw [← CompilationModel.compileExprWithInternals_nil_eq] at hexpr
        simp [CompilationModel.compileRequireFailCond, CompilationModel.compileRequireFailCondWithInternals, hexpr]
      · simpa using finishIszeroEval (expr := .param name)
          (show ExprCompileCore (.param name) from ExprCompileCore.param name) hexact hpresent hexpr
  | constructorArg idx =>
      rcases compileExpr_core_ok (fields := fields)
          (show ExprCompileCore (.constructorArg idx) from ExprCompileCore.constructorArg idx) with ⟨exprIR, hexpr⟩
      refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
      · rw [← CompilationModel.compileExprWithInternals_nil_eq] at hexpr
        simp [CompilationModel.compileRequireFailCond, CompilationModel.compileRequireFailCondWithInternals, hexpr]
      · simpa using finishIszeroEval (expr := .constructorArg idx)
          (show ExprCompileCore (.constructorArg idx) from ExprCompileCore.constructorArg idx) hexact hpresent hexpr
  | localVar name =>
      rcases compileExpr_core_ok (fields := fields)
          (show ExprCompileCore (.localVar name) from ExprCompileCore.localVar name) with ⟨exprIR, hexpr⟩
      refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
      · rw [← CompilationModel.compileExprWithInternals_nil_eq] at hexpr
        simp [CompilationModel.compileRequireFailCond, CompilationModel.compileRequireFailCondWithInternals, hexpr]
      · simpa using finishIszeroEval (expr := .localVar name)
          (show ExprCompileCore (.localVar name) from ExprCompileCore.localVar name) hexact hpresent hexpr
  | caller =>
      rcases compileExpr_core_ok (fields := fields)
          (show ExprCompileCore (.caller) from ExprCompileCore.caller) with ⟨exprIR, hexpr⟩
      refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
      · rw [← CompilationModel.compileExprWithInternals_nil_eq] at hexpr
        simp [CompilationModel.compileRequireFailCond, CompilationModel.compileRequireFailCondWithInternals, hexpr]
      · simpa using finishIszeroEval (expr := .caller)
          (show ExprCompileCore (.caller) from ExprCompileCore.caller) hexact hpresent hexpr
  | contractAddress =>
      rcases compileExpr_core_ok (fields := fields)
          (show ExprCompileCore (.contractAddress) from ExprCompileCore.contractAddress) with ⟨exprIR, hexpr⟩
      refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
      · rw [← CompilationModel.compileExprWithInternals_nil_eq] at hexpr
        simp [CompilationModel.compileRequireFailCond, CompilationModel.compileRequireFailCondWithInternals, hexpr]
      · simpa using finishIszeroEval (expr := .contractAddress)
          (show ExprCompileCore (.contractAddress) from ExprCompileCore.contractAddress) hexact hpresent hexpr
  | txOrigin =>
      rcases compileExpr_core_ok (fields := fields)
          (show ExprCompileCore (.txOrigin) from ExprCompileCore.txOrigin) with ⟨exprIR, hexpr⟩
      refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
      · rw [← CompilationModel.compileExprWithInternals_nil_eq] at hexpr
        simp [CompilationModel.compileRequireFailCond, CompilationModel.compileRequireFailCondWithInternals, hexpr]
      · simpa using finishIszeroEval (expr := .txOrigin)
          (show ExprCompileCore (.txOrigin) from ExprCompileCore.txOrigin) hexact hpresent hexpr
  | msgValue =>
      rcases compileExpr_core_ok (fields := fields)
          (show ExprCompileCore (.msgValue) from ExprCompileCore.msgValue) with ⟨exprIR, hexpr⟩
      refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
      · rw [← CompilationModel.compileExprWithInternals_nil_eq] at hexpr
        simp [CompilationModel.compileRequireFailCond, CompilationModel.compileRequireFailCondWithInternals, hexpr]
      · simpa using finishIszeroEval (expr := .msgValue)
          (show ExprCompileCore (.msgValue) from ExprCompileCore.msgValue) hexact hpresent hexpr
  | blockTimestamp =>
      rcases compileExpr_core_ok (fields := fields)
          (show ExprCompileCore (.blockTimestamp) from ExprCompileCore.blockTimestamp) with ⟨exprIR, hexpr⟩
      refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
      · rw [← CompilationModel.compileExprWithInternals_nil_eq] at hexpr
        simp [CompilationModel.compileRequireFailCond, CompilationModel.compileRequireFailCondWithInternals, hexpr]
      · simpa using finishIszeroEval (expr := .blockTimestamp)
          (show ExprCompileCore (.blockTimestamp) from ExprCompileCore.blockTimestamp) hexact hpresent hexpr
  | blockNumber =>
      rcases compileExpr_core_ok (fields := fields)
          (show ExprCompileCore (.blockNumber) from ExprCompileCore.blockNumber) with ⟨exprIR, hexpr⟩
      refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
      · rw [← CompilationModel.compileExprWithInternals_nil_eq] at hexpr
        simp [CompilationModel.compileRequireFailCond, CompilationModel.compileRequireFailCondWithInternals, hexpr]
      · simpa using finishIszeroEval (expr := .blockNumber)
          (show ExprCompileCore (.blockNumber) from ExprCompileCore.blockNumber) hexact hpresent hexpr
  | chainid =>
      rcases compileExpr_core_ok (fields := fields)
          (show ExprCompileCore (.chainid) from ExprCompileCore.chainid) with ⟨exprIR, hexpr⟩
      refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
      · rw [← CompilationModel.compileExprWithInternals_nil_eq] at hexpr
        simp [CompilationModel.compileRequireFailCond, CompilationModel.compileRequireFailCondWithInternals, hexpr]
      · simpa using finishIszeroEval (expr := .chainid)
          (show ExprCompileCore (.chainid) from ExprCompileCore.chainid) hexact hpresent hexpr
  | blobbasefee =>
      rcases compileExpr_core_ok (fields := fields)
          (show ExprCompileCore (.blobbasefee) from ExprCompileCore.blobbasefee) with ⟨exprIR, hexpr⟩
      refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
      · rw [← CompilationModel.compileExprWithInternals_nil_eq] at hexpr
        simp [CompilationModel.compileRequireFailCond, CompilationModel.compileRequireFailCondWithInternals, hexpr]
      · simpa using finishIszeroEval (expr := .blobbasefee)
          (show ExprCompileCore (.blobbasefee) from ExprCompileCore.blobbasefee) hexact hpresent hexpr
  | calldatasize =>
      rcases compileExpr_core_ok (fields := fields)
          (show ExprCompileCore (.calldatasize) from ExprCompileCore.calldatasize) with ⟨exprIR, hexpr⟩
      refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
      · rw [← CompilationModel.compileExprWithInternals_nil_eq] at hexpr
        simp [CompilationModel.compileRequireFailCond, CompilationModel.compileRequireFailCondWithInternals, hexpr]
      · simpa using finishIszeroEval (expr := .calldatasize)
          (show ExprCompileCore (.calldatasize) from ExprCompileCore.calldatasize) hexact hpresent hexpr
  | returndataSize =>
      rcases compileExpr_core_ok (fields := fields)
          (show ExprCompileCore (.returndataSize) from ExprCompileCore.returndataSize) with ⟨exprIR, hexpr⟩
      refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
      · rw [← CompilationModel.compileExprWithInternals_nil_eq] at hexpr
        simp [CompilationModel.compileRequireFailCond, CompilationModel.compileRequireFailCondWithInternals, hexpr]
      · simpa using finishIszeroEval (expr := .returndataSize)
          (show ExprCompileCore (.returndataSize) from ExprCompileCore.returndataSize) hexact hpresent hexpr
  | add hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields)
          (show ExprCompileCore (.add lhs rhs) from ExprCompileCore.add hL hR) with ⟨exprIR, hexpr⟩
      refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
      · rw [← CompilationModel.compileExprWithInternals_nil_eq] at hexpr
        simp [CompilationModel.compileRequireFailCond, CompilationModel.compileRequireFailCondWithInternals, hexpr]
      · simpa using finishIszeroEval (expr := .add lhs rhs)
          (show ExprCompileCore (.add lhs rhs) from ExprCompileCore.add hL hR) hexact hpresent hexpr
  | sub hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields)
          (show ExprCompileCore (.sub lhs rhs) from ExprCompileCore.sub hL hR) with ⟨exprIR, hexpr⟩
      refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
      · rw [← CompilationModel.compileExprWithInternals_nil_eq] at hexpr
        simp [CompilationModel.compileRequireFailCond, CompilationModel.compileRequireFailCondWithInternals, hexpr]
      · simpa using finishIszeroEval (expr := .sub lhs rhs)
          (show ExprCompileCore (.sub lhs rhs) from ExprCompileCore.sub hL hR) hexact hpresent hexpr
  | mul hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields)
          (show ExprCompileCore (.mul lhs rhs) from ExprCompileCore.mul hL hR) with ⟨exprIR, hexpr⟩
      refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
      · rw [← CompilationModel.compileExprWithInternals_nil_eq] at hexpr
        simp [CompilationModel.compileRequireFailCond, CompilationModel.compileRequireFailCondWithInternals, hexpr]
      · simpa using finishIszeroEval (expr := .mul lhs rhs)
          (show ExprCompileCore (.mul lhs rhs) from ExprCompileCore.mul hL hR) hexact hpresent hexpr
  | div hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields)
          (show ExprCompileCore (.div lhs rhs) from ExprCompileCore.div hL hR) with ⟨exprIR, hexpr⟩
      refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
      · rw [← CompilationModel.compileExprWithInternals_nil_eq] at hexpr
        simp [CompilationModel.compileRequireFailCond, CompilationModel.compileRequireFailCondWithInternals, hexpr]
      · simpa using finishIszeroEval (expr := .div lhs rhs)
          (show ExprCompileCore (.div lhs rhs) from ExprCompileCore.div hL hR) hexact hpresent hexpr
  | mod hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields)
          (show ExprCompileCore (.mod lhs rhs) from ExprCompileCore.mod hL hR) with ⟨exprIR, hexpr⟩
      refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
      · rw [← CompilationModel.compileExprWithInternals_nil_eq] at hexpr
        simp [CompilationModel.compileRequireFailCond, CompilationModel.compileRequireFailCondWithInternals, hexpr]
      · simpa using finishIszeroEval (expr := .mod lhs rhs)
          (show ExprCompileCore (.mod lhs rhs) from ExprCompileCore.mod hL hR) hexact hpresent hexpr
  | eq hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields)
          (show ExprCompileCore (.eq lhs rhs) from ExprCompileCore.eq hL hR) with ⟨exprIR, hexpr⟩
      refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
      · rw [← CompilationModel.compileExprWithInternals_nil_eq] at hexpr
        simp [CompilationModel.compileRequireFailCond, CompilationModel.compileRequireFailCondWithInternals, hexpr]
      · simpa using finishIszeroEval (expr := .eq lhs rhs)
          (show ExprCompileCore (.eq lhs rhs) from ExprCompileCore.eq hL hR) hexact hpresent hexpr
  | lt hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields)
          (show ExprCompileCore (.lt lhs rhs) from ExprCompileCore.lt hL hR) with ⟨exprIR, hexpr⟩
      refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
      · rw [← CompilationModel.compileExprWithInternals_nil_eq] at hexpr
        simp [CompilationModel.compileRequireFailCond, CompilationModel.compileRequireFailCondWithInternals, hexpr]
      · simpa using finishIszeroEval (expr := .lt lhs rhs)
          (show ExprCompileCore (.lt lhs rhs) from ExprCompileCore.lt hL hR) hexact hpresent hexpr
  | slt hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields)
          (show ExprCompileCore (.slt lhs rhs) from ExprCompileCore.slt hL hR) with ⟨exprIR, hexpr⟩
      refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
      · rw [← CompilationModel.compileExprWithInternals_nil_eq] at hexpr
        simp [CompilationModel.compileRequireFailCond, CompilationModel.compileRequireFailCondWithInternals, hexpr]
      · simpa using finishIszeroEval (expr := .slt lhs rhs)
          (show ExprCompileCore (.slt lhs rhs) from ExprCompileCore.slt hL hR) hexact hpresent hexpr
  | sgt hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields)
          (show ExprCompileCore (.sgt lhs rhs) from ExprCompileCore.sgt hL hR) with ⟨exprIR, hexpr⟩
      refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
      · rw [← CompilationModel.compileExprWithInternals_nil_eq] at hexpr
        simp [CompilationModel.compileRequireFailCond, CompilationModel.compileRequireFailCondWithInternals, hexpr]
      · simpa using finishIszeroEval (expr := .sgt lhs rhs)
          (show ExprCompileCore (.sgt lhs rhs) from ExprCompileCore.sgt hL hR) hexact hpresent hexpr
  | sdiv hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields)
          (show ExprCompileCore (.sdiv lhs rhs) from ExprCompileCore.sdiv hL hR) with ⟨exprIR, hexpr⟩
      refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
      · rw [← CompilationModel.compileExprWithInternals_nil_eq] at hexpr
        simp [CompilationModel.compileRequireFailCond, CompilationModel.compileRequireFailCondWithInternals, hexpr]
      · simpa using finishIszeroEval (expr := .sdiv lhs rhs)
          (show ExprCompileCore (.sdiv lhs rhs) from ExprCompileCore.sdiv hL hR) hexact hpresent hexpr
  | smod hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields)
          (show ExprCompileCore (.smod lhs rhs) from ExprCompileCore.smod hL hR) with ⟨exprIR, hexpr⟩
      refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
      · rw [← CompilationModel.compileExprWithInternals_nil_eq] at hexpr
        simp [CompilationModel.compileRequireFailCond, CompilationModel.compileRequireFailCondWithInternals, hexpr]
      · simpa using finishIszeroEval (expr := .smod lhs rhs)
          (show ExprCompileCore (.smod lhs rhs) from ExprCompileCore.smod hL hR) hexact hpresent hexpr
  | sar hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields)
          (show ExprCompileCore (.sar lhs rhs) from ExprCompileCore.sar hL hR) with ⟨exprIR, hexpr⟩
      refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
      · rw [← CompilationModel.compileExprWithInternals_nil_eq] at hexpr
        simp [CompilationModel.compileRequireFailCond, CompilationModel.compileRequireFailCondWithInternals, hexpr]
      · simpa using finishIszeroEval (expr := .sar lhs rhs)
          (show ExprCompileCore (.sar lhs rhs) from ExprCompileCore.sar hL hR) hexact hpresent hexpr
  | byte hL hR =>
      rename_i index value
      rcases compileExpr_core_ok (fields := fields)
          (show ExprCompileCore (.byte index value) from ExprCompileCore.byte hL hR) with ⟨exprIR, hexpr⟩
      refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
      · rw [← CompilationModel.compileExprWithInternals_nil_eq] at hexpr
        simp [CompilationModel.compileRequireFailCond, CompilationModel.compileRequireFailCondWithInternals, hexpr]
      · simpa using finishIszeroEval (expr := .byte index value)
          (show ExprCompileCore (.byte index value) from ExprCompileCore.byte hL hR) hexact hpresent hexpr
  | signextend hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields)
          (show ExprCompileCore (.signextend lhs rhs) from ExprCompileCore.signextend hL hR) with ⟨exprIR, hexpr⟩
      refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
      · rw [← CompilationModel.compileExprWithInternals_nil_eq] at hexpr
        simp [CompilationModel.compileRequireFailCond, CompilationModel.compileRequireFailCondWithInternals, hexpr]
      · simpa using finishIszeroEval (expr := .signextend lhs rhs)
          (show ExprCompileCore (.signextend lhs rhs) from ExprCompileCore.signextend hL hR) hexact hpresent hexpr
  | gt hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields)
          (show ExprCompileCore (.gt lhs rhs) from ExprCompileCore.gt hL hR) with ⟨exprIR, hexpr⟩
      refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
      · rw [← CompilationModel.compileExprWithInternals_nil_eq] at hexpr
        simp [CompilationModel.compileRequireFailCond, CompilationModel.compileRequireFailCondWithInternals, hexpr]
      · simpa using finishIszeroEval (expr := .gt lhs rhs)
          (show ExprCompileCore (.gt lhs rhs) from ExprCompileCore.gt hL hR) hexact hpresent hexpr
  | ge hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields) hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok (fields := fields) hR with ⟨rhsIR, hrhs⟩
      have hexactL : bindingsExactlyMatchIRVarsOnExpr lhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hname
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hname))
      have hexactR : bindingsExactlyMatchIRVarsOnExpr rhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hname
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hname))
      have hpresentL : exprBoundNamesPresent lhs runtime.bindings :=
        exprBoundNamesPresent_of_subset hpresent (by
          intro name hname
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hname))
      have hpresentR : exprBoundNamesPresent rhs runtime.bindings :=
        exprBoundNamesPresent_of_subset hpresent (by
          intro name hname
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hname))
      -- Extract Nat values from evalIRExpr for lhs
      have hlhsEval := eval_compileExpr_core_onExpr hL hexactL hbounded hpresentL hruntime
      rw [hlhs] at hlhsEval
      simp [Except.toOption] at hlhsEval
      rcases hLhsIR : evalIRExpr state lhsIR with _ | lhsVal
      · simp [hLhsIR, Option.bind] at hlhsEval
      · simp [hLhsIR, Option.bind] at hlhsEval
        have hLhsSrc : SourceSemantics.evalExpr fields runtime lhs = some lhsVal := hlhsEval.symm
        -- Extract Nat values from evalIRExpr for rhs
        have hrhsEval := eval_compileExpr_core_onExpr hR hexactR hbounded hpresentR hruntime
        rw [hrhs] at hrhsEval
        simp [Except.toOption] at hrhsEval
        rcases hRhsIR : evalIRExpr state rhsIR with _ | rhsVal
        · simp [hRhsIR, Option.bind] at hrhsEval
        · simp [hRhsIR, Option.bind] at hrhsEval
          have hRhsSrc : SourceSemantics.evalExpr fields runtime rhs = some rhsVal := hrhsEval.symm
          -- Boundedness
          have hlhsLt := evalExpr_lt_evmModulus_core_onExpr hL hexactL hbounded hpresentL hruntime
          rw [hLhsSrc] at hlhsLt; simp at hlhsLt
          have hrhsLt := evalExpr_lt_evmModulus_core_onExpr hR hexactR hbounded hpresentR hruntime
          rw [hRhsSrc] at hrhsLt; simp at hrhsLt
          refine ⟨YulExpr.call "lt" [lhsIR, rhsIR], ?_, ?_⟩
          · rw [CompilationModel.compileRequireFailCond]
            rw [← CompilationModel.compileExprWithInternals_nil_eq] at hlhs hrhs
            simp [CompilationModel.compileRequireFailCondWithInternals, CompilationModel.yulBinOp, hlhs, hrhs]
            rfl
          · have hltEval := evalIRExpr_lt_of_eval hLhsIR hRhsIR
            -- evalExpr (.ge lhs rhs) = do lhsV ← ...; rhsV ← ...; pure (boolWord (decide (rhsV ≤ lhsV)))
            -- With lhs = some lhsVal, rhs = some rhsVal:
            -- evalExpr (.ge lhs rhs) = some (boolWord (decide (rhsVal ≤ lhsVal)))
            -- evalExpr (.ge lhs rhs) = 0 means some (boolWord ...) = some 0 means boolWord ... = 0
            -- boolWord (decide (rhsVal ≤ lhsVal)) = 0 iff ¬ (rhsVal ≤ lhsVal) iff lhsVal < rhsVal
            -- So boolWord (evalExpr (.ge ...) = 0) = boolWord (lhsVal < rhsVal)
            --    = boolWord (lhsVal % evm < rhsVal % evm)  (since both < evmModulus)
            simp [Nat.mod_eq_of_lt hlhsLt, Nat.mod_eq_of_lt hrhsLt] at hltEval
            -- hltEval : evalIRExpr state (call "lt" [lhsIR, rhsIR]) = some (boolWord (lhsVal < rhsVal))
            -- Goal: evalIRExpr state (call "lt" [..]) = some (boolWord (decide (evalExpr (.ge ..) = some 0)))
            -- evalExpr (.ge lhs rhs) = some (boolWord (decide (rhsVal ≤ lhsVal)))
            have hGeEval : SourceSemantics.evalExpr fields runtime (.ge lhs rhs) =
                some (SourceSemantics.boolWord (decide (rhsVal ≤ lhsVal))) := by
              change (do let l ← SourceSemantics.evalExpr fields runtime lhs
                         let r ← SourceSemantics.evalExpr fields runtime rhs
                         pure (SourceSemantics.boolWord (decide (r ≤ l)))) = _
              rw [hLhsSrc, hRhsSrc]; rfl
            -- Reduce to: (lhsVal < rhsVal) ↔ ¬ (rhsVal ≤ lhsVal) ↔ (boolWord (decide (rhsVal ≤ lhsVal)) = 0)
            -- So boolWord (lhsVal < rhsVal) = boolWord (decide (some (boolWord ..) = some 0))
            -- Use simp only with hGeEval to handle the Decidable dependency
            rw [hltEval]
            simp only [Option.some.injEq, hGeEval, boolWord_eq_if]
            by_cases hle : rhsVal ≤ lhsVal
            · simp [hle, Nat.not_lt_of_le hle]
            · simp [hle, Nat.lt_of_not_le hle]
  | le hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields) hL with ⟨lhsIR, hlhs⟩
      rcases compileExpr_core_ok (fields := fields) hR with ⟨rhsIR, hrhs⟩
      have hexactL : bindingsExactlyMatchIRVarsOnExpr lhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hname
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hname))
      have hexactR : bindingsExactlyMatchIRVarsOnExpr rhs runtime.bindings state :=
        bindingsExactlyMatchIRVarsOnExpr_of_subset hexact (by
          intro name hname
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hname))
      have hpresentL : exprBoundNamesPresent lhs runtime.bindings :=
        exprBoundNamesPresent_of_subset hpresent (by
          intro name hname
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inl hname))
      have hpresentR : exprBoundNamesPresent rhs runtime.bindings :=
        exprBoundNamesPresent_of_subset hpresent (by
          intro name hname
          simpa [exprBoundNames] using List.mem_append.mpr (Or.inr hname))
      -- Extract Nat values from evalIRExpr for lhs
      have hlhsEval := eval_compileExpr_core_onExpr hL hexactL hbounded hpresentL hruntime
      rw [hlhs] at hlhsEval
      simp [Except.toOption] at hlhsEval
      rcases hLhsIR : evalIRExpr state lhsIR with _ | lhsVal
      · simp [hLhsIR, Option.bind] at hlhsEval
      · simp [hLhsIR, Option.bind] at hlhsEval
        have hLhsSrc : SourceSemantics.evalExpr fields runtime lhs = some lhsVal := hlhsEval.symm
        -- Extract Nat values from evalIRExpr for rhs
        have hrhsEval := eval_compileExpr_core_onExpr hR hexactR hbounded hpresentR hruntime
        rw [hrhs] at hrhsEval
        simp [Except.toOption] at hrhsEval
        rcases hRhsIR : evalIRExpr state rhsIR with _ | rhsVal
        · simp [hRhsIR, Option.bind] at hrhsEval
        · simp [hRhsIR, Option.bind] at hrhsEval
          have hRhsSrc : SourceSemantics.evalExpr fields runtime rhs = some rhsVal := hrhsEval.symm
          -- Boundedness
          have hlhsLt := evalExpr_lt_evmModulus_core_onExpr hL hexactL hbounded hpresentL hruntime
          rw [hLhsSrc] at hlhsLt; simp at hlhsLt
          have hrhsLt := evalExpr_lt_evmModulus_core_onExpr hR hexactR hbounded hpresentR hruntime
          rw [hRhsSrc] at hrhsLt; simp at hrhsLt
          refine ⟨YulExpr.call "gt" [lhsIR, rhsIR], ?_, ?_⟩
          · rw [CompilationModel.compileRequireFailCond]
            rw [← CompilationModel.compileExprWithInternals_nil_eq] at hlhs hrhs
            simp [CompilationModel.compileRequireFailCondWithInternals, CompilationModel.yulBinOp, hlhs, hrhs]
            rfl
          · have hgtEval := evalIRExpr_gt_of_eval hLhsIR hRhsIR
            simp [Nat.mod_eq_of_lt hlhsLt, Nat.mod_eq_of_lt hrhsLt] at hgtEval
            -- hgtEval : evalIRExpr state (call "gt" [..]) = some (boolWord (rhsVal < lhsVal))
            have hLeEval : SourceSemantics.evalExpr fields runtime (.le lhs rhs) =
                some (SourceSemantics.boolWord (decide (lhsVal ≤ rhsVal))) := by
              change (do let l ← SourceSemantics.evalExpr fields runtime lhs
                         let r ← SourceSemantics.evalExpr fields runtime rhs
                         pure (SourceSemantics.boolWord (decide (l ≤ r)))) = _
              rw [hLhsSrc, hRhsSrc]; rfl
            rw [hgtEval]
            simp only [Option.some.injEq, hLeEval, boolWord_eq_if]
            by_cases hle : lhsVal ≤ rhsVal
            · simp [hle, Nat.not_lt_of_le hle]
            · simp [hle, Nat.lt_of_not_le hle]
  | logicalNot h =>
      rename_i expr
      rcases compileExpr_core_ok (fields := fields)
          (show ExprCompileCore (.logicalNot expr) from ExprCompileCore.logicalNot h) with ⟨exprIR, hexpr⟩
      refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
      · rw [← CompilationModel.compileExprWithInternals_nil_eq] at hexpr
        simp [CompilationModel.compileRequireFailCond, CompilationModel.compileRequireFailCondWithInternals, hexpr]
      · simpa using finishIszeroEval (expr := .logicalNot expr)
          (show ExprCompileCore (.logicalNot expr) from ExprCompileCore.logicalNot h) hexact hpresent hexpr
  | logicalAnd hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields)
          (show ExprCompileCore (.logicalAnd lhs rhs) from ExprCompileCore.logicalAnd hL hR) with ⟨exprIR, hexpr⟩
      refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
      · rw [← CompilationModel.compileExprWithInternals_nil_eq] at hexpr
        simp [CompilationModel.compileRequireFailCond, CompilationModel.compileRequireFailCondWithInternals, hexpr]
      · simpa using finishIszeroEval (expr := .logicalAnd lhs rhs)
          (show ExprCompileCore (.logicalAnd lhs rhs) from ExprCompileCore.logicalAnd hL hR) hexact hpresent hexpr
  | logicalOr hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields)
          (show ExprCompileCore (.logicalOr lhs rhs) from ExprCompileCore.logicalOr hL hR) with ⟨exprIR, hexpr⟩
      refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
      · rw [← CompilationModel.compileExprWithInternals_nil_eq] at hexpr
        simp [CompilationModel.compileRequireFailCond, CompilationModel.compileRequireFailCondWithInternals, hexpr]
      · simpa using finishIszeroEval (expr := .logicalOr lhs rhs)
          (show ExprCompileCore (.logicalOr lhs rhs) from ExprCompileCore.logicalOr hL hR) hexact hpresent hexpr
  | bitAnd hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields)
          (show ExprCompileCore (.bitAnd lhs rhs) from ExprCompileCore.bitAnd hL hR) with ⟨exprIR, hexpr⟩
      refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
      · rw [← CompilationModel.compileExprWithInternals_nil_eq] at hexpr
        simp [CompilationModel.compileRequireFailCond, CompilationModel.compileRequireFailCondWithInternals, hexpr]
      · simpa using finishIszeroEval (expr := .bitAnd lhs rhs)
          (show ExprCompileCore (.bitAnd lhs rhs) from ExprCompileCore.bitAnd hL hR) hexact hpresent hexpr
  | bitOr hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields)
          (show ExprCompileCore (.bitOr lhs rhs) from ExprCompileCore.bitOr hL hR) with ⟨exprIR, hexpr⟩
      refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
      · rw [← CompilationModel.compileExprWithInternals_nil_eq] at hexpr
        simp [CompilationModel.compileRequireFailCond, CompilationModel.compileRequireFailCondWithInternals, hexpr]
      · simpa using finishIszeroEval (expr := .bitOr lhs rhs)
          (show ExprCompileCore (.bitOr lhs rhs) from ExprCompileCore.bitOr hL hR) hexact hpresent hexpr
  | bitXor hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields)
          (show ExprCompileCore (.bitXor lhs rhs) from ExprCompileCore.bitXor hL hR) with ⟨exprIR, hexpr⟩
      refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
      · rw [← CompilationModel.compileExprWithInternals_nil_eq] at hexpr
        simp [CompilationModel.compileRequireFailCond, CompilationModel.compileRequireFailCondWithInternals, hexpr]
      · simpa using finishIszeroEval (expr := .bitXor lhs rhs)
          (show ExprCompileCore (.bitXor lhs rhs) from ExprCompileCore.bitXor hL hR) hexact hpresent hexpr
  | bitNot h =>
      rename_i expr
      rcases compileExpr_core_ok (fields := fields)
          (show ExprCompileCore (.bitNot expr) from ExprCompileCore.bitNot h) with ⟨exprIR, hexpr⟩
      refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
      · rw [← CompilationModel.compileExprWithInternals_nil_eq] at hexpr
        simp [CompilationModel.compileRequireFailCond, CompilationModel.compileRequireFailCondWithInternals, hexpr]
      · simpa using finishIszeroEval (expr := .bitNot expr)
          (show ExprCompileCore (.bitNot expr) from ExprCompileCore.bitNot h) hexact hpresent hexpr
  | shl hS hV =>
      rename_i shift value
      rcases compileExpr_core_ok (fields := fields)
          (show ExprCompileCore (.shl shift value) from ExprCompileCore.shl hS hV) with ⟨exprIR, hexpr⟩
      refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
      · rw [← CompilationModel.compileExprWithInternals_nil_eq] at hexpr
        simp [CompilationModel.compileRequireFailCond, CompilationModel.compileRequireFailCondWithInternals, hexpr]
      · simpa using finishIszeroEval (expr := .shl shift value)
          (show ExprCompileCore (.shl shift value) from ExprCompileCore.shl hS hV) hexact hpresent hexpr
  | shr hS hV =>
      rename_i shift value
      rcases compileExpr_core_ok (fields := fields)
          (show ExprCompileCore (.shr shift value) from ExprCompileCore.shr hS hV) with ⟨exprIR, hexpr⟩
      refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
      · rw [← CompilationModel.compileExprWithInternals_nil_eq] at hexpr
        simp [CompilationModel.compileRequireFailCond, CompilationModel.compileRequireFailCondWithInternals, hexpr]
      · simpa using finishIszeroEval (expr := .shr shift value)
          (show ExprCompileCore (.shr shift value) from ExprCompileCore.shr hS hV) hexact hpresent hexpr
  | min hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields)
          (show ExprCompileCore (.min lhs rhs) from ExprCompileCore.min hL hR) with ⟨exprIR, hexpr⟩
      refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
      · rw [← CompilationModel.compileExprWithInternals_nil_eq] at hexpr
        simp [CompilationModel.compileRequireFailCond, CompilationModel.compileRequireFailCondWithInternals, hexpr]
      · simpa using finishIszeroEval (expr := .min lhs rhs)
          (show ExprCompileCore (.min lhs rhs) from ExprCompileCore.min hL hR) hexact hpresent hexpr
  | max hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields)
          (show ExprCompileCore (.max lhs rhs) from ExprCompileCore.max hL hR) with ⟨exprIR, hexpr⟩
      refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
      · rw [← CompilationModel.compileExprWithInternals_nil_eq] at hexpr
        simp [CompilationModel.compileRequireFailCond, CompilationModel.compileRequireFailCondWithInternals, hexpr]
      · simpa using finishIszeroEval (expr := .max lhs rhs)
          (show ExprCompileCore (.max lhs rhs) from ExprCompileCore.max hL hR) hexact hpresent hexpr
  | ite hC hT hE =>
      rename_i cond thenVal elseVal
      rcases compileExpr_core_ok (fields := fields)
          (show ExprCompileCore (.ite cond thenVal elseVal) from ExprCompileCore.ite hC hT hE) with ⟨exprIR, hexpr⟩
      refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
      · rw [← CompilationModel.compileExprWithInternals_nil_eq] at hexpr
        simp [CompilationModel.compileRequireFailCond, CompilationModel.compileRequireFailCondWithInternals, hexpr]
      · simpa using finishIszeroEval (expr := .ite cond thenVal elseVal)
          (show ExprCompileCore (.ite cond thenVal elseVal) from ExprCompileCore.ite hC hT hE) hexact hpresent hexpr
  | ceilDiv hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields)
          (show ExprCompileCore (.ceilDiv lhs rhs) from ExprCompileCore.ceilDiv hL hR) with ⟨exprIR, hexpr⟩
      refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
      · rw [← CompilationModel.compileExprWithInternals_nil_eq] at hexpr
        simp [CompilationModel.compileRequireFailCond, CompilationModel.compileRequireFailCondWithInternals, hexpr]
      · simpa using finishIszeroEval (expr := .ceilDiv lhs rhs)
          (show ExprCompileCore (.ceilDiv lhs rhs) from ExprCompileCore.ceilDiv hL hR) hexact hpresent hexpr
  | wMulDown hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields)
          (show ExprCompileCore (.wMulDown lhs rhs) from ExprCompileCore.wMulDown hL hR) with ⟨exprIR, hexpr⟩
      refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
      · rw [← CompilationModel.compileExprWithInternals_nil_eq] at hexpr
        simp [CompilationModel.compileRequireFailCond, CompilationModel.compileRequireFailCondWithInternals, hexpr]
      · simpa using finishIszeroEval (expr := .wMulDown lhs rhs)
          (show ExprCompileCore (.wMulDown lhs rhs) from ExprCompileCore.wMulDown hL hR) hexact hpresent hexpr
  | wDivUp hL hR =>
      rename_i lhs rhs
      rcases compileExpr_core_ok (fields := fields)
          (show ExprCompileCore (.wDivUp lhs rhs) from ExprCompileCore.wDivUp hL hR) with ⟨exprIR, hexpr⟩
      refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
      · rw [← CompilationModel.compileExprWithInternals_nil_eq] at hexpr
        simp [CompilationModel.compileRequireFailCond, CompilationModel.compileRequireFailCondWithInternals, hexpr]
      · simpa using finishIszeroEval (expr := .wDivUp lhs rhs)
          (show ExprCompileCore (.wDivUp lhs rhs) from ExprCompileCore.wDivUp hL hR) hexact hpresent hexpr
  | mulDivDown hA hB hC =>
      rename_i a b c
      rcases compileExpr_core_ok (fields := fields)
          (show ExprCompileCore (.mulDivDown a b c) from ExprCompileCore.mulDivDown hA hB hC) with ⟨exprIR, hexpr⟩
      refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
      · rw [← CompilationModel.compileExprWithInternals_nil_eq] at hexpr
        simp [CompilationModel.compileRequireFailCond, CompilationModel.compileRequireFailCondWithInternals, hexpr]
      · simpa using finishIszeroEval (expr := .mulDivDown a b c)
          (show ExprCompileCore (.mulDivDown a b c) from ExprCompileCore.mulDivDown hA hB hC) hexact hpresent hexpr
  | mulDivUp hA hB hC =>
      rename_i a b c
      rcases compileExpr_core_ok (fields := fields)
          (show ExprCompileCore (.mulDivUp a b c) from ExprCompileCore.mulDivUp hA hB hC) with ⟨exprIR, hexpr⟩
      refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
      · rw [← CompilationModel.compileExprWithInternals_nil_eq] at hexpr
        simp [CompilationModel.compileRequireFailCond, CompilationModel.compileRequireFailCondWithInternals, hexpr]
      · simpa using finishIszeroEval (expr := .mulDivUp a b c)
          (show ExprCompileCore (.mulDivUp a b c) from ExprCompileCore.mulDivUp hA hB hC) hexact hpresent hexpr
  | tload h =>
      rename_i expr
      rcases compileExpr_core_ok (fields := fields)
          (show ExprCompileCore (.tload expr) from ExprCompileCore.tload h) with ⟨exprIR, hexpr⟩
      refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
      · rw [← CompilationModel.compileExprWithInternals_nil_eq] at hexpr
        simp [CompilationModel.compileRequireFailCond, CompilationModel.compileRequireFailCondWithInternals, hexpr]
      · simpa using finishIszeroEval (expr := .tload expr)
          (show ExprCompileCore (.tload expr) from ExprCompileCore.tload h) hexact hpresent hexpr
  | calldataload h =>
      rename_i expr
      rcases compileExpr_core_ok (fields := fields)
          (show ExprCompileCore (.calldataload expr) from
            ExprCompileCore.calldataload h) with ⟨exprIR, hexpr⟩
      refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
      · rw [← CompilationModel.compileExprWithInternals_nil_eq] at hexpr
        simp [CompilationModel.compileRequireFailCond, CompilationModel.compileRequireFailCondWithInternals, hexpr]
      · simpa using finishIszeroEval (expr := .calldataload expr)
          (show ExprCompileCore (.calldataload expr) from
            ExprCompileCore.calldataload h) hexact hpresent hexpr
  | mload h =>
      rename_i expr
      rcases compileExpr_core_ok (fields := fields)
          (show ExprCompileCore (.mload expr) from
            ExprCompileCore.mload h) with ⟨exprIR, hexpr⟩
      refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
      · rw [← CompilationModel.compileExprWithInternals_nil_eq] at hexpr
        simp [CompilationModel.compileRequireFailCond, CompilationModel.compileRequireFailCondWithInternals, hexpr]
      · simpa using finishIszeroEval (expr := .mload expr)
          (show ExprCompileCore (.mload expr) from
            ExprCompileCore.mload h) hexact hpresent hexpr
  | extcodesize h =>
      rename_i expr
      rcases compileExpr_core_ok (fields := fields)
          (show ExprCompileCore (.extcodesize expr) from
            ExprCompileCore.extcodesize h) with ⟨exprIR, hexpr⟩
      refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
      · rw [← CompilationModel.compileExprWithInternals_nil_eq] at hexpr
        simp [CompilationModel.compileRequireFailCond, CompilationModel.compileRequireFailCondWithInternals, hexpr]
      · simpa using finishIszeroEval (expr := .extcodesize expr)
          (show ExprCompileCore (.extcodesize expr) from
            ExprCompileCore.extcodesize h) hexact hpresent hexpr
  | returndataOptionalBoolAt h =>
      rename_i expr
      rcases compileExpr_core_ok (fields := fields)
          (show ExprCompileCore (.returndataOptionalBoolAt expr) from
            ExprCompileCore.returndataOptionalBoolAt h) with ⟨exprIR, hexpr⟩
      refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
      · rw [← CompilationModel.compileExprWithInternals_nil_eq] at hexpr
        simp [CompilationModel.compileRequireFailCond, CompilationModel.compileRequireFailCondWithInternals, hexpr]
      · simpa using finishIszeroEval (expr := .returndataOptionalBoolAt expr)
          (show ExprCompileCore (.returndataOptionalBoolAt expr) from
            ExprCompileCore.returndataOptionalBoolAt h) hexact hpresent hexpr
  | keccak256 hO hS =>
      rename_i offset size
      rcases compileExpr_core_ok (fields := fields)
          (show ExprCompileCore (.keccak256 offset size) from
            ExprCompileCore.keccak256 hO hS) with ⟨exprIR, hexpr⟩
      refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
      · rw [← CompilationModel.compileExprWithInternals_nil_eq] at hexpr
        simp [CompilationModel.compileRequireFailCond,
          CompilationModel.compileRequireFailCondWithInternals, hexpr]
      · simpa using finishIszeroEval (expr := .keccak256 offset size)
          (show ExprCompileCore (.keccak256 offset size) from
            ExprCompileCore.keccak256 hO hS) hexact hpresent hexpr
  | builtinExp hB hE =>
      rename_i base exponent
      rcases compileExpr_core_ok (fields := fields)
          (show ExprCompileCore (.externalCall builtinExpName [base, exponent]) from
            ExprCompileCore.builtinExp hB hE) with ⟨exprIR, hexpr⟩
      refine ⟨YulExpr.call "iszero" [exprIR], ?_, ?_⟩
      · rw [← CompilationModel.compileExprWithInternals_nil_eq] at hexpr
        simp [CompilationModel.compileRequireFailCond,
          CompilationModel.compileRequireFailCondWithInternals, hexpr]
      · simpa using finishIszeroEval (expr := .externalCall builtinExpName [base, exponent])
          (show ExprCompileCore (.externalCall builtinExpName [base, exponent]) from
            ExprCompileCore.builtinExp hB hE) hexact hpresent hexpr


end FunctionBody

end Compiler.Proofs.IRGeneration

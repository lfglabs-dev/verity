import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanNativeCalldata

namespace Compiler.Proofs.YulGeneration.Backends.Native

/-! ## Native EVMYulLean primitive step lemmas

This module collects direct `EvmYul.step` facts that are reused by the native
runtime harness and its primitive-call proofs. Keeping these definitional facts
out of the harness leaves the dispatcher and projection proof layers easier to
scan without changing theorem statements or proof strength.
-/

@[simp] theorem step_calldataload_ok
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (offset : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.CALLDATALOAD none
        (.Ok shared store) [offset] =
      .ok (.Ok shared store,
        some (EvmYul.State.calldataload shared.toState offset)) := by
  rfl

@[simp] theorem step_shr_ok
    (state : EvmYul.Yul.State)
    (shift value : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.SHR none state [shift, value] =
      .ok (state, some (EvmYul.UInt256.shiftRight value shift)) := by
  rfl

@[simp] theorem step_add_ok
    (state : EvmYul.Yul.State)
    (left right : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.ADD none state [left, right] =
      .ok (state, some (EvmYul.UInt256.add left right)) := by
  rfl

@[simp] theorem step_sub_ok
    (state : EvmYul.Yul.State)
    (left right : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.SUB none state [left, right] =
      .ok (state, some (EvmYul.UInt256.sub left right)) := by
  rfl

@[simp] theorem step_mul_ok
    (state : EvmYul.Yul.State)
    (left right : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.MUL none state [left, right] =
      .ok (state, some (EvmYul.UInt256.mul left right)) := by
  rfl

@[simp] theorem step_eq_ok
    (state : EvmYul.Yul.State)
    (left right : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.EQ none state [left, right] =
      .ok (state, some (EvmYul.UInt256.eq left right)) := by
  rfl

@[simp] theorem step_iszero_ok
    (state : EvmYul.Yul.State)
    (value : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.ISZERO none state [value] =
      .ok (state, some (EvmYul.UInt256.isZero value)) := by
  rfl

@[simp] theorem step_lt_ok
    (state : EvmYul.Yul.State)
    (left right : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.LT none state [left, right] =
      .ok (state, some (EvmYul.UInt256.lt left right)) := by
  rfl

@[simp] theorem step_calldatasize_ok
    (state : EvmYul.Yul.State) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.CALLDATASIZE none state [] =
      .ok (state, some (EvmYul.UInt256.ofNat state.executionEnv.calldata.size)) := by
  rfl

theorem step_calldatasize_any
    (state : EvmYul.Yul.State)
    (values : List EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.CALLDATASIZE none state values =
      .ok (state, some (EvmYul.UInt256.ofNat state.executionEnv.calldata.size)) := by
  rfl

@[simp] theorem step_callvalue_ok
    (state : EvmYul.Yul.State) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.CALLVALUE none state [] =
      .ok (state, some state.executionEnv.weiValue) := by
  rfl

theorem step_callvalue_any
    (state : EvmYul.Yul.State)
    (values : List EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.CALLVALUE none state values =
      .ok (state, some state.executionEnv.weiValue) := by
  rfl

@[simp] theorem step_address_ok
    (state : EvmYul.Yul.State) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.ADDRESS none state [] =
      .ok (state, some (EvmYul.UInt256.ofNat state.executionEnv.codeOwner.val)) := by
  rfl

theorem step_address_any
    (state : EvmYul.Yul.State)
    (values : List EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.ADDRESS none state values =
      .ok (state, some (EvmYul.UInt256.ofNat state.executionEnv.codeOwner.val)) := by
  rfl

@[simp] theorem step_balance_ok
    (state : EvmYul.Yul.State)
    (account : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.BALANCE none state [account] =
      let (state', value) := state.toState.balance account
      .ok (state.setSharedState { state.toSharedState with toState := state' },
        some value) := by
  rfl

@[simp] theorem step_origin_ok
    (state : EvmYul.Yul.State) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.ORIGIN none state [] =
      .ok (state, some (EvmYul.UInt256.ofNat state.executionEnv.sender.val)) := by
  rfl

@[simp] theorem step_caller_ok
    (state : EvmYul.Yul.State) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.CALLER none state [] =
      .ok (state, some (EvmYul.UInt256.ofNat state.executionEnv.source.val)) := by
  rfl

theorem step_caller_any
    (state : EvmYul.Yul.State)
    (values : List EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.CALLER none state values =
      .ok (state, some (EvmYul.UInt256.ofNat state.executionEnv.source.val)) := by
  rfl

@[simp] theorem step_timestamp_ok
    (state : EvmYul.Yul.State) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.TIMESTAMP none state [] =
      .ok (state, some state.toState.timeStamp) := by
  rfl

theorem step_timestamp_any
    (state : EvmYul.Yul.State)
    (values : List EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.TIMESTAMP none state values =
      .ok (state, some state.toState.timeStamp) := by
  rfl

@[simp] theorem step_number_ok
    (state : EvmYul.Yul.State) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.NUMBER none state [] =
      .ok (state, some state.toState.number) := by
  rfl

theorem step_number_any
    (state : EvmYul.Yul.State)
    (values : List EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.NUMBER none state values =
      .ok (state, some state.toState.number) := by
  rfl

@[simp] theorem step_chainid_ok
    (state : EvmYul.Yul.State) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.CHAINID none state [] =
      .ok (state, some state.toState.chainId) := by
  rfl

theorem step_chainid_any
    (state : EvmYul.Yul.State)
    (values : List EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.CHAINID none state values =
      .ok (state, some state.toState.chainId) := by
  rfl

@[simp] theorem step_blobbasefee_ok
    (state : EvmYul.Yul.State) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.BLOBBASEFEE none state [] =
      .ok (state, some state.executionEnv.getBlobGasprice) := by
  rfl

theorem step_blobbasefee_any
    (state : EvmYul.Yul.State)
    (values : List EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.BLOBBASEFEE none state values =
      .ok (state, some state.executionEnv.getBlobGasprice) := by
  rfl

@[simp] theorem step_gasprice_ok
    (state : EvmYul.Yul.State) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.GASPRICE none state [] =
      .ok (state, some (EvmYul.UInt256.ofNat state.executionEnv.gasPrice)) := by
  rfl

@[simp] theorem step_coinbase_ok
    (state : EvmYul.Yul.State) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.COINBASE none state [] =
      .ok (state, some (EvmYul.UInt256.ofNat state.toState.coinBase.val)) := by
  rfl

@[simp] theorem step_gaslimit_ok
    (state : EvmYul.Yul.State) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.GASLIMIT none state [] =
      .ok (state, some state.toState.gasLimit) := by
  rfl

@[simp] theorem step_selfbalance_ok
    (state : EvmYul.Yul.State) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.SELFBALANCE none state [] =
      .ok (state, some state.toState.selfbalance) := by
  rfl

@[simp] theorem step_and_ok
    (state : EvmYul.Yul.State)
    (left right : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.AND none state [left, right] =
      .ok (state, some (EvmYul.UInt256.land left right)) := by
  rfl

end Compiler.Proofs.YulGeneration.Backends.Native

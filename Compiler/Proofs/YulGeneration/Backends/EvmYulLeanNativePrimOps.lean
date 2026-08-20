import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanNativeStepLemmas
import Lean

namespace Compiler.Proofs.YulGeneration.Backends.Native

open Compiler.Yul
open Compiler.Proofs.YulGeneration
open Compiler.Proofs.YulGeneration.Backends.StateBridge
open Lean Elab Tactic Meta
open Compiler.Proofs.IRGeneration
  (IRResult IRState IRStorageSlot IRStorageWord IRTransaction)

/-! ## Native EVMYulLean primitive operation execution lemmas

This module collects direct `EvmYul.step` and `EvmYul.Yul.primCall` facts,
plus the small primitive-exec helpers reused by the native dispatcher harness.
Keeping these definitional operation facts out of `EvmYulLeanNativeHarness.lean`
leaves that file focused on dispatcher/result proof structure.
-/

@[simp] theorem step_mstore_ok
    (state : EvmYul.Yul.State)
    (offset value : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.MSTORE none state [offset, value] =
      .ok (state.setMachineState (state.toMachineState.mstore offset value),
        none) := by
  rfl

theorem step_mstore_nil_invalid
    (state : EvmYul.Yul.State) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.MSTORE none state [] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_mstore_singleton_invalid
    (state : EvmYul.Yul.State)
    (offset : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.MSTORE none state [offset] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_mstore_overarity_invalid
    (state : EvmYul.Yul.State)
    (offset value extra : EvmYul.UInt256)
    (rest : List EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.MSTORE none state
        (offset :: value :: extra :: rest) =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

@[simp] theorem step_mstore8_ok
    (state : EvmYul.Yul.State)
    (offset value : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.MSTORE8 none state [offset, value] =
      .ok (state.setMachineState (state.toMachineState.mstore8 offset value),
        none) := by
  rfl

theorem step_mstore8_nil_invalid
    (state : EvmYul.Yul.State) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.MSTORE8 none state [] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_mstore8_singleton_invalid
    (state : EvmYul.Yul.State)
    (offset : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.MSTORE8 none state [offset] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_mstore8_overarity_invalid
    (state : EvmYul.Yul.State)
    (offset value extra : EvmYul.UInt256)
    (rest : List EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.MSTORE8 none state
        (offset :: value :: extra :: rest) =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

@[simp] theorem step_sload_ok
    (state : EvmYul.Yul.State)
    (slot : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.SLOAD none state [slot] =
      let (state', value) := state.toState.sload slot
      .ok (state.setSharedState { state.toSharedState with toState := state' },
        some value) := by
  rfl

@[simp] theorem step_mload_ok
    (state : EvmYul.Yul.State)
    (offset : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.MLOAD none state [offset] =
      let (value, machineState') := state.toSharedState.toMachineState.mload offset
      .ok (state.setMachineState machineState', some value) := by
  rfl

@[simp] theorem step_keccak256_ok
    (state : EvmYul.Yul.State)
    (offset size : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.KECCAK256 none state [offset, size] =
      let (value, machineState') := state.toMachineState.keccak256 offset size
      .ok (state.setMachineState machineState', some value) := by
  rfl

@[simp] theorem step_log0_nil_invalid
    (state : EvmYul.Yul.State) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.LOG0 none state [] =
      Except.ok (state, none) := by
  rfl

@[simp] theorem step_log0_singleton_invalid
    (state : EvmYul.Yul.State)
    (offset : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.LOG0 none state [offset] =
      Except.ok (state, none) := by
  rfl

@[simp] theorem step_log0_overarity_invalid
    (state : EvmYul.Yul.State)
    (offset size extra : EvmYul.UInt256)
    (rest : List EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.LOG0 none state
        (offset :: size :: extra :: rest) =
      Except.ok (state, none) := by
  rfl

@[simp] theorem step_log0_ok
    (state : EvmYul.Yul.State)
    (offset size : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.LOG0 none state [offset, size] =
      .ok (state.setSharedState
        (EvmYul.SharedState.logOp offset size #[] state.toSharedState), none) := by
  rfl

@[simp] theorem step_log1_nil_invalid
    (state : EvmYul.Yul.State) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.LOG1 none state [] =
      Except.ok (state, none) := by
  rfl

@[simp] theorem step_log1_singleton_invalid
    (state : EvmYul.Yul.State)
    (offset : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.LOG1 none state [offset] =
      Except.ok (state, none) := by
  rfl

@[simp] theorem step_log1_pair_invalid
    (state : EvmYul.Yul.State)
    (offset size : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.LOG1 none state [offset, size] =
      Except.ok (state, none) := by
  rfl

@[simp] theorem step_log1_overarity_invalid
    (state : EvmYul.Yul.State)
    (offset size topic0 extra : EvmYul.UInt256)
    (rest : List EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.LOG1 none state
        (offset :: size :: topic0 :: extra :: rest) =
      Except.ok (state, none) := by
  rfl

@[simp] theorem step_log1_ok
    (state : EvmYul.Yul.State)
    (offset size topic0 : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.LOG1 none state
        [offset, size, topic0] =
      .ok (state.setSharedState
        (EvmYul.SharedState.logOp offset size #[topic0] state.toSharedState), none) := by
  rfl

@[simp] theorem step_log2_nil_invalid
    (state : EvmYul.Yul.State) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.LOG2 none state [] =
      Except.ok (state, none) := by
  rfl

@[simp] theorem step_log2_singleton_invalid
    (state : EvmYul.Yul.State)
    (offset : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.LOG2 none state [offset] =
      Except.ok (state, none) := by
  rfl

@[simp] theorem step_log2_pair_invalid
    (state : EvmYul.Yul.State)
    (offset size : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.LOG2 none state [offset, size] =
      Except.ok (state, none) := by
  rfl

@[simp] theorem step_log2_triple_invalid
    (state : EvmYul.Yul.State)
    (offset size topic0 : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.LOG2 none state
        [offset, size, topic0] =
      Except.ok (state, none) := by
  rfl

@[simp] theorem step_log2_overarity_invalid
    (state : EvmYul.Yul.State)
    (offset size topic0 topic1 extra : EvmYul.UInt256)
    (rest : List EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.LOG2 none state
        (offset :: size :: topic0 :: topic1 :: extra :: rest) =
      Except.ok (state, none) := by
  rfl

@[simp] theorem step_log2_ok
    (state : EvmYul.Yul.State)
    (offset size topic0 topic1 : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.LOG2 none state
        [offset, size, topic0, topic1] =
      .ok (state.setSharedState
        (EvmYul.SharedState.logOp offset size #[topic0, topic1]
          state.toSharedState), none) := by
  rfl

@[simp] theorem step_log3_nil_invalid
    (state : EvmYul.Yul.State) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.LOG3 none state [] =
      Except.ok (state, none) := by
  rfl

@[simp] theorem step_log3_singleton_invalid
    (state : EvmYul.Yul.State)
    (offset : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.LOG3 none state [offset] =
      Except.ok (state, none) := by
  rfl

@[simp] theorem step_log3_pair_invalid
    (state : EvmYul.Yul.State)
    (offset size : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.LOG3 none state [offset, size] =
      Except.ok (state, none) := by
  rfl

@[simp] theorem step_log3_triple_invalid
    (state : EvmYul.Yul.State)
    (offset size topic0 : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.LOG3 none state
        [offset, size, topic0] =
      Except.ok (state, none) := by
  rfl

@[simp] theorem step_log3_quad_invalid
    (state : EvmYul.Yul.State)
    (offset size topic0 topic1 : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.LOG3 none state
        [offset, size, topic0, topic1] =
      Except.ok (state, none) := by
  rfl

@[simp] theorem step_log3_overarity_invalid
    (state : EvmYul.Yul.State)
    (offset size topic0 topic1 topic2 extra : EvmYul.UInt256)
    (rest : List EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.LOG3 none state
        (offset :: size :: topic0 :: topic1 :: topic2 :: extra :: rest) =
      Except.ok (state, none) := by
  rfl

@[simp] theorem step_log3_ok
    (state : EvmYul.Yul.State)
    (offset size topic0 topic1 topic2 : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.LOG3 none state
        [offset, size, topic0, topic1, topic2] =
      .ok (state.setSharedState
        (EvmYul.SharedState.logOp offset size #[topic0, topic1, topic2]
          state.toSharedState), none) := by
  rfl

@[simp] theorem step_log4_nil_invalid
    (state : EvmYul.Yul.State) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.LOG4 none state [] =
      Except.ok (state, none) := by
  rfl

@[simp] theorem step_log4_singleton_invalid
    (state : EvmYul.Yul.State)
    (offset : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.LOG4 none state [offset] =
      Except.ok (state, none) := by
  rfl

@[simp] theorem step_log4_pair_invalid
    (state : EvmYul.Yul.State)
    (offset size : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.LOG4 none state [offset, size] =
      Except.ok (state, none) := by
  rfl

@[simp] theorem step_log4_triple_invalid
    (state : EvmYul.Yul.State)
    (offset size topic0 : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.LOG4 none state
        [offset, size, topic0] =
      Except.ok (state, none) := by
  rfl

@[simp] theorem step_log4_quad_invalid
    (state : EvmYul.Yul.State)
    (offset size topic0 topic1 : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.LOG4 none state
        [offset, size, topic0, topic1] =
      Except.ok (state, none) := by
  rfl

@[simp] theorem step_log4_quint_invalid
    (state : EvmYul.Yul.State)
    (offset size topic0 topic1 topic2 : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.LOG4 none state
        [offset, size, topic0, topic1, topic2] =
      Except.ok (state, none) := by
  rfl

@[simp] theorem step_log4_overarity_invalid
    (state : EvmYul.Yul.State)
    (offset size topic0 topic1 topic2 topic3 extra : EvmYul.UInt256)
    (rest : List EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.LOG4 none state
        (offset :: size :: topic0 :: topic1 :: topic2 :: topic3 :: extra :: rest) =
      Except.ok (state, none) := by
  rfl

@[simp] theorem step_log4_ok
    (state : EvmYul.Yul.State)
    (offset size topic0 topic1 topic2 topic3 : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.LOG4 none state
        [offset, size, topic0, topic1, topic2, topic3] =
      .ok (state.setSharedState
        (EvmYul.SharedState.logOp offset size #[topic0, topic1, topic2, topic3]
          state.toSharedState), none) := by
  rfl

@[simp] theorem step_sstore_ok
    (state : EvmYul.Yul.State)
    (slot value : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.SSTORE none state [slot, value] =
      .ok (state.setState (state.toState.sstore slot value), none) := by
  rfl

theorem step_sstore_nil_invalid
    (state : EvmYul.Yul.State) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.SSTORE none state [] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_sstore_singleton_invalid
    (state : EvmYul.Yul.State)
    (slot : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.SSTORE none state [slot] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_sstore_overarity_invalid
    (state : EvmYul.Yul.State)
    (slot value extra : EvmYul.UInt256)
    (rest : List EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.SSTORE none state
        (slot :: value :: extra :: rest) =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

@[simp] theorem step_tload_ok
    (state : EvmYul.Yul.State)
    (slot : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.TLOAD none state [slot] =
      let (state', value) := state.toState.tload slot
      .ok (state.setSharedState { state.toSharedState with toState := state' },
        some value) := by
  rfl

@[simp] theorem step_tstore_ok
    (state : EvmYul.Yul.State)
    (slot value : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.TSTORE none state [slot, value] =
      .ok (state.setState (state.toState.tstore slot value), none) := by
  rfl

theorem step_tstore_nil_invalid
    (state : EvmYul.Yul.State) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.TSTORE none state [] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_tstore_singleton_invalid
    (state : EvmYul.Yul.State)
    (slot : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.TSTORE none state [slot] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_tstore_overarity_invalid
    (state : EvmYul.Yul.State)
    (slot value extra : EvmYul.UInt256)
    (rest : List EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.TSTORE none state
        (slot :: value :: extra :: rest) =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

@[simp] theorem step_msize_ok
    (state : EvmYul.Yul.State) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.MSIZE none state [] =
      .ok (state, some (state.toMachineState.msize)) := by
  rfl

@[simp] theorem step_gas_ok
    (state : EvmYul.Yul.State) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.GAS none state [] =
      .ok (state, some (state.toMachineState.gas)) := by
  rfl

@[simp] theorem step_returndatasize_ok
    (state : EvmYul.Yul.State) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.RETURNDATASIZE none state [] =
      .ok (state, some (state.toMachineState.returndatasize)) := by
  rfl

@[simp] theorem step_calldatacopy_ok
    (state : EvmYul.Yul.State)
    (mstart datastart size : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.CALLDATACOPY none state
        [mstart, datastart, size] =
      .ok (state.setSharedState
        (state.toSharedState.calldatacopy mstart datastart size), none) := by
  rfl

theorem step_calldatacopy_nil_invalid
    (state : EvmYul.Yul.State) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.CALLDATACOPY none state [] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_calldatacopy_singleton_invalid
    (state : EvmYul.Yul.State)
    (mstart : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.CALLDATACOPY none state
        [mstart] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_calldatacopy_pair_invalid
    (state : EvmYul.Yul.State)
    (mstart datastart : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.CALLDATACOPY none state
        [mstart, datastart] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_calldatacopy_overarity_invalid
    (state : EvmYul.Yul.State)
    (mstart datastart size extra : EvmYul.UInt256)
    (rest : List EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.CALLDATACOPY none state
        (mstart :: datastart :: size :: extra :: rest) =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

@[simp] theorem step_returndatacopy_ok
    (state : EvmYul.Yul.State)
    (mstart rstart size : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.RETURNDATACOPY none state
        [mstart, rstart, size] =
      .ok (state.setMachineState
        (state.toSharedState.toMachineState.returndatacopy mstart rstart size),
        none) := by
  rfl

theorem step_returndatacopy_nil_invalid
    (state : EvmYul.Yul.State) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.RETURNDATACOPY none state [] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_returndatacopy_singleton_invalid
    (state : EvmYul.Yul.State)
    (mstart : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.RETURNDATACOPY none state
        [mstart] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_returndatacopy_pair_invalid
    (state : EvmYul.Yul.State)
    (mstart rstart : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.RETURNDATACOPY none state
        [mstart, rstart] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_returndatacopy_overarity_invalid
    (state : EvmYul.Yul.State)
    (mstart rstart size extra : EvmYul.UInt256)
    (rest : List EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.RETURNDATACOPY none state
        (mstart :: rstart :: size :: extra :: rest) =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

@[simp] theorem step_pop_ok
    (state : EvmYul.Yul.State)
    (value : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.POP none state [value] =
      .ok (state, none) := by
  rfl

@[simp] theorem step_stop_ok
    (state : EvmYul.Yul.State) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.STOP none state [] =
      .error (EvmYul.Yul.Exception.YulHalt state ⟨0⟩) := by
  rfl

@[simp] theorem step_return_ok
    (state : EvmYul.Yul.State)
    (offset size : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.RETURN none state [offset, size] =
      match EvmYul.Yul.binaryMachineStateOp EvmYul.MachineState.evmReturn
          state [offset, size] with
      | .error e => .error e
      | .ok (s, value) =>
          .error (EvmYul.Yul.Exception.YulHalt s (value.getD ⟨1⟩)) := by
  rfl

theorem step_return_nil_invalid
    (state : EvmYul.Yul.State) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.RETURN none state [] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_return_singleton_invalid
    (state : EvmYul.Yul.State)
    (offset : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.RETURN none state [offset] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_return_overarity_invalid
    (state : EvmYul.Yul.State)
    (offset size extra : EvmYul.UInt256)
    (rest : List EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.RETURN none state
        (offset :: size :: extra :: rest) =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

@[simp] theorem step_revert_ok
    (state : EvmYul.Yul.State)
    (offset size : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.REVERT none state [offset, size] =
      match EvmYul.Yul.binaryMachineStateOp EvmYul.MachineState.evmRevert
          state [offset, size] with
      | .error e => .error e
      | .ok (_, _) => .error EvmYul.Yul.Exception.Revert := by
  rfl

theorem step_revert_nil_invalid
    (state : EvmYul.Yul.State) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.REVERT none state [] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_revert_singleton_invalid
    (state : EvmYul.Yul.State)
    (offset : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.REVERT none state [offset] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_revert_overarity_invalid
    (state : EvmYul.Yul.State)
    (offset size extra : EvmYul.UInt256)
    (rest : List EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.REVERT none state
        (offset :: size :: extra :: rest) =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

@[simp] theorem primCall_calldataload_ok
    (fuel : Nat)
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (offset : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) (.Ok shared store)
        EvmYul.Operation.CALLDATALOAD [offset] =
      .ok (.Ok shared store,
        [EvmYul.State.calldataload shared.toState offset]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

/-- Native primitive execution of `calldataload(4)` on initial bridged calldata
    returns the first aligned ABI argument word. This packages the byte-level
    calldata decode through EVMYulLean's actual `CALLDATALOAD` primitive
    relation, in the shape needed by the generated `store(uint256)` body. -/
theorem primCall_calldataload4_initialState_arg0_ok
    (fuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (arg : Nat)
    (rest : List Nat)
    (hArgs : tx.args = arg :: rest) :
    EvmYul.Yul.primCall (fuel + 1)
        (initialState contract tx storage observableSlots)
        EvmYul.Operation.CALLDATALOAD [EvmYul.UInt256.ofNat 4] =
      .ok (initialState contract tx storage observableSlots,
        [natToUInt256 arg]) := by
  have hWord :=
    initialState_calldataload4_arg0_word contract tx storage
      observableSlots arg rest hArgs
  unfold initialState at hWord ⊢
  rw [primCall_calldataload_ok]
  simpa [hWord]

/-- Native primitive execution of `calldataload(4)` is independent of the
    current Yul local-variable store. This is the selected-body shape needed
    after the lowered dispatcher has inserted its switch temporaries. -/
theorem primCall_calldataload4_initialState_arg0_ok_withStore
    (fuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (arg : Nat)
    (rest : List Nat)
    (hArgs : tx.args = arg :: rest) :
    EvmYul.Yul.primCall (fuel + 1)
        (.Ok (initialState contract tx storage observableSlots).sharedState store)
        EvmYul.Operation.CALLDATALOAD [EvmYul.UInt256.ofNat 4] =
      .ok (.Ok (initialState contract tx storage observableSlots).sharedState store,
        [natToUInt256 arg]) := by
  have hWord :=
    initialState_calldataload4_arg0_word contract tx storage
      observableSlots arg rest hArgs
  unfold initialState at hWord ⊢
  rw [primCall_calldataload_ok]
  simpa [hWord]

/-- Native primitive execution of `calldataload(4)` for an IR transaction
    already converted to the native Yul transaction surface. This is the
    dispatcher-selected setter shape: the lowered switch has installed local
    temporaries, but calldata still decodes the first aligned ABI argument
    exactly through EVMYulLean's `CALLDATALOAD` primitive. -/
theorem primCall_calldataload4_initialState_ofIR_arg0_ok_withStore
    (fuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : Compiler.Proofs.IRGeneration.IRTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (arg : Nat)
    (rest : List Nat)
    (hArgs : tx.args = arg :: rest) :
    EvmYul.Yul.primCall (fuel + 1)
        (.Ok (initialState contract (YulTransaction.ofIR tx) storage
            observableSlots).sharedState store)
        EvmYul.Operation.CALLDATALOAD [EvmYul.UInt256.ofNat 4] =
      .ok (.Ok (initialState contract (YulTransaction.ofIR tx) storage
            observableSlots).sharedState store,
        [natToUInt256 arg]) := by
  exact
    primCall_calldataload4_initialState_arg0_ok_withStore
      fuel contract (YulTransaction.ofIR tx) storage observableSlots store arg
      rest (by simpa using hArgs)

@[simp] theorem primCall_shr_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (shift value : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.SHR [shift, value] =
      .ok (state, [EvmYul.UInt256.shiftRight value shift]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

@[simp] theorem primCall_add_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (left right : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.ADD [left, right] =
      .ok (state, [EvmYul.UInt256.add left right]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

theorem step_add_nil_invalid
    (state : EvmYul.Yul.State) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.ADD none) state [] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_add_singleton_invalid
    (state : EvmYul.Yul.State)
    (left : EvmYul.UInt256) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.ADD none) state [left] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_add_overarity_invalid
    (state : EvmYul.Yul.State)
    (left right extra : EvmYul.UInt256)
    (rest : List EvmYul.UInt256) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.ADD none) state
        (left :: right :: extra :: rest) =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

@[simp] theorem primCall_sub_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (left right : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.SUB [left, right] =
      .ok (state, [EvmYul.UInt256.sub left right]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

theorem step_sub_nil_invalid
    (state : EvmYul.Yul.State) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.SUB none) state [] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_sub_singleton_invalid
    (state : EvmYul.Yul.State)
    (left : EvmYul.UInt256) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.SUB none) state [left] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_sub_overarity_invalid
    (state : EvmYul.Yul.State)
    (left right extra : EvmYul.UInt256)
    (rest : List EvmYul.UInt256) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.SUB none) state
        (left :: right :: extra :: rest) =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

@[simp] theorem primCall_mul_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (left right : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.MUL [left, right] =
      .ok (state, [EvmYul.UInt256.mul left right]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

theorem step_mul_nil_invalid
    (state : EvmYul.Yul.State) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.MUL none) state [] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_mul_singleton_invalid
    (state : EvmYul.Yul.State)
    (left : EvmYul.UInt256) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.MUL none) state [left] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_mul_overarity_invalid
    (state : EvmYul.Yul.State)
    (left right extra : EvmYul.UInt256)
    (rest : List EvmYul.UInt256) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.MUL none) state
        (left :: right :: extra :: rest) =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

@[simp] theorem primCall_div_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (left right : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.DIV [left, right] =
      .ok (state, [EvmYul.UInt256.div left right]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall] <;> rfl

theorem step_div_nil_invalid
    (state : EvmYul.Yul.State) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.DIV none) state [] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_div_singleton_invalid
    (state : EvmYul.Yul.State)
    (left : EvmYul.UInt256) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.DIV none) state [left] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_div_overarity_invalid
    (state : EvmYul.Yul.State)
    (left right extra : EvmYul.UInt256)
    (rest : List EvmYul.UInt256) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.DIV none) state
        (left :: right :: extra :: rest) =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem primCall_div_nil_invalid
    (fuel : Nat)
    (state : EvmYul.Yul.State) :
    EvmYul.Yul.primCall (fuel + 1) state EvmYul.Operation.DIV [] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall, step_div_nil_invalid]
  | succ fuel' =>
      simp [EvmYul.Yul.primCall, step_div_nil_invalid]

theorem primCall_div_singleton_invalid
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (left : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state EvmYul.Operation.DIV [left] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall, step_div_singleton_invalid]
  | succ fuel' =>
      simp [EvmYul.Yul.primCall, step_div_singleton_invalid]

theorem primCall_div_overarity_invalid
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (left right extra : EvmYul.UInt256)
    (rest : List EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state EvmYul.Operation.DIV
        (left :: right :: extra :: rest) =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall, step_div_overarity_invalid]
  | succ fuel' =>
      simp [EvmYul.Yul.primCall, step_div_overarity_invalid]

@[simp] theorem primCall_mod_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (left right : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.MOD [left, right] =
      .ok (state, [EvmYul.UInt256.mod left right]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall] <;> rfl

theorem step_mod_nil_invalid
    (state : EvmYul.Yul.State) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.MOD none) state [] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_mod_singleton_invalid
    (state : EvmYul.Yul.State)
    (left : EvmYul.UInt256) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.MOD none) state [left] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_mod_overarity_invalid
    (state : EvmYul.Yul.State)
    (left right extra : EvmYul.UInt256)
    (rest : List EvmYul.UInt256) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.MOD none) state
        (left :: right :: extra :: rest) =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem primCall_mod_nil_invalid
    (fuel : Nat)
    (state : EvmYul.Yul.State) :
    EvmYul.Yul.primCall (fuel + 1) state EvmYul.Operation.MOD [] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  cases fuel <;> simp [EvmYul.Yul.primCall, step_mod_nil_invalid]

theorem primCall_mod_singleton_invalid
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (left : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state EvmYul.Operation.MOD [left] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  cases fuel <;> simp [EvmYul.Yul.primCall, step_mod_singleton_invalid]

theorem primCall_mod_overarity_invalid
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (left right extra : EvmYul.UInt256)
    (rest : List EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state EvmYul.Operation.MOD
        (left :: right :: extra :: rest) =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  cases fuel <;> simp [EvmYul.Yul.primCall, step_mod_overarity_invalid]

@[simp] theorem primCall_sdiv_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (left right : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.SDIV [left, right] =
      .ok (state, [EvmYul.UInt256.sdiv left right]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall] <;> rfl

@[simp] theorem primCall_smod_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (left right : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.SMOD [left, right] =
      .ok (state, [EvmYul.UInt256.smod left right]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall] <;> rfl

@[simp] theorem primCall_addmod_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (left right modulus : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.ADDMOD [left, right, modulus] =
      .ok (state, [EvmYul.UInt256.addMod left right modulus]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall] <;> rfl

@[simp] theorem primCall_mulmod_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (left right modulus : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.MULMOD [left, right, modulus] =
      .ok (state, [EvmYul.UInt256.mulMod left right modulus]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall] <;> rfl

@[simp] theorem primCall_exp_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (left right : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.EXP [left, right] =
      .ok (state, [EvmYul.UInt256.exp left right]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall] <;> rfl

@[simp] theorem primCall_signextend_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (byteIdx value : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.SIGNEXTEND [byteIdx, value] =
      .ok (state, [EvmYul.UInt256.signextend byteIdx value]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall] <;> rfl

/-- Native primitive execution of the generated dispatcher selector core:
    `calldataload(0)` reads the ABI selector word and `shr(224, ...)` decodes
    the normalized 32-bit selector used by the lowered native switch. -/
theorem primCall_calldataload0_then_shr224_initialState_selector_ok
    (loadFuel shrFuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat) :
    (do
      let (state', values) ←
        EvmYul.Yul.primCall (loadFuel + 1)
          (initialState contract tx storage observableSlots)
          EvmYul.Operation.CALLDATALOAD [EvmYul.UInt256.ofNat 0]
      match values with
      | [selectorWord] =>
          EvmYul.Yul.primCall (shrFuel + 1) state' EvmYul.Operation.SHR
            [EvmYul.UInt256.ofNat Compiler.Constants.selectorShift,
              selectorWord]
      | _ => .error EvmYul.Yul.Exception.InvalidArguments) =
      .ok (initialState contract tx storage observableSlots,
        [EvmYul.UInt256.ofNat
          (tx.functionSelector % Compiler.Constants.selectorModulus)]) := by
  have hInit :
      initialState contract tx storage observableSlots =
        (.Ok (initialState contract tx storage observableSlots).sharedState ∅ :
          EvmYul.Yul.State) := by
    simp [initialState, EvmYul.Yul.State.sharedState]
  rw [hInit]
  rw [primCall_calldataload_ok]
  change EvmYul.Yul.primCall (shrFuel + 1)
      (.Ok (initialState contract tx storage observableSlots).sharedState ∅)
      EvmYul.Operation.SHR
        [EvmYul.UInt256.ofNat Compiler.Constants.selectorShift,
        EvmYul.State.calldataload
          (EvmYul.Yul.State.Ok
            (initialState contract tx storage observableSlots).sharedState ∅).toState
          (EvmYul.UInt256.ofNat 0)] =
    .ok (.Ok (initialState contract tx storage observableSlots).sharedState ∅,
      [EvmYul.UInt256.ofNat
        (tx.functionSelector % Compiler.Constants.selectorModulus)])
  rw [primCall_shr_ok]
  rw [show
      EvmYul.UInt256.shiftRight
        (EvmYul.State.calldataload
          (EvmYul.Yul.State.Ok
            (initialState contract tx storage observableSlots).sharedState ∅).toState
          (EvmYul.UInt256.ofNat 0))
        (EvmYul.UInt256.ofNat Compiler.Constants.selectorShift) =
      EvmYul.UInt256.ofNat
        (tx.functionSelector % Compiler.Constants.selectorModulus) by
    simpa [initialState, EvmYul.Yul.State.toState] using
      initialState_selectorExpr_native_uint256 contract tx storage observableSlots]

@[simp] theorem primCall_eq_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (left right : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.EQ [left, right] =
      .ok (state, [EvmYul.UInt256.eq left right]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

theorem step_eq_nil_invalid
    (state : EvmYul.Yul.State) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.EQ none) state [] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_eq_singleton_invalid
    (state : EvmYul.Yul.State)
    (left : EvmYul.UInt256) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.EQ none) state [left] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_eq_overarity_invalid
    (state : EvmYul.Yul.State)
    (left right extra : EvmYul.UInt256)
    (rest : List EvmYul.UInt256) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.EQ none) state
        (left :: right :: extra :: rest) =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem primCall_eq_nil_invalid
    (fuel : Nat)
    (state : EvmYul.Yul.State) :
    EvmYul.Yul.primCall (fuel + 1) state EvmYul.Operation.EQ [] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  cases fuel <;> simp [EvmYul.Yul.primCall, step_eq_nil_invalid]

theorem primCall_eq_singleton_invalid
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (left : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state EvmYul.Operation.EQ [left] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  cases fuel <;> simp [EvmYul.Yul.primCall, step_eq_singleton_invalid]

theorem primCall_eq_overarity_invalid
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (left right extra : EvmYul.UInt256)
    (rest : List EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state EvmYul.Operation.EQ
        (left :: right :: extra :: rest) =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  cases fuel <;> simp [EvmYul.Yul.primCall, step_eq_overarity_invalid]

@[simp] theorem primCall_iszero_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (value : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.ISZERO [value] =
      .ok (state, [EvmYul.UInt256.isZero value]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

theorem step_iszero_nil_invalid
    (state : EvmYul.Yul.State) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.ISZERO none) state [] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_iszero_overarity_invalid
    (state : EvmYul.Yul.State)
    (value extra : EvmYul.UInt256)
    (rest : List EvmYul.UInt256) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.ISZERO none) state
        (value :: extra :: rest) =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem primCall_iszero_nil_invalid
    (fuel : Nat)
    (state : EvmYul.Yul.State) :
    EvmYul.Yul.primCall (fuel + 1) state EvmYul.Operation.ISZERO [] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  cases fuel <;> simp [EvmYul.Yul.primCall, step_iszero_nil_invalid]

theorem primCall_iszero_overarity_invalid
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (value extra : EvmYul.UInt256)
    (rest : List EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state EvmYul.Operation.ISZERO
        (value :: extra :: rest) =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  cases fuel <;> simp [EvmYul.Yul.primCall, step_iszero_overarity_invalid]

@[simp] theorem primCall_lt_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (left right : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.LT [left, right] =
      .ok (state, [EvmYul.UInt256.lt left right]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

theorem step_lt_nil_invalid
    (state : EvmYul.Yul.State) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.LT none) state [] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_lt_singleton_invalid
    (state : EvmYul.Yul.State)
    (left : EvmYul.UInt256) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.LT none) state [left] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_lt_overarity_invalid
    (state : EvmYul.Yul.State)
    (left right extra : EvmYul.UInt256)
    (rest : List EvmYul.UInt256) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.LT none) state
        (left :: right :: extra :: rest) =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem primCall_lt_nil_invalid
    (fuel : Nat)
    (state : EvmYul.Yul.State) :
    EvmYul.Yul.primCall (fuel + 1) state EvmYul.Operation.LT [] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  cases fuel <;> simp [EvmYul.Yul.primCall, step_lt_nil_invalid]

theorem primCall_lt_singleton_invalid
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (left : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state EvmYul.Operation.LT [left] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  cases fuel <;> simp [EvmYul.Yul.primCall, step_lt_singleton_invalid]

theorem primCall_lt_overarity_invalid
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (left right extra : EvmYul.UInt256)
    (rest : List EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state EvmYul.Operation.LT
        (left :: right :: extra :: rest) =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  cases fuel <;> simp [EvmYul.Yul.primCall, step_lt_overarity_invalid]

@[simp] theorem primCall_gt_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (left right : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.GT [left, right] =
      .ok (state, [EvmYul.UInt256.gt left right]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall] <;> rfl

theorem step_gt_nil_invalid
    (state : EvmYul.Yul.State) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.GT none) state [] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_gt_singleton_invalid
    (state : EvmYul.Yul.State)
    (left : EvmYul.UInt256) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.GT none) state [left] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_gt_overarity_invalid
    (state : EvmYul.Yul.State)
    (left right extra : EvmYul.UInt256)
    (rest : List EvmYul.UInt256) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.GT none) state
        (left :: right :: extra :: rest) =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem primCall_gt_nil_invalid
    (fuel : Nat)
    (state : EvmYul.Yul.State) :
    EvmYul.Yul.primCall (fuel + 1) state EvmYul.Operation.GT [] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  cases fuel <;> simp [EvmYul.Yul.primCall, step_gt_nil_invalid]

theorem primCall_gt_singleton_invalid
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (left : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state EvmYul.Operation.GT [left] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  cases fuel <;> simp [EvmYul.Yul.primCall, step_gt_singleton_invalid]

theorem primCall_gt_overarity_invalid
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (left right extra : EvmYul.UInt256)
    (rest : List EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state EvmYul.Operation.GT
        (left :: right :: extra :: rest) =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  cases fuel <;> simp [EvmYul.Yul.primCall, step_gt_overarity_invalid]

@[simp] theorem primCall_slt_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (left right : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.SLT [left, right] =
      .ok (state, [EvmYul.UInt256.slt left right]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall] <;> rfl

@[simp] theorem primCall_sgt_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (left right : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.SGT [left, right] =
      .ok (state, [EvmYul.UInt256.sgt left right]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall] <;> rfl

@[simp] theorem primCall_calldatasize_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.CALLDATASIZE [] =
      .ok (state, [EvmYul.UInt256.ofNat state.executionEnv.calldata.size]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

@[simp] theorem primCall_callvalue_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.CALLVALUE [] =
      .ok (state, [state.executionEnv.weiValue]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

@[simp] theorem primCall_address_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.ADDRESS [] =
      .ok (state, [EvmYul.UInt256.ofNat state.executionEnv.codeOwner.val]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

@[simp] theorem primCall_balance_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (account : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.BALANCE [account] =
      let (state', value) := state.toState.balance account
      .ok (state.setSharedState { state.toSharedState with toState := state' },
        [value]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

@[simp] theorem primCall_origin_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.ORIGIN [] =
      .ok (state, [EvmYul.UInt256.ofNat state.executionEnv.sender.val]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

@[simp] theorem primCall_caller_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.CALLER [] =
      .ok (state, [EvmYul.UInt256.ofNat state.executionEnv.source.val]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

@[simp] theorem primCall_timestamp_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.TIMESTAMP [] =
      .ok (state, [state.toState.timeStamp]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

@[simp] theorem primCall_number_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.NUMBER [] =
      .ok (state, [state.toState.number]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

@[simp] theorem primCall_chainid_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.CHAINID [] =
      .ok (state, [state.toState.chainId]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

@[simp] theorem primCall_blobbasefee_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.BLOBBASEFEE [] =
      .ok (state, [state.executionEnv.getBlobGasprice]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

theorem primCall_calldatasize_any_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (values : List EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.CALLDATASIZE values =
      .ok (state, [EvmYul.UInt256.ofNat state.executionEnv.calldata.size]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall, step_calldatasize_any]

theorem primCall_callvalue_any_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (values : List EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.CALLVALUE values =
      .ok (state, [state.executionEnv.weiValue]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall, step_callvalue_any]

theorem primCall_address_any_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (values : List EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state EvmYul.Operation.ADDRESS values =
      .ok (state, [EvmYul.UInt256.ofNat state.executionEnv.codeOwner.val]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall, step_address_any]

theorem primCall_origin_any_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (values : List EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state EvmYul.Operation.ORIGIN values =
      .ok (state, [EvmYul.UInt256.ofNat state.executionEnv.sender.val]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall, step_origin_any]

theorem primCall_caller_any_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (values : List EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state EvmYul.Operation.CALLER values =
      .ok (state, [EvmYul.UInt256.ofNat state.executionEnv.source.val]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall, step_caller_any]

theorem primCall_timestamp_any_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (values : List EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state EvmYul.Operation.TIMESTAMP values =
      .ok (state, [state.toState.timeStamp]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall, step_timestamp_any]

theorem primCall_number_any_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (values : List EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state EvmYul.Operation.NUMBER values =
      .ok (state, [state.toState.number]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall, step_number_any]

theorem primCall_chainid_any_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (values : List EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state EvmYul.Operation.CHAINID values =
      .ok (state, [state.toState.chainId]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall, step_chainid_any]

theorem primCall_blobbasefee_any_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (values : List EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.BLOBBASEFEE values =
      .ok (state, [state.executionEnv.getBlobGasprice]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall, step_blobbasefee_any]

@[simp] theorem primCall_gasprice_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.GASPRICE [] =
      .ok (state, [EvmYul.UInt256.ofNat state.executionEnv.gasPrice]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

@[simp] theorem primCall_coinbase_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.COINBASE [] =
      .ok (state, [EvmYul.UInt256.ofNat state.toState.coinBase.val]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

@[simp] theorem primCall_gaslimit_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.GASLIMIT [] =
      .ok (state, [state.toState.gasLimit]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

@[simp] theorem primCall_selfbalance_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.SELFBALANCE [] =
      .ok (state, [state.toState.selfbalance]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

@[simp] theorem primCall_and_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (left right : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.AND [left, right] =
      .ok (state, [EvmYul.UInt256.land left right]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

@[simp] theorem primCall_or_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (left right : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.OR [left, right] =
      .ok (state, [EvmYul.UInt256.lor left right]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall] <;> rfl

@[simp] theorem primCall_xor_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (left right : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.XOR [left, right] =
      .ok (state, [EvmYul.UInt256.xor left right]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall] <;> rfl

@[simp] theorem primCall_not_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (value : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.NOT [value] =
      .ok (state, [EvmYul.UInt256.lnot value]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall] <;> rfl

theorem step_not_nil_invalid
    (state : EvmYul.Yul.State) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.NOT none) state [] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_not_overarity_invalid
    (state : EvmYul.Yul.State)
    (value extra : EvmYul.UInt256)
    (rest : List EvmYul.UInt256) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.NOT none) state
        (value :: extra :: rest) =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem primCall_not_nil_invalid
    (fuel : Nat)
    (state : EvmYul.Yul.State) :
    EvmYul.Yul.primCall (fuel + 1) state EvmYul.Operation.NOT [] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  cases fuel <;> simp [EvmYul.Yul.primCall, step_not_nil_invalid]

theorem primCall_not_overarity_invalid
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (value extra : EvmYul.UInt256)
    (rest : List EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state EvmYul.Operation.NOT
        (value :: extra :: rest) =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  cases fuel <;> simp [EvmYul.Yul.primCall, step_not_overarity_invalid]

@[simp] theorem primCall_shl_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (shift value : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.SHL [shift, value] =
      .ok (state, [EvmYul.UInt256.shiftLeft value shift]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall] <;> rfl

@[simp] theorem primCall_byte_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (index value : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.BYTE [index, value] =
      .ok (state, [EvmYul.UInt256.byteAt index value]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall] <;> rfl

@[simp] theorem primCall_sar_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (shift value : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.SAR [shift, value] =
      .ok (state, [EvmYul.UInt256.sar shift value]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall] <;> rfl

theorem step_sdiv_nil_invalid
    (state : EvmYul.Yul.State) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.SDIV none) state [] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_sdiv_singleton_invalid
    (state : EvmYul.Yul.State)
    (left : EvmYul.UInt256) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.SDIV none) state [left] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_sdiv_overarity_invalid
    (state : EvmYul.Yul.State)
    (left right extra : EvmYul.UInt256)
    (rest : List EvmYul.UInt256) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.SDIV none) state
        (left :: right :: extra :: rest) =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_smod_nil_invalid
    (state : EvmYul.Yul.State) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.SMOD none) state [] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_smod_singleton_invalid
    (state : EvmYul.Yul.State)
    (left : EvmYul.UInt256) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.SMOD none) state [left] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_smod_overarity_invalid
    (state : EvmYul.Yul.State)
    (left right extra : EvmYul.UInt256)
    (rest : List EvmYul.UInt256) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.SMOD none) state
        (left :: right :: extra :: rest) =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_exp_nil_invalid
    (state : EvmYul.Yul.State) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.EXP none) state [] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_exp_singleton_invalid
    (state : EvmYul.Yul.State)
    (left : EvmYul.UInt256) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.EXP none) state [left] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_exp_overarity_invalid
    (state : EvmYul.Yul.State)
    (left right extra : EvmYul.UInt256)
    (rest : List EvmYul.UInt256) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.EXP none) state
        (left :: right :: extra :: rest) =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_signextend_nil_invalid
    (state : EvmYul.Yul.State) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.SIGNEXTEND none) state [] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_signextend_singleton_invalid
    (state : EvmYul.Yul.State)
    (byteIdx : EvmYul.UInt256) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.SIGNEXTEND none) state [byteIdx] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_signextend_overarity_invalid
    (state : EvmYul.Yul.State)
    (byteIdx value extra : EvmYul.UInt256)
    (rest : List EvmYul.UInt256) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.SIGNEXTEND none) state
        (byteIdx :: value :: extra :: rest) =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_slt_nil_invalid
    (state : EvmYul.Yul.State) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.SLT none) state [] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_slt_singleton_invalid
    (state : EvmYul.Yul.State)
    (left : EvmYul.UInt256) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.SLT none) state [left] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_slt_overarity_invalid
    (state : EvmYul.Yul.State)
    (left right extra : EvmYul.UInt256)
    (rest : List EvmYul.UInt256) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.SLT none) state
        (left :: right :: extra :: rest) =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_sgt_nil_invalid
    (state : EvmYul.Yul.State) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.SGT none) state [] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_sgt_singleton_invalid
    (state : EvmYul.Yul.State)
    (left : EvmYul.UInt256) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.SGT none) state [left] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_sgt_overarity_invalid
    (state : EvmYul.Yul.State)
    (left right extra : EvmYul.UInt256)
    (rest : List EvmYul.UInt256) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.SGT none) state
        (left :: right :: extra :: rest) =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_and_nil_invalid
    (state : EvmYul.Yul.State) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.AND none) state [] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_and_singleton_invalid
    (state : EvmYul.Yul.State)
    (left : EvmYul.UInt256) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.AND none) state [left] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_and_overarity_invalid
    (state : EvmYul.Yul.State)
    (left right extra : EvmYul.UInt256)
    (rest : List EvmYul.UInt256) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.AND none) state
        (left :: right :: extra :: rest) =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_or_nil_invalid
    (state : EvmYul.Yul.State) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.OR none) state [] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_or_singleton_invalid
    (state : EvmYul.Yul.State)
    (left : EvmYul.UInt256) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.OR none) state [left] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_or_overarity_invalid
    (state : EvmYul.Yul.State)
    (left right extra : EvmYul.UInt256)
    (rest : List EvmYul.UInt256) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.OR none) state
        (left :: right :: extra :: rest) =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_xor_nil_invalid
    (state : EvmYul.Yul.State) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.XOR none) state [] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_xor_singleton_invalid
    (state : EvmYul.Yul.State)
    (left : EvmYul.UInt256) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.XOR none) state [left] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_xor_overarity_invalid
    (state : EvmYul.Yul.State)
    (left right extra : EvmYul.UInt256)
    (rest : List EvmYul.UInt256) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.XOR none) state
        (left :: right :: extra :: rest) =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_shl_nil_invalid
    (state : EvmYul.Yul.State) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.SHL none) state [] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_shl_singleton_invalid
    (state : EvmYul.Yul.State)
    (shift : EvmYul.UInt256) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.SHL none) state [shift] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_shl_overarity_invalid
    (state : EvmYul.Yul.State)
    (shift value extra : EvmYul.UInt256)
    (rest : List EvmYul.UInt256) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.SHL none) state
        (shift :: value :: extra :: rest) =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_shr_nil_invalid
    (state : EvmYul.Yul.State) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.SHR none) state [] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_shr_singleton_invalid
    (state : EvmYul.Yul.State)
    (shift : EvmYul.UInt256) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.SHR none) state [shift] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_shr_overarity_invalid
    (state : EvmYul.Yul.State)
    (shift value extra : EvmYul.UInt256)
    (rest : List EvmYul.UInt256) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.SHR none) state
        (shift :: value :: extra :: rest) =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_byte_nil_invalid
    (state : EvmYul.Yul.State) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.BYTE none) state [] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_byte_singleton_invalid
    (state : EvmYul.Yul.State)
    (index : EvmYul.UInt256) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.BYTE none) state [index] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_byte_overarity_invalid
    (state : EvmYul.Yul.State)
    (index value extra : EvmYul.UInt256)
    (rest : List EvmYul.UInt256) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.BYTE none) state
        (index :: value :: extra :: rest) =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_sar_nil_invalid
    (state : EvmYul.Yul.State) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.SAR none) state [] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_sar_singleton_invalid
    (state : EvmYul.Yul.State)
    (shift : EvmYul.UInt256) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.SAR none) state [shift] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_sar_overarity_invalid
    (state : EvmYul.Yul.State)
    (shift value extra : EvmYul.UInt256)
    (rest : List EvmYul.UInt256) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.SAR none) state
        (shift :: value :: extra :: rest) =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_sload_nil_invalid
    (state : EvmYul.Yul.State) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.SLOAD none) state [] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_sload_overarity_invalid
    (state : EvmYul.Yul.State)
    (slot extra : EvmYul.UInt256)
    (rest : List EvmYul.UInt256) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.SLOAD none) state
        (slot :: extra :: rest) =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_calldataload_nil_invalid
    (state : EvmYul.Yul.State) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.CALLDATALOAD none) state [] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_calldataload_overarity_invalid
    (state : EvmYul.Yul.State)
    (offset extra : EvmYul.UInt256)
    (rest : List EvmYul.UInt256) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.CALLDATALOAD none) state
        (offset :: extra :: rest) =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_mload_nil_invalid
    (state : EvmYul.Yul.State) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.MLOAD none) state [] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_mload_overarity_invalid
    (state : EvmYul.Yul.State)
    (offset extra : EvmYul.UInt256)
    (rest : List EvmYul.UInt256) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.MLOAD none) state
        (offset :: extra :: rest) =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_tload_nil_invalid
    (state : EvmYul.Yul.State) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.TLOAD none) state [] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_tload_overarity_invalid
    (state : EvmYul.Yul.State)
    (slot extra : EvmYul.UInt256)
    (rest : List EvmYul.UInt256) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.TLOAD none) state
        (slot :: extra :: rest) =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_keccak256_nil_invalid
    (state : EvmYul.Yul.State) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.KECCAK256 none) state [] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_keccak256_singleton_invalid
    (state : EvmYul.Yul.State)
    (offset : EvmYul.UInt256) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.KECCAK256 none) state [offset] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_keccak256_overarity_invalid
    (state : EvmYul.Yul.State)
    (offset size extra : EvmYul.UInt256)
    (rest : List EvmYul.UInt256) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.KECCAK256 none) state
        (offset :: size :: extra :: rest) =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_addmod_nil_invalid
    (state : EvmYul.Yul.State) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.ADDMOD none) state [] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_addmod_singleton_invalid
    (state : EvmYul.Yul.State)
    (left : EvmYul.UInt256) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.ADDMOD none) state [left] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_addmod_pair_invalid
    (state : EvmYul.Yul.State)
    (left right : EvmYul.UInt256) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.ADDMOD none) state [left, right] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_addmod_overarity_invalid
    (state : EvmYul.Yul.State)
    (left right modulus extra : EvmYul.UInt256)
    (rest : List EvmYul.UInt256) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.ADDMOD none) state
        (left :: right :: modulus :: extra :: rest) =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_mulmod_nil_invalid
    (state : EvmYul.Yul.State) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.MULMOD none) state [] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_mulmod_singleton_invalid
    (state : EvmYul.Yul.State)
    (left : EvmYul.UInt256) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.MULMOD none) state [left] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_mulmod_pair_invalid
    (state : EvmYul.Yul.State)
    (left right : EvmYul.UInt256) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.MULMOD none) state [left, right] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

theorem step_mulmod_overarity_invalid
    (state : EvmYul.Yul.State)
    (left right modulus extra : EvmYul.UInt256)
    (rest : List EvmYul.UInt256) :
    (EvmYul.step (τ := .Yul) EvmYul.Operation.MULMOD none) state
        (left :: right :: modulus :: extra :: rest) =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  rfl

@[simp] theorem primCall_mstore_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (offset value : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.MSTORE [offset, value] =
      .ok (state.setMachineState (state.toMachineState.mstore offset value),
        []) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

theorem primCall_mstore_nil_invalid
    (fuel : Nat)
    (state : EvmYul.Yul.State) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.MSTORE [] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  cases fuel <;> simp [EvmYul.Yul.primCall, step_mstore_nil_invalid]

theorem primCall_mstore_singleton_invalid
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (offset : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.MSTORE [offset] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  cases fuel <;> simp [EvmYul.Yul.primCall, step_mstore_singleton_invalid]

theorem primCall_mstore_overarity_invalid
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (offset value extra : EvmYul.UInt256)
    (rest : List EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.MSTORE (offset :: value :: extra :: rest) =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  cases fuel <;> simp [EvmYul.Yul.primCall, step_mstore_overarity_invalid]

@[simp] theorem primCall_mstore8_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (offset value : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.MSTORE8 [offset, value] =
      .ok (state.setMachineState (state.toMachineState.mstore8 offset value),
        []) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

theorem primCall_mstore8_nil_invalid
    (fuel : Nat)
    (state : EvmYul.Yul.State) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.MSTORE8 [] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  cases fuel <;> simp [EvmYul.Yul.primCall, step_mstore8_nil_invalid]

theorem primCall_mstore8_singleton_invalid
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (offset : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.MSTORE8 [offset] =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  cases fuel <;> simp [EvmYul.Yul.primCall, step_mstore8_singleton_invalid]

theorem primCall_mstore8_overarity_invalid
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (offset value extra : EvmYul.UInt256)
    (rest : List EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.MSTORE8 (offset :: value :: extra :: rest) =
      Except.error EvmYul.Yul.Exception.InvalidArguments := by
  cases fuel <;> simp [EvmYul.Yul.primCall, step_mstore8_overarity_invalid]

@[simp] theorem primCall_sload_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (slot : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.SLOAD [slot] =
      let (state', value) := state.toState.sload slot
      .ok (state.setSharedState { state.toSharedState with toState := state' },
        [value]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

@[simp] theorem primCall_mload_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (offset : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.MLOAD [offset] =
      let (value, machineState') := state.toSharedState.toMachineState.mload offset
      .ok (state.setMachineState machineState', [value]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

@[simp] theorem primCall_keccak256_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (offset size : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.KECCAK256 [offset, size] =
      let (value, machineState') := state.toMachineState.keccak256 offset size
      .ok (state.setMachineState machineState', [value]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

set_option linter.unusedSimpArgs false in
theorem nativeMappingSlotFunctionDefinition_exec_revivable
    (fuel : Nat)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (calleeState : EvmYul.Yul.State)
    (hExec :
      EvmYul.Yul.exec fuel (.Block nativeMappingSlotFunctionDefinition.body)
        codeOverride (EvmYul.Yul.State.Ok shared store) = .ok calleeState) :
    ∃ shared' store',
      calleeState.reviveJump = EvmYul.Yul.State.Ok shared' store' := by
  rw [nativeMappingSlotFunctionDefinition_body] at hExec
  unfold nativeMappingSlotFunctionBody at hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.exec] at hExec
  | succ f1 =>
      cases f1 with
      | zero =>
          simp [EvmYul.Yul.exec] at hExec
      | succ f2 =>
          cases f2 with
          | zero =>
              simp [EvmYul.Yul.exec, EvmYul.Yul.execPrimCall,
                EvmYul.Yul.evalArgs, EvmYul.Yul.evalTail, EvmYul.Yul.eval,
                EvmYul.Yul.reverse'] at hExec
          | succ f3 =>
              cases f3 with
              | zero =>
                  simp [EvmYul.Yul.exec, EvmYul.Yul.execPrimCall,
                    EvmYul.Yul.evalArgs, EvmYul.Yul.evalTail, EvmYul.Yul.eval,
                    EvmYul.Yul.reverse'] at hExec
              | succ f4 =>
                  cases f4 with
                  | zero =>
                      simp [EvmYul.Yul.exec, EvmYul.Yul.execPrimCall,
                        EvmYul.Yul.evalArgs, EvmYul.Yul.evalTail,
                        EvmYul.Yul.eval, EvmYul.Yul.cons',
                        EvmYul.Yul.reverse'] at hExec
                  | succ f5 =>
                      cases f5 with
                      | zero =>
                          simp [EvmYul.Yul.exec, EvmYul.Yul.execPrimCall,
                            EvmYul.Yul.evalArgs, EvmYul.Yul.evalTail,
                            EvmYul.Yul.eval, EvmYul.Yul.cons',
                            EvmYul.Yul.reverse'] at hExec
                      | succ f6 =>
                          cases f6 with
                          | zero =>
                              simp [EvmYul.Yul.exec, EvmYul.Yul.execPrimCall,
                                EvmYul.Yul.evalArgs, EvmYul.Yul.evalTail,
                                EvmYul.Yul.eval, EvmYul.Yul.cons',
                                EvmYul.Yul.reverse'] at hExec
                          | succ f7 =>
                              cases f7 with
                              | zero =>
                                  simp [EvmYul.Yul.exec, EvmYul.Yul.execPrimCall,
                                    EvmYul.Yul.evalArgs, EvmYul.Yul.evalTail,
                                    EvmYul.Yul.eval, EvmYul.Yul.cons',
                                    EvmYul.Yul.reverse', EvmYul.Yul.multifill']
                                    at hExec
                              | succ f8 =>
                                  cases f8 with
                                  | zero =>
                                      simp [EvmYul.Yul.exec,
                                        EvmYul.Yul.execPrimCall,
                                        EvmYul.Yul.evalArgs,
                                        EvmYul.Yul.evalTail, EvmYul.Yul.eval,
                                        EvmYul.Yul.cons', EvmYul.Yul.reverse',
                                        EvmYul.Yul.multifill'] at hExec
                                  | succ f9 =>
                                      simp [EvmYul.Yul.exec,
                                        EvmYul.Yul.execPrimCall,
                                        EvmYul.Yul.evalArgs,
                                        EvmYul.Yul.evalTail, EvmYul.Yul.eval,
                                        EvmYul.Yul.cons', EvmYul.Yul.reverse',
                                        EvmYul.Yul.multifill',
                                        EvmYul.Yul.State.multifill,
                                        EvmYul.Yul.State.setMachineState,
                                        EvmYul.Yul.State.lookup!,
                                        EvmYul.Yul.State.insert,
                                        EvmYul.Yul.State.reviveJump] at hExec ⊢
                                      subst calleeState
                                      simp [EvmYul.Yul.State.reviveJump]

@[simp] theorem primCall_log0_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (offset size : EvmYul.UInt256)
    (hPerm : state.executionEnv.perm = true) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.LOG0 [offset, size] =
      .ok (state.setSharedState
        (EvmYul.SharedState.logOp offset size #[] state.toSharedState), []) := by
  cases fuel <;> simp [EvmYul.Yul.primCall, hPerm]

@[simp] theorem primCall_log1_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (offset size topic0 : EvmYul.UInt256)
    (hPerm : state.executionEnv.perm = true) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.LOG1 [offset, size, topic0] =
      .ok (state.setSharedState
        (EvmYul.SharedState.logOp offset size #[topic0] state.toSharedState), []) := by
  cases fuel <;> simp [EvmYul.Yul.primCall, hPerm]

@[simp] theorem primCall_log2_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (offset size topic0 topic1 : EvmYul.UInt256)
    (hPerm : state.executionEnv.perm = true) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.LOG2 [offset, size, topic0, topic1] =
      .ok (state.setSharedState
        (EvmYul.SharedState.logOp offset size #[topic0, topic1]
          state.toSharedState), []) := by
  cases fuel <;> simp [EvmYul.Yul.primCall, hPerm]

@[simp] theorem primCall_log3_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (offset size topic0 topic1 topic2 : EvmYul.UInt256)
    (hPerm : state.executionEnv.perm = true) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.LOG3 [offset, size, topic0, topic1, topic2] =
      .ok (state.setSharedState
        (EvmYul.SharedState.logOp offset size #[topic0, topic1, topic2]
          state.toSharedState), []) := by
  cases fuel <;> simp [EvmYul.Yul.primCall, hPerm]

@[simp] theorem primCall_log4_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (offset size topic0 topic1 topic2 topic3 : EvmYul.UInt256)
    (hPerm : state.executionEnv.perm = true) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.LOG4 [offset, size, topic0, topic1, topic2, topic3] =
      .ok (state.setSharedState
        (EvmYul.SharedState.logOp offset size #[topic0, topic1, topic2, topic3]
          state.toSharedState), []) := by
  cases fuel <;> simp [EvmYul.Yul.primCall, hPerm]

@[simp] theorem primCall_sstore_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (slot value : EvmYul.UInt256)
    (hPerm : state.executionEnv.perm = true) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.SSTORE [slot, value] =
      .ok (state.setState (state.toState.sstore slot value), []) := by
  cases fuel <;> simp [EvmYul.Yul.primCall, hPerm]

@[simp] theorem primCall_tload_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (slot : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.TLOAD [slot] =
      let (state', value) := state.toState.tload slot
      .ok (state.setSharedState { state.toSharedState with toState := state' },
        [value]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

@[simp] theorem primCall_tstore_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (slot value : EvmYul.UInt256)
    (hPerm : state.executionEnv.perm = true) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.TSTORE [slot, value] =
      .ok (state.setState (state.toState.tstore slot value), []) := by
  cases fuel <;> simp [EvmYul.Yul.primCall, hPerm]

@[simp] theorem primCall_msize_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State) :
    EvmYul.Yul.primCall (fuel + 1) state EvmYul.Operation.MSIZE [] =
      .ok (state, [state.toMachineState.msize]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

@[simp] theorem primCall_gas_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State) :
    EvmYul.Yul.primCall (fuel + 1) state EvmYul.Operation.GAS [] =
      .ok (state, [state.toMachineState.gas]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

@[simp] theorem primCall_returndatasize_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State) :
    EvmYul.Yul.primCall (fuel + 1) state EvmYul.Operation.RETURNDATASIZE [] =
      .ok (state, [state.toMachineState.returndatasize]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

theorem primCall_returndatasize_any_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (values : List EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.RETURNDATASIZE values =
      .ok (state, [state.toMachineState.returndatasize]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall, step_returndatasize_any]

@[simp] theorem primCall_calldatacopy_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (mstart datastart size : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.CALLDATACOPY [mstart, datastart, size] =
      .ok (state.setSharedState
        (state.toSharedState.calldatacopy mstart datastart size), []) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

@[simp] theorem primCall_returndatacopy_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (mstart rstart size : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.RETURNDATACOPY [mstart, rstart, size] =
      .ok (state.setMachineState
        (state.toSharedState.toMachineState.returndatacopy mstart rstart size),
        []) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

@[simp] theorem primCall_pop_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (value : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state EvmYul.Operation.POP [value] =
      .ok (state, []) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

@[simp] theorem primCall_stop_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State) :
    EvmYul.Yul.primCall (fuel + 1) state EvmYul.Operation.STOP [] =
      .error (EvmYul.Yul.Exception.YulHalt state ⟨0⟩) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

@[simp] theorem primCall_return_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (offset size : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.RETURN [offset, size] =
      match EvmYul.Yul.binaryMachineStateOp EvmYul.MachineState.evmReturn
          state [offset, size] with
      | .error e => .error e
      | .ok (s, value) =>
          .error (EvmYul.Yul.Exception.YulHalt s (value.getD ⟨1⟩)) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]
  all_goals
    cases EvmYul.Yul.binaryMachineStateOp EvmYul.MachineState.evmReturn
      state [offset, size] <;> rfl

@[simp] theorem primCall_revert_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (offset size : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.REVERT [offset, size] =
      match EvmYul.Yul.binaryMachineStateOp EvmYul.MachineState.evmRevert
          state [offset, size] with
      | .error e => .error e
      | .ok (_, _) => .error EvmYul.Yul.Exception.Revert := by
  cases fuel <;> simp [EvmYul.Yul.primCall]
  all_goals
    cases EvmYul.Yul.binaryMachineStateOp EvmYul.MachineState.evmRevert
      state [offset, size] <;> rfl

/-- The compiler's proof-side `revert(0, 0)` default lowers to the concrete
    native statement used by the selector-miss execution lemma. -/
theorem lowerStmtsNative_revert_zero_zero :
    Backends.lowerStmtsNative
      [YulStmt.exprStmt (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])] =
      .ok [nativeRevertZeroZeroStmt] := by
  simp only [Backends.lowerStmtsNative,
    lowerStmtsNativeWithSwitchIds_revert_zero_zero,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Native execution of the generated selector-miss body `revert(0, 0)`.
    This is the concrete primitive halt used by the dispatcher default path. -/
theorem exec_revert_zero_zero_error
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) :
    EvmYul.Yul.exec (fuel + 6)
      nativeRevertZeroZeroStmt codeOverride state =
      .error EvmYul.Yul.Exception.Revert := by
  cases fuel <;>
    simp [nativeRevertZeroZeroStmt, EvmYul.Yul.exec, EvmYul.Yul.eval, EvmYul.Yul.evalArgs,
      EvmYul.Yul.evalTail, EvmYul.Yul.execPrimCall, EvmYul.Yul.reverse',
      EvmYul.Yul.cons', EvmYul.Yul.multifill',
      EvmYul.Yul.binaryMachineStateOp]

theorem exec_expr_prim_ok
    (fuel : Nat)
    (state next : EvmYul.Yul.State)
    (op : EvmYul.Operation .Yul)
    (args : List EvmYul.Yul.Ast.Expr)
    (values : List EvmYul.Yul.Ast.Literal)
    (hEval :
      EvmYul.Yul.evalArgs fuel args.reverse none state =
        .ok (state, values.reverse))
    (hPrim :
      EvmYul.Yul.primCall fuel state op values = .ok (next, [])) :
    EvmYul.Yul.exec (fuel + 1)
        (.ExprStmtCall (.Call (Sum.inl op) args)) none state =
      .ok next := by
  simp [EvmYul.Yul.exec]
  rw [hEval]
  simp [EvmYul.Yul.reverse', EvmYul.Yul.execPrimCall, hPrim,
    EvmYul.Yul.multifill']
  cases next <;> rfl

theorem exec_let_prim_one_ok
    (fuel : Nat)
    (state next : EvmYul.Yul.State)
    (op : EvmYul.Operation .Yul)
    (name : EvmYul.Identifier)
    (args : List EvmYul.Yul.Ast.Expr)
    (values : List EvmYul.Yul.Ast.Literal)
    (value : EvmYul.Yul.Ast.Literal)
    (hEval :
      EvmYul.Yul.evalArgs fuel args.reverse none state =
        .ok (state, values.reverse))
    (hPrim :
      EvmYul.Yul.primCall fuel state op values = .ok (next, [value])) :
    EvmYul.Yul.exec (fuel + 1)
        (.Let [name] (some (.Call (Sum.inl op) args))) none state =
      .ok (next.insert name value) := by
  simp [EvmYul.Yul.exec]
  rw [hEval]
  simp [EvmYul.Yul.reverse', EvmYul.Yul.execPrimCall, hPrim,
    EvmYul.Yul.multifill']
  cases next <;> rfl


end Compiler.Proofs.YulGeneration.Backends.Native

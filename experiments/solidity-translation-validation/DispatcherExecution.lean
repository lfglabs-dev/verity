import TranslationValidationDispatcherNodes
import TranslationValidationReturnObservation

set_option backward.isDefEq.respectTransparency false
namespace SolidityTranslationValidation.AstBridge.Dispatcher
open EvmYul Yul
open Compiler.Proofs.YulGeneration.Backends.Native
open Compiler.Proofs.YulGeneration.Backends.StateBridge
open Compiler.Proofs.YulGeneration
open Compiler.Proofs.IRGeneration

theorem exec_load_x (fuel : Nat) (shared : SharedState .Yul) (store : Yul.VarStore)
    (code : Option Yul.Ast.YulContract) :
    Yul.exec (fuel + 10) capturedLoadX code (.Ok shared store) =
      .ok ((Yul.State.Ok shared store).insert "value"
        (EvmYul.State.calldataload shared.toState (UInt256.ofNat 4))) := by
  simp [capturedLoadX, Yul.exec, Yul.eval, Yul.evalArgs, Yul.evalTail,
    Yul.execPrimCall, Yul.reverse', Yul.cons', Yul.multifill']
  rfl

theorem exec_load_y (fuel : Nat) (shared : SharedState .Yul) (store : Yul.VarStore)
    (code : Option Yul.Ast.YulContract) :
    Yul.exec (fuel + 10) capturedLoadY code (.Ok shared store) =
      .ok ((Yul.State.Ok shared store).insert "value_1"
        (EvmYul.State.calldataload shared.toState (UInt256.ofNat 36))) := by
  simp [capturedLoadY, Yul.exec, Yul.eval, Yul.evalArgs, Yul.evalTail,
    Yul.execPrimCall, Yul.reverse', Yul.cons', Yul.multifill']
  rfl

theorem exec_load_d (fuel : Nat) (shared : SharedState .Yul) (store : Yul.VarStore)
    (code : Option Yul.Ast.YulContract) :
    Yul.exec (fuel + 10) capturedLoadD code (.Ok shared store) =
      .ok ((Yul.State.Ok shared store).insert "value_2"
        (EvmYul.State.calldataload shared.toState (UInt256.ofNat 68))) := by
  simp [capturedLoadD, Yul.exec, Yul.eval, Yul.evalArgs, Yul.evalTail,
    Yul.execPrimCall, Yul.reverse', Yul.cons', Yul.multifill']
  rfl

def loadedState (shared : SharedState .Yul) (store : Yul.VarStore) : Yul.State :=
  ((Yul.State.Ok shared store).insert "value" (EvmYul.State.calldataload shared.toState (UInt256.ofNat 4))).insert
    "value_1" (EvmYul.State.calldataload shared.toState (UInt256.ofNat 36)) |>.insert
    "value_2" (EvmYul.State.calldataload shared.toState (UInt256.ofNat 68))

/-- Actual three contiguous ABI declarations, with an arbitrary native continuation. -/
theorem captured_loads_continuation (fuel : Nat) (shared : SharedState .Yul) (store : Yul.VarStore)
    (code : Option Yul.Ast.YulContract) (rest : List Yul.Ast.Stmt) :
    Yul.exec (fuel + 20) (.Block ([capturedLoadX, capturedLoadY, capturedLoadD] ++ rest)) code (.Ok shared store) =
      Yul.exec (fuel + 17) (.Block rest) code (loadedState shared store) := by
  simp only [List.cons_append, List.nil_append]
  rw [exec_block_cons_ok_eq (fuel + 19) _ _ _ _ _ (exec_load_x (fuel + 9) shared store code)]
  simp only [Yul.State.insert]
  rw [exec_block_cons_ok_eq (fuel + 18) _ _ _ _ _ (exec_load_y (fuel + 8) shared _ code)]
  simp only [Yul.State.insert]
  rw [exec_block_cons_ok_eq (fuel + 17) _ _ _ _ _ (exec_load_d (fuel + 7) shared _ code)]
  rfl

/-- The bound ABI words and untouched output pointer in the actual post-load state. -/
theorem loaded_bindings (shared : SharedState .Yul) (store : Yul.VarStore) :
    variableValue (loadedState shared store) "value" = EvmYul.State.calldataload shared.toState (UInt256.ofNat 4) ∧
    variableValue (loadedState shared store) "value_1" = EvmYul.State.calldataload shared.toState (UInt256.ofNat 36) ∧
    variableValue (loadedState shared store) "value_2" = EvmYul.State.calldataload shared.toState (UInt256.ofNat 68) ∧
    variableValue (loadedState shared store) "_1" = variableValue (.Ok shared store) "_1" := by
  simp only [loadedState]
  simp only [variableValue_insert_other _ _ _ _ (by decide : "value" ≠ "value_2"),
    variableValue_insert_other _ _ _ _ (by decide : "value" ≠ "value_1"),
    variableValue_insert_other _ _ _ _ (by decide : "value_1" ≠ "value_2"),
    variableValue_insert_other _ _ _ _ (by decide : "_1" ≠ "value_2"),
    variableValue_insert_other _ _ _ _ (by decide : "_1" ≠ "value_1"),
    variableValue_insert_other _ _ _ _ (by decide : "_1" ≠ "value")]
  refine ⟨?_, ?_, ?_, True.intro⟩ <;> exact variableValue_insert_self shared _ _ _

/-- Byte-level decoding of all three present ABI words, not assumed load results. -/
theorem initial_abi_words (contract : Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (slots : List Nat) (x y d : Nat)
    (hargs : tx.args = [x, y, d]) :
    let shared := (initialState contract tx storage slots).sharedState
    EvmYul.State.calldataload shared.toState (UInt256.ofNat 4) = UInt256.ofNat x ∧
    EvmYul.State.calldataload shared.toState (UInt256.ofNat 36) = UInt256.ofNat y ∧
    EvmYul.State.calldataload shared.toState (UInt256.ofNat 68) = UInt256.ofNat d := by
  have hx := initialState_calldataload_aligned_arg_word contract tx storage slots 0 x [y,d]
    (by simp [hargs]) (by norm_num)
  have hy := initialState_calldataload_aligned_arg_word contract tx storage slots 1 y [d]
    (by simp [hargs]) (by norm_num)
  have hd := initialState_calldataload_aligned_arg_word contract tx storage slots 2 d []
    (by simp [hargs]) (by norm_num)
  exact ⟨hx, hy, hd⟩

/-- The actual zero-value guard skips its intact revert body. -/
theorem value_guard_passes (fuel : Nat) (s : Yul.State) (code : Option Yul.Ast.YulContract)
    (hvalue : s.executionEnv.weiValue = UInt256.ofNat 0) :
    Yul.exec (fuel + 21) capturedValueGuard code s = .ok s := by
  unfold capturedValueGuard
  apply exec_if_eval_zero (fuel + 20)
  simp [Yul.eval, Yul.evalArgs, Yul.evalPrimCall, Yul.reverse', Yul.head', hvalue]
  rfl

/-- At exactly three ABI words the signed length guard evaluates to false. -/
theorem length_guard_passes (fuel : Nat) (s : Yul.State) (code : Option Yul.Ast.YulContract)
    (hsize : s.executionEnv.calldata.size = 100) :
    Yul.exec (fuel + 21) capturedLengthGuard code s = .ok s := by
  unfold capturedLengthGuard
  apply exec_if_eval_zero (fuel + 20)
  simp [Yul.eval, Yul.evalArgs, Yul.evalTail,
    Yul.evalPrimCall, Yul.reverse', Yul.cons', Yul.head', hsize]
  decide

theorem eval_selector_condition (fuel : Nat) (shared : SharedState .Yul) (store : Yul.VarStore)
    (code : Option Yul.Ast.YulContract) :
    Yul.eval (fuel + 20) capturedSelectorGateCondition code (.Ok shared store) =
      .ok (.Ok shared store, UInt256.eq (UInt256.ofNat 0xb67bee04)
        (UInt256.shiftRight (EvmYul.State.calldataload shared.toState (UInt256.ofNat 0)) (UInt256.ofNat 224))) := by
  simp [capturedSelectorGateCondition, Yul.eval, Yul.evalArgs, Yul.evalTail,
    Yul.evalPrimCall, Yul.reverse', Yul.cons', Yul.head']

theorem calldata_gate_true (fuel : Nat) (s : Yul.State) (code : Option Yul.Ast.YulContract)
    (hsize : s.executionEnv.calldata.size = 100) :
    Yul.eval (fuel + 20) capturedCalldataGateCondition code s = .ok (s, UInt256.ofNat 1) := by
  simp [capturedCalldataGateCondition, Yul.eval, Yul.evalArgs, Yul.evalTail,
    Yul.evalPrimCall, Yul.reverse', Yul.cons', Yul.head', hsize]
  decide

/-- The selector equality is established from actual ABI selector bytes. -/
theorem initial_selector_gate_true (fuel : Nat) (contract : Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (slots : List Nat) (store : Yul.VarStore)
    (code : Option Yul.Ast.YulContract) (hselector : tx.functionSelector = 0xb67bee04) :
    Yul.eval (fuel + 20) capturedSelectorGateCondition code
      (.Ok (initialState contract tx storage slots).sharedState store) =
      .ok (.Ok (initialState contract tx storage slots).sharedState store, UInt256.ofNat 1) := by
  rw [eval_selector_condition]
  have h := initialState_selectorExpr_native_uint256 contract tx storage slots
  simp only [Compiler.Constants.selectorShift] at h
  rw [h, hselector]
  rfl

theorem initial_calldata_size (contract : Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (slots : List Nat) (x y d : Nat)
    (hargs : tx.args = [x,y,d]) :
    (initialState contract tx storage slots).executionEnv.calldata.size = 100 := by
  change (calldataToByteArray tx.functionSelector tx.args).size = 100
  rw [calldataToByteArray_size, hargs]
  rfl

/-- The actual function-branch prefix (both guards and all ABI loads) composes
with the original arithmetic body and exact returned-byte/imported-model theorem.
The selector traversal and pointer-producing prologue are still separate. -/
theorem abi_branch_bytes_match_imported
    (oracle : Compiler.CompilationModel.Denote.DenoteOracle) (world : Verity.ContractState)
    (contract : Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (slots : List Nat) (store : Yul.VarStore)
    (code : Option Yul.Ast.YulContract) (x y d : Verity.Core.Uint256)
    (hargs : tx.args = [x.val,y.val,d.val]) (hvalue : tx.msgValue = 0)
    (hfit : x.val * y.val < Verity.Core.Uint256.modulus) (hdzero : d.val ≠ 0)
    (hptr : variableValue (.Ok (initialState contract tx storage slots).sharedState store) "_1" = UInt256.ofNat 128) :
    nativeReturnBytes (Yul.exec 105 capturedFunctionBody code
      (.Ok (initialState contract tx storage slots).sharedState store)) =
      (captured.mulDivDown oracle world x y d).map
        (fun word => (UInt256.ofNat word.val).toByteArray) := by
  let shared := (initialState contract tx storage slots).sharedState
  have hv : (Yul.State.Ok shared store).executionEnv.weiValue = UInt256.ofNat 0 := by
    change UInt256.ofNat tx.msgValue = UInt256.ofNat 0
    rw [hvalue]
  have hs : (Yul.State.Ok shared store).executionEnv.calldata.size = 100 :=
    initial_calldata_size contract tx storage slots x.val y.val d.val hargs
  change nativeReturnBytes (Yul.exec 105 (.Block
    (capturedValueGuard :: capturedLengthGuard :: [capturedLoadX,capturedLoadY,capturedLoadD] ++
      [capturedProductDeclaration,capturedOverflowGuard,capturedDenominatorGuard,capturedReturnStore,capturedReturn]))
    code (.Ok shared store)) = _
  simp only [List.cons_append, List.nil_append]
  rw [exec_block_cons_ok_eq 104 _ _ _ _ _ (value_guard_passes 83 (.Ok shared store) code hv)]
  rw [exec_block_cons_ok_eq 103 _ _ _ _ _ (length_guard_passes 82 (.Ok shared store) code hs)]
  have hc := captured_loads_continuation 83 shared store code
    [capturedProductDeclaration,capturedOverflowGuard,capturedDenominatorGuard,capturedReturnStore,capturedReturn]
  simp only [List.cons_append, List.nil_append] at hc
  rw [hc]
  change nativeReturnBytes (Yul.exec 100 capturedArithmeticBody code (loadedState shared store)) = _
  have hb := loaded_bindings shared store
  have ha := initial_abi_words contract tx storage slots x.val y.val d.val hargs
  apply captured_body_bytes_match_imported oracle world shared _ code x y d hfit hdzero
  · exact hb.1.trans ha.1
  · exact hb.2.1.trans ha.2.1
  · exact hb.2.2.1.trans ha.2.2
  · exact hb.2.2.2.trans hptr

#print axioms abi_branch_bytes_match_imported
#print axioms calldata_gate_true
#print axioms initial_selector_gate_true
#print axioms initial_calldata_size
#print axioms value_guard_passes
#print axioms length_guard_passes
#print axioms captured_loads_continuation
#print axioms loaded_bindings
#print axioms initial_abi_words
end SolidityTranslationValidation.AstBridge.Dispatcher

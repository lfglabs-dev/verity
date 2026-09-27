import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Coverage

open Compiler.CompilationModel
open Compiler.CompilationModel.SolidityImport
open Compiler.CompilationModel.Denote

solidity_profile smokeBuild where
  evmVersion := "osaka"
  viaIR := true
  optimizerRuns := some 466
  bytecodeHash := "none"

solidity_import smoke from "Contracts/SolidityImportSmoke" entry "Slice.sol" using smokeBuild
  contract C
  function f(Mkt, bytes32, address)

/-- Oracle used only to place the two struct words of this witness.
The numeric claim is about the values `structMember` reads back. -/
def sliceOracle : DenoteOracle where
  mappingSlot base key := base + key + 1
  keccakMemorySlice _ _ _ := 0

def packHalves (lo hi : Nat) : Nat := lo + hi * 2 ^ 128

/-- `id = 1`, `user = 2`. Position words land at slots 5 and 6; the market
state word lands at slot 3. -/
def witnessWorld (credit pending lossFactor lastLoss lastAccrual : Nat) : Verity.ContractState :=
  Verity.defaultState.withStorageWords fun key =>
    let word :=
      match key with
      | .slot 5 => packHalves credit pending
      | .slot 6 => packHalves lastLoss lastAccrual
      | .slot 3 => packHalves 0 lossFactor
      | _ => 0
    Verity.Core.Uint256.ofNat word

/-- Canonical full ABI: dynamic Mkt offset, id/user, then the three-word
Mkt head and its empty uint128 array. No projected parameter is supplied. -/
def witnessCalldata (maturity : Nat) : List Nat :=
  [96, 1, 2, 0, 96, maturity, 0]

def witnessBindings (_maturity : Nat) : Env := []

private def smokeBody : List Stmt :=
  match smoke.model.functions with
  | fn :: _ => fn.body
  | [] => []

def peel (stmts : List Stmt) : Stmt × List Stmt :=
  match stmts with
  | s :: r => (s, r)
  | [] => (.panic .arithmeticOverflow, [])

theorem smokeBody_peel : smokeBody = (peel smokeBody).1 :: (peel smokeBody).2 := by
  unfold smokeBody peel
  rfl

def witnessState (credit pending lossFactor lastLoss lastAccrual timestamp maturity : Nat) : DenoteState :=
  { world := withTransactionContext
      (witnessWorld credit pending lossFactor lastLoss lastAccrual)
      { sender := 0, functionSelector := 0, blockTimestamp := timestamp, args := witnessCalldata maturity }
    bindings := witnessBindings maturity }

/-- Explicit expected decoder state, including every memory write and binding.
Persistent storage and all other state fields remain those of the input. -/
def decodedWitnessState : DenoteState :=
  let initial := witnessState 100 10 0 0 0 50 100
  let writes : List (Nat × Nat) :=
    [(64,128),(64,224),(128,0),(224,0),(64,256),(160,224),(192,100)]
  let memory := writes.foldl (fun mem (offset,value) =>
    fun o => if o = offset then Verity.Core.Uint256.ofNat value else mem o) initial.world.memory
  let bindings := ([
    ("_verity_slice_tmp_0_calldata",100), ("_verity_slice_tmp_0_memory",128),
    ("_verity_slice_tmp_0_next",224), ("_verity_slice_tmp_0_array1_memory",224),
    ("_verity_slice_tmp_0_array1_header",196), ("_verity_slice_tmp_0_array1_length",0),
    ("_verity_slice_tmp_0_array1_next",256), ("_verity_slice_tmp_0_array1_data",228),
    ("_verity_slice_tmp_0_array1_element_index",0),
    ("_verity_slice_tmp_1",1), ("_verity_slice_tmp_2",2)] : List (String × Nat)).foldl
      (fun env (name,value) => bindValue env name value) []
  { initial with world := { initial.world with memory }, bindings }

theorem string_beq_kernel : ("_verity_slice_tmp_1" == "_verity_slice_tmp_2") = false := by
  decide

/-- Concrete states keep each reduction bounded to one imported instruction. -/
private def abiState0 : DenoteState := witnessState 100 10 0 0 0 50 100

private def abiState1 : DenoteState :=
  { abiState0 with world := { abiState0.world with
    memory := fun o => if o = 64 then Verity.Core.Uint256.ofNat 128 else abiState0.world.memory o } }

private theorem abi_step_0 :
    execStmt sliceOracle smoke.model.fields abiState0 (peel (smokeBody.drop 0)).1 =
      .continue abiState1 := by rfl

private theorem abi_step_1 :
    execStmt sliceOracle smoke.model.fields abiState1 (peel (smokeBody.drop 1)).1 =
      .continue abiState1 := by rfl

private theorem abi_step_2 :
    execStmt sliceOracle smoke.model.fields abiState1 (peel (smokeBody.drop 2)).1 =
      .continue abiState1 := by rfl

private def abiState4 : DenoteState :=
  { abiState1 with bindings := bindValue abiState1.bindings "_verity_slice_tmp_0_calldata" 100 }

private theorem abi_step_3 :
    execStmt sliceOracle smoke.model.fields abiState1 (peel (smokeBody.drop 3)).1 =
      .continue abiState4 := by rfl

private theorem abi_step_4 :
    execStmt sliceOracle smoke.model.fields abiState4 (peel (smokeBody.drop 4)).1 =
      .continue abiState4 := by rfl

private def abiState6 : DenoteState :=
  { abiState4 with bindings := bindValue abiState4.bindings "_verity_slice_tmp_0_memory" 128 }

private theorem abi_step_5 :
    execStmt sliceOracle smoke.model.fields abiState4 (peel (smokeBody.drop 5)).1 =
      .continue abiState6 := by rfl

private def abiState7 : DenoteState :=
  { abiState6 with bindings := bindValue abiState6.bindings "_verity_slice_tmp_0_next" 224 }

private theorem abi_step_6 :
    execStmt sliceOracle smoke.model.fields abiState6 (peel (smokeBody.drop 6)).1 =
      .continue abiState7 := by rfl

private theorem abi_step_7 :
    execStmt sliceOracle smoke.model.fields abiState7 (peel (smokeBody.drop 7)).1 =
      .continue abiState7 := by rfl

private theorem abi_step_8 :
    execStmt sliceOracle smoke.model.fields abiState7 (peel (smokeBody.drop 8)).1 =
      .continue abiState7 := by rfl

private def abiState10 : DenoteState :=
  { abiState7 with world := { abiState7.world with
    memory := fun o => if o = 64 then Verity.Core.Uint256.ofNat 224 else abiState7.world.memory o } }

private theorem abi_step_9 :
    execStmt sliceOracle smoke.model.fields abiState7 (peel (smokeBody.drop 9)).1 =
      .continue abiState10 := by rfl

private def abiState11 : DenoteState :=
  { abiState10 with world := { abiState10.world with
    memory := fun o => if o = 128 then Verity.Core.Uint256.ofNat 0 else abiState10.world.memory o } }

private theorem abi_step_10 :
    execStmt sliceOracle smoke.model.fields abiState10 (peel (smokeBody.drop 10)).1 =
      .continue abiState11 := by rfl

private def abiState12 : DenoteState :=
  { abiState11 with bindings := bindValue abiState11.bindings "_verity_slice_tmp_0_array1_memory" 224 }

private theorem abi_step_11 :
    execStmt sliceOracle smoke.model.fields abiState11 (peel (smokeBody.drop 11)).1 =
      .continue abiState12 := by rfl

private theorem abi_step_12 :
    execStmt sliceOracle smoke.model.fields abiState12 (peel (smokeBody.drop 12)).1 =
      .continue abiState12 := by rfl

private def abiState14 : DenoteState :=
  { abiState12 with bindings := bindValue abiState12.bindings "_verity_slice_tmp_0_array1_header" 196 }

private theorem abi_step_13 :
    execStmt sliceOracle smoke.model.fields abiState12 (peel (smokeBody.drop 13)).1 =
      .continue abiState14 := by rfl

private theorem abi_step_14 :
    execStmt sliceOracle smoke.model.fields abiState14 (peel (smokeBody.drop 14)).1 =
      .continue abiState14 := by rfl

private def abiState16 : DenoteState :=
  { abiState14 with bindings := bindValue abiState14.bindings "_verity_slice_tmp_0_array1_length" 0 }

private theorem abi_step_15 :
    execStmt sliceOracle smoke.model.fields abiState14 (peel (smokeBody.drop 15)).1 =
      .continue abiState16 := by rfl

private theorem abi_step_16 :
    execStmt sliceOracle smoke.model.fields abiState16 (peel (smokeBody.drop 16)).1 =
      .continue abiState16 := by rfl

private def abiState18 : DenoteState :=
  { abiState16 with bindings := bindValue abiState16.bindings "_verity_slice_tmp_0_array1_next" 256 }

private theorem abi_step_17 :
    execStmt sliceOracle smoke.model.fields abiState16 (peel (smokeBody.drop 17)).1 =
      .continue abiState18 := by rfl

private theorem abi_step_18 :
    execStmt sliceOracle smoke.model.fields abiState18 (peel (smokeBody.drop 18)).1 =
      .continue abiState18 := by rfl

private theorem abi_step_19 :
    execStmt sliceOracle smoke.model.fields abiState18 (peel (smokeBody.drop 19)).1 =
      .continue abiState18 := by rfl

private def abiState21 : DenoteState :=
  { abiState18 with bindings := bindValue abiState18.bindings "_verity_slice_tmp_0_array1_data" 228 }

private theorem abi_step_20 :
    execStmt sliceOracle smoke.model.fields abiState18 (peel (smokeBody.drop 20)).1 =
      .continue abiState21 := by rfl

private theorem abi_step_21 :
    execStmt sliceOracle smoke.model.fields abiState21 (peel (smokeBody.drop 21)).1 =
      .continue abiState21 := by rfl

private def abiState23 : DenoteState :=
  { abiState21 with world := { abiState21.world with
    memory := fun o => if o = 224 then Verity.Core.Uint256.ofNat 0 else abiState21.world.memory o } }

private theorem abi_step_22 :
    execStmt sliceOracle smoke.model.fields abiState21 (peel (smokeBody.drop 22)).1 =
      .continue abiState23 := by rfl

private def abiState24 : DenoteState :=
  { abiState23 with world := { abiState23.world with
    memory := fun o => if o = 64 then Verity.Core.Uint256.ofNat 256 else abiState23.world.memory o } }

private theorem abi_step_23 :
    execStmt sliceOracle smoke.model.fields abiState23 (peel (smokeBody.drop 23)).1 =
      .continue abiState24 := by rfl

private def abiState25 : DenoteState :=
  { abiState24 with bindings := bindValue abiState24.bindings "_verity_slice_tmp_0_array1_element_index" 0 }

private theorem abi_step_24 :
    execStmt sliceOracle smoke.model.fields abiState24 (peel (smokeBody.drop 24)).1 =
      .continue abiState25 := by rfl

private def abiState26 : DenoteState :=
  { abiState25 with world := { abiState25.world with
    memory := fun o => if o = 160 then Verity.Core.Uint256.ofNat 224 else abiState25.world.memory o } }

private theorem abi_step_25 :
    execStmt sliceOracle smoke.model.fields abiState25 (peel (smokeBody.drop 25)).1 =
      .continue abiState26 := by rfl

private def abiState27 : DenoteState :=
  { abiState26 with world := { abiState26.world with
    memory := fun o => if o = 192 then Verity.Core.Uint256.ofNat 100 else abiState26.world.memory o } }

private theorem abi_step_26 :
    execStmt sliceOracle smoke.model.fields abiState26 (peel (smokeBody.drop 26)).1 =
      .continue abiState27 := by rfl

private def abiState28 : DenoteState :=
  { abiState27 with bindings := bindValue abiState27.bindings "_verity_slice_tmp_1" 1 }

private theorem abi_step_27 :
    execStmt sliceOracle smoke.model.fields abiState27 (peel (smokeBody.drop 27)).1 =
      .continue abiState28 := by rfl

private theorem abi_step_28 :
    execStmt sliceOracle smoke.model.fields abiState28 (peel (smokeBody.drop 28)).1 =
      .continue abiState28 := by rfl

private def abiState30 : DenoteState :=
  { abiState28 with bindings := bindValue abiState28.bindings "_verity_slice_tmp_2" 2 }

private theorem abi_step_29 :
    execStmt sliceOracle smoke.model.fields abiState28 (peel (smokeBody.drop 29)).1 =
      .continue abiState30 := by rfl

private theorem decoded_state_eq : abiState30 = decodedWitnessState := by rfl

private theorem exec_cons_continue (state next : DenoteState) (stmt : Stmt) (rest : List Stmt)
    (h : execStmt sliceOracle smoke.model.fields state stmt = .continue next) :
    execStmtList sliceOracle smoke.model.fields state (stmt :: rest) =
      execStmtList sliceOracle smoke.model.fields next rest := by
  simp only [execStmtList, h]

private theorem smoke_prelude_shape : smokeBody.take 30 =
    [(peel (smokeBody.drop 0)).1,
     (peel (smokeBody.drop 1)).1,
     (peel (smokeBody.drop 2)).1,
     (peel (smokeBody.drop 3)).1,
     (peel (smokeBody.drop 4)).1,
     (peel (smokeBody.drop 5)).1,
     (peel (smokeBody.drop 6)).1,
     (peel (smokeBody.drop 7)).1,
     (peel (smokeBody.drop 8)).1,
     (peel (smokeBody.drop 9)).1,
     (peel (smokeBody.drop 10)).1,
     (peel (smokeBody.drop 11)).1,
     (peel (smokeBody.drop 12)).1,
     (peel (smokeBody.drop 13)).1,
     (peel (smokeBody.drop 14)).1,
     (peel (smokeBody.drop 15)).1,
     (peel (smokeBody.drop 16)).1,
     (peel (smokeBody.drop 17)).1,
     (peel (smokeBody.drop 18)).1,
     (peel (smokeBody.drop 19)).1,
     (peel (smokeBody.drop 20)).1,
     (peel (smokeBody.drop 21)).1,
     (peel (smokeBody.drop 22)).1,
     (peel (smokeBody.drop 23)).1,
     (peel (smokeBody.drop 24)).1,
     (peel (smokeBody.drop 25)).1,
     (peel (smokeBody.drop 26)).1,
     (peel (smokeBody.drop 27)).1,
     (peel (smokeBody.drop 28)).1,
     (peel (smokeBody.drop 29)).1] := by rfl

/-- The complete imported prelude produces exactly the expected decoded state. -/
theorem smoke_entry_guard :
    execStmtList sliceOracle smoke.model.fields (witnessState 100 10 0 0 0 50 100)
      (smokeBody.take 30) = .continue decodedWitnessState := by
  change execStmtList sliceOracle smoke.model.fields abiState0 _ = _
  rw [smoke_prelude_shape]
  rw [exec_cons_continue _ _ _ _ abi_step_0]
  rw [exec_cons_continue _ _ _ _ abi_step_1]
  rw [exec_cons_continue _ _ _ _ abi_step_2]
  rw [exec_cons_continue _ _ _ _ abi_step_3]
  rw [exec_cons_continue _ _ _ _ abi_step_4]
  rw [exec_cons_continue _ _ _ _ abi_step_5]
  rw [exec_cons_continue _ _ _ _ abi_step_6]
  rw [exec_cons_continue _ _ _ _ abi_step_7]
  rw [exec_cons_continue _ _ _ _ abi_step_8]
  rw [exec_cons_continue _ _ _ _ abi_step_9]
  rw [exec_cons_continue _ _ _ _ abi_step_10]
  rw [exec_cons_continue _ _ _ _ abi_step_11]
  rw [exec_cons_continue _ _ _ _ abi_step_12]
  rw [exec_cons_continue _ _ _ _ abi_step_13]
  rw [exec_cons_continue _ _ _ _ abi_step_14]
  rw [exec_cons_continue _ _ _ _ abi_step_15]
  rw [exec_cons_continue _ _ _ _ abi_step_16]
  rw [exec_cons_continue _ _ _ _ abi_step_17]
  rw [exec_cons_continue _ _ _ _ abi_step_18]
  rw [exec_cons_continue _ _ _ _ abi_step_19]
  rw [exec_cons_continue _ _ _ _ abi_step_20]
  rw [exec_cons_continue _ _ _ _ abi_step_21]
  rw [exec_cons_continue _ _ _ _ abi_step_22]
  rw [exec_cons_continue _ _ _ _ abi_step_23]
  rw [exec_cons_continue _ _ _ _ abi_step_24]
  rw [exec_cons_continue _ _ _ _ abi_step_25]
  rw [exec_cons_continue _ _ _ _ abi_step_26]
  rw [exec_cons_continue _ _ _ _ abi_step_27]
  rw [exec_cons_continue _ _ _ _ abi_step_28]
  rw [exec_cons_continue _ _ _ _ abi_step_29]
  simp only [execStmtList, decoded_state_eq]

theorem smoke_credit_statement :
    execStmt sliceOracle smoke.model.fields decodedWitnessState (peel (smokeBody.drop 30)).1 =
      .continue { decodedWitnessState with
        bindings := bindValue decodedWitnessState.bindings "credit" 100 } := by
  rfl

/-- Decode the full tuple and then read the unchanged credit witness. -/
theorem smoke_step_credit :
    execStmtList sliceOracle smoke.model.fields (witnessState 100 10 0 0 0 50 100)
      (smokeBody.take 31) =
      .continue { decodedWitnessState with
        bindings := bindValue decodedWitnessState.bindings "credit" 100 } := by
  have append_continue (state next : DenoteState) (xs ys : List Stmt)
      (h : execStmtList sliceOracle smoke.model.fields state xs = .continue next) :
      execStmtList sliceOracle smoke.model.fields state (xs ++ ys) =
        execStmtList sliceOracle smoke.model.fields next ys := by
    induction xs generalizing state with
    | nil => simp only [execStmtList] at h; cases h; rfl
    | cons x xs ih =>
      simp only [List.cons_append, execStmtList] at *
      split at h <;> simp_all
  have shape : smokeBody.take 31 = smokeBody.take 30 ++ [(peel (smokeBody.drop 30)).1] := by rfl
  rw [shape, append_continue _ _ _ _ smoke_entry_guard]
  rw [exec_cons_continue _ _ _ _ smoke_credit_statement]
  rfl

-- Interpreter witnesses A/B live in scripts/solidity_import_mutations.py.
-- Keeping test execution out of this proof module satisfies Lean hygiene.

/-- The generated storage reader follows the imported layout: in the witness,
`position[1][2].credit` is the low half of slot 5 and `pendingFee` its high half. -/
example : (smoke.position.credit sliceOracle (witnessWorld 100 10 0 0 0) 1 2).val = 100 := by
  decide

example : (smoke.position.pendingFee sliceOracle (witnessWorld 100 10 0 0 0) 1 2).val = 10 := by
  decide

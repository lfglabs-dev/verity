import Compiler.SoliditySlice.Import
import Compiler.SoliditySlice.Coverage

open Compiler.CompilationModel
open Compiler.CompilationModel.SoliditySlice
open Compiler.CompilationModel.Denote

solidity_slice_import slice
  slice_root "Contracts/SoliditySliceSmoke" slice_entry "Slice.sol"
  slice_contract "C" slice_function "f"
  slice_param_tys ["struct Mkt", "bytes32", "address"]
  slice_solc "0.8.34+commit.80d5c536" slice_via_ir true slice_evm "osaka"
  slice_optimizer true slice_runs 466 slice_bytecode_hash "none"

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

def witnessBindings (maturity : Nat) : Env :=
  [("m_maturity", maturity), ("id", 1), ("user", 2)]

private def smokeBody : List Stmt :=
  match slice.model.functions with
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
  { world :=
      { witnessWorld credit pending lossFactor lastLoss lastAccrual with
        blockTimestamp := Verity.Core.Uint256.ofNat timestamp }
    bindings := witnessBindings maturity }

theorem string_beq_kernel : ("m_maturity" == "id") = false := by
  decide

set_option maxHeartbeats 2000000 in
theorem smoke_step_credit :
    execStmt sliceOracle slice.model.fields (witnessState 100 10 0 0 0 50 100) (peel smokeBody).1 =
      .continue
        { witnessState 100 10 0 0 0 50 100 with
          bindings := bindValue (witnessBindings 100) "slice.tmp.0" 100 } := by
  dsimp only [peel, smokeBody, slice.model]
  have hmi : ("m_maturity" == "id") = false := by decide
  have hmu : ("m_maturity" == "user") = false := by decide
  have hiu : ("id" == "user") = false := by decide
  have hft : (false = true) = False := by decide
  have h5 : 5 % Verity.Core.Uint256.modulus = 5 := Nat.mod_eq_of_lt (by decide)
  have h0m : 0 % Verity.Core.Uint256.modulus = 0 := Nat.mod_eq_of_lt (by decide)
  simp only [hmi, hmu, hiu, hft, h5, h0m, Nat.mod_mod, Nat.shiftRight_zero,
    execStmt, evalExpr, findFieldWithResolvedSlot_eq_CopyFrom,
    findFieldWithResolvedSlotCopyFrom, findStructMembers, findStructMember, readFieldWord,
    packedMaskNat, lookupValue, sliceOracle, witnessState, witnessWorld, witnessBindings,
    packHalves, bindValue, wordNormalize, Verity.ContractState.withStorageWords,
    Verity.ContractState.readSlot, Verity.ContractState.storage, Verity.Core.Uint256.shr,
    Verity.Core.Uint256.and, Verity.Core.Uint256.ofNat, bind, Option.bind, Option.map,
    Option.getD, List.find?, beq_self_eq_true, ↓reduceIte,
    ↓Nat.reduceAdd, ↓Nat.reduceMul, ↓Nat.reducePow, ↓Nat.reduceSub]
  have hcredit :
      (3402823669209384634633746074317682114660 % Verity.Core.Uint256.modulus &&&
        340282366920938463463374607431768211455 % Verity.Core.Uint256.modulus) %
      Verity.Core.Uint256.modulus = 100 := by decide
  simp [hcredit]

-- Interpreter witnesses A/B live in scripts/solidity_slice_mutations.py.
-- Keeping test execution out of this proof module satisfies Lean hygiene.

import Compiler.SolidityImport.Coverage
import Verity.Core.NarrowTypes
import Verity.Core.Address

/-!
Typed access to an imported model: calling a function and reading a storage
member. `solidity_import` generates a named, typed wrapper around each of these
(`example.f`, `example.position.credit`), so specifications do not name slots,
bindings or packing.
-/

open Compiler.CompilationModel Compiler.CompilationModel.Denote
open Verity.Core
namespace Compiler.CompilationModel.SolidityImport

/-- A Solidity value carried in one 256-bit word. -/
class Word (α : Type) where
  toWord : α → Nat
  ofWord : Nat → α

instance : Word Uint256 := ⟨Uint256.val, Uint256.ofNat⟩
instance : Word (UIntN bits) := ⟨UIntN.val, UIntN.ofNat bits⟩
instance : Word Address := ⟨Address.val, Address.ofNat⟩
instance : Word (BytesN 32) := ⟨BytesN.val, BytesN.ofNat 32⟩
instance : Word Bool := ⟨fun b => if b then 1 else 0, fun n => n != 0⟩

@[simp] theorem toWord_uint256 (x : Uint256) : Word.toWord x = x.val := rfl
@[simp] theorem toWord_uintN (x : UIntN bits) : Word.toWord x = x.val := rfl
@[simp] theorem toWord_address (x : Address) : Word.toWord x = x.val := rfl
@[simp] theorem toWord_bytes32 (x : BytesN 32) : Word.toWord x = x.val := rfl
@[simp] theorem ofWord_uint256 (n : Nat) : (Word.ofWord n : Uint256) = Uint256.ofNat n := rfl
@[simp] theorem ofWord_uintN (n : Nat) : (Word.ofWord n : UIntN bits) = UIntN.ofNat bits n := rfl

/-- Body of the function `name` in `model`; `[]` if there is none. -/
def functionBody (model : CompilationModel) (name : String) : List Stmt :=
  go model.functions
where
  go : List FunctionSpec → List Stmt
    | [] => []
    | fn :: rest => if fn.name = name then fn.body else go rest

/-- Run the function `name` of an imported model in `world` with the given
argument words; `none` means it reverted. -/
def runFunction (oracle : DenoteOracle) (model : CompilationModel) (name : String)
    (world : Verity.ContractState) (args : Env) : Option (List Nat) :=
  match execStmtList oracle model.fields { world, bindings := args } (functionBody model name) with
  | .stop state | .continue state | .return _ state => state.observedReturnWords
  | .revert | .revertWithData _ => none

/-- `field[keys].member` in `world`, read exactly as the imported model reads
it: solc's slot, word offset and packing. `0` if there is no such member. -/
def readMember (oracle : DenoteOracle) (model : CompilationModel) (world : Verity.ContractState)
    (field : String) (keys : List Nat) (member : String) : Nat :=
  match keys with
  | [k] => (evalExpr oracle model.fields { world, bindings := [("key1", k)] }
      (.structMember field (.param "key1") member)).getD 0
  | [k1, k2] => (evalExpr oracle model.fields { world, bindings := [("key1", k1), ("key2", k2)] }
      (.structMember2 field (.param "key1") (.param "key2") member)).getD 0
  | _ => 0

/-- The layout entry of `field[..].member`, if the model has one. -/
def findMember (model : CompilationModel) (field member : String) : Option StructMember :=
  (findStructMembers model.fields field).bind (findStructMember · member)

/-- Bit width of `field[..].member`: its packed width, else a full word. -/
def memberWidth (model : CompilationModel) (field member : String) : Nat :=
  match findMember model field member with
  | some { packed := some packed, .. } => packed.width
  | _ => 256

private theorem masked_lt (x : Uint256) (packed : PackedBits) :
    (Uint256.and x (Uint256.ofNat (packedMaskNat packed))).val < 2 ^ packed.width := by
  have hle : (Uint256.and x (Uint256.ofNat (packedMaskNat packed))).val ≤ packedMaskNat packed :=
    Nat.le_trans (Nat.mod_le _ _) (Nat.le_trans Nat.and_le_right (Nat.mod_le _ _))
  have hlt : (Uint256.and x (Uint256.ofNat (packedMaskNat packed))).val < 2 ^ 256 :=
    (Uint256.and x _).isLt
  generalize (Uint256.and x (Uint256.ofNat (packedMaskNat packed))).val = v at hle hlt
  have hpos : 0 < 2 ^ packed.width := Nat.pow_pos (by decide)
  unfold packedMaskNat at hle
  split at hle
  · exact Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide) (by omega))
  · omega

/-- A member read fits in the member's width. -/
theorem readMember_lt (oracle : DenoteOracle) (model : CompilationModel)
    (world : Verity.ContractState) (field : String) (keys : List Nat) (member : String) :
    readMember oracle model world field keys member < 2 ^ memberWidth model field member := by
  unfold readMember memberWidth findMember
  split
  all_goals first
    | exact Nat.pow_pos (by decide)
    | skip
  all_goals
    simp only [evalExpr, lookupValue, List.find?, bind, Option.bind]
    split <;> try exact Nat.pow_pos (by decide)
    rename_i fieldInfo slot members _ hmembers
    simp only [hmembers]
    split <;> try exact Nat.pow_pos (by decide)
    rename_i m hm
    simp only [hm]
    cases m with
    | mk name ty wordOffset packed =>
      cases packed with
      | none => exact (readFieldWord _ _ _).isLt
      | some packed => exact masked_lt _ packed

/-- A member read of width `bits` is exactly representable as `UIntN bits`. -/
theorem val_uintN_readMember (oracle : DenoteOracle) (model : CompilationModel)
    (world : Verity.ContractState) (field : String) (keys : List Nat) (member : String)
    (h : memberWidth model field member = bits) :
    (UIntN.ofNat bits (readMember oracle model world field keys member)).val =
      readMember oracle model world field keys member :=
  Nat.mod_eq_of_lt (h ▸ readMember_lt oracle model world field keys member)

/-- A full-word member read is exactly representable as `Uint256`. -/
theorem val_uint256_readMember (oracle : DenoteOracle) (model : CompilationModel)
    (world : Verity.ContractState) (field : String) (keys : List Nat) (member : String)
    (h : memberWidth model field member = 256) :
    (Uint256.ofNat (readMember oracle model world field keys member)).val =
      readMember oracle model world field keys member := by
  have hlt := readMember_lt oracle model world field keys member
  rw [h] at hlt
  exact Nat.mod_eq_of_lt hlt

/-- The model's own read of `field[a][b].member`, with keys bound to `a` and `b`,
is `readMember` at their values. -/
theorem evalExpr_structMember2_param (oracle : DenoteOracle) (model : CompilationModel)
    (state : DenoteState) (field a b member : String)
    (h : (findFieldWithResolvedSlot model.fields field).isSome ∧
      (findMember model field member).isSome) :
    evalExpr oracle model.fields state (.structMember2 field (.param a) (.param b) member) =
      some (readMember oracle model state.world field
        [lookupValue state.bindings a, lookupValue state.bindings b] member) := by
  obtain ⟨hf, hm⟩ := h
  unfold findMember at hm
  simp only [readMember, evalExpr, bind, Option.bind]
  cases hfs : findFieldWithResolvedSlot model.fields field with
  | none => simp [hfs] at hf
  | some fs =>
    cases hms : findStructMembers model.fields field with
    | none => simp [hms] at hm
    | some ms =>
      cases hmm : findStructMember ms member with
      | none => simp [hms, hmm] at hm
      | some m =>
        simp only [hmm, lookupValue]
        cases m.packed <;> simp

/-- The model's own read of `field[a].member`, with the key bound to `a`, is
`readMember` at its value. -/
theorem evalExpr_structMember_param (oracle : DenoteOracle) (model : CompilationModel)
    (state : DenoteState) (field a member : String)
    (h : (findFieldWithResolvedSlot model.fields field).isSome ∧
      (findMember model field member).isSome) :
    evalExpr oracle model.fields state (.structMember field (.param a) member) =
      some (readMember oracle model state.world field [lookupValue state.bindings a] member) := by
  obtain ⟨hf, hm⟩ := h
  unfold findMember at hm
  simp only [readMember, evalExpr, bind, Option.bind]
  cases hfs : findFieldWithResolvedSlot model.fields field with
  | none => simp [hfs] at hf
  | some fs =>
    cases hms : findStructMembers model.fields field with
    | none => simp [hms] at hm
    | some ms =>
      cases hmm : findStructMember ms member with
      | none => simp [hms, hmm] at hm
      | some m =>
        simp only [hmm, lookupValue]
        cases m.packed <;> simp

end Compiler.CompilationModel.SolidityImport

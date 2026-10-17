import Compiler.Proofs.IRGeneration.IRInterpreter

/-! Physical payload writes shared by literal and pointer-based compiler proofs.
Recovered from the preserved physical-memory branch. These laws describe the
complete state and byte frame; they do not claim a revert-byte observation. -/
namespace Compiler.Proofs.IRGeneration.PhysicalPayloadStores
open Compiler.Yul

def stores (writes : List (Nat × Nat)) : List YulStmt :=
  writes.map (fun (offset, value) => .exprStmt (.call "mstore" [.lit offset, .lit value]))

def applyStores : IRState → List (Nat × Nat) → IRState
  | state, [] => state
  | state, (offset, value) :: rest =>
      applyStores (state.writePhysicalMemoryValue (Verity.Core.Uint256.ofNat offset).val value) rest

theorem exec_stores (writes : List (Nat × Nat)) (state : IRState) (fuel : Nat) :
    execIRStmts (writes.length + fuel + 2) state (stores writes) =
      .continue (applyStores state writes) := by
  induction writes generalizing state with
  | nil => rfl
  | cons head rest ih =>
      rcases head with ⟨offset, value⟩
      simp only [stores, List.map_cons, List.length_cons, applyStores]
      rw [show rest.length + 1 + fuel + 2 = (rest.length + fuel + 2) + 1 by omega]
      simp only [execIRStmts, execIRStmt, evalIRExpr]
      exact ih _

/-- Payload construction preserves persistent storage and emitted events. -/
theorem applyStores_storage (state : IRState) (writes : List (Nat × Nat)) :
    (applyStores state writes).storage = state.storage := by
  induction writes generalizing state with
  | nil => rfl
  | cons pair tail ih =>
      simp only [applyStores]
      rw [ih]
      rfl

theorem applyStores_events (state : IRState) (writes : List (Nat × Nat)) :
    (applyStores state writes).events = state.events := by
  induction writes generalizing state with
  | nil => rfl
  | cons pair tail ih =>
      simp only [applyStores]
      rw [ih]
      rfl

/-- Bytes outside every actual normalized store extent retain their value. -/
theorem applyStores_byte_outside (state : IRState) (writes : List (Nat × Nat))
    (query : Nat)
    (outside : ∀ pair ∈ writes,
      query < (Verity.Core.Uint256.ofNat pair.1).val ∨
        (Verity.Core.Uint256.ofNat pair.1).val + 32 ≤ query) :
    (applyStores state writes).byteMemory.readByte query = state.byteMemory.readByte query := by
  induction writes generalizing state with
  | nil => rfl
  | cons pair tail ih =>
      simp only [applyStores]
      rw [ih _ (fun entry member => outside entry (List.mem_cons_of_mem _ member))]
      exact Compiler.CompilationModel.DenoteMemory.Memory.readByte_writeWord_outside _ _ _ query
        (outside pair (List.mem_cons_self))

/-- Split a physical payload into bounded execution stages. -/
theorem applyStores_append (state : IRState) (left right : List (Nat × Nat)) :
    applyStores state (left ++ right) = applyStores (applyStores state left) right := by
  induction left generalizing state with
  | nil => rfl
  | cons pair tail ih =>
      simp only [List.cons_append, applyStores]
      exact ih _

/-- A byte of a store survives all later stores whose physical extents miss it.
This includes overlapping unaligned headers when the selected byte is outside
only the later extents, rather than requiring the complete words disjoint. -/
theorem applyStores_byte_written (state : IRState) (offset value : Nat)
    (tail : List (Nat × Nat)) (index : Fin 32)
    (outside : ∀ pair ∈ tail,
      (Verity.Core.Uint256.ofNat offset).val + index.val <
        (Verity.Core.Uint256.ofNat pair.1).val ∨
      (Verity.Core.Uint256.ofNat pair.1).val + 32 ≤
        (Verity.Core.Uint256.ofNat offset).val + index.val) :
    (applyStores state ((offset, value) :: tail)).byteMemory.readByte
      ((Verity.Core.Uint256.ofNat offset).val + index.val) =
      Compiler.CompilationModel.DenoteMemory.valueWord
        (Verity.Core.Uint256.ofNat value) index := by
  simp only [applyStores]
  rw [applyStores_byte_outside _ tail _ outside]
  exact Compiler.CompilationModel.DenoteMemory.Memory.readByte_writeWord_at _ _ _ index


theorem exec_stores_revert (writes : List (Nat × Nat)) (state : IRState)
    (fuel offset size : Nat) :
    execIRStmts (writes.length + fuel + 2) state
      (stores writes ++ [.exprStmt (.call "revert" [.lit offset, .lit size])]) =
      .revert (applyStores state writes) := by
  induction writes generalizing state with
  | nil => simp only [stores, List.map_nil, List.nil_append, List.length_nil,
                     Nat.zero_add, applyStores, execIRStmts, execIRStmt, evalIRExpr]
  | cons head rest ih =>
      rcases head with ⟨destination, value⟩
      simp only [stores, List.map_cons, List.cons_append, List.length_cons, applyStores]
      rw [show rest.length + 1 + fuel + 2 = (rest.length + fuel + 2) + 1 by omega]
      simp only [execIRStmts, execIRStmt, evalIRExpr]
      exact ih _

/-- Literal and hexadecimal payload stores share physical-memory semantics. -/
inductive StoreTrace : List YulStmt → List (Nat × Nat) → Prop where
  | nil : StoreTrace [] []
  | consLit (offset value : Nat) {tail writes} : StoreTrace tail writes →
      StoreTrace (.exprStmt (.call "mstore" [.lit offset, .lit value]) :: tail)
        ((offset, value) :: writes)
  | consHex (offset value : Nat) {tail writes} : StoreTrace tail writes →
      StoreTrace (.exprStmt (.call "mstore" [.lit offset, .hex value]) :: tail)
        ((offset, value) :: writes)

theorem exec_trace_revert {statements writes} (trace : StoreTrace statements writes)
    (state : IRState) (fuel offset size : Nat) :
    execIRStmts (writes.length + fuel + 2) state
      (statements ++ [.exprStmt (.call "revert" [.lit offset, .lit size])]) =
      .revert (applyStores state writes) := by
  induction trace generalizing state with
  | nil => simp only [List.nil_append, List.length_nil, Nat.zero_add, applyStores,
                     execIRStmts, execIRStmt, evalIRExpr]
  | @consLit destination value tail writes trace ih =>
      simp only [List.cons_append, List.length_cons, applyStores]
      rw [show writes.length + 1 + fuel + 2 = (writes.length + fuel + 2) + 1 by omega]
      simp only [execIRStmts, execIRStmt, evalIRExpr]
      exact ih _
  | @consHex destination value tail writes trace ih =>
      simp only [List.cons_append, List.length_cons, applyStores]
      rw [show writes.length + 1 + fuel + 2 = (writes.length + fuel + 2) + 1 by omega]
      simp only [execIRStmts, execIRStmt, evalIRExpr]
      exact ih _

theorem StoreTrace.append {left right writesLeft writesRight}
    (first : StoreTrace left writesLeft) (second : StoreTrace right writesRight) :
    StoreTrace (left ++ right) (writesLeft ++ writesRight) := by
  induction first with
  | nil => exact second
  | consLit offset value trace ih => exact .consLit offset value ih
  | consHex offset value trace ih => exact .consHex offset value ih

def hexStores (writes : List (Nat × Nat)) : List YulStmt :=
  writes.map (fun (offset, value) => .exprStmt (.call "mstore" [.lit offset, .hex value]))

theorem StoreTrace.hexStores (writes : List (Nat × Nat)) :
    StoreTrace (hexStores writes) writes := by
  induction writes with
  | nil => exact .nil
  | cons pair tail ih =>
      rcases pair with ⟨offset, value⟩
      exact .consHex offset value ih


end Compiler.Proofs.IRGeneration.PhysicalPayloadStores

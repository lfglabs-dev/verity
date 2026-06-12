import Compiler.Proofs.IRGeneration.SourceSemantics
import Compiler.Proofs.IRGeneration.FunctionBody.Base

/-!
Generic EVM Frames (minimal extraction for climb / loop proofs).

This is the smallest useful surface extracted from SPHINCS- style proofs:
- Preservation of bindings for names a step does not write.
- Preservation of selector and calldata (common for read-only-calldata verifiers).

All lemmas case on evalExpr results abstractly so large terms (keccaks, bodies)
are not forced. Additive, no new axioms.
-/

namespace Compiler.Proofs.Frames

open Compiler.Proofs.IRGeneration.SourceSemantics
open Compiler.CompilationModel (Expr Stmt)

abbrev PreservesBindingsExcept (st s : RuntimeState) (written : List String) : Prop :=
  forall key, key ∉ written -> lookupValue s.bindings key = lookupValue st.bindings key

abbrev PreservesStorageExcept (st s : RuntimeState) (writtenSlots : List Nat) : Prop :=
  forall slot, slot ∉ writtenSlots -> s.world.storage slot = st.world.storage slot

abbrev PreservesAddressStorageExcept (st s : RuntimeState) (writtenSlots : List Nat) : Prop :=
  forall slot, slot ∉ writtenSlots -> s.world.storageAddr slot = st.world.storageAddr slot

abbrev PreservesStorageArraysExcept (st s : RuntimeState) (writtenSlots : List Nat) : Prop :=
  forall slot, slot ∉ writtenSlots -> s.world.storageArray slot = st.world.storageArray slot

abbrev PreservesSelectorCalldata (st s : RuntimeState) : Prop :=
  s.selector = st.selector /\ s.world.calldata = st.world.calldata

structure ExecutionSummary (st s : RuntimeState)
    (writtenBindings : List String) (writtenStorageSlots : List Nat)
    (writtenAddressSlots : List Nat) (writtenArraySlots : List Nat) : Prop where
  bindings : PreservesBindingsExcept st s writtenBindings
  storage : PreservesStorageExcept st s writtenStorageSlots
  addressStorage : PreservesAddressStorageExcept st s writtenAddressSlots
  storageArrays : PreservesStorageArraysExcept st s writtenArraySlots
  selectorCalldata : PreservesSelectorCalldata st s

theorem ExecutionSummary.refl
    (st : RuntimeState) :
    ExecutionSummary st st [] [] [] [] := by
  constructor
  · intro _ _; rfl
  · intro _ _; rfl
  · intro _ _; rfl
  · intro _ _; rfl
  · exact And.intro rfl rfl

theorem ExecutionSummary.weaken
    {st s : RuntimeState}
    {ws ws' wa wa' wsa wsa' : List Nat}
    {writtenBindings writtenBindings' : List String}
    (h : ExecutionSummary st s writtenBindings ws wa wsa)
    (hb : ∀ key, key ∈ writtenBindings -> key ∈ writtenBindings')
    (hs : ∀ slot, slot ∈ ws -> slot ∈ ws')
    (ha : ∀ slot, slot ∈ wa -> slot ∈ wa')
    (hsa : ∀ slot, slot ∈ wsa -> slot ∈ wsa') :
    ExecutionSummary st s writtenBindings' ws' wa' wsa' := by
  constructor
  · intro key hnot
    exact h.bindings key (fun hm => hnot (hb key hm))
  · intro slot hnot
    exact h.storage slot (fun hm => hnot (hs slot hm))
  · intro slot hnot
    exact h.addressStorage slot (fun hm => hnot (ha slot hm))
  · intro slot hnot
    exact h.storageArrays slot (fun hm => hnot (hsa slot hm))
  · exact h.selectorCalldata

private theorem not_mem_append_left {α : Type} [DecidableEq α] {x : α} {xs ys : List α}
    (h : x ∉ xs ++ ys) : x ∉ xs := by
  intro hx
  exact h (List.mem_append_left ys hx)

private theorem not_mem_append_right {α : Type} [DecidableEq α] {x : α} {xs ys : List α}
    (h : x ∉ xs ++ ys) : x ∉ ys := by
  intro hy
  exact h (List.mem_append_right xs hy)

theorem ExecutionSummary.trans
    {st mid s : RuntimeState}
    {wb₁ wb₂ : List String} {ws₁ ws₂ wa₁ wa₂ wsa₁ wsa₂ : List Nat}
    (h₁ : ExecutionSummary st mid wb₁ ws₁ wa₁ wsa₁)
    (h₂ : ExecutionSummary mid s wb₂ ws₂ wa₂ wsa₂) :
    ExecutionSummary st s (wb₁ ++ wb₂) (ws₁ ++ ws₂) (wa₁ ++ wa₂) (wsa₁ ++ wsa₂) := by
  constructor
  · intro key hnot
    rw [h₂.bindings key (not_mem_append_right hnot),
      h₁.bindings key (not_mem_append_left hnot)]
  · intro slot hnot
    rw [h₂.storage slot (not_mem_append_right hnot),
      h₁.storage slot (not_mem_append_left hnot)]
  · intro slot hnot
    rw [h₂.addressStorage slot (not_mem_append_right hnot),
      h₁.addressStorage slot (not_mem_append_left hnot)]
  · intro slot hnot
    rw [h₂.storageArrays slot (not_mem_append_right hnot),
      h₁.storageArrays slot (not_mem_append_left hnot)]
  · exact ⟨h₂.selectorCalldata.1.trans h₁.selectorCalldata.1,
      h₂.selectorCalldata.2.trans h₁.selectorCalldata.2⟩

theorem execStmt_letVar_preserves_bindings_except
    (st s : RuntimeState) (name : String) (e : Expr)
    (h : execStmt [] st (.letVar name e) = .continue s) :
    PreservesBindingsExcept st s [name] := by
  rw [show execStmt [] st (.letVar name e) = (match evalExpr [] st e with
    | some resolved => .continue { st with bindings := bindValue st.bindings name resolved }
    | none => .revert) from rfl] at h
  cases hev : evalExpr [] st e with
  | none => rw [hev] at h; exact absurd h (by simp)
  | some r =>
      rw [hev] at h
      injection h with hh; subst hh
      intro key hne
      have hNe : key ≠ name := by simpa using hne
      simp [Compiler.Proofs.IRGeneration.FunctionBody.lookupValue_bindValue_ne _ _ _ _ hNe]

theorem execStmt_mstore_preserves_bindings_except
    (st s : RuntimeState) (off val : Expr)
    (h : execStmt [] st (.mstore off val) = .continue s) :
    PreservesBindingsExcept st s [] := by
  rw [show execStmt [] st (.mstore off val) = (match evalExpr [] st off, evalExpr [] st val with
    | some ro, some rv => .continue { st with world := { st.world with
        memory := fun o => if o = ro then rv else st.world.memory o } }
    | _, _ => .revert) from rfl] at h
  cases hoff : evalExpr [] st off with
  | none => rw [hoff] at h; exact absurd h (by simp)
  | some _ =>
      cases hval : evalExpr [] st val with
      | none => rw [hoff, hval] at h; exact absurd h (by simp)
      | some _ =>
          rw [hoff, hval] at h
          injection h with hh; subst hh
          intro key _; rfl

theorem execStmt_letVar_preserves_selector_calldata
    (st s : RuntimeState) (name : String) (e : Expr)
    (h : execStmt [] st (.letVar name e) = .continue s) :
    PreservesSelectorCalldata st s := by
  rw [show execStmt [] st (.letVar name e) = (match evalExpr [] st e with
    | some resolved => .continue { st with bindings := bindValue st.bindings name resolved }
    | none => .revert) from rfl] at h
  cases hev : evalExpr [] st e with
  | none => rw [hev] at h; exact absurd h (by simp)
  | some _ =>
      rw [hev] at h
      injection h with hh; subst hh
      exact And.intro rfl rfl

theorem execStmt_mstore_preserves_selector_calldata
    (st s : RuntimeState) (off val : Expr)
    (h : execStmt [] st (.mstore off val) = .continue s) :
    PreservesSelectorCalldata st s := by
  rw [show execStmt [] st (.mstore off val) = (match evalExpr [] st off, evalExpr [] st val with
    | some ro, some rv => .continue { st with world := { st.world with
        memory := fun o => if o = ro then rv else st.world.memory o } }
    | _, _ => .revert) from rfl] at h
  cases hoff : evalExpr [] st off with
  | none => rw [hoff] at h; exact absurd h (by simp)
  | some _ =>
      cases hval : evalExpr [] st val with
      | none => rw [hoff, hval] at h; exact absurd h (by simp)
      | some _ =>
          rw [hoff, hval] at h
          injection h with hh; subst hh
          exact And.intro rfl rfl

theorem writeUintSlots_preserves_storage_except
    (world : Verity.ContractState) (slots : List Nat) (value slot : Nat)
    (hslot : slot ∉ slots.map wordNormalize) :
    (writeUintSlots world slots value).storage slot = world.storage slot := by
  have hcontains : (slots.map wordNormalize).contains slot = false := by
    simpa [List.elem_eq_contains] using hslot
  simp only [writeUintSlots]
  rw [hcontains]
  simp

theorem writeStorageWordSlots_preserves_storage_except
    (world : Verity.ContractState) (slots : List Nat) (wordOffset value slot : Nat)
    (hslot : slot ∉ slots.map (fun base => wordNormalize (base + wordOffset))) :
    (writeStorageWordSlots world slots wordOffset value).storage slot = world.storage slot := by
  have hcontains :
      (slots.map (fun base => wordNormalize (base + wordOffset))).contains slot = false := by
    simpa [List.elem_eq_contains] using hslot
  simp only [writeStorageWordSlots]
  rw [hcontains]
  simp

theorem writeStorageWordSlots_preserves_address_except
    (world : Verity.ContractState) (slots : List Nat) (wordOffset value slot : Nat)
    (hslot : slot ∉ slots.map (fun base => wordNormalize (base + wordOffset))) :
    (writeStorageWordSlots world slots wordOffset value).storageAddr slot =
      world.storageAddr slot := by
  have hcontains :
      (slots.map (fun base => wordNormalize (base + wordOffset))).contains slot = false := by
    simpa [List.elem_eq_contains] using hslot
  simp only [writeStorageWordSlots]
  rw [hcontains]
  simp

theorem writeAddressSlots_preserves_address_except
    (world : Verity.ContractState) (slots : List Nat) (value slot : Nat)
    (hslot : slot ∉ slots.map wordNormalize) :
    (writeAddressSlots world slots value).storageAddr slot = world.storageAddr slot := by
  have hcontains : (slots.map wordNormalize).contains slot = false := by
    simpa [List.elem_eq_contains] using hslot
  simp only [writeAddressSlots]
  rw [hcontains]
  simp

theorem writeStorageArray_preserves_arrays_except
    (world : Verity.ContractState) (arraySlot slot : Nat) (values : List Verity.Core.Uint256)
    (hslot : slot ∉ [arraySlot]) :
    (writeStorageArray world arraySlot values).storageArray slot = world.storageArray slot := by
  have hne : slot ≠ arraySlot := by simpa using hslot
  simp [writeStorageArray, hne, BEq.beq]

theorem execStmt_setStorage_execution_summary
    (fields : List Compiler.CompilationModel.Field)
    (st s : RuntimeState) (fieldName : String) (value : Expr) (slots : List Nat)
    (hslots : Compiler.CompilationModel.findFieldWriteSlots fields fieldName = some slots)
    (h : execStmt fields st (.setStorage fieldName value) = .continue s) :
    ExecutionSummary st s [] (slots.map wordNormalize) [] [] := by
  rw [show execStmt fields st (.setStorage fieldName value) =
    (match Compiler.CompilationModel.findFieldWriteSlots fields fieldName, evalExpr fields st value with
    | some slots, some resolved =>
        .continue { st with world := writeUintSlots st.world slots resolved }
    | _, _ => .revert) from rfl] at h
  rw [hslots] at h
  cases hval : evalExpr fields st value with
  | none => rw [hval] at h; exact absurd h (by simp)
  | some resolved =>
      rw [hval] at h
      injection h with hh; subst hh
      constructor
      · intro _ _; rfl
      · intro slot hslot
        exact writeUintSlots_preserves_storage_except st.world slots resolved slot hslot
      · intro _ _; rfl
      · intro _ _; rfl
      · exact And.intro rfl rfl

theorem execStmt_setStorageAddr_execution_summary
    (fields : List Compiler.CompilationModel.Field)
    (st s : RuntimeState) (fieldName : String) (value : Expr) (slots : List Nat)
    (hslots : Compiler.CompilationModel.findFieldWriteSlots fields fieldName = some slots)
    (h : execStmt fields st (.setStorageAddr fieldName value) = .continue s) :
    ExecutionSummary st s [] [] (slots.map wordNormalize) [] := by
  rw [show execStmt fields st (.setStorageAddr fieldName value) =
    (match Compiler.CompilationModel.findFieldWriteSlots fields fieldName, evalExpr fields st value with
    | some slots, some resolved =>
        .continue { st with world := writeAddressSlots st.world slots resolved }
    | _, _ => .revert) from rfl] at h
  rw [hslots] at h
  cases hval : evalExpr fields st value with
  | none => rw [hval] at h; exact absurd h (by simp)
  | some resolved =>
      rw [hval] at h
      injection h with hh; subst hh
      constructor
      · intro _ _; rfl
      · intro _ _; rfl
      · intro slot hslot
        exact writeAddressSlots_preserves_address_except st.world slots resolved slot hslot
      · intro _ _; rfl
      · exact And.intro rfl rfl

theorem execStmtList_execution_summary_cons
    (fields : List Compiler.CompilationModel.Field)
    (st mid s : RuntimeState) (stmt : Stmt) (rest : List Stmt)
    {wb₁ wb₂ : List String} {ws₁ ws₂ wa₁ wa₂ wsa₁ wsa₂ : List Nat}
    (hstmt : execStmt fields st stmt = .continue mid)
    (hrest : execStmtList fields mid rest = .continue s)
    (hs₁ : ExecutionSummary st mid wb₁ ws₁ wa₁ wsa₁)
    (hs₂ : ExecutionSummary mid s wb₂ ws₂ wa₂ wsa₂) :
    execStmtList fields st (stmt :: rest) = .continue s /\
      ExecutionSummary st s (wb₁ ++ wb₂) (ws₁ ++ ws₂) (wa₁ ++ wa₂) (wsa₁ ++ wsa₂) := by
  constructor
  · simp [execStmtList, hstmt, hrest]
  · exact ExecutionSummary.trans hs₁ hs₂

end Compiler.Proofs.Frames

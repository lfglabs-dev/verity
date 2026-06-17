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
open Compiler.CompilationModel (Expr Field Stmt)

/-- Disjoint pieces of the source IR interpreter state.  This is intentionally
small: footprint computation will produce lists of these resources in a later
PR, while this module only proves the frame algebra over explicit write sets. -/
inductive Resource where
  | mem (lo hi : Nat)
  | binding (name : String)
  | static
  deriving Repr, DecidableEq

namespace Resource

/-- Two resources are disjoint when no state component can be written through
one and observed through the other.  Static fields are read-only for the source
interpreter, so they are disjoint from mutable resources but not from `static`
itself. -/
def Disjoint : Resource → Resource → Prop
  | .mem lo hi, .mem lo' hi' => hi ≤ lo' ∨ hi' ≤ lo
  | .binding name, .binding name' => name ≠ name'
  | .static, .static => False
  | .static, .mem _ _ => True
  | .static, .binding _ => True
  | .mem _ _, .static => True
  | .binding _, .static => True
  | .mem _ _, .binding _ => True
  | .binding _, .mem _ _ => True

theorem disjoint_comm {r w : Resource} (h : Disjoint r w) : Disjoint w r := by
  cases r <;> cases w <;> simp [Disjoint] at h ⊢
  · rcases h with h | h
    · exact Or.inr h
    · exact Or.inl h
  · exact fun heq => h heq.symm

/-- Agreement of two runtime states on one resource. -/
def OwnedEq (r : Resource) (st s : RuntimeState) : Prop :=
  match r with
  | .mem lo hi =>
      ∀ i, lo ≤ i → i < hi → s.world.memory i = st.world.memory i
  | .binding name =>
      lookupValue s.bindings name = lookupValue st.bindings name
  | .static =>
      s.selector = st.selector ∧ s.world.calldata = st.world.calldata

theorem ownedEq_refl (r : Resource) (st : RuntimeState) : OwnedEq r st st := by
  cases r <;> simp [OwnedEq]

theorem ownedEq_symm {r : Resource} {st s : RuntimeState}
    (h : OwnedEq r st s) : OwnedEq r s st := by
  cases r <;> simp [OwnedEq] at h ⊢
  · intro i hlo hhi; exact (h i hlo hhi).symm
  · exact h.symm
  · exact ⟨h.1.symm, h.2.symm⟩

theorem ownedEq_trans {r : Resource} {st mid s : RuntimeState}
    (h₁ : OwnedEq r st mid) (h₂ : OwnedEq r mid s) : OwnedEq r st s := by
  cases r <;> simp [OwnedEq] at h₁ h₂ ⊢
  · intro i hlo hhi; exact Eq.trans (h₂ i hlo hhi) (h₁ i hlo hhi)
  · exact Eq.trans h₂ h₁
  · exact ⟨Eq.trans h₂.1 h₁.1, Eq.trans h₂.2 h₁.2⟩

end Resource

open Resource

abbrev OwnedEq := Resource.OwnedEq
abbrev Disjoint := Resource.Disjoint

/-- A state transition preserves every resource disjoint from a supplied write
set.  Later footprint computation can instantiate `written`; the frame rule
below does not depend on how that list was obtained. -/
abbrev PreservesExcept (st s : RuntimeState) (written : List Resource) : Prop :=
  ∀ r, (∀ w, w ∈ written → Disjoint r w) → OwnedEq r st s

theorem preservesExcept_nil (st : RuntimeState) :
    PreservesExcept st st [] := by
  intro r _; exact Resource.ownedEq_refl r st

theorem preservesExcept_mono {st s : RuntimeState} {written written' : List Resource}
    (h : PreservesExcept st s written)
    (hsub : ∀ w, w ∈ written → w ∈ written') :
    PreservesExcept st s written' := by
  intro r hdisj
  exact h r (fun w hw => hdisj w (hsub w hw))

theorem preservesExcept_trans {st mid s : RuntimeState}
    {left right : List Resource}
    (hleft : PreservesExcept st mid left)
    (hright : PreservesExcept mid s right) :
    PreservesExcept st s (left ++ right) := by
  intro r hdisj
  apply Resource.ownedEq_trans (hleft r ?_) (hright r ?_)
  · intro w hw; exact hdisj w (List.mem_append_left _ hw)
  · intro w hw; exact hdisj w (List.mem_append_right _ hw)

/-- Statement-level frame contract over an explicit write set. -/
abbrev StmtWritesOnly (fields : List Field) (stmt : Stmt)
    (written : List Resource) : Prop :=
  ∀ ⦃st s : RuntimeState⦄,
    execStmt fields st stmt = .continue s → PreservesExcept st s written

/-- Statement-list frame contract over an explicit write set. -/
abbrev StmtsWriteOnly (fields : List Field) (stmts : List Stmt)
    (written : List Resource) : Prop :=
  ∀ ⦃st s : RuntimeState⦄,
    execStmtList fields st stmts = .continue s → PreservesExcept st s written

/-- Headline frame rule for the source IR interpreter: if a program writes only
`written`, then every resource disjoint from that write set is unchanged. -/
theorem execStmts_frame_rule
    {fields : List Field} {prog : List Stmt} {written : List Resource}
    {st s : RuntimeState} {r : Resource}
    (hwrite : StmtsWriteOnly fields prog written)
    (hdisj : ∀ w, w ∈ written → Disjoint r w)
    (hexec : execStmtList fields st prog = .continue s) :
    OwnedEq r st s :=
  hwrite hexec r hdisj

/-- Dual two-run form: if two initial states agree on a resource outside a
program's writes, then two successful executions still agree on that resource. -/
theorem execStmts_frame_rule_two_state
    {fields : List Field} {prog : List Stmt} {written : List Resource}
    {st₁ st₂ s₁ s₂ : RuntimeState} {r : Resource}
    (hwrite : StmtsWriteOnly fields prog written)
    (hagrees : OwnedEq r st₁ st₂)
    (hdisj : ∀ w, w ∈ written → Disjoint r w)
    (hexec₁ : execStmtList fields st₁ prog = .continue s₁)
    (hexec₂ : execStmtList fields st₂ prog = .continue s₂) :
    OwnedEq r s₁ s₂ := by
  exact Resource.ownedEq_trans
    (Resource.ownedEq_symm (execStmts_frame_rule hwrite hdisj hexec₁))
    (Resource.ownedEq_trans hagrees (execStmts_frame_rule hwrite hdisj hexec₂))

theorem execStmt_frame_rule
    {fields : List Field} {stmt : Stmt} {written : List Resource}
    {st s : RuntimeState} {r : Resource}
    (hwrite : StmtWritesOnly fields stmt written)
    (hdisj : ∀ w, w ∈ written → Disjoint r w)
    (hexec : execStmt fields st stmt = .continue s) :
    OwnedEq r st s :=
  hwrite hexec r hdisj

theorem stmtsWriteOnly_nil (fields : List Field) :
    StmtsWriteOnly fields [] [] := by
  intro st s h
  simp [execStmtList] at h
  subst s
  exact preservesExcept_nil st

theorem stmtsWriteOnly_cons
    {fields : List Field} {stmt : Stmt} {rest : List Stmt}
    {headWrites tailWrites : List Resource}
    (hhead : StmtWritesOnly fields stmt headWrites)
    (htail : StmtsWriteOnly fields rest tailWrites) :
    StmtsWriteOnly fields (stmt :: rest) (headWrites ++ tailWrites) := by
  intro st s hexec
  simp only [execStmtList] at hexec
  cases hstep : execStmt fields st stmt with
  | «continue» mid =>
      rw [hstep] at hexec
      exact preservesExcept_trans (hhead hstep) (htail hexec)
  | stop mid => rw [hstep] at hexec; cases hexec
  | «return» value mid => rw [hstep] at hexec; cases hexec
  | revert => rw [hstep] at hexec; cases hexec

theorem stmtWritesOnly_letVar
    (fields : List Field) (name : String) (value : Expr) :
    StmtWritesOnly fields (.letVar name value) [.binding name] := by
  intro st s h r hdisj
  cases r with
  | mem lo hi =>
      simp [OwnedEq, execStmt] at h ⊢
      split at h <;> cases h
      intro i _ _; rfl
  | binding key =>
      have hne : key ≠ name := by simpa [Disjoint] using hdisj (.binding name) (by simp)
      simp [OwnedEq, execStmt] at h ⊢
      split at h <;> cases h
      exact Compiler.Proofs.IRGeneration.FunctionBody.lookupValue_bindValue_ne _ _ _ _ hne
  | static =>
      simp [OwnedEq, execStmt] at h ⊢
      split at h <;> cases h
      exact ⟨rfl, rfl⟩

theorem stmtWritesOnly_assignVar
    (fields : List Field) (name : String) (value : Expr) :
    StmtWritesOnly fields (.assignVar name value) [.binding name] := by
  intro st s h r hdisj
  cases r with
  | mem lo hi =>
      simp [OwnedEq, execStmt] at h ⊢
      split at h <;> cases h
      intro i _ _; rfl
  | binding key =>
      have hne : key ≠ name := by simpa [Disjoint] using hdisj (.binding name) (by simp)
      simp [OwnedEq, execStmt] at h ⊢
      split at h <;> cases h
      exact Compiler.Proofs.IRGeneration.FunctionBody.lookupValue_bindValue_ne _ _ _ _ hne
  | static =>
      simp [OwnedEq, execStmt] at h ⊢
      split at h <;> cases h
      exact ⟨rfl, rfl⟩

theorem stmtWritesOnly_mstore
    (fields : List Field) (offset value : Expr) (resolvedOffset : Nat)
    (hoff : ∀ ⦃st s : RuntimeState⦄,
      execStmt fields st (.mstore offset value) = .continue s →
      evalExpr fields st offset = some resolvedOffset) :
    StmtWritesOnly fields (.mstore offset value) [.mem resolvedOffset (resolvedOffset + 1)] := by
  intro st s h r hdisj
  have hoff' := hoff h
  cases r with
  | mem lo hi =>
      simp [OwnedEq, execStmt] at h ⊢
      rw [hoff'] at h
      cases hval : evalExpr fields st value <;> simp [hval] at h
      cases h
      intro i hlo hhi
      have hne : i ≠ resolvedOffset := by
        intro heq
        have hdisj' := hdisj (.mem resolvedOffset (resolvedOffset + 1)) (by simp)
        subst i
        simp [Disjoint] at hdisj'
        rcases hdisj' with hleft | hright <;> omega
      simp [hne]
  | binding key =>
      simp [OwnedEq, execStmt] at h ⊢
      rw [hoff'] at h
      cases hval : evalExpr fields st value <;> simp [hval] at h
      cases h
      rfl
  | static =>
      simp [OwnedEq, execStmt] at h ⊢
      rw [hoff'] at h
      cases hval : evalExpr fields st value <;> simp [hval] at h
      cases h
      exact ⟨rfl, rfl⟩

theorem stmtWritesOnly_tstore
    (fields : List Field) (offset value : Expr) (resolvedOffset : Nat)
    (hoff : ∀ ⦃st s : RuntimeState⦄,
      execStmt fields st (.tstore offset value) = .continue s →
      evalExpr fields st offset = some resolvedOffset) :
    StmtWritesOnly fields (.tstore offset value) [] := by
  intro st s h r _
  cases r with
  | mem lo hi =>
      simp [OwnedEq, execStmt] at h ⊢
      rw [hoff h] at h
      cases hval : evalExpr fields st value <;> simp [hval] at h
      cases h
      intro i _ _; rfl
  | binding key =>
      simp [OwnedEq, execStmt] at h ⊢
      rw [hoff h] at h
      cases hval : evalExpr fields st value <;> simp [hval] at h
      cases h
      rfl
  | static =>
      simp [OwnedEq, execStmt] at h ⊢
      rw [hoff h] at h
      cases hval : evalExpr fields st value <;> simp [hval] at h
      cases h
      exact ⟨rfl, rfl⟩

abbrev PreservesBindingsExcept (st s : RuntimeState) (written : List String) : Prop :=
  forall key, key ∉ written -> lookupValue s.bindings key = lookupValue st.bindings key

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

abbrev PreservesSelectorCalldata (st s : RuntimeState) : Prop :=
  s.selector = st.selector /\ s.world.calldata = st.world.calldata

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

end Compiler.Proofs.Frames

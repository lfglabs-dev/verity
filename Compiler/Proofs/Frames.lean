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
      have hne : key ≠ name := by
        intro h
        subst key
        exact (hdisj (.binding name) (by simp)) rfl
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
      have hne : key ≠ name := by
        intro h
        subst key
        exact (hdisj (.binding name) (by simp)) rfl
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

/-- Syntactic constants accepted by footprint computation.  This is deliberately
state-independent: any returned value evaluates to the same word in every
runtime state. -/
def Expr.staticValue : Expr → Option Nat
  | .literal n => some (wordNormalize n)
  | _ => none

theorem evalExpr_staticValue
    {fields : List Field} {st : RuntimeState} {e : Expr} {n : Nat}
    (h : Expr.staticValue e = some n) :
    evalExpr fields st e = some n := by
  cases e
  case literal k =>
    simp [Expr.staticValue] at h
    change some (wordNormalize k) = some n
    exact congrArg some h
  all_goals simp [Expr.staticValue] at h

namespace Stmt

mutual
  /-- Computable over-approximation of resources a statement may write.

  `none` means the statement is not syntactically analyzable by this lightweight
  footprint pass, for example a memory store at a non-static offset or statements
  whose effects are outside the current `Resource` algebra. -/
  def writeFootprint : Stmt → Option (List Resource)
    | .letVar name _ => some [.binding name]
    | .assignVar name _ => some [.binding name]
    | .mstore offset _ => do
        let resolvedOffset ← Expr.staticValue offset
        some [.mem resolvedOffset (resolvedOffset + 1)]
    | .tstore _ _ => some []
    | .require _ _ => some []
    | .return _ => some []
    | .stop => some []
    | .ite _ thenBranch elseBranch => do
        let thenWrites ← writeFootprintList thenBranch
        let elseWrites ← writeFootprintList elseBranch
        some (thenWrites ++ elseWrites)
    | _ => none

  /-- List-level footprint, concatenating all successfully analyzed statements. -/
  def writeFootprintList : List Stmt → Option (List Resource)
    | [] => some []
    | stmt :: rest => do
        let headWrites ← writeFootprint stmt
        let tailWrites ← writeFootprintList rest
        some (headWrites ++ tailWrites)
end
end Stmt

theorem stmtWritesOnly_tstore_any
    (fields : List Field) (offset value : Expr) :
    StmtWritesOnly fields (.tstore offset value) [] := by
  intro st s h r _
  cases r <;> simp [OwnedEq, execStmt] at h ⊢
  · cases hoff : evalExpr fields st offset <;> simp [hoff] at h
    cases hval : evalExpr fields st value <;> simp [hval] at h
    cases h
    intro i _ _; rfl
  · cases hoff : evalExpr fields st offset <;> simp [hoff] at h
    cases hval : evalExpr fields st value <;> simp [hval] at h
    cases h
    rfl
  · cases hoff : evalExpr fields st offset <;> simp [hoff] at h
    cases hval : evalExpr fields st value <;> simp [hval] at h
    cases h
    exact ⟨rfl, rfl⟩

theorem stmtWritesOnly_require
    (fields : List Field) (cond : Expr) (message : String) :
    StmtWritesOnly fields (.require cond message) [] := by
  intro st s h r _
  simp [execStmt] at h
  split at h <;> try cases h
  split at h <;> cases h
  exact preservesExcept_nil st r (by simp)

theorem stmtWritesOnly_return
    (fields : List Field) (value : Expr) :
    StmtWritesOnly fields (.return value) [] := by
  intro st s h
  simp [execStmt] at h
  split at h <;> cases h

theorem stmtWritesOnly_stop
    (fields : List Field) :
    StmtWritesOnly fields .stop [] := by
  intro st s h
  simp [execStmt] at h

mutual
  theorem stmtWritesOnly_writeFootprint
      {fields : List Field} {stmt : Stmt} {written : List Resource}
      (hfp : Stmt.writeFootprint stmt = some written) :
      StmtWritesOnly fields stmt written := by
    revert written
    cases stmt <;> intro written hfp <;> simp [Stmt.writeFootprint] at hfp
    case letVar name value =>
      cases hfp; exact stmtWritesOnly_letVar fields name value
    case assignVar name value =>
      cases hfp; exact stmtWritesOnly_assignVar fields name value
    case mstore offset value =>
      cases hoff : Expr.staticValue offset <;> simp [hoff] at hfp
      cases hfp
      apply stmtWritesOnly_mstore fields offset value _
      intro st' _s' _h
      exact evalExpr_staticValue (fields := fields) (st := st') (h := hoff)
    case tstore offset value =>
      cases hfp; exact stmtWritesOnly_tstore_any fields offset value
    case require cond message =>
      cases hfp; exact stmtWritesOnly_require fields cond message
    case «return» value =>
      cases hfp; exact stmtWritesOnly_return fields value
    case stop =>
      cases hfp; exact stmtWritesOnly_stop fields
    case ite cond thenBranch elseBranch =>
      cases hthen : Stmt.writeFootprintList thenBranch <;> simp [hthen] at hfp
      cases helse : Stmt.writeFootprintList elseBranch <;> simp [helse] at hfp
      cases hfp
      intro st s hexec
      simp [execStmt] at hexec
      split at hexec <;> try cases hexec
      split at hexec
      · exact preservesExcept_mono
          (stmtListWritesOnly_writeFootprint helse hexec)
          (fun w hw => List.mem_append_right _ hw)
      · exact preservesExcept_mono
          (stmtListWritesOnly_writeFootprint hthen hexec)
          (fun w hw => List.mem_append_left _ hw)

  theorem stmtListWritesOnly_writeFootprint
      {fields : List Field} {stmts : List Stmt} {written : List Resource}
      (hfp : Stmt.writeFootprintList stmts = some written) :
      StmtsWriteOnly fields stmts written := by
    cases stmts with
    | nil =>
        simp [Stmt.writeFootprintList] at hfp
        cases hfp
        exact stmtsWriteOnly_nil fields
    | cons stmt rest =>
        simp [Stmt.writeFootprintList] at hfp
        cases hhead : Stmt.writeFootprint stmt <;> simp [hhead] at hfp
        cases htail : Stmt.writeFootprintList rest <;> simp [htail] at hfp
        cases hfp
        exact stmtsWriteOnly_cons
          (stmtWritesOnly_writeFootprint hhead)
          (stmtListWritesOnly_writeFootprint htail)
end

theorem execStmt_frame_rule_writeFootprint
    {fields : List Field} {stmt : Stmt} {written : List Resource}
    {st s : RuntimeState} {r : Resource}
    (hfp : Stmt.writeFootprint stmt = some written)
    (hdisj : ∀ w, w ∈ written → Disjoint r w)
    (hexec : execStmt fields st stmt = .continue s) :
    OwnedEq r st s :=
  execStmt_frame_rule (stmtWritesOnly_writeFootprint hfp) hdisj hexec

theorem execStmts_frame_rule_writeFootprint
    {fields : List Field} {prog : List Stmt} {written : List Resource}
    {st s : RuntimeState} {r : Resource}
    (hfp : Stmt.writeFootprintList prog = some written)
    (hdisj : ∀ w, w ∈ written → Disjoint r w)
    (hexec : execStmtList fields st prog = .continue s) :
    OwnedEq r st s :=
  execStmts_frame_rule (stmtListWritesOnly_writeFootprint hfp) hdisj hexec

/-- A coupling invariant relates a concrete interpreter state to an abstract
model state. -/
structure Coupling (Abs : Type u) where
  Inv : RuntimeState → Abs → Prop

namespace Coupling

/-- The conjunction of two couplings over a product abstract state. -/
def and (left : Coupling Abs) (right : Coupling Beta) :
    Coupling (Abs × Beta) where
  Inv st ab := left.Inv st ab.1 ∧ right.Inv st ab.2

/-- A resource support is sufficient for a coupling when agreement on every
supported resource transports the invariant between concrete states. -/
def Supported (c : Coupling Abs) (support : List Resource) : Prop :=
  ∀ ⦃st s : RuntimeState⦄ ⦃a : Abs⦄,
    (∀ r, r ∈ support → OwnedEq r st s) → c.Inv st a → c.Inv s a

theorem supported_mono {c : Coupling Abs} {support support' : List Resource}
    (hs : Supported c support)
    (hsub : ∀ r, r ∈ support → r ∈ support') :
    Supported c support' := by
  intro st s a hsame hinv
  exact hs (fun r hr => hsame r (hsub r hr)) hinv

theorem supported_and {left : Coupling Abs} {right : Coupling Beta}
    {leftSupport rightSupport : List Resource}
    (hleft : Supported left leftSupport)
    (hright : Supported right rightSupport) :
    Supported (Coupling.and left right) (leftSupport ++ rightSupport) := by
  intro st s ab hsame hinv
  exact ⟨
    hleft (fun r hr => hsame r (List.mem_append_left _ hr)) hinv.1,
    hright (fun r hr => hsame r (List.mem_append_right _ hr)) hinv.2⟩

/-- Abstract transition produced by iterating an indexed step from `index` for
`remaining` iterations. -/
def iterFrom (step : Nat → Abs → Abs) :
    Nat → Nat → Abs → Abs
  | _, 0, a => a
  | index, remaining + 1, a =>
      iterFrom step (index + 1) remaining (step index a)

@[simp] theorem iterFrom_zero
    (step : Nat → Abs → Abs) (index : Nat) :
    iterFrom step index 0 = _root_.id := by
  funext a
  rfl

@[simp] theorem iterFrom_succ
    (step : Nat → Abs → Abs) (index remaining : Nat) (a : Abs) :
    iterFrom step index (remaining + 1) a =
      iterFrom step (index + 1) remaining (step index a) := rfl

end Coupling

/-- Generalized segment simulation for a source IR program under a field
environment. The issue-facing `SegmentSim` below specializes this to `[]`. -/
def SegmentSimWithFields (fields : List Field) (c : Coupling Abs)
    (prog : List Stmt) (f : Abs → Abs) : Prop :=
  ∀ ⦃st : RuntimeState⦄ ⦃a : Abs⦄ ⦃s : RuntimeState⦄,
    c.Inv st a → execStmtList fields st prog = .continue s → c.Inv s (f a)

/-- Issue-facing simulation predicate for source IR segments. -/
abbrev SegmentSim (c : Coupling Abs) (prog : List Stmt) (f : Abs → Abs) : Prop :=
  SegmentSimWithFields [] c prog f

theorem execStmtList_append_continue
    {fields : List Field} {p q : List Stmt} {st s : RuntimeState}
    (hexec : execStmtList fields st (p ++ q) = .continue s) :
    ∃ mid,
      execStmtList fields st p = .continue mid ∧
      execStmtList fields mid q = .continue s := by
  induction p generalizing st with
  | nil =>
      exact ⟨st, rfl, hexec⟩
  | cons stmt rest ih =>
      simp only [List.cons_append, execStmtList] at hexec ⊢
      cases hstmt : execStmt fields st stmt with
      | «continue» next =>
          rw [hstmt] at hexec
          rcases ih hexec with ⟨mid, hrest, hq⟩
          exact ⟨mid, by simp [hrest], hq⟩
      | stop next => rw [hstmt] at hexec; cases hexec
      | «return» value next => rw [hstmt] at hexec; cases hexec
      | revert => rw [hstmt] at hexec; cases hexec

theorem execStmtList_append_continue_of
    {fields : List Field} {p q : List Stmt} {st mid s : RuntimeState}
    (hp : execStmtList fields st p = .continue mid)
    (hq : execStmtList fields mid q = .continue s) :
    execStmtList fields st (p ++ q) = .continue s := by
  induction p generalizing st with
  | nil =>
      simp [execStmtList] at hp
      cases hp
      exact hq
  | cons stmt rest ih =>
      simp only [List.cons_append, execStmtList] at hp ⊢
      cases hstmt : execStmt fields st stmt with
      | «continue» next =>
          rw [hstmt] at hp
          exact ih hp
      | stop next => rw [hstmt] at hp; cases hp
      | «return» value next => rw [hstmt] at hp; cases hp
      | revert => rw [hstmt] at hp; cases hp

namespace SegmentSimWithFields

theorem id (fields : List Field) (c : Coupling Abs) :
    SegmentSimWithFields fields c [] _root_.id := by
  intro st a s hinv hexec
  simp [execStmtList] at hexec
  cases hexec
  exact hinv

theorem seq {fields : List Field} {c : Coupling Abs}
    {p q : List Stmt} {f g : Abs → Abs}
    (hp : SegmentSimWithFields fields c p f)
    (hq : SegmentSimWithFields fields c q g) :
    SegmentSimWithFields fields c (p ++ q) (g ∘ f) := by
  intro st a s hinv hexec
  rcases execStmtList_append_continue hexec with ⟨mid, hpExec, hqExec⟩
  exact hq (hp hinv hpExec) hqExec

theorem weaken {fields : List Field} {c d : Coupling Abs}
    {prog : List Stmt} {f : Abs → Abs}
    (hcd : ∀ ⦃st a⦄, d.Inv st a → c.Inv st a)
    (hdc : ∀ ⦃st a⦄, c.Inv st (f a) → d.Inv st (f a))
    (hsim : SegmentSimWithFields fields c prog f) :
    SegmentSimWithFields fields d prog f := by
  intro st a s hinv hexec
  exact hdc (hsim (hcd hinv) hexec)

/-- A segment whose writes are disjoint from a coupling support preserves that
coupling with the identity abstract transition. -/
theorem frame {fields : List Field} {c : Coupling Abs}
    {prog : List Stmt} {written support : List Resource}
    (hsupport : Coupling.Supported c support)
    (hwrite : StmtsWriteOnly fields prog written)
    (hdisj : ∀ r, r ∈ support → ∀ w, w ∈ written → Disjoint r w) :
    SegmentSimWithFields fields c prog _root_.id := by
  intro st a s hinv hexec
  exact hsupport
    (fun r hr => execStmts_frame_rule hwrite (hdisj r hr) hexec)
    hinv

theorem frame_writeFootprint {fields : List Field} {c : Coupling Abs}
    {prog : List Stmt} {written support : List Resource}
    (hsupport : Coupling.Supported c support)
    (hfp : Stmt.writeFootprintList prog = some written)
    (hdisj : ∀ r, r ∈ support → ∀ w, w ∈ written → Disjoint r w) :
    SegmentSimWithFields fields c prog _root_.id :=
  frame hsupport (stmtListWritesOnly_writeFootprint hfp) hdisj

/-- Combine a local simulation with a framed invariant for untouched resources. -/
theorem and_frame {fields : List Field}
    {localCoupling : Coupling Abs} {framed : Coupling Beta}
    {prog : List Stmt} {written support : List Resource}
    {f : Abs → Abs}
    (hlocal : SegmentSimWithFields fields localCoupling prog f)
    (hsupport : Coupling.Supported framed support)
    (hwrite : StmtsWriteOnly fields prog written)
    (hdisj : ∀ r, r ∈ support → ∀ w, w ∈ written → Disjoint r w) :
    SegmentSimWithFields fields (Coupling.and localCoupling framed) prog
      (fun ab => (f ab.1, ab.2)) := by
  intro st ab s hinv hexec
  exact ⟨
    hlocal hinv.1 hexec,
    frame hsupport hwrite hdisj hinv.2 hexec⟩

theorem execForEachLoop_sim
    {fields : List Field} {c : Coupling Abs} {varName : String}
    {body : List Stmt} {step : Nat → Abs → Abs}
    (hbody : ∀ index, SegmentSimWithFields fields c body (step index))
    (hbind : ∀ ⦃st : RuntimeState⦄ ⦃a : Abs⦄ index,
      c.Inv st a →
      c.Inv { st with bindings := bindValue st.bindings varName (wordNormalize index) } a) :
    ∀ ⦃remaining index : Nat⦄ ⦃st s : RuntimeState⦄ ⦃a : Abs⦄,
      c.Inv st a →
      execForEachLoop varName
        (fun loopState => execStmtList fields loopState body)
        st index remaining = .continue s →
      c.Inv s (Coupling.iterFrom step index remaining a) := by
  intro remaining
  induction remaining with
  | zero =>
      intro index st s a hinv hexec
      simp [execForEachLoop] at hexec
      cases hexec
      exact hinv
  | succ remaining ih =>
      intro index st s a hinv hexec
      rw [execForEachLoop_succ] at hexec
      let loopState :=
        { st with bindings := bindValue st.bindings varName (wordNormalize index) }
      cases hrun : execStmtList fields loopState body with
      | «continue» next =>
          simp only [loopState, hrun] at hexec
          exact ih
            (hbody index (hbind index hinv) hrun)
            hexec
      | stop next => simp only [loopState, hrun] at hexec; cases hexec
      | «return» value next => simp only [loopState, hrun] at hexec; cases hexec
      | revert => simp only [loopState, hrun] at hexec; cases hexec

theorem forEach
    {fields : List Field} {c : Coupling Abs} {varName : String}
    {count : Expr} {body : List Stmt} {step : Nat → Abs → Abs} {bound : Nat}
    (hbody : ∀ index, SegmentSimWithFields fields c body (step index))
    (hbind : ∀ ⦃st : RuntimeState⦄ ⦃a : Abs⦄ index,
      c.Inv st a →
      c.Inv { st with bindings := bindValue st.bindings varName (wordNormalize index) } a)
    (hcount : ∀ ⦃st s : RuntimeState⦄,
      execStmt fields st (.forEach varName count body) = .continue s →
      evalExpr fields st count = some bound) :
    SegmentSimWithFields fields c [.forEach varName count body]
      (Coupling.iterFrom step 0 bound) := by
  intro st a s hinv hexec
  simp [execStmtList] at hexec
  cases hstmt : execStmt fields st (.forEach varName count body) with
  | «continue» next =>
      rw [hstmt] at hexec
      cases hexec
      rw [show execStmt fields st (.forEach varName count body) =
        match evalExpr fields st count with
        | some bound =>
            let initialLoopState :=
              { st with bindings := bindValue st.bindings varName (wordNormalize 0) }
            execForEachLoop varName
              (fun loopState => execStmtList fields loopState body)
              initialLoopState 0 bound
        | none => .revert from rfl] at hstmt
      rw [hcount hstmt] at hstmt
      exact execForEachLoop_sim hbody hbind (hbind 0 hinv) hstmt
  | stop next => rw [hstmt] at hexec; cases hexec
  | «return» value next => rw [hstmt] at hexec; cases hexec
  | revert => rw [hstmt] at hexec; cases hexec

end SegmentSimWithFields

namespace SegmentSim

theorem id (c : Coupling Abs) : SegmentSim c [] id :=
  SegmentSimWithFields.id [] c

theorem seq {c : Coupling Abs} {p q : List Stmt} {f g : Abs → Abs}
    (hp : SegmentSim c p f) (hq : SegmentSim c q g) :
    SegmentSim c (p ++ q) (g ∘ f) :=
  SegmentSimWithFields.seq hp hq

theorem weaken {c d : Coupling Abs} {prog : List Stmt} {f : Abs → Abs}
    (hcd : ∀ ⦃st a⦄, d.Inv st a → c.Inv st a)
    (hdc : ∀ ⦃st a⦄, c.Inv st (f a) → d.Inv st (f a))
    (hsim : SegmentSim c prog f) :
    SegmentSim d prog f :=
  SegmentSimWithFields.weaken hcd hdc hsim

theorem frame {c : Coupling Abs} {prog : List Stmt}
    {written support : List Resource}
    (hsupport : Coupling.Supported c support)
    (hwrite : StmtsWriteOnly [] prog written)
    (hdisj : ∀ r, r ∈ support → ∀ w, w ∈ written → Disjoint r w) :
    SegmentSim c prog _root_.id :=
  SegmentSimWithFields.frame hsupport hwrite hdisj

theorem frame_writeFootprint {c : Coupling Abs} {prog : List Stmt}
    {written support : List Resource}
    (hsupport : Coupling.Supported c support)
    (hfp : Stmt.writeFootprintList prog = some written)
    (hdisj : ∀ r, r ∈ support → ∀ w, w ∈ written → Disjoint r w) :
    SegmentSim c prog _root_.id :=
  SegmentSimWithFields.frame_writeFootprint hsupport hfp hdisj

theorem and_frame {localCoupling : Coupling Abs} {framed : Coupling Beta}
    {prog : List Stmt} {written support : List Resource} {f : Abs → Abs}
    (hlocal : SegmentSim localCoupling prog f)
    (hsupport : Coupling.Supported framed support)
    (hwrite : StmtsWriteOnly [] prog written)
    (hdisj : ∀ r, r ∈ support → ∀ w, w ∈ written → Disjoint r w) :
    SegmentSim (Coupling.and localCoupling framed) prog (fun ab => (f ab.1, ab.2)) :=
  SegmentSimWithFields.and_frame hlocal hsupport hwrite hdisj

theorem forEach
    {c : Coupling Abs} {varName : String} {count : Expr}
    {body : List Stmt} {step : Nat → Abs → Abs} {bound : Nat}
    (hbody : ∀ index, SegmentSim c body (step index))
    (hbind : ∀ ⦃st : RuntimeState⦄ ⦃a : Abs⦄ index,
      c.Inv st a →
      c.Inv { st with bindings := bindValue st.bindings varName (wordNormalize index) } a)
    (hcount : ∀ ⦃st s : RuntimeState⦄,
      execStmt [] st (.forEach varName count body) = .continue s →
      evalExpr [] st count = some bound) :
    SegmentSim c [.forEach varName count body] (Coupling.iterFrom step 0 bound) :=
  SegmentSimWithFields.forEach hbody hbind hcount

end SegmentSim

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
  simp [writeUintSlots, hcontains]

theorem writeStorageWordSlots_preserves_storage_except
    (world : Verity.ContractState) (slots : List Nat) (wordOffset value slot : Nat)
    (hslot : slot ∉ slots.map (fun base => wordNormalize (base + wordOffset))) :
    (writeStorageWordSlots world slots wordOffset value).storage slot = world.storage slot := by
  have hcontains :
      (slots.map (fun base => wordNormalize (base + wordOffset))).contains slot = false := by
    simpa [List.elem_eq_contains] using hslot
  simp [writeStorageWordSlots, hcontains]

theorem writeStorageWordSlots_preserves_address_except
    (world : Verity.ContractState) (slots : List Nat) (wordOffset value slot : Nat)
    (hslot : slot ∉ slots.map (fun base => wordNormalize (base + wordOffset))) :
    (writeStorageWordSlots world slots wordOffset value).storageAddr slot =
      world.storageAddr slot := by
  have hcontains :
      (slots.map (fun base => wordNormalize (base + wordOffset))).contains slot = false := by
    simpa [List.elem_eq_contains] using hslot
  simp [writeStorageWordSlots, hcontains]

theorem writeAddressSlots_preserves_address_except
    (world : Verity.ContractState) (slots : List Nat) (value slot : Nat)
    (hslot : slot ∉ slots.map wordNormalize) :
    (writeAddressSlots world slots value).storageAddr slot = world.storageAddr slot := by
  have hcontains : (slots.map wordNormalize).contains slot = false := by
    simpa [List.elem_eq_contains] using hslot
  simp [writeAddressSlots, hcontains]

theorem writeUintFieldSlots_preserves_storage_except
    (fields : List Compiler.CompilationModel.Field) (fieldName : String)
    (world : Verity.ContractState) (slots : List Nat) (value slot : Nat)
    (hslot : slot ∉ slots.map wordNormalize) :
    (writeUintFieldSlots fields fieldName world slots value).storage slot = world.storage slot := by
  have hcontains : (slots.map wordNormalize).contains slot = false := by
    simpa [List.elem_eq_contains] using hslot
  generalize hfind : Compiler.CompilationModel.findFieldWithResolvedSlot fields fieldName = found
  cases found with
  | none =>
      simpa [writeUintFieldSlots, hfind] using
        writeUintSlots_preserves_storage_except world slots value slot hslot
  | some result =>
      rcases result with ⟨field, resolvedSlot⟩
      generalize hpacked : field.packedBits = packed
      cases packed <;> simp only [writeUintFieldSlots, hfind, hpacked] <;> split
      · simp [writeTransientTargets]
      · exact writeUintSlots_preserves_storage_except world slots value slot hslot
      · simp
      · simp [hcontains]

theorem writeUintFieldSlots_preserves_address
    (fields : List Compiler.CompilationModel.Field) (fieldName : String)
    (world : Verity.ContractState) (slots : List Nat) (value slot : Nat) :
    (writeUintFieldSlots fields fieldName world slots value).storageAddr slot =
      world.storageAddr slot := by
  generalize hfind : Compiler.CompilationModel.findFieldWithResolvedSlot fields fieldName = found
  cases found with
  | none => simp [writeUintFieldSlots, hfind, writeUintSlots]
  | some result =>
      rcases result with ⟨field, resolvedSlot⟩
      generalize hpacked : field.packedBits = packed
      cases packed <;> simp only [writeUintFieldSlots, hfind, hpacked] <;>
        split <;> simp [writeUintSlots, writeTransientTargets]

theorem writeUintFieldSlots_preserves_arrays
    (fields : List Compiler.CompilationModel.Field) (fieldName : String)
    (world : Verity.ContractState) (slots : List Nat) (value slot : Nat) :
    (writeUintFieldSlots fields fieldName world slots value).storageArray slot =
      world.storageArray slot := by
  generalize hfind : Compiler.CompilationModel.findFieldWithResolvedSlot fields fieldName = found
  cases found with
  | none => simp [writeUintFieldSlots, hfind, writeUintSlots]
  | some result =>
      rcases result with ⟨field, resolvedSlot⟩
      generalize hpacked : field.packedBits = packed
      cases packed <;> simp only [writeUintFieldSlots, hfind, hpacked] <;>
        split <;> simp [writeUintSlots, writeTransientTargets]

theorem writeUintFieldSlots_preserves_calldata
    (fields : List Compiler.CompilationModel.Field) (fieldName : String)
    (world : Verity.ContractState) (slots : List Nat) (value : Nat) :
    (writeUintFieldSlots fields fieldName world slots value).calldata = world.calldata := by
  generalize hfind : Compiler.CompilationModel.findFieldWithResolvedSlot fields fieldName = found
  cases found with
  | none => simp [writeUintFieldSlots, hfind, writeUintSlots]
  | some result =>
      rcases result with ⟨field, resolvedSlot⟩
      generalize hpacked : field.packedBits = packed
      cases packed <;> simp only [writeUintFieldSlots, hfind, hpacked] <;>
        split <;> simp [writeUintSlots, writeTransientTargets]

theorem writeAddressFieldSlots_preserves_address_except
    (fields : List Compiler.CompilationModel.Field) (fieldName : String)
    (world : Verity.ContractState) (slots : List Nat) (value slot : Nat)
    (hslot : slot ∉ slots.map wordNormalize) :
    (writeAddressFieldSlots fields fieldName world slots value).storageAddr slot =
      world.storageAddr slot := by
  simp only [writeAddressFieldSlots]
  split
  · have hcontains : (slots.map wordNormalize).contains slot = false := by
      simpa [List.elem_eq_contains] using hslot
    simp [writeTransientTargets, hcontains]
  · exact writeAddressSlots_preserves_address_except world slots value slot hslot

theorem writeAddressFieldSlots_preserves_storage
    (fields : List Compiler.CompilationModel.Field) (fieldName : String)
    (world : Verity.ContractState) (slots : List Nat) (value slot : Nat) :
    (writeAddressFieldSlots fields fieldName world slots value).storage slot = world.storage slot := by
  simp only [writeAddressFieldSlots]
  split <;> simp [writeTransientTargets, writeAddressSlots]

theorem writeAddressFieldSlots_preserves_arrays
    (fields : List Compiler.CompilationModel.Field) (fieldName : String)
    (world : Verity.ContractState) (slots : List Nat) (value slot : Nat) :
    (writeAddressFieldSlots fields fieldName world slots value).storageArray slot =
      world.storageArray slot := by
  simp only [writeAddressFieldSlots]
  split <;> simp [writeTransientTargets, writeAddressSlots]

theorem writeAddressFieldSlots_preserves_calldata
    (fields : List Compiler.CompilationModel.Field) (fieldName : String)
    (world : Verity.ContractState) (slots : List Nat) (value : Nat) :
    (writeAddressFieldSlots fields fieldName world slots value).calldata = world.calldata := by
  simp only [writeAddressFieldSlots]
  split <;> simp [writeTransientTargets, writeAddressSlots]

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
        .continue { st with world := writeUintFieldSlots fields fieldName st.world slots resolved }
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
        exact writeUintFieldSlots_preserves_storage_except fields fieldName st.world slots resolved slot hslot
      · intro slot _
        exact writeUintFieldSlots_preserves_address fields fieldName st.world slots resolved slot
      · intro slot _
        exact writeUintFieldSlots_preserves_arrays fields fieldName st.world slots resolved slot
      · exact And.intro rfl
          (writeUintFieldSlots_preserves_calldata fields fieldName st.world slots resolved)

theorem execStmt_setStorageAddr_execution_summary
    (fields : List Compiler.CompilationModel.Field)
    (st s : RuntimeState) (fieldName : String) (value : Expr) (slots : List Nat)
    (hslots : Compiler.CompilationModel.findFieldWriteSlots fields fieldName = some slots)
    (h : execStmt fields st (.setStorageAddr fieldName value) = .continue s) :
    ExecutionSummary st s [] [] (slots.map wordNormalize) [] := by
  rw [show execStmt fields st (.setStorageAddr fieldName value) =
    (match Compiler.CompilationModel.findFieldWriteSlots fields fieldName, evalExpr fields st value with
    | some slots, some resolved =>
        .continue { st with world := writeAddressFieldSlots fields fieldName st.world slots resolved }
    | _, _ => .revert) from rfl] at h
  rw [hslots] at h
  cases hval : evalExpr fields st value with
  | none => rw [hval] at h; exact absurd h (by simp)
  | some resolved =>
      rw [hval] at h
      injection h with hh; subst hh
      constructor
      · intro _ _; rfl
      · intro slot _
        exact writeAddressFieldSlots_preserves_storage fields fieldName st.world slots resolved slot
      · intro slot hslot
        exact writeAddressFieldSlots_preserves_address_except fields fieldName st.world slots resolved slot hslot
      · intro slot _
        exact writeAddressFieldSlots_preserves_arrays fields fieldName st.world slots resolved slot
      · exact And.intro rfl
          (writeAddressFieldSlots_preserves_calldata fields fieldName st.world slots resolved)

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

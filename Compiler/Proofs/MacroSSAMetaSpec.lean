import Compiler.CompilationModel.InternalNaming

namespace Compiler.Proofs.MacroSSAMetaSpec

/-!
# Meta-Spec 11: Macro SSA & Syntax Desugaring Equivalence (`verity_contract` v2)

Formalizes the Three-Layer Specification Architecture for the `verity_contract` v2
SSA and syntax desugaring pass (`Verity.Macro.Translate.SSADesugar`):

- **Layer I (Foundational Meta-Specification)**:
  Models the imperative/mutable `do`-block statement language (`ImpStmt`: `letMut`,
  `assign`, `bindEffect`, `oneArmedIf`, `ite`, `discardBind`, `seq`, `ret`) and
  expression language (`ImpExpr`: `var`, `litInt`, `litBool`, `boolNot`, `cond`,
  `add`, `zeroArgCall`), together with the pure functional SSA target (`SSAStmt`,
  `SSAExpr`) and explicit SSA version/discard environment (`SSAEnv`).
  Proves the universal semantic preservation theorem `SSADesugarMetaSpec`.

- **Layer II (Derived Structural Corollaries)**:
  - `desugarOneArmedIf_sound` (`#2427`)
  - `desugarBoolNot_sound` (`#2434`)
  - `desugarDiscardBind_sound` and `freshDiscardName_not_mem` (`#2421`)
  - `desugarZeroArgHelper_sound` (`#2431`)

- **Layer III (Executable Witness Suite)**:
  Concrete `by decide` regression witnesses (`0 native_decide`) covering
  interleaved `let mut` / monadic binds, one-armed `if`, hygienic discard binds,
  `!b` / signed `Int256` ternary `if c then -1 else 1`, and 0-arg helper calls.
-/

/-! ## Layer I: Foundational Meta-Specification -/

/-- Runtime values in the macro desugaring semantics (signed 256-bit words and Booleans). -/
inductive Val where
  | int (n : Int)
  | bool (b : Bool)
  deriving DecidableEq, Repr, Inhabited

namespace Val

def toInt : Val → Int
  | .int n => n
  | .bool b => if b then 1 else 0

def toBool : Val → Bool
  | .bool b => b
  | .int n => n != 0

def logicalNot : Val → Val
  | .bool b => .bool (!b)
  | .int n => .bool (n == 0)

end Val

/-- Abstract contract storage state (finite slot table with default 0). -/
structure State where
  slots : List (Nat × Int) := []
  deriving DecidableEq, Repr, Inhabited

namespace State

def read (s : State) (slot : Nat) : Int :=
  match s.slots.lookup slot with
  | some v => v
  | none => 0

def write (s : State) (slot : Nat) (v : Int) : State :=
  ⟨(slot, v) :: s.slots.filter (fun entry => entry.1 != slot)⟩

end State

/-- Imperative local variable environment (`String` identifiers). -/
structure ImpLocalEnv where
  entries : List (String × Val) := []
  deriving DecidableEq, Repr, Inhabited

namespace ImpLocalEnv

def get (env : ImpLocalEnv) (x : String) : Val :=
  match env.entries.lookup x with
  | some v => v
  | none => .int 0

def set (env : ImpLocalEnv) (x : String) (v : Val) : ImpLocalEnv :=
  ⟨(x, v) :: env.entries⟩

@[simp] theorem get_set_same (env : ImpLocalEnv) (x : String) (v : Val) :
    (env.set x v).get x = v := by
  simp [get, set]

@[simp] theorem get_set_ne (env : ImpLocalEnv) {x y : String} (v : Val) (h : y ≠ x) :
    (env.set x v).get y = env.get y := by
  have hbeq : (y == x) = false := beq_eq_false_iff_ne.mpr h
  simp [get, set, List.lookup, hbeq]

end ImpLocalEnv

/-- Partitioned SSA variable namespace separating user variables from synthetic discards. -/
inductive SSAVar where
  | user (name : String)
  | discard (index : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- SSA local variable environment keyed by `SSAVar`. -/
structure SSALocalEnv where
  entries : List (SSAVar × Val) := []
  deriving DecidableEq, Repr, Inhabited

namespace SSALocalEnv

def get (env : SSALocalEnv) (k : SSAVar) : Val :=
  match env.entries.lookup k with
  | some v => v
  | none => .int 0

def set (env : SSALocalEnv) (k : SSAVar) (v : Val) : SSALocalEnv :=
  ⟨(k, v) :: env.entries⟩

@[simp] theorem get_set_same (env : SSALocalEnv) (k : SSAVar) (v : Val) :
    (env.set k v).get k = v := by
  simp [get, set]

@[simp] theorem get_set_ne (env : SSALocalEnv) {k q : SSAVar} (v : Val) (h : q ≠ k) :
    (env.set k v).get q = env.get q := by
  have hbeq : (q == k) = false := beq_eq_false_iff_ne.mpr h
  simp [get, set, List.lookup, hbeq]

end SSALocalEnv

/-- Zero-argument helper call form before normalization (`fn ()` vs `fn`). -/
inductive ZeroArgCallStyle where
  | unitTupleArg
  | bareRef
  deriving DecidableEq, Repr

/-- Source imperative expressions (`#2427`, `#2434`, `#2431`). -/
inductive ImpExpr where
  | var (name : String)
  | litInt (n : Int)
  | litBool (b : Bool)
  | boolNot (arg : ImpExpr)
  | cond (c thenVal elseVal : ImpExpr)
  | add (lhs rhs : ImpExpr)
  | zeroArgCall (style : ZeroArgCallStyle) (retVal : Int)
  deriving DecidableEq, Repr

/-- Target SSA / CompilationModel expressions. -/
inductive SSAExpr where
  | var (v : SSAVar)
  | litInt (n : Int)
  | litBool (b : Bool)
  | logicalNot (arg : SSAExpr)
  | ite (c thenVal elseVal : SSAExpr)
  | add (lhs rhs : SSAExpr)
  | zeroArgCallNormalized (retVal : Int)
  deriving DecidableEq, Repr

/-- Monadic state effect operations (`getStorage`, `setStorage`, and 0-arg helper effects). -/
inductive EffectOp (ExprTy : Type) where
  | getStorage (slot : Nat)
  | setStorage (slot : Nat) (valExpr : ExprTy)
  | zeroArgHelperEffect (hasUnitArg : Bool) (slot : Nat) (delta : Int)
  deriving DecidableEq, Repr

/-- Source imperative `do`-block statements (`#2427`, `#2421`, `#2431`). -/
inductive ImpStmt where
  | letMut (x : String) (rhs : ImpExpr)
  | assign (x : String) (rhs : ImpExpr)
  | bindEffect (x : String) (eff : EffectOp ImpExpr)
  | oneArmedIf (cond : ImpExpr) (thenBranch : ImpStmt)
  | ite (cond : ImpExpr) (thenBranch elseBranch : ImpStmt)
  | discardBind (eff : EffectOp ImpExpr)
  | seq (s1 s2 : ImpStmt)
  | ret (rhs : ImpExpr)
  deriving DecidableEq, Repr

/-- Target desugared SSA / monadic statements. -/
inductive SSAStmt where
  | skip
  | letImm (v : SSAVar) (rhs : SSAExpr)
  | bindEffect (v : SSAVar) (eff : EffectOp SSAExpr)
  | ite (cond : SSAExpr) (thenBranch elseBranch : SSAStmt)
  | seq (s1 s2 : SSAStmt)
  | ret (rhs : SSAExpr)
  deriving DecidableEq, Repr

/-- Explicit SSA version and fresh-discard environment threaded by the desugaring pass. -/
structure SSAEnv where
  versions : List (String × Nat) := []
  nextDiscard : Nat := 0
  deriving DecidableEq, Repr, Inhabited

namespace SSAEnv

def versionOf (env : SSAEnv) (x : String) : Nat :=
  (env.versions.lookup x).getD 0

def bumpVersion (env : SSAEnv) (x : String) : SSAEnv :=
  let v := env.versionOf x + 1
  { env with versions := (x, v) :: env.versions.filter (fun e => e.1 != x) }

def allocDiscard (env : SSAEnv) : Nat × SSAEnv :=
  (env.nextDiscard, { env with nextDiscard := env.nextDiscard + 1 })

end SSAEnv

/-- Desugar an imperative expression into its SSA / CompilationModel counterpart. -/
def desugarExpr : ImpExpr → SSAExpr
  | .var name => .var (.user name)
  | .litInt n => .litInt n
  | .litBool b => .litBool b
  | .boolNot arg => .logicalNot (desugarExpr arg)
  | .cond c t f => .ite (desugarExpr c) (desugarExpr t) (desugarExpr f)
  | .add l r => .add (desugarExpr l) (desugarExpr r)
  | .zeroArgCall _ retVal => .zeroArgCallNormalized retVal

/-- Desugar a monadic effect operation, normalizing 0-arg helper calls (`fn ()` → `fn`). -/
def desugarEffect : EffectOp ImpExpr → EffectOp SSAExpr
  | .getStorage slot => .getStorage slot
  | .setStorage slot valExpr => .setStorage slot (desugarExpr valExpr)
  | .zeroArgHelperEffect _ slot delta => .zeroArgHelperEffect false slot delta

/-- Desugar an imperative `do` statement into `SSAStmt` while threading `SSAEnv`. -/
def desugarImpToSSA (env : SSAEnv) : ImpStmt → SSAStmt × SSAEnv
  | .letMut x rhs =>
      (.letImm (.user x) (desugarExpr rhs), env.bumpVersion x)
  | .assign x rhs =>
      (.letImm (.user x) (desugarExpr rhs), env.bumpVersion x)
  | .bindEffect x eff =>
      (.bindEffect (.user x) (desugarEffect eff), env.bumpVersion x)
  | .oneArmedIf cond thenBranch =>
      let (ssaThen, envThen) := desugarImpToSSA env thenBranch
      (.ite (desugarExpr cond) ssaThen .skip, envThen)
  | .ite cond thenBranch elseBranch =>
      let (ssaThen, envThen) := desugarImpToSSA env thenBranch
      let (ssaElse, envElse) := desugarImpToSSA envThen elseBranch
      (.ite (desugarExpr cond) ssaThen ssaElse, envElse)
  | .discardBind eff =>
      let (idx, env') := env.allocDiscard
      (.bindEffect (.discard idx) (desugarEffect eff), env')
  | .seq s1 s2 =>
      let (ssa1, env1) := desugarImpToSSA env s1
      let (ssa2, env2) := desugarImpToSSA env1 s2
      (.seq ssa1 ssa2, env2)
  | .ret rhs =>
      (.ret (desugarExpr rhs), env)

/-- Evaluate an imperative expression against `ImpLocalEnv`. -/
def evalImpExpr (locals : ImpLocalEnv) : ImpExpr → Val
  | .var name => locals.get name
  | .litInt n => .int n
  | .litBool b => .bool b
  | .boolNot arg => (evalImpExpr locals arg).logicalNot
  | .cond c t f =>
      if (evalImpExpr locals c).toBool then evalImpExpr locals t else evalImpExpr locals f
  | .add l r => .int ((evalImpExpr locals l).toInt + (evalImpExpr locals r).toInt)
  | .zeroArgCall _ retVal => .int retVal

/-- Evaluate an SSA expression against `SSALocalEnv`. -/
def evalSSAExpr (locals : SSALocalEnv) : SSAExpr → Val
  | .var v => locals.get v
  | .litInt n => .int n
  | .litBool b => .bool b
  | .logicalNot arg => (evalSSAExpr locals arg).logicalNot
  | .ite c t f =>
      if (evalSSAExpr locals c).toBool then evalSSAExpr locals t else evalSSAExpr locals f
  | .add l r => .int ((evalSSAExpr locals l).toInt + (evalSSAExpr locals r).toInt)
  | .zeroArgCallNormalized retVal => .int retVal

/-- Evaluate an imperative effect operation on contract `State`. -/
def evalImpEffect (s : State) (locals : ImpLocalEnv) : EffectOp ImpExpr → State × Val
  | .getStorage slot => (s, .int (s.read slot))
  | .setStorage slot valExpr =>
      let v := (evalImpExpr locals valExpr).toInt
      (s.write slot v, .int 0)
  | .zeroArgHelperEffect _ slot delta =>
      let next := s.read slot + delta
      (s.write slot next, .int next)

/-- Evaluate an SSA effect operation on contract `State`. -/
def evalSSAEffect (s : State) (locals : SSALocalEnv) : EffectOp SSAExpr → State × Val
  | .getStorage slot => (s, .int (s.read slot))
  | .setStorage slot valExpr =>
      let v := (evalSSAExpr locals valExpr).toInt
      (s.write slot v, .int 0)
  | .zeroArgHelperEffect _ slot delta =>
      let next := s.read slot + delta
      (s.write slot next, .int next)

/-- Big-step operational semantics for imperative `do`-block statements. -/
def evalImpStmt (s : State) (locals : ImpLocalEnv) : ImpStmt → State × ImpLocalEnv × Option Val
  | .letMut x rhs =>
      (s, locals.set x (evalImpExpr locals rhs), none)
  | .assign x rhs =>
      (s, locals.set x (evalImpExpr locals rhs), none)
  | .bindEffect x eff =>
      let (s', v) := evalImpEffect s locals eff
      (s', locals.set x v, none)
  | .oneArmedIf cond thenBranch =>
      if (evalImpExpr locals cond).toBool then
        evalImpStmt s locals thenBranch
      else
        (s, locals, none)
  | .ite cond thenBranch elseBranch =>
      if (evalImpExpr locals cond).toBool then
        evalImpStmt s locals thenBranch
      else
        evalImpStmt s locals elseBranch
  | .discardBind eff =>
      let (s', _) := evalImpEffect s locals eff
      (s', locals, none)
  | .seq s1 s2 =>
      let (s1', locals1, ret1) := evalImpStmt s locals s1
      match ret1 with
      | some v => (s1', locals1, some v)
      | none => evalImpStmt s1' locals1 s2
  | .ret rhs =>
      (s, locals, some (evalImpExpr locals rhs))

/-- Big-step operational semantics for desugared `SSAStmt` programs. -/
def evalSSAStmt (s : State) (locals : SSALocalEnv) : SSAStmt → State × SSALocalEnv × Option Val
  | .skip =>
      (s, locals, none)
  | .letImm v rhs =>
      (s, locals.set v (evalSSAExpr locals rhs), none)
  | .bindEffect v eff =>
      let (s', val) := evalSSAEffect s locals eff
      (s', locals.set v val, none)
  | .ite cond thenBranch elseBranch =>
      if (evalSSAExpr locals cond).toBool then
        evalSSAStmt s locals thenBranch
      else
        evalSSAStmt s locals elseBranch
  | .seq s1 s2 =>
      let (s1', locals1, ret1) := evalSSAStmt s locals s1
      match ret1 with
      | some v => (s1', locals1, some v)
      | none => evalSSAStmt s1' locals1 s2
  | .ret rhs =>
      (s, locals, some (evalSSAExpr locals rhs))

/-- Coherence invariant relating imperative locals to user SSA variables. -/
def SSAEnvCoherent (impLocals : ImpLocalEnv) (ssaLocals : SSALocalEnv) : Prop :=
  ∀ x : String, ssaLocals.get (.user x) = impLocals.get x

theorem SSAEnvCoherent.empty : SSAEnvCoherent ⟨[]⟩ ⟨[]⟩ := by
  intro x
  rfl

theorem SSAEnvCoherent.set_user
    {impLocals : ImpLocalEnv} {ssaLocals : SSALocalEnv}
    (hCoh : SSAEnvCoherent impLocals ssaLocals) (x : String) (v : Val) :
    SSAEnvCoherent (impLocals.set x v) (ssaLocals.set (.user x) v) := by
  intro y
  by_cases hyx : y = x
  · subst hyx
    simp
  · have hne : (SSAVar.user y) ≠ (SSAVar.user x) := by
      intro hEq
      cases hEq
      exact hyx rfl
    simp [hyx, hne, hCoh y]

theorem SSAEnvCoherent.set_discard
    {impLocals : ImpLocalEnv} {ssaLocals : SSALocalEnv}
    (hCoh : SSAEnvCoherent impLocals ssaLocals) (idx : Nat) (v : Val) :
    SSAEnvCoherent impLocals (ssaLocals.set (.discard idx) v) := by
  intro y
  have hne : (SSAVar.user y) ≠ (SSAVar.discard idx) := by
    intro hEq
    cases hEq
  simp [hne, hCoh y]

/-- Expression desugaring preserves evaluation under `SSAEnvCoherent`. -/
theorem desugarExpr_sound
    {impLocals : ImpLocalEnv} {ssaLocals : SSALocalEnv}
    (hCoh : SSAEnvCoherent impLocals ssaLocals) (e : ImpExpr) :
    evalSSAExpr ssaLocals (desugarExpr e) = evalImpExpr impLocals e := by
  induction e with
  | var name =>
      exact hCoh name
  | litInt n =>
      rfl
  | litBool b =>
      rfl
  | boolNot arg ih =>
      simp [desugarExpr, evalSSAExpr, evalImpExpr, ih]
  | cond c t f ihc iht ihf =>
      simp [desugarExpr, evalSSAExpr, evalImpExpr, ihc, iht, ihf]
  | add l r ihl ihr =>
      simp [desugarExpr, evalSSAExpr, evalImpExpr, ihl, ihr]
  | zeroArgCall style retVal =>
      rfl

/-- Effect desugaring preserves state transition and return value under `SSAEnvCoherent`. -/
theorem desugarEffect_sound
    (s : State) {impLocals : ImpLocalEnv} {ssaLocals : SSALocalEnv}
    (hCoh : SSAEnvCoherent impLocals ssaLocals) (eff : EffectOp ImpExpr) :
    evalSSAEffect s ssaLocals (desugarEffect eff) = evalImpEffect s impLocals eff := by
  cases eff with
  | getStorage slot =>
      rfl
  | setStorage slot valExpr =>
      simp [desugarEffect, evalSSAEffect, evalImpEffect, desugarExpr_sound hCoh]
  | zeroArgHelperEffect hasUnitArg slot delta =>
      rfl

/-- Statement-level equivalence predicate between `evalImpStmt` and `evalSSAStmt`. -/
abbrev SSADesugarStmtEquiv
    (stmt : ImpStmt) (s : State) (env : SSAEnv)
    (impLocals : ImpLocalEnv) (ssaLocals : SSALocalEnv) : Prop :=
  let (ssaStmt, _) := desugarImpToSSA env stmt
  let (sImp, impLocals', retImp) := evalImpStmt s impLocals stmt
  let (sSSA, ssaLocals', retSSA) := evalSSAStmt s ssaLocals ssaStmt
  sSSA = sImp ∧ retSSA = retImp ∧ SSAEnvCoherent impLocals' ssaLocals'

theorem desugarImpToSSA_oneArmedIf_step
    (cond : ImpExpr) (thenBranch : ImpStmt) (s : State) (env : SSAEnv)
    (impLocals : ImpLocalEnv) (ssaLocals : SSALocalEnv)
    (hCoh : SSAEnvCoherent impLocals ssaLocals)
    (ihThen : ∀ s env impLocals ssaLocals,
      SSAEnvCoherent impLocals ssaLocals → SSADesugarStmtEquiv thenBranch s env impLocals ssaLocals) :
    SSADesugarStmtEquiv (.oneArmedIf cond thenBranch) s env impLocals ssaLocals := by
  dsimp [SSADesugarStmtEquiv, desugarImpToSSA, evalImpStmt, evalSSAStmt]
  rw [desugarExpr_sound hCoh]
  by_cases hc : (evalImpExpr impLocals cond).toBool
  · simpa [hc] using ihThen s env impLocals ssaLocals hCoh
  · simp [hc, hCoh]

theorem desugarImpToSSA_ite_step
    (cond : ImpExpr) (thenBranch elseBranch : ImpStmt) (s : State) (env : SSAEnv)
    (impLocals : ImpLocalEnv) (ssaLocals : SSALocalEnv)
    (hCoh : SSAEnvCoherent impLocals ssaLocals)
    (ihThen : ∀ s env impLocals ssaLocals,
      SSAEnvCoherent impLocals ssaLocals → SSADesugarStmtEquiv thenBranch s env impLocals ssaLocals)
    (ihElse : ∀ s env impLocals ssaLocals,
      SSAEnvCoherent impLocals ssaLocals → SSADesugarStmtEquiv elseBranch s env impLocals ssaLocals) :
    SSADesugarStmtEquiv (.ite cond thenBranch elseBranch) s env impLocals ssaLocals := by
  dsimp [SSADesugarStmtEquiv, desugarImpToSSA, evalImpStmt, evalSSAStmt]
  rw [desugarExpr_sound hCoh]
  by_cases hc : (evalImpExpr impLocals cond).toBool
  · simpa [hc] using ihThen s env impLocals ssaLocals hCoh
  · simpa [hc] using ihElse s (desugarImpToSSA env thenBranch).2 impLocals ssaLocals hCoh

theorem desugarImpToSSA_seq_step (s1 s2 : ImpStmt) (s : State) (env : SSAEnv)
    (impLocals : ImpLocalEnv) (ssaLocals : SSALocalEnv) (hCoh : SSAEnvCoherent impLocals ssaLocals)
    (ih1 : ∀ s env impLocals ssaLocals,
      SSAEnvCoherent impLocals ssaLocals → SSADesugarStmtEquiv s1 s env impLocals ssaLocals)
    (ih2 : ∀ s env impLocals ssaLocals,
      SSAEnvCoherent impLocals ssaLocals → SSADesugarStmtEquiv s2 s env impLocals ssaLocals) :
    SSADesugarStmtEquiv (.seq s1 s2) s env impLocals ssaLocals := by
  dsimp [SSADesugarStmtEquiv, desugarImpToSSA, evalImpStmt, evalSSAStmt]
  rcases ih1 s env impLocals ssaLocals hCoh with ⟨hs1, hret1, hCoh1⟩
  cases hRetEq : (evalImpStmt s impLocals s1).2.2 with
  | none =>
      simp only [hs1, hret1, hRetEq]
      exact ih2 (evalImpStmt s impLocals s1).1 (desugarImpToSSA env s1).2
        (evalImpStmt s impLocals s1).2.1 (evalSSAStmt s ssaLocals (desugarImpToSSA env s1).1).2.1 hCoh1
  | some v => simp [hs1, hret1, hRetEq, hCoh1]

/-- **Foundational Meta-Specification (`SSADesugarMetaSpec`)**:
    Evaluating `(desugarImpToSSA env stmt).1` preserves contract `State`,
    return value `Option Val`, and `SSAEnvCoherent` across all user variables. -/
theorem SSADesugarMetaSpec (stmt : ImpStmt) (s : State) (env : SSAEnv)
    (impLocals : ImpLocalEnv) (ssaLocals : SSALocalEnv) (hCoh : SSAEnvCoherent impLocals ssaLocals) :
    SSADesugarStmtEquiv stmt s env impLocals ssaLocals := by
  induction stmt generalizing s env impLocals ssaLocals with
  | letMut x rhs | assign x rhs =>
      exact ⟨rfl, rfl, by simpa [desugarImpToSSA, evalImpStmt, evalSSAStmt, desugarExpr_sound hCoh] using
        SSAEnvCoherent.set_user hCoh x (evalImpExpr impLocals rhs)⟩
  | bindEffect x eff =>
      dsimp only [SSADesugarStmtEquiv, desugarImpToSSA, evalImpStmt, evalSSAStmt]
      rw [desugarEffect_sound s hCoh eff]
      exact ⟨rfl, rfl, SSAEnvCoherent.set_user hCoh x (evalImpEffect s impLocals eff).2⟩
  | oneArmedIf cond thenB ihThen => exact desugarImpToSSA_oneArmedIf_step cond thenB s env impLocals ssaLocals hCoh ihThen
  | ite cond thenB elseB ihThen ihElse => exact desugarImpToSSA_ite_step cond thenB elseB s env impLocals ssaLocals hCoh ihThen ihElse
  | discardBind eff =>
      dsimp only [SSADesugarStmtEquiv, desugarImpToSSA, SSAEnv.allocDiscard, evalImpStmt, evalSSAStmt]
      rw [desugarEffect_sound s hCoh eff]
      exact ⟨rfl, rfl, SSAEnvCoherent.set_discard hCoh env.nextDiscard (evalImpEffect s impLocals eff).2⟩
  | seq s1 s2 ih1 ih2 => exact desugarImpToSSA_seq_step s1 s2 s env impLocals ssaLocals hCoh ih1 ih2
  | ret rhs => exact ⟨rfl, congrArg some (desugarExpr_sound hCoh rhs), hCoh⟩

/-! ## Layer II: Derived Structural Corollaries -/

/-- **Corollary 1 (`desugarOneArmedIf_sound`, `#2427`)**:
    One-armed `if c then body` desugars to `if c then body else skip`. -/
theorem desugarOneArmedIf_sound
    (c : ImpExpr) (body : ImpStmt) (s : State) (env : SSAEnv)
    (impLocals : ImpLocalEnv) (ssaLocals : SSALocalEnv)
    (hCoh : SSAEnvCoherent impLocals ssaLocals) :
    let (ssaBody, _) := desugarImpToSSA env body
    let (sImp, impLocals', retImp) := evalImpStmt s impLocals (.oneArmedIf c body)
    let (sSSA, ssaLocals', retSSA) := evalSSAStmt s ssaLocals (.ite (desugarExpr c) ssaBody .skip)
    sSSA = sImp ∧ retSSA = retImp ∧ SSAEnvCoherent impLocals' ssaLocals' := by
  exact SSADesugarMetaSpec (.oneArmedIf c body) s env impLocals ssaLocals hCoh

/-- **Corollary 2 (`desugarBoolNot_sound`, `#2434`)**:
    Desugaring boolean negation `!b` to `SSAExpr.logicalNot` preserves boolean
    and word-level negation semantics across all coherent environments. -/
theorem desugarBoolNot_sound
    {impLocals : ImpLocalEnv} {ssaLocals : SSALocalEnv}
    (hCoh : SSAEnvCoherent impLocals ssaLocals) (b : ImpExpr) :
    evalSSAExpr ssaLocals (desugarExpr (.boolNot b)) =
      (evalImpExpr impLocals b).logicalNot := by
  simpa [evalImpExpr] using desugarExpr_sound hCoh (.boolNot b)

/-- **Corollary 3a (`desugarDiscardBind_sound`, `#2421`)**:
    Desugaring `let _ ← eff; rest` into a fresh synthetic discard binding
    `let __discard_k ← eff; rest` preserves contract state, return value, and
    every user-visible local variable in `rest`. -/
theorem desugarDiscardBind_sound
    (eff : EffectOp ImpExpr) (rest : ImpStmt) (s : State) (env : SSAEnv)
    (impLocals : ImpLocalEnv) (ssaLocals : SSALocalEnv)
    (hCoh : SSAEnvCoherent impLocals ssaLocals) :
    let (ssaProg, _) := desugarImpToSSA env (.seq (.discardBind eff) rest)
    let (sImp, impLocals', retImp) := evalImpStmt s impLocals (.seq (.discardBind eff) rest)
    let (sSSA, ssaLocals', retSSA) := evalSSAStmt s ssaLocals ssaProg
    sSSA = sImp ∧ retSSA = retImp ∧ SSAEnvCoherent impLocals' ssaLocals' := by
  exact SSADesugarMetaSpec (.seq (.discardBind eff) rest) s env impLocals ssaLocals hCoh

/-- **Corollary 3b (`freshDiscardName_not_mem`, `#2421`)**:
    The string-level fresh discard name generator `pickFreshName` used by
    `SSADesugar.freshHygienicDiscardName` never collides with any existing parameter,
    local, or mutable variable name. -/
theorem freshDiscardName_not_mem (base : String) (usedNames : List String) :
    Compiler.CompilationModel.pickFreshName base usedNames ∉ usedNames :=
  Compiler.CompilationModel.pickFreshName_not_mem_usedNames base usedNames

/-- **Corollary 4 (`desugarZeroArgHelper_sound`, `#2431`)**:
    Calling a 0-argument internal helper with unit tuple syntax `fn ()` vs bare
    reference `fn` lowers to the exact same normalized SSA call and produces
    identical contract state transitions and return values. -/
theorem desugarZeroArgHelper_sound
    (slot : Nat) (delta : Int) (s : State) (env : SSAEnv)
    (impLocals : ImpLocalEnv) (ssaLocals : SSALocalEnv) :
    desugarImpToSSA env (.bindEffect "res" (.zeroArgHelperEffect true slot delta)) =
      desugarImpToSSA env (.bindEffect "res" (.zeroArgHelperEffect false slot delta)) ∧
    evalImpStmt s impLocals (.bindEffect "res" (.zeroArgHelperEffect true slot delta)) =
      evalImpStmt s impLocals (.bindEffect "res" (.zeroArgHelperEffect false slot delta)) ∧
    evalSSAExpr ssaLocals (desugarExpr (.zeroArgCall .unitTupleArg delta)) =
      evalSSAExpr ssaLocals (desugarExpr (.zeroArgCall .bareRef delta)) := by
  refine ⟨rfl, rfl, rfl⟩

/-! ## Layer III: Executable Witness Suite (`by decide`) -/

/-- Witness 1 (`#2427`): Multiple `let mut` reassignments interleaved with monadic
    storage writes and reads (`setStorage` / `getStorage`). -/
def witnessInterleavedLetMutProg : ImpStmt :=
  .seq (.letMut "acc" (.litInt 10))
  (.seq (.bindEffect "loaded" (.getStorage 0))
  (.seq (.assign "acc" (.add (.var "acc") (.var "loaded")))
  (.seq (.discardBind (.setStorage 1 (.var "acc")))
  (.seq (.assign "acc" (.add (.var "acc") (.litInt 5)))
        (.ret (.var "acc"))))))

theorem witness_interleaved_let_mut_and_monadic_binds :
    let initState : State := ⟨[(0, 32)]⟩
    let (ssaProg, finalEnv) := desugarImpToSSA ⟨[], 0⟩ witnessInterleavedLetMutProg
    let (sImp, _, retImp) := evalImpStmt initState ⟨[]⟩ witnessInterleavedLetMutProg
    let (sSSA, _, retSSA) := evalSSAStmt initState ⟨[]⟩ ssaProg
    sImp.read 1 = 42 ∧ retImp = some (.int 47) ∧
      sSSA = sImp ∧ retSSA = retImp ∧ finalEnv.versionOf "acc" = 3 := by
  decide

/-- Witness 2 (`#2427`): One-armed `if` inside a mutable accumulator sequence. -/
def witnessOneArmedIfAccumulatorProg (flag : Bool) : ImpStmt :=
  .seq (.letMut "acc" (.litInt 100))
  (.seq (.oneArmedIf (.litBool flag)
          (.assign "acc" (.add (.var "acc") (.litInt 23))))
        (.ret (.var "acc")))

theorem witness_one_armed_if_accumulator :
    let (ssaTrue, _) := desugarImpToSSA ⟨[], 0⟩ (witnessOneArmedIfAccumulatorProg true)
    let (ssaFalse, _) := desugarImpToSSA ⟨[], 0⟩ (witnessOneArmedIfAccumulatorProg false)
    (evalSSAStmt ⟨[]⟩ ⟨[]⟩ ssaTrue).2.2 = some (.int 123) ∧
      (evalSSAStmt ⟨[]⟩ ⟨[]⟩ ssaFalse).2.2 = some (.int 100) ∧
      (evalImpStmt ⟨[]⟩ ⟨[]⟩ (witnessOneArmedIfAccumulatorProg true)).2.2 = some (.int 123) ∧
      (evalImpStmt ⟨[]⟩ ⟨[]⟩ (witnessOneArmedIfAccumulatorProg false)).2.2 = some (.int 100) := by
  decide

/-- Witness 3 (`#2421`): Multiple discard bindings (`let _ ← ...`) do not collide
    with each other or with user variables. -/
def witnessHygienicDiscardsProg : ImpStmt :=
  .seq (.letMut "__discard" (.litInt 7))
  (.seq (.discardBind (.zeroArgHelperEffect true 0 10))
  (.seq (.discardBind (.zeroArgHelperEffect true 0 20))
        (.ret (.var "__discard"))))

theorem witness_hygienic_discard_binds :
    let (ssaProg, finalEnv) := desugarImpToSSA ⟨[], 0⟩ witnessHygienicDiscardsProg
    let (sImp, _, retImp) := evalImpStmt ⟨[]⟩ ⟨[]⟩ witnessHygienicDiscardsProg
    let (sSSA, _, retSSA) := evalSSAStmt ⟨[]⟩ ⟨[]⟩ ssaProg
    let fresh := Compiler.CompilationModel.pickFreshName "__discard" ["__discard", "x"]
    sImp.read 0 = 30 ∧ retImp = some (.int 7) ∧
      sSSA = sImp ∧ retSSA = retImp ∧ finalEnv.nextDiscard = 2 ∧
      !(["__discard", "x"].contains fresh) = true := by
  decide

/-- Witness 4 (`#2434`, `#2427`): Boolean negation (`!b`) and signed `Int256`
    ternary conditional (`if c then -1 else 1`). -/
def witnessBoolNotAndSignedTernaryExpr (flag : Bool) : ImpExpr :=
  .cond (.boolNot (.litBool flag)) (.litInt (-1)) (.litInt 1)

theorem witness_bool_not_and_signed_ternary :
    evalSSAExpr ⟨[]⟩ (desugarExpr (witnessBoolNotAndSignedTernaryExpr false)) = .int (-1) ∧
    evalSSAExpr ⟨[]⟩ (desugarExpr (witnessBoolNotAndSignedTernaryExpr true)) = .int 1 ∧
    evalImpExpr ⟨[]⟩ (witnessBoolNotAndSignedTernaryExpr false) = .int (-1) ∧
    evalImpExpr ⟨[]⟩ (witnessBoolNotAndSignedTernaryExpr true) = .int 1 := by
  decide

/-- Witness 5 (`#2431`): 0-arg helper call normalization (`fn ()` vs `fn`). -/
theorem witness_zero_arg_helper_normalization :
    let pTuple : ImpStmt :=
      .seq (.bindEffect "v" (.zeroArgHelperEffect true 3 99)) (.ret (.var "v"))
    let pBare : ImpStmt :=
      .seq (.bindEffect "v" (.zeroArgHelperEffect false 3 99)) (.ret (.var "v"))
    desugarImpToSSA ⟨[], 0⟩ pTuple = desugarImpToSSA ⟨[], 0⟩ pBare ∧
    evalSSAStmt ⟨[]⟩ ⟨[]⟩ (desugarImpToSSA ⟨[], 0⟩ pTuple).1 =
      (⟨[(3, 99)]⟩, ⟨[(.user "v", .int 99)]⟩, some (.int 99)) := by
  decide

end Compiler.Proofs.MacroSSAMetaSpec

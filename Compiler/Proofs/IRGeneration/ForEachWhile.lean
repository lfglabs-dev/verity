import Compiler.Proofs.IRGeneration.SourceSemantics
import Compiler.Proofs.IRGeneration.BoundedLoopFuel

/-!
# Early-exit bounded loops: `Stmt.forEachWhile` (#2916)

`Stmt.forEachWhile varName count guard body` is the bounded `forEach` loop with a
guard that is re-evaluated before every iteration check. The loop stops at the first
check where the guard is zero. Its lowering conjoins the guard to the `forEach` loop
test:

```
for { let idx := 0  let cnt := count  let varName := 0 }
    and(lt(idx, cnt), iszero(iszero(guard)))
    { idx := add(idx, 1) }
    { varName := idx  body }
```

This module proves:

1. **Conservativity**: with a guard that is constantly nonzero, `forEachWhile` is exactly
   `forEach` (`execStmt_forEachWhile_eq_forEach_of_guard_const`).
2. **Lowering equivalence**: an importer flag loop
   `forEach i n [ite guard inner []]`, whose iterations are no-ops once the guard is zero,
   has the same outcome as `forEachWhile i n guard [ite guard inner []]` up to the final
   binding of the loop-scoped variable `i`
   (`execStmt_forEach_guarded_eq_forEachWhile`). The `forEachWhile` form stops instead of
   running the remaining empty iterations, which is the gas behaviour of solc's
   `return`/`break`. Gas itself is not modeled.
3. **IR loop test**: the lowered condition evaluates to `1` exactly when the counter is
   below the bound and the guard is nonzero (`evalIRExpr_forEachWhile_cond`), and a false
   test leaves the loop with the state unchanged (`execIRStmt_forEachWhile_exit`).
-/

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.CompilationModel
open Compiler.Yul

namespace SourceSemantics

/-! ## 1. Conservativity over `forEach` -/

/-- With a constant nonzero guard, the early-exit loop is the `forEach` loop. -/
theorem execForEachWhileLoop_eq_execForEachLoop_of_guard_const
    (varName : String) (runBody : RuntimeState → StmtResult) (g : Nat) (hg : g ≠ 0) :
    ∀ (state : RuntimeState) (index remaining : Nat),
      execForEachWhileLoop varName (fun _ => some g) runBody state index remaining =
        execForEachLoop varName runBody state index remaining
  | _, _, 0 => rfl
  | state, index, remaining + 1 => by
      rw [execForEachWhileLoop_succ, execForEachLoop_succ]
      simp only [if_neg hg]
      cases runBody
          { state with bindings := bindValue state.bindings varName (wordNormalize index) } with
      | «continue» next =>
          exact execForEachWhileLoop_eq_execForEachLoop_of_guard_const varName runBody g hg
            next (index + 1) remaining
      | stop _ => rfl
      | «return» _ _ => rfl
      | revert _ => rfl

/-- Statement form of the conservativity law: a `forEachWhile` whose guard always
evaluates to the same nonzero word executes as the plain `forEach`. -/
theorem execStmt_forEachWhile_eq_forEach_of_guard_const
    (fields : List Field) (state : RuntimeState) (varName : String) (count guard : Expr)
    (body : List Stmt) (g : Nat) (hg : g ≠ 0)
    (hguard : ∀ st, evalExpr fields st guard = some g) :
    execStmt fields state (.forEachWhile varName count guard body) =
      execStmt fields state (.forEach varName count body) := by
  have hfun : (fun st => evalExpr fields st guard) = fun _ => some g := funext hguard
  simp only [execStmt, hfun]
  cases evalExpr fields state count with
  | none => rfl
  | some bound =>
      exact execForEachWhileLoop_eq_execForEachLoop_of_guard_const varName _ g hg _ 0 bound

/-- The literal guard `1` makes `forEachWhile` the plain `forEach`. -/
theorem execStmt_forEachWhile_literal_one_eq_forEach
    (fields : List Field) (state : RuntimeState) (varName : String) (count : Expr)
    (body : List Stmt) :
    execStmt fields state (.forEachWhile varName count (.literal 1) body) =
      execStmt fields state (.forEach varName count body) :=
  execStmt_forEachWhile_eq_forEach_of_guard_const fields state varName count (.literal 1)
    body 1 (by decide) (fun _ => by simp [evalExpr, Compiler.Constants.evmModulus])

/-! ## 2. Equivalence with the guarded `forEach` lowering -/

/-- Forget the binding of the loop variable: the loop declares it in the Yul `for`
initializer, so it is out of scope once the loop ends. -/
def eraseLoopVar (varName : String) (state : RuntimeState) : RuntimeState :=
  { state with bindings := state.bindings.filter (fun entry => entry.1 != varName) }

/-- `eraseLoopVar` on the state a loop falls through with; other outcomes unchanged. -/
def eraseLoopVarResult (varName : String) : StmtResult → StmtResult
  | .continue state => .continue (eraseLoopVar varName state)
  | other => other

@[simp] theorem eraseLoopVar_bindValue (varName : String) (state : RuntimeState)
    (value : Nat) :
    eraseLoopVar varName { state with bindings := bindValue state.bindings varName value } =
      eraseLoopVar varName state := by
  simp [eraseLoopVar, bindValue, List.filter_filter]

/-- Reading a variable is unaffected by binding a different one. -/
theorem lookupValue_bindValue_ne (bindings : List (String × Nat))
    (boundName queryName : String) (value : Nat) (hNe : queryName ≠ boundName) :
    lookupValue (bindValue bindings boundName value) queryName =
      lookupValue bindings queryName := by
  have h := lookupBinding?_bindValue_ne bindings boundName queryName value hNe
  simp only [lookupValue, lookupBinding?] at h ⊢
  rw [h]

/-- Once the guard is zero, the remaining `forEach` iterations of a body that is a
no-op under a zero guard only rebind the loop variable. -/
theorem execForEachLoop_noop_of_guard_zero
    (varName : String) (evalGuard : RuntimeState → Option Nat)
    (runBody : RuntimeState → StmtResult)
    (hindep : ∀ st value,
      evalGuard { st with bindings := bindValue st.bindings varName value } = evalGuard st)
    (hzero : ∀ st value, evalGuard st = some 0 →
      runBody { st with bindings := bindValue st.bindings varName value } =
        .continue { st with bindings := bindValue st.bindings varName value }) :
    ∀ (state : RuntimeState) (index remaining : Nat), evalGuard state = some 0 →
      eraseLoopVarResult varName (execForEachLoop varName runBody state index remaining) =
        .continue (eraseLoopVar varName state)
  | _, _, 0, _ => rfl
  | state, index, remaining + 1, h0 => by
      rw [execForEachLoop_succ]
      simp only [hzero state (wordNormalize index) h0]
      rw [execForEachLoop_noop_of_guard_zero varName evalGuard runBody hindep hzero
        { state with bindings := bindValue state.bindings varName (wordNormalize index) }
        (index + 1) remaining (by rw [hindep]; exact h0)]
      simp

/-- One iteration that runs the body: both loops run it identically. -/
theorem execForEachLoop_eq_execForEachWhileLoop_step
    (varName : String) (evalGuard : RuntimeState → Option Nat)
    (runBody : RuntimeState → StmtResult) (state : RuntimeState) (index remaining : Nat)
    (ih : ∀ next : RuntimeState,
      eraseLoopVarResult varName (execForEachLoop varName runBody next (index + 1) remaining) =
        eraseLoopVarResult varName
          (execForEachWhileLoop varName evalGuard runBody next (index + 1) remaining)) :
    eraseLoopVarResult varName
        (match runBody
            { state with bindings := bindValue state.bindings varName (wordNormalize index) }
          with
        | .continue next => execForEachLoop varName runBody next (index + 1) remaining
        | .stop next => .stop next
        | .return value next => .return value next
        | .revert payload => .revert payload) =
      eraseLoopVarResult varName
        (match runBody
            { state with bindings := bindValue state.bindings varName (wordNormalize index) }
          with
        | .continue next =>
            execForEachWhileLoop varName evalGuard runBody next (index + 1) remaining
        | .stop next => .stop next
        | .return value next => .return value next
        | .revert payload => .revert payload) := by
  cases runBody
      { state with bindings := bindValue state.bindings varName (wordNormalize index) } with
  | «continue» next => exact ih next
  | stop _ => rfl
  | «return» _ _ => rfl
  | revert _ => rfl

/-- Loop-level equivalence: the guarded `forEach` and the early-exit loop agree up to
the loop variable's final binding, for a total guard that does not read the loop
variable and a body that is a no-op while the guard is zero. -/
theorem execForEachLoop_eq_execForEachWhileLoop
    (varName : String) (evalGuard : RuntimeState → Option Nat)
    (runBody : RuntimeState → StmtResult)
    (htotal : ∀ st, evalGuard st ≠ none)
    (hindep : ∀ st value,
      evalGuard { st with bindings := bindValue st.bindings varName value } = evalGuard st)
    (hzero : ∀ st value, evalGuard st = some 0 →
      runBody { st with bindings := bindValue st.bindings varName value } =
        .continue { st with bindings := bindValue st.bindings varName value }) :
    ∀ (state : RuntimeState) (index remaining : Nat),
      eraseLoopVarResult varName (execForEachLoop varName runBody state index remaining) =
        eraseLoopVarResult varName
          (execForEachWhileLoop varName evalGuard runBody state index remaining)
  | state, _, 0 => by
      rw [execForEachWhileLoop_zero]
      cases hg : evalGuard state with
      | none => exact absurd hg (htotal state)
      | some _ => rfl
  | state, index, remaining + 1 => by
      rw [execForEachWhileLoop_succ]
      cases hg : evalGuard state with
      | none => exact absurd hg (htotal state)
      | some gv =>
          by_cases h0 : gv = 0
          · subst h0
            dsimp only
            rw [if_pos rfl]
            exact execForEachLoop_noop_of_guard_zero varName evalGuard runBody hindep hzero
              state index (remaining + 1) hg
          · dsimp only
            rw [if_neg h0, execForEachLoop_succ]
            exact execForEachLoop_eq_execForEachWhileLoop_step varName evalGuard runBody
              state index remaining
              (execForEachLoop_eq_execForEachWhileLoop varName evalGuard runBody htotal hindep
                hzero · (index + 1) remaining)

/-- A guarded body `[ite guard inner []]` is a no-op whenever the guard is zero. -/
theorem execStmtList_ite_guard_zero
    (fields : List Field) (state : RuntimeState) (guard : Expr) (inner : List Stmt)
    (h0 : evalExpr fields state guard = some 0) :
    execStmtList fields state [.ite guard inner []] = .continue state := by
  simp [execStmtList, execStmt, h0]

/-- Statement-level lowering equivalence (#2916): the importer's guarded flag loop
`forEach i n [ite guard inner []]` and the early-exit loop
`forEachWhile i n guard [ite guard inner []]` have the same outcome up to the final
binding of the loop variable `i`, which is out of Yul scope after the loop. The guard
must evaluate on every state and must not depend on `i`. -/
theorem execStmt_forEach_guarded_eq_forEachWhile
    (fields : List Field) (state : RuntimeState) (varName : String) (count guard : Expr)
    (inner : List Stmt)
    (htotal : ∀ st, evalExpr fields st guard ≠ none)
    (hindep : ∀ st value,
      evalExpr fields { st with bindings := bindValue st.bindings varName value } guard =
        evalExpr fields st guard) :
    eraseLoopVarResult varName
        (execStmt fields state (.forEach varName count [.ite guard inner []])) =
      eraseLoopVarResult varName
        (execStmt fields state (.forEachWhile varName count guard [.ite guard inner []])) := by
  simp only [execStmt]
  cases evalExpr fields state count with
  | none => rfl
  | some bound =>
      exact execForEachLoop_eq_execForEachWhileLoop varName
        (fun st => evalExpr fields st guard)
        (fun st => execStmtList fields st [.ite guard inner []]) htotal hindep
        (fun st value h0 => execStmtList_ite_guard_zero fields _ guard inner
          (by rw [hindep]; exact h0))
        _ 0 bound

/-- The importer's exit-flag guard `flag < bound` reads only `flag`, so the lowering
equivalence applies whenever the flag is not the loop variable. -/
theorem execStmt_forEach_flagGuarded_eq_forEachWhile
    (fields : List Field) (state : RuntimeState) (varName flag : String) (count : Expr)
    (bound : Nat) (inner : List Stmt) (hne : flag ≠ varName) :
    eraseLoopVarResult varName
        (execStmt fields state
          (.forEach varName count [.ite (.lt (.localVar flag) (.literal bound)) inner []])) =
      eraseLoopVarResult varName
        (execStmt fields state
          (.forEachWhile varName count (.lt (.localVar flag) (.literal bound))
            [.ite (.lt (.localVar flag) (.literal bound)) inner []])) :=
  execStmt_forEach_guarded_eq_forEachWhile fields state varName count _ inner
    (fun st => by simp [evalExpr])
    (fun st value => by simp [evalExpr, lookupValue_bindValue_ne _ _ _ _ hne])

end SourceSemantics

/-! ## 3. The lowered loop test in the IR interpreter -/

/-- The `forEachWhile` loop test `and(lt(idx, cnt), iszero(iszero(guard)))` is `1`
exactly when the counter is below the bound and the guard is nonzero. -/
theorem evalIRExpr_forEachWhile_cond (idxN cntN : String) (guard : YulExpr)
    (state : IRState) (k C g : Nat)
    (hidx : state.getVar idxN = some k)
    (hcnt : state.getVar cntN = some C)
    (hguard : evalIRExpr state guard = some g)
    (hkM : k < Compiler.Constants.evmModulus)
    (hCM : C < Compiler.Constants.evmModulus)
    (hgM : g < Compiler.Constants.evmModulus) :
    evalIRExpr state
        (.call "and" [.call "lt" [.ident idxN, .ident cntN],
          .call "iszero" [.call "iszero" [guard]]]) =
      some (if k < C ∧ g ≠ 0 then 1 else 0) := by
  simp only [evalIRExpr, evalIRCall, evalIRExprs, hidx, hcnt, hguard]
  by_cases hkC : k < C <;> by_cases hg0 : g = 0 <;>
    simp [Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
      Nat.mod_eq_of_lt hkM, Nat.mod_eq_of_lt hCM, Nat.mod_eq_of_lt hgM, hkC, hg0]

/-- A false loop test leaves the steady-state `for` loop with the state unchanged:
the early exit runs no further iteration. -/
theorem execIRStmt_forEachWhile_exit (fuel : Nat) (state : IRState)
    (cond : YulExpr) (post body : List YulStmt)
    (hcond : evalIRExpr state cond = some 0) :
    execIRStmt (fuel + 1) state (.for_ [] cond post body) = .continue state := by
  simp [execIRStmt, hcond]

end Compiler.Proofs.IRGeneration

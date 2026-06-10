/-
  Compiler.CompilationModel.ValidationFold: single-fold validator pattern (POC)

  Validation.lean defines ~17 validator passes that each recursively walk the
  `Stmt`/`StmtList`/`Branches` AST.  Adding a new `Stmt` constructor today
  requires updating every one of those hand-written recursions; missing one is
  silent.

  This module introduces ONE generic structural traversal parameterised by a
  per-constructor "check" function (an algebra).  A validation pass then only
  declares what to check at each node; recursion into nested bodies is shared.
  Adding a new constructor forces a compile error in exactly one place per
  pass.

  As a proof of concept we re-express the simplest existing validator,
  `validateNoRuntimeReturnsInConstructorStmt`, via the generic fold and prove
  the two are extensionally equal (the "oracle" that the fold faithfully
  reproduces the hand-written walk).
-/
import Compiler.CompilationModel.Validation

namespace Compiler.CompilationModel

open Compiler

/-- A per-`Stmt` check function used by `Stmt.checkRec`.  Returning `pure ()`
means "no issue on this node"; returning `throw msg` aborts the traversal with
the error message.  This is the algebra for an `Except`-returning pass. -/
abbrev StmtCheck := Stmt → Except String Unit

mutual
/-- Generic structural traversal: apply `f` to the current node, then recurse
into every nested `List Stmt` reached through `ite`, `forEach`, `unsafeBlock`,
or `matchAdt`.  The first error wins (short-circuiting `Except` semantics).
A new `Stmt` constructor with nested bodies will force a `missing cases`
compile error here — one place to update, not seventeen. -/
def Stmt.checkRec (f : StmtCheck) : Stmt → Except String Unit
  | s@(.ite _ thenBranch elseBranch) => do
      f s
      Stmt.checkRecList f thenBranch
      Stmt.checkRecList f elseBranch
  | s@(.forEach _ _ body) => do
      f s
      Stmt.checkRecList f body
  | s@(.unsafeBlock _ body) => do
      f s
      Stmt.checkRecList f body
  | s@(.matchAdt _ _ branches) => do
      f s
      Stmt.checkRecBranches f branches
  | s => f s
termination_by s => sizeOf s
decreasing_by all_goals simp_wf; all_goals omega

def Stmt.checkRecList (f : StmtCheck) : List Stmt → Except String Unit
  | [] => pure ()
  | s :: rest => do
      Stmt.checkRec f s
      Stmt.checkRecList f rest
termination_by ss => sizeOf ss
decreasing_by all_goals simp_wf; all_goals omega

def Stmt.checkRecBranches (f : StmtCheck) :
    List (String × List String × List Stmt) → Except String Unit
  | [] => pure ()
  | (_, _, body) :: rest => do
      Stmt.checkRecList f body
      Stmt.checkRecBranches f rest
termination_by bs => sizeOf bs
decreasing_by all_goals simp_wf; all_goals omega
end

/-! ### POC re-expression: `validateNoRuntimeReturnsInConstructor` via fold -/

/-- Per-constructor predicate for the "no runtime returns in constructor" pass.
The framework's recursion handles `ite`/`forEach`/`unsafeBlock`/`matchAdt`. -/
def runtimeReturnCheck : Stmt → Except String Unit
  | .return _ | .returnValues _ | .returnArray _
  | .returnBytes _ | .returnStorageWords _ | .returnCodeData _ =>
      throw "Compilation error: constructor must not return runtime data directly"
  | _ => pure ()

/-- The "no runtime returns" pass re-expressed as a single fold. -/
def validateNoRuntimeReturnsInConstructorStmt__viaFold :
    Stmt → Except String Unit :=
  Stmt.checkRec runtimeReturnCheck

/-- List-level form via the generic fold. -/
def validateNoRuntimeReturnsInConstructorStmtList__viaFold :
    List Stmt → Except String Unit :=
  Stmt.checkRecList runtimeReturnCheck

/-- Branches-level form via the generic fold. -/
def validateNoRuntimeReturnsInConstructorBranches__viaFold :
    List (String × List String × List Stmt) → Except String Unit :=
  Stmt.checkRecBranches runtimeReturnCheck

/-! ### Agreement theorem: the fold-based version equals the hand-written one. -/

mutual

/-- Agreement at the `Stmt` level. -/
theorem validateNoRuntimeReturnsInConstructorStmt_eq_viaFold
    (s : Stmt) :
    validateNoRuntimeReturnsInConstructorStmt s =
      validateNoRuntimeReturnsInConstructorStmt__viaFold s := by
  unfold validateNoRuntimeReturnsInConstructorStmt__viaFold
  cases s <;>
    first
    | (simp [validateNoRuntimeReturnsInConstructorStmt, Stmt.checkRec,
        runtimeReturnCheck, pure_bind])
    | rfl
  case ite c t e =>
      rw [validateNoRuntimeReturnsInConstructorStmtList_eq_viaFold t,
          validateNoRuntimeReturnsInConstructorStmtList_eq_viaFold e]
      rfl
  case forEach _ _ body =>
      rw [validateNoRuntimeReturnsInConstructorStmtList_eq_viaFold body]
      rfl
  case unsafeBlock _ body =>
      rw [validateNoRuntimeReturnsInConstructorStmtList_eq_viaFold body]
      rfl
  case matchAdt _ _ branches =>
      rw [validateNoRuntimeReturnsInConstructorBranches_eq_viaFold branches]
      rfl
termination_by sizeOf s
decreasing_by all_goals simp_wf; all_goals omega

/-- Agreement at the `List Stmt` level. -/
theorem validateNoRuntimeReturnsInConstructorStmtList_eq_viaFold
    (ss : List Stmt) :
    validateNoRuntimeReturnsInConstructorStmtList ss =
      validateNoRuntimeReturnsInConstructorStmtList__viaFold ss := by
  unfold validateNoRuntimeReturnsInConstructorStmtList__viaFold
  match ss with
  | [] =>
      simp [validateNoRuntimeReturnsInConstructorStmtList, Stmt.checkRecList]
  | s :: rest =>
      simp [validateNoRuntimeReturnsInConstructorStmtList, Stmt.checkRecList]
      rw [validateNoRuntimeReturnsInConstructorStmt_eq_viaFold s,
          validateNoRuntimeReturnsInConstructorStmtList_eq_viaFold rest]
      rfl
termination_by sizeOf ss
decreasing_by all_goals simp_wf; all_goals omega

/-- Agreement at the branches level. -/
theorem validateNoRuntimeReturnsInConstructorBranches_eq_viaFold
    (bs : List (String × List String × List Stmt)) :
    validateNoRuntimeReturnsInConstructorBranches bs =
      validateNoRuntimeReturnsInConstructorBranches__viaFold bs := by
  unfold validateNoRuntimeReturnsInConstructorBranches__viaFold
  match bs with
  | [] =>
      simp [validateNoRuntimeReturnsInConstructorBranches, Stmt.checkRecBranches]
  | (_, _, body) :: rest =>
      simp [validateNoRuntimeReturnsInConstructorBranches, Stmt.checkRecBranches]
      rw [validateNoRuntimeReturnsInConstructorStmtList_eq_viaFold body,
          validateNoRuntimeReturnsInConstructorBranches_eq_viaFold rest]
      rfl
termination_by sizeOf bs
decreasing_by all_goals simp_wf; all_goals omega

end

end Compiler.CompilationModel

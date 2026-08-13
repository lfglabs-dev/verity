import Compiler.Proofs.IRGeneration.BoundedLoopCheck
import Compiler.Proofs.IRGeneration.SupportedFragment

/-!
# Name discipline of compiled fragment output

The `forEach` loop coupling needs: the compiled body never binds or assigns
the loop's synthetic counters.  The compiler guarantees this by scope
threading — `forEachBodyScope` places the counters in `inScopeNames`, so
every `pickFreshName`-generated scratch name avoids them, and every other
emitted target is a source name.  This module packages that discipline:

- a prefix-discrimination toolkit (`pickFreshName_startsWith`,
  `ne_of_startsWith_of_not_startsWith`) in the kernel-friendly
  `String.startsWith` style of `ReservedScratchNames.lean`;
- (next step) `supportedStmtList_compiled_varUntouched`, by induction over
  `SupportedStmtList`: each fragment constructor's compiled shape is
  explicit, its targets are source names or `__compat_*`/`__evt_*` scratch,
  and `varUntouchedCheck` never inspects expression innards.
-/
namespace Compiler.Proofs.IRGeneration

open Compiler.CompilationModel

/-- `pickFreshName` output always extends its base. -/
theorem pickFreshName_startsWith (base : String) (usedNames : List String) :
    (pickFreshName base usedNames).startsWith base = true := by
  unfold pickFreshName
  by_cases h : usedNames.contains base
  · simp only [h, Bool.not_true, Bool.false_eq_true, if_false]
    rw [String.startsWith_string_iff]
    exact ⟨_, by simp [String.toList_append, List.append_assoc]; rfl⟩
  · have hnot : base ∉ usedNames := by simpa using h
    simp [List.contains_eq_mem, hnot]

/-- Prefix discrimination: a name extending `p` is distinct from any name
that does not extend `p`. -/
theorem ne_of_startsWith_of_not_startsWith
    {v s p : String}
    (hv : v.startsWith p = true) (hs : s.startsWith p = false) :
    v ≠ s := by
  intro hEq
  rw [hEq, hs] at hv
  cases hv

open Compiler.Yul

mutual

/-- Executable mirror of `LoopFree`. -/
def loopFreeCheck : YulStmt → Bool
  | .if_ _ body => loopFreeCheckList body
  | .block stmts => loopFreeCheckList stmts
  | .switch _ cases dflt => loopFreeCheckCases cases && loopFreeCheckDflt dflt
  | .for_ _ _ _ _ => false
  | _ => true

def loopFreeCheckCases : List (Nat × List YulStmt) → Bool
  | [] => true
  | c :: rest => loopFreeCheckList c.2 && loopFreeCheckCases rest

def loopFreeCheckDflt : Option (List YulStmt) → Bool
  | none => true
  | some stmts => loopFreeCheckList stmts

def loopFreeCheckList : List YulStmt → Bool
  | [] => true
  | s :: rest => loopFreeCheck s && loopFreeCheckList rest

end

mutual

/-- Soundness: a checked statement is loop-free. -/
theorem loopFreeCheck_sound : ∀ (s : YulStmt), loopFreeCheck s = true → LoopFree s
  | .if_ _ body, h => by
      simp only [LoopFree]
      exact loopFreeCheckList_sound body (by simpa [loopFreeCheck] using h)
  | .block stmts, h => by
      simp only [LoopFree]
      exact loopFreeCheckList_sound stmts (by simpa [loopFreeCheck] using h)
  | .switch _ cases dflt, h => by
      obtain ⟨hc, hd⟩ : loopFreeCheckCases cases = true ∧
          loopFreeCheckDflt dflt = true := by
        simpa [loopFreeCheck, Bool.and_eq_true] using h
      exact ⟨loopFreeCheckCases_sound cases hc, loopFreeCheckDflt_sound dflt hd⟩
  | .for_ _ _ _ _, h => by simp [loopFreeCheck] at h
  | .comment _, _ => trivial
  | .let_ _ _, _ => trivial
  | .letMany _ _, _ => trivial
  | .assign _ _, _ => trivial
  | .leave, _ => trivial
  | .funcDef _ _ _ _, _ => trivial
  | .exprStmt _, _ => trivial

theorem loopFreeCheckCases_sound :
    ∀ (cs : List (Nat × List YulStmt)), loopFreeCheckCases cs = true →
      LoopFreeCases cs
  | [], _ => trivial
  | c :: rest, h => by
      obtain ⟨hc, hrest⟩ : loopFreeCheckList c.2 = true ∧
          loopFreeCheckCases rest = true := by
        simpa [loopFreeCheckCases, Bool.and_eq_true] using h
      exact ⟨loopFreeCheckList_sound c.2 hc, loopFreeCheckCases_sound rest hrest⟩

theorem loopFreeCheckDflt_sound :
    ∀ (d : Option (List YulStmt)), loopFreeCheckDflt d = true → LoopFreeDflt d
  | none, _ => trivial
  | some stmts, h =>
      loopFreeCheckList_sound stmts (by simpa [loopFreeCheckDflt] using h)

theorem loopFreeCheckList_sound :
    ∀ (xs : List YulStmt), loopFreeCheckList xs = true → LoopFreeList xs
  | [], _ => trivial
  | s :: rest, h => by
      obtain ⟨hs, hrest⟩ : loopFreeCheck s = true ∧
          loopFreeCheckList rest = true := by
        simpa [loopFreeCheckList, Bool.and_eq_true] using h
      exact ⟨loopFreeCheck_sound s hs, loopFreeCheckList_sound rest hrest⟩

end

/-- Per-contract decidable gate for admitting a literal-bound `forEach` body:
the compiled body must be loop-free and must never touch the loop's synthetic
counters.  Discharged by `decide` on concrete contracts; a generic
name-discipline theorem can later eliminate the counter checks. -/
def forEachCompiledBodyChecks
    (fields : List Compiler.CompilationModel.Field)
    (scope : List String) (varName : String)
    (count : Compiler.CompilationModel.Expr)
    (body : List Compiler.CompilationModel.Stmt) : Bool :=
  let forUsedNames := varName :: (scope ++
    Compiler.CompilationModel.collectExprNames count ++
    Compiler.CompilationModel.collectStmtListNames body)
  let idxName := Compiler.CompilationModel.pickFreshName "__forEach_idx" forUsedNames
  let countName := Compiler.CompilationModel.pickFreshName "__forEach_count"
    (idxName :: forUsedNames)
  match Compiler.CompilationModel.compileStmtList fields [] [] .calldata [] false
      (Compiler.CompilationModel.forEachBodyScope scope varName count body) [] body with
  | .ok ir =>
      loopFreeCheckList ir &&
        varUntouchedCheckList idxName ir &&
        varUntouchedCheckList countName ir
  | .error _ => false

end Compiler.Proofs.IRGeneration

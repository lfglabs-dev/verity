import Compiler.Proofs.IRGeneration.SourceSemantics

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
  forall key, key notin written -> lookupValue s.bindings key = lookupValue st.bindings key

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
      simp [lookupValue_bindValue_ne _ _ _ _ hne]

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

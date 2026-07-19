import Compiler.CompilationModel.Types

namespace Compiler.CompilationModel

/-!
Kernel-facing facts about compiler-reserved scratch identifiers.

Lean 4.24 makes the recursive worker of `String.substrEq` private, while the
public string API still has no correctness theorem for `String.startsWith`.
Consequently these closed computations cannot be replayed with `decide` or a
structural kernel proof.  Keep the two native decisions isolated here so their
trust-surface impact is explicit and does not spread implementation unfolding
through the semantic proof files.  Replace them with library lemmas once Lean
or Batteries exposes `substrEq`/`startsWith` correctness.
-/

theorem compatScratch_startsWith_reserved
    {name : String}
    (h :
      name = "__compat_value" ∨
      name = "__compat_packed" ∨
      name = "__compat_slot_word" ∨
      name = "__compat_slot_cleared") :
    name.startsWith "__" = true := by
  rcases h with rfl | rfl | rfl | rfl <;> native_decide

theorem compatScratch_not_internalImmutable
    {name : String}
    (h :
      name = "__compat_value" ∨
      name = "__compat_packed" ∨
      name = "__compat_slot_word" ∨
      name = "__compat_slot_cleared") :
    name.startsWith "__immutable_" = false := by
  rcases h with rfl | rfl | rfl | rfl <;> native_decide

end Compiler.CompilationModel

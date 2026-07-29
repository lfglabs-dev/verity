import Compiler.CompilationModel.Types
import Init.Data.String.Lemmas.Pattern.TakeDrop.String

namespace Compiler.CompilationModel

/-!
Kernel-facing facts about compiler-reserved scratch identifiers.

Lean 4.31 exposes correctness lemmas for `String.startsWith`, so these closed
facts reduce through the kernel without a native-code trust boundary.
-/

theorem compatScratch_startsWith_reserved
    {name : String}
    (h :
      name = "__compat_value" ∨
      name = "__compat_packed" ∨
      name = "__compat_slot_word" ∨
      name = "__compat_slot_cleared") :
    name.startsWith "__" = true := by
  rcases h with rfl | rfl | rfl | rfl <;>
    rw [String.startsWith_string_iff] <;> decide

theorem compatScratch_not_internalImmutable
    {name : String}
    (h :
      name = "__compat_value" ∨
      name = "__compat_packed" ∨
      name = "__compat_slot_word" ∨
      name = "__compat_slot_cleared") :
    name.startsWith "__immutable_" = false := by
  rcases h with rfl | rfl | rfl | rfl <;>
    rw [String.startsWith_string_eq_false_iff] <;> decide

end Compiler.CompilationModel

import Compiler.Codegen
import Compiler.Proofs.IRGeneration.Expr
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanNativeLowering

namespace Compiler.SimpleStorageNativeWitness

open Compiler.Proofs.IRGeneration

/-- Kernel-checked native lowering witness for the generated `simpleStorage` runtime.

The executable artifact and its equality are both checked by the Lean kernel.
The total identifier collector and first-free temporary search let the kernel
reduce the lowering without a native-code decision axiom. -/
theorem lowerRuntimeContractNative_ok :
    ∃ nativeContract,
      Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
        (Compiler.emitYul simpleStorageIRContract).runtimeCode = .ok nativeContract := by
  have hOk :
      (match
          Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
            (Compiler.emitYul simpleStorageIRContract).runtimeCode with
        | .ok _ => true
        | .error _ => false) = true := by
    decide +kernel
  cases hLower :
      Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
        (Compiler.emitYul simpleStorageIRContract).runtimeCode with
  | ok nativeContract =>
      exact ⟨nativeContract, rfl⟩
  | error _ =>
      have := hOk
      rw [hLower] at this
      cases this

/-- The concrete lowered native contract for `simpleStorage`.

Keeping this definition executable lets downstream concrete proofs reduce the
generated dispatcher instead of reasoning through an opaque `Classical.choose`
witness. The accompanying theorem below proves that the fallback arm is not
used for the generated runtime. -/
def nativeContract : EvmYul.Yul.Ast.YulContract :=
  match
    Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
      (Compiler.emitYul simpleStorageIRContract).runtimeCode with
  | .ok nativeContract => nativeContract
  | .error _ => { dispatcher := .Block [], functions := ∅ }

@[simp] theorem lowerRuntimeContractNative_eq :
    Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
      (Compiler.emitYul simpleStorageIRContract).runtimeCode =
        .ok nativeContract :=
  by
    have hOk :
        (match
            Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
              (Compiler.emitYul simpleStorageIRContract).runtimeCode with
          | .ok _ => true
          | .error _ => false) = true := by
      decide +kernel
    cases hLower :
        Compiler.Proofs.YulGeneration.Backends.lowerRuntimeContractNative
          (Compiler.emitYul simpleStorageIRContract).runtimeCode with
    | ok lowered =>
        unfold nativeContract
        rw [hLower]
    | error err =>
        rw [hLower] at hOk
        cases hOk

end Compiler.SimpleStorageNativeWitness

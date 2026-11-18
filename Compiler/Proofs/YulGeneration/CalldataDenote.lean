import Compiler.Proofs.YulGeneration.Calldata
import Verity.Core.Model.Denote

/-!
# Calldata helpers: proof model = executable mirror

`Verity.Core.Model.Denote` keeps compiler-free copies of the calldata helpers in
`Compiler.Proofs.YulGeneration.Calldata` so contract code (`Contracts.Common`)
can run them without importing a proof module. This module proves each copy
equal to its proof-side original.
-/

namespace Compiler.Proofs.YulGeneration

theorem selectorWord_eq_denote (selector : Nat) :
    selectorWord selector = Compiler.CompilationModel.Denote.selectorWord selector := rfl

theorem calldataloadWord_eq_denote (selector : Nat) (calldata : List Nat) (offset : Nat) :
    calldataloadWord selector calldata offset =
      Compiler.CompilationModel.Denote.calldataloadWord selector calldata offset := rfl

theorem calldatacopyMemoryPadded_eq_denote (selector : Nat) (calldata : List Nat)
    (dst src size : Nat) (memory : Nat → Nat) (offset : Nat) :
    calldatacopyMemoryPadded selector calldata dst src size memory offset =
      Compiler.CompilationModel.Denote.calldatacopyMemoryPadded
        selector calldata dst src size memory offset := by
  by_cases hw : calldatacopyWritesAt dst size offset
  · have hw' : Compiler.CompilationModel.Denote.calldatacopyWritesAt dst size offset := hw
    simp only [calldatacopyMemoryPadded, calldatacopyMemory, hw, if_true,
      Compiler.CompilationModel.Denote.calldatacopyMemoryPadded, hw', calldataloadWord_eq_denote]
  · have hw' : ¬Compiler.CompilationModel.Denote.calldatacopyWritesAt dst size offset := hw
    simp only [calldatacopyMemoryPadded, calldatacopyMemory, hw, if_false,
      Compiler.CompilationModel.Denote.calldatacopyMemoryPadded, hw', calldataloadWord_eq_denote]

end Compiler.Proofs.YulGeneration

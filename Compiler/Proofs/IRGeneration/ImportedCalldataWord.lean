import Compiler.Proofs.IRGeneration.ImportedAbiTupleHead

namespace Compiler.Proofs.IRGeneration.ImportedCalldataWord
open Compiler.CompilationModel Denote PhysicalMemory DenoteMemory

def word (state : DenoteState) (source : Nat) : Nat :=
  calldataloadWord state.selector state.world.calldata source

def copied (state : DenoteState) (source destination : Nat) : DenoteState :=
  { state with world := (state.world.writePhysicalMemoryValue destination
    (Verity.Core.Uint256.ofNat (word state source))) }

/-- A real calldata load reads the original transaction word at its actual address. -/
theorem read_evaluated (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (sourceExpr : Expr) (source : Nat) (resolved : evalExpr oracle fields state sourceExpr = some source) :
    evalExpr oracle fields state (.calldataload sourceExpr) = some (word state source) := by
  rw [evalExpr, resolved]
  rfl

/-- Execute the real calldata load/store with exact complete physical poststate. -/
theorem execute (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (sourceExpr destinationExpr : Expr) (source destination : Nat)
    (read : evalExpr oracle fields state sourceExpr = some source)
    (write : evalExpr oracle fields state destinationExpr = some destination) :
    execStmt oracle fields state (.mstore destinationExpr (.calldataload sourceExpr)) =
      .continue (copied state source destination) := by
  exact execStmt_mstore_physical oracle fields state destinationExpr (.calldataload sourceExpr)
    destination (word state source) write (read_evaluated oracle fields state sourceExpr source read)

/-- Canonicality of a loaded scalar proves its actual strict-bound condition. -/
theorem canonical_evaluated (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (sourceExpr : Expr) (source bound : Nat)
    (read : evalExpr oracle fields state sourceExpr = some source)
    (boundSmall : bound < Verity.Core.Uint256.modulus) (canonical : word state source < bound) :
    evalExpr oracle fields state (.lt (.calldataload sourceExpr) (.literal bound)) = some 1 := by
  rw [evalExpr, read_evaluated oracle fields state sourceExpr source read]
  change some (boolWord (decide (word state source < wordNormalize bound))) = _
  rw [show wordNormalize bound = bound from Nat.mod_eq_of_lt boundSmall]
  simp only [canonical, decide_true, boolWord, ite_true]

/-- Every stored byte is derived from the loaded transaction word. -/
theorem byte_at (state : DenoteState) (source destination : Nat) (index : Fin 32) :
    (copied state source destination).world.physicalByte (destination + index.val) =
      valueWord (Verity.Core.Uint256.ofNat (word state source)) index := by
  exact writePhysicalMemoryValue_byte_at _ _ _ _

theorem byte_frame (state : DenoteState) (source destination query : Nat)
    (outside : query < destination ∨ destination + 32 ≤ query) :
    (copied state source destination).world.physicalByte query = state.world.physicalByte query := by
  exact writePhysicalMemoryValue_byte_outside _ _ _ _ outside

theorem coherent (state : DenoteState) (source destination : Nat) : Coherent (copied state source destination).world :=
  writePhysicalMemoryValue_coherent _ _ _

/-- A memory copy cannot change ANY calldata observation or the selector. -/
theorem input_word (state : DenoteState) (source destination query : Nat) :
    word (copied state source destination) query = word state query := by rfl

end Compiler.Proofs.IRGeneration.ImportedCalldataWord

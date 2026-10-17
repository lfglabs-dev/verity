import Compiler.Proofs.IRGeneration.ImportedAbiWordCopy

namespace Compiler.Proofs.IRGeneration.ImportedAbiWordBinding
open Compiler.CompilationModel Denote PhysicalMemory

/-- Resolve an actual addition after deriving that neither input nor result wraps. -/
theorem add_evaluated (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (left right : Expr) (a b : Nat)
    (l : evalExpr oracle fields state left = some a)
    (r : evalExpr oracle fields state right = some b)
    (bound : a + b < Verity.Core.Uint256.modulus) :
    evalExpr oracle fields state (.add left right) = some (a + b) := by
  have aBound : a < Verity.Core.Uint256.modulus := by omega
  have bBound : b < Verity.Core.Uint256.modulus := by omega
  rw [evalExpr, l, r]
  change some ((a % Verity.Core.Uint256.modulus + b % Verity.Core.Uint256.modulus) % Verity.Core.Uint256.modulus) = _
  rw [Nat.mod_eq_of_lt aBound, Nat.mod_eq_of_lt bBound, Nat.mod_eq_of_lt bound]

def ready (state : DenoteState) (name : String) (source : Nat) : DenoteState :=
  { state with bindings := bindValue state.bindings name (state.world.memory source).val }

def copied (state : DenoteState) (name : String) (source destination : Nat) : DenoteState :=
  { ready state name source with world := state.world.copyPhysicalBytes state.world.physicalByte destination source 32 }

/-- The actual let(mload); mstore(local) pair is a whole-state physical snapshot
copy, retaining the generated binding and all nonmemory state. -/
theorem execute (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (name : String) (sourceExpr destinationExpr : Expr) (source destination : Nat)
    (coherent : Coherent state.world)
    (read : evalExpr oracle fields state sourceExpr = some source)
    (write : evalExpr oracle fields (ready state name source) destinationExpr = some destination) :
    execStmtList oracle fields state [.letVar name (.mload sourceExpr), .mstore destinationExpr (.localVar name)] =
      .continue (copied state name source destination) := by
  have loaded : evalExpr oracle fields state (.mload sourceExpr) = some (state.world.memory source).val := by
    rw [evalExpr, read]
    rfl
  rw [SolidityImport.exec_let_cons, loaded]
  have stored := execStmt_mstore_physical oracle fields (ready state name source) destinationExpr (.localVar name)
    destination (state.world.memory source).val write (by simp only [ready, evalExpr, SolidityImport.lookup_bind_same])
  have word : Verity.Core.Uint256.ofNat (state.world.memory source).val = state.world.memory source := by
    apply Verity.Core.Uint256.ext
    exact Nat.mod_eq_of_lt (state.world.memory source).isLt
  change execStmt oracle fields (ready state name source) _ = .continue
    { ready state name source with world := (state.world.writePhysicalMemoryValue destination
      (Verity.Core.Uint256.ofNat (state.world.memory source).val)) } at stored
  rw [word, ImportedAbiWordCopy.copied_world state.world coherent source destination] at stored
  exact (SolidityImport.exec_singleton oracle fields (ready state name source) _).trans stored

end Compiler.Proofs.IRGeneration.ImportedAbiWordBinding

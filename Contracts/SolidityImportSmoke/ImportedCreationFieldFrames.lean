import Contracts.SolidityImportSmoke.ImportedCreationHeadFields

namespace Contracts.SolidityImportSmoke.ImportedCreationFieldFrames
open Compiler.CompilationModel Denote PhysicalMemory DenoteMemory
open Compiler.Proofs.IRGeneration ImportedCreationHeadFields

theorem coherent (state : DenoteState) (source head : Nat) (entries : List (String × Nat))
    (initial : Coherent state.world) : Coherent (runFields state source head entries).world := by
  induction entries generalizing state with
  | nil => exact initial
  | cons entry rest ih => exact ih _ (copyPhysicalMemory_coherent _ _ _ _ _)

/-- Whole field sequences preserve every descriptor not used as a temporary. -/
theorem binding (state : DenoteState) (source head : Nat) (entries : List (String × Nat)) (key : String)
    (fresh : ∀ entry ∈ entries, entry.1 ≠ key) :
    lookupValue (runFields state source head entries).bindings key = lookupValue state.bindings key := by
  induction entries generalizing state with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨name, lane⟩
      change lookupValue (runFields (ImportedAbiWordBinding.copied state name (source + lane) (head + 32 + lane)) source head rest).bindings key = _
      rw [ih _ (fun e h => fresh e (List.mem_cons_of_mem _ h))]
      exact binding_frame state name key _ _ (fresh (name, lane) (by simp))

/-- Exact overlapping word observations follow from the complete byte frame. -/
theorem word (state : DenoteState) (source head query : Nat) (entries : List (String × Nat))
    (initial : Coherent state.world)
    (outside : ∀ entry ∈ entries, query + 32 ≤ head + 32 + entry.2 ∨ head + 32 + entry.2 + 32 ≤ query) :
    (runFields state source head entries).world.memory query = state.world.memory query := by
  apply ImportedAbiArray.word_of_bytes state.world _ query initial (coherent state source head entries initial)
  intro offset
  apply run_frame state source head (query + offset.val) entries
  intro entry belongs
  have := outside entry belongs
  have := offset.isLt
  omega

end Contracts.SolidityImportSmoke.ImportedCreationFieldFrames

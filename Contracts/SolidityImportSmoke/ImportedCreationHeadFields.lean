import Compiler.Proofs.IRGeneration.ImportedAbiWordBinding
import Contracts.SolidityImportSmoke.ImportedCreationHeadAllocation

namespace Contracts.SolidityImportSmoke.ImportedCreationHeadFields
open Compiler.CompilationModel Denote PhysicalMemory DenoteMemory
open Compiler.Proofs.IRGeneration

def sourceExpr (lane : Nat) : Expr := .add (.localVar "_verity_slice_tmp_0_memory") (.literal lane)
def destinationExpr (lane : Nat) : Expr := .add (.add (.localVar "_verity_slice_tmp_3") (.literal 32)) (.literal lane)
def pair (name : String) (lane : Nat) : List Stmt :=
  [.letVar name (.mload (sourceExpr lane)), .mstore (destinationExpr lane) (.localVar name)]
def first : List Stmt := pair "_verity_slice_tmp_5" 0 ++ pair "_verity_slice_tmp_6" 32 ++ pair "_verity_slice_tmp_7" 64
def last : List Stmt := pair "_verity_slice_tmp_15" 128 ++ pair "_verity_slice_tmp_16" 160 ++
  pair "_verity_slice_tmp_17" 192 ++ pair "_verity_slice_tmp_18" 224

theorem actual_first :
    (ImportedCreationPrefixFrames.imported.model.functions.head?.map
      fun fn => (fn.body.drop 45).take 6) = some first := by rfl

theorem actual_last :
    (ImportedCreationPrefixFrames.imported.model.functions.head?.map
      fun fn => (fn.body.drop 62).take 8) = some last := by rfl

/-- Resolve the actual field source, including arbitrary noncanonical word
contents. Only address arithmetic is normalized. -/
theorem source_evaluated (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (source lane : Nat) (held : lookupValue state.bindings "_verity_slice_tmp_0_memory" = source)
    (bound : source + lane < Verity.Core.Uint256.modulus) :
    evalExpr oracle fields state (sourceExpr lane) = some (source + lane) := by
  apply ImportedAbiWordBinding.add_evaluated oracle fields state _ _ source lane
    (by simp only [evalExpr, held]) _ bound
  change some (lane % Verity.Core.Uint256.modulus) = some lane
  rw [Nat.mod_eq_of_lt (by omega)]

/-- Resolve the real nested tuple-head+lane address after its source let. -/
theorem destination_evaluated (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (head lane : Nat) (held : lookupValue state.bindings "_verity_slice_tmp_3" = head)
    (bound : head + 32 + lane < Verity.Core.Uint256.modulus) :
    evalExpr oracle fields state (destinationExpr lane) = some (head + 32 + lane) := by
  apply ImportedAbiWordBinding.add_evaluated oracle fields state _ _ (head + 32) lane _ _ bound
  · exact ImportedAbiWordBinding.add_evaluated oracle fields state _ _ head 32
      (by simp only [evalExpr, held]) (by rfl) (by omega)
  · change some (lane % Verity.Core.Uint256.modulus) = some lane
    rw [Nat.mod_eq_of_lt (by omega)]

/-- Every real static-field pair executes to its whole physical snapshot-copy
world and actual temporary binding, without assuming a loaded word value. -/
theorem execute_pair (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (name : String) (source head lane : Nat) (coherent : Coherent state.world)
    (fresh : name ≠ "_verity_slice_tmp_3")
    (heldSource : lookupValue state.bindings "_verity_slice_tmp_0_memory" = source)
    (heldHead : lookupValue state.bindings "_verity_slice_tmp_3" = head)
    (sourceBound : source + lane < Verity.Core.Uint256.modulus)
    (destBound : head + 32 + lane < Verity.Core.Uint256.modulus) :
    execStmtList oracle fields state (pair name lane) =
      .continue (ImportedAbiWordBinding.copied state name (source + lane) (head + 32 + lane)) := by
  apply ImportedAbiWordBinding.execute oracle fields state name _ _ (source + lane) (head + 32 + lane) coherent
    (source_evaluated oracle fields state source lane heldSource sourceBound)
  apply destination_evaluated oracle fields _ head lane _ destBound
  simpa only [ImportedAbiWordBinding.ready, SolidityImport.lookup_bind_other _ _ _ _ fresh] using heldHead

/-- A real pair preserves every protected input descriptor apart from its
actual temporary binding. -/
theorem binding_frame (state : DenoteState) (name key : String) (source destination : Nat)
    (fresh : name ≠ key) :
    lookupValue (ImportedAbiWordBinding.copied state name source destination).bindings key =
      lookupValue state.bindings key := by
  exact SolidityImport.lookup_bind_other _ _ _ _ fresh

/-- The actual copy result contains every one of the32 input bytes. -/
theorem copied_byte (state : DenoteState) (name : String) (source head lane : Nat) (offset : Fin 32) :
    (ImportedAbiWordBinding.copied state name (source + lane) (head + 32 + lane)).world.physicalByte
      (head + 32 + lane + offset.val) = state.world.physicalByte (source + lane + offset.val) := by
  exact Verity.ContractState.copyPhysicalBytes_at _ _ _ _ _ offset

def code (entries : List (String × Nat)) : List Stmt := entries.flatMap fun entry => pair entry.1 entry.2

def runFields (state : DenoteState) (source head : Nat) : List (String × Nat) → DenoteState
  | [] => state
  | (name, lane) :: rest => runFields
      (ImportedAbiWordBinding.copied state name (source + lane) (head + 32 + lane)) source head rest

/-- Execute an entire sequence of actual static-field pairs. Fresh names and
all source/destination bounds are checked for EACH entry, including unreachable
nearby slots rather than assuming the final world. -/
theorem execute_fields (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (source head : Nat) (entries : List (String × Nat)) (coherent : Coherent state.world)
    (heldSource : lookupValue state.bindings "_verity_slice_tmp_0_memory" = source)
    (heldHead : lookupValue state.bindings "_verity_slice_tmp_3" = head)
    (valid : ∀ entry ∈ entries, entry.1 ≠ "_verity_slice_tmp_3" ∧
      entry.1 ≠ "_verity_slice_tmp_0_memory" ∧ source + entry.2 < Verity.Core.Uint256.modulus ∧
      head + 32 + entry.2 < Verity.Core.Uint256.modulus) :
    execStmtList oracle fields state (code entries) = .continue (runFields state source head entries) := by
  induction entries generalizing state with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨name, lane⟩
      obtain ⟨freshHead, freshSource, sourceBound, destBound⟩ := valid (name, lane) (by simp)
      have copied := execute_pair oracle fields state name source head lane coherent freshHead
        heldSource heldHead sourceBound destBound
      rw [code, List.flatMap_cons, SolidityImport.exec_append, copied]
      exact ih _ (copyPhysicalMemory_coherent _ _ _ _ _)
        ((binding_frame state name "_verity_slice_tmp_0_memory" _ _ freshSource).trans heldSource)
        ((binding_frame state name "_verity_slice_tmp_3" _ _ freshHead).trans heldHead)
        (fun entry belongs => valid entry (by simp only [List.mem_cons]; exact Or.inr belongs))

def firstEntries : List (String × Nat) := [("_verity_slice_tmp_5", 0), ("_verity_slice_tmp_6", 32), ("_verity_slice_tmp_7", 64)]
def lastEntries : List (String × Nat) := [("_verity_slice_tmp_15", 128), ("_verity_slice_tmp_16", 160),
  ("_verity_slice_tmp_17", 192), ("_verity_slice_tmp_18", 224)]

theorem first_code : first = code firstEntries := by rfl
theorem last_code : last = code lastEntries := by rfl

/-- Execute all first3realfieldpairs without assuming their success. -/
theorem execute_first (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (source head : Nat) (coherent : Coherent state.world)
    (heldSource : lookupValue state.bindings "_verity_slice_tmp_0_memory" = source)
    (heldHead : lookupValue state.bindings "_verity_slice_tmp_3" = head)
    (sourceBound : source + 64 < Verity.Core.Uint256.modulus)
    (destBound : head + 96 < Verity.Core.Uint256.modulus) :
    execStmtList oracle fields state first = .continue (runFields state source head firstEntries) := by
  rw [first_code]
  apply execute_fields oracle fields state source head firstEntries coherent heldSource heldHead
  intro entry belongs
  simp only [firstEntries, List.mem_cons, List.not_mem_nil, or_false] at belongs
  rcases belongs with rfl | rfl | rfl <;> refine ⟨by decide, by decide, ?_, ?_⟩ <;> omega

/-- Execute all last4realfieldpairs without assuming their success. -/
theorem execute_last (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (source head : Nat) (coherent : Coherent state.world)
    (heldSource : lookupValue state.bindings "_verity_slice_tmp_0_memory" = source)
    (heldHead : lookupValue state.bindings "_verity_slice_tmp_3" = head)
    (sourceBound : source + 224 < Verity.Core.Uint256.modulus)
    (destBound : head + 256 < Verity.Core.Uint256.modulus) :
    execStmtList oracle fields state last = .continue (runFields state source head lastEntries) := by
  rw [last_code]
  apply execute_fields oracle fields state source head lastEntries coherent heldSource heldHead
  intro entry belongs
  simp only [lastEntries, List.mem_cons, List.not_mem_nil, or_false] at belongs
  rcases belongs with rfl | rfl | rfl | rfl <;> refine ⟨by decide, by decide, ?_, ?_⟩ <;> omega

/-- All bytes outside every actual field destination are preserved. -/
theorem run_frame (state : DenoteState) (source head query : Nat) (entries : List (String × Nat))
    (outside : ∀ entry ∈ entries, query < head + 32 + entry.2 ∨ head + 32 + entry.2 + 32 ≤ query) :
    (runFields state source head entries).world.physicalByte query = state.world.physicalByte query := by
  induction entries generalizing state with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨name, lane⟩
      change (runFields (ImportedAbiWordBinding.copied state name (source + lane) (head + 32 + lane)) source head rest).world.physicalByte query = _
      rw [ih _ (fun e belongs => outside e (List.mem_cons_of_mem _ belongs))]
      exact Verity.ContractState.copyPhysicalBytes_outside _ _ _ _ _ _ (outside (name, lane) (by simp))

/-- Static copies use ORIGINAL input bytes when the entire input struct region
precedes the output. Repeated or overlapping field slices remain exact. -/
theorem written_byte (state : DenoteState) (source head offset : Nat) (entries : List (String × Nat))
    (sources : ∀ entry ∈ entries, source + entry.2 + 32 ≤ head + 32)
    (covered : ∃ entry ∈ entries, entry.2 ≤ offset ∧ offset < entry.2 + 32) :
    (runFields state source head entries).world.physicalByte (head + 32 + offset) =
      state.world.physicalByte (source + offset) := by
  induction entries generalizing state with
  | nil => obtain ⟨entry, impossible, _⟩ := covered; exact False.elim (List.not_mem_nil impossible)
  | cons entry rest ih =>
      rcases entry with ⟨name, lane⟩
      let current := ImportedAbiWordBinding.copied state name (source + lane) (head + 32 + lane)
      have remaining : ∀ e ∈ rest, source + e.2 + 32 ≤ head + 32 := fun e h => sources e (List.mem_cons_of_mem _ h)
      by_cases later : ∃ e ∈ rest, e.2 ≤ offset ∧ offset < e.2 + 32
      · have copied := ih current remaining later
        have before : source + offset < head + 32 := by
          obtain ⟨e, belongs, inside⟩ := later
          have := remaining e belongs
          omega
        exact copied.trans (Verity.ContractState.copyPhysicalBytes_outside _ _ _ _ _ _ (Or.inl (by omega)))
      · have here : lane ≤ offset ∧ offset < lane + 32 := by
          obtain ⟨e, belongs, inside⟩ := covered
          rcases List.mem_cons.mp belongs with same | belongs
          · cases same; exact inside
          · exact False.elim (later ⟨e, belongs, inside⟩)
        have retained := run_frame current source head (head + 32 + offset) rest (by
          intro e belongs
          have missing : ¬ (e.2 ≤ offset ∧ offset < e.2 + 32) := fun h => later ⟨e, belongs, h⟩
          omega)
        have target : head + 32 + offset = head + 32 + lane + (offset - lane) := by omega
        have origin : source + lane + (offset - lane) = source + offset := by omega
        change (runFields current source head rest).world.physicalByte _ = _
        rw [retained, target]
        exact (Verity.ContractState.copyPhysicalBytes_at state.world state.world.physicalByte _ _ 32
          ⟨offset - lane, by omega⟩).trans (by rw [origin])

end Contracts.SolidityImportSmoke.ImportedCreationHeadFields

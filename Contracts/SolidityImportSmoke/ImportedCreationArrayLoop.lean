import Compiler.Proofs.IRGeneration.ImportedAbiArray
import Contracts.SolidityImportSmoke.ImportedCreationArrayElement

namespace Contracts.SolidityImportSmoke.ImportedCreationArrayLoop
open Compiler.CompilationModel Denote DenoteMemory PhysicalMemory
open Compiler.Proofs.IRGeneration
open ImportedCreationArrayElement

def indexed (state : DenoteState) (index : Nat) : DenoteState :=
  { state with bindings := bindValue state.bindings "_verity_slice_tmp_13" (wordNormalize index) }

def next (state : DenoteState) (source tail index : Nat) : DenoteState :=
  fourLanes { (indexed state index) with
    bindings := bindValue (indexed state index).bindings "_verity_slice_tmp_14" source } source tail index

def runElements (state : DenoteState) (base tail : Nat) : Nat → DenoteState
  | 0 => indexed state 0
  | count + 1 => next (runElements state base tail count)
      (ImportedAbiArray.sourceAt state.world base count) tail count

/-- Exact world recurrence; the loop state keeps all other Denote fields. -/
theorem world_eq (state : DenoteState) (base tail count : Nat) :
    (runElements state base tail count).world =
      ImportedAbiArray.copyElements state.world base (tail + 32) count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change (fourLanes _ _ _ _).world = _
      rw [fourLanes_world]
      change ImportedAbiWords.copyWords (runElements state base tail count).world
        (ImportedAbiArray.sourceAt state.world base count) (tail + 32 + count * 128) 4 = _
      rw [ih, Nat.mul_comm count 128]
      rfl

/-- Generated loop bindings cannot clobber the source/count/tail descriptors. -/
theorem binding_frame (state : DenoteState) (base tail count : Nat) (key : String)
    (notIndex : "_verity_slice_tmp_13" ≠ key) (notSource : "_verity_slice_tmp_14" ≠ key) :
    lookupValue (runElements state base tail count).bindings key = lookupValue state.bindings key := by
  induction count with
  | zero => exact SolidityImport.lookup_bind_other _ _ _ _ notIndex
  | succ count ih =>
      change lookupValue (bindValue (bindValue (runElements state base tail count).bindings
        "_verity_slice_tmp_13" (wordNormalize count)) "_verity_slice_tmp_14" _) key = _
      rw [SolidityImport.lookup_bind_other _ _ _ _ notSource,
        SolidityImport.lookup_bind_other _ _ _ _ notIndex, ih]

/-- Every original pointer-array cell is framed by the output separation. -/
theorem pointer_frame (state : DenoteState) (base tail count index : Nat)
    (coherent : Coherent state.world) (before : base + 32 * (index + 1) ≤ tail + 32) :
    ((indexed (runElements state base tail count) index).world.memory (base + 32 * index)).val =
      ImportedAbiArray.sourceAt state.world base index := by
  change ((runElements state base tail count).world.memory (base + 32 * index)).val = _
  rw [world_eq, ImportedAbiArray.word_frame _ _ _ _ _ coherent (Or.inl (by omega))]
  rfl

/-- One actual live loop iteration uses the preserved original pointer and
executes all four stores. Word bounds follow from the allocation ceiling. -/
theorem body_step (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (base tail count index : Nat) (coherent : Coherent state.world)
    (heldBase : lookupValue state.bindings "_verity_slice_tmp_10" = base)
    (heldTail : lookupValue state.bindings "_verity_slice_tmp_11" = tail)
    (live : index < count) (pointers : base + 32 * count ≤ tail)
    (sources : ∀ i < count, ImportedAbiArray.sourceAt state.world base i + 128 ≤ tail)
    (budget : tail + 32 + 128 * count ≤ 2^64 - 1) :
    execStmtList oracle fields (indexed (runElements state base tail index) index) body =
      .continue (runElements state base tail (index + 1)) := by
  have ceiling : 2^64 - 1 < Verity.Core.Uint256.modulus := by decide
  have small : index < Verity.Core.Uint256.modulus := by omega
  have sourceBound := sources index live
  have ptr : ((indexed (runElements state base tail index) index).world.memory (base + index * 32)).val =
      ImportedAbiArray.sourceAt state.world base index := by
    simpa only [Nat.mul_comm] using pointer_frame state base tail index index coherent (by omega)
  have baseHeld := binding_frame state base tail index "_verity_slice_tmp_10" (by decide) (by decide)
  have tailHeld := binding_frame state base tail index "_verity_slice_tmp_11" (by decide) (by decide)
  have coherentNow : Coherent (indexed (runElements state base tail index) index).world := by
    change Coherent (runElements state base tail index).world
    rw [world_eq]
    exact ImportedAbiArray.coherent _ _ _ _ coherent
  have executed := execute_body oracle fields (indexed (runElements state base tail index) index)
    base tail index coherentNow
    (by simpa only [indexed, SolidityImport.lookup_bind_other _ "_verity_slice_tmp_13" "_verity_slice_tmp_10" _ (by decide), baseHeld] using heldBase)
    (by simpa only [indexed, SolidityImport.lookup_bind_other _ "_verity_slice_tmp_13" "_verity_slice_tmp_11" _ (by decide), tailHeld] using heldTail)
    (by simp only [indexed, SolidityImport.lookup_bind_same, wordNormalize, Verity.Core.Uint256.val_ofNat, Nat.mod_eq_of_lt small])
    (by omega) (by rw [ptr]; omega) (by omega)
  rw [ptr] at executed
  exact executed

/-- Run every remaining actual iteration, with an explicit bounded live-index
premise. No successful-body outcome is assumed by the induction. -/
theorem run_loop (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (base tail count : Nat) (coherent : Coherent state.world)
    (heldBase : lookupValue state.bindings "_verity_slice_tmp_10" = base)
    (heldTail : lookupValue state.bindings "_verity_slice_tmp_11" = tail)
    (pointers : base + 32 * count ≤ tail)
    (sources : ∀ i < count, ImportedAbiArray.sourceAt state.world base i + 128 ≤ tail)
    (budget : tail + 32 + 128 * count ≤ 2^64 - 1)
    (remaining index : Nat) (bounded : index + remaining ≤ count) :
    execForEachLoop "_verity_slice_tmp_13" (fun current => execStmtList oracle fields current body)
      (runElements state base tail index) index remaining =
      .continue (runElements state base tail (index + remaining)) := by
  induction remaining generalizing index with
  | zero => rfl
  | succ remaining ih =>
      rw [execForEachLoop]
      change (match execStmtList oracle fields (indexed (runElements state base tail index) index) body with
        | .continue after => execForEachLoop "_verity_slice_tmp_13"
            (fun current => execStmtList oracle fields current body) after (index + 1) remaining
        | other => other) = _
      rw [body_step oracle fields state base tail count index coherent heldBase heldTail
        (by omega) pointers sources budget]
      simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih (index + 1) (by omega)

def statement : Stmt := .forEach "_verity_slice_tmp_13" (.localVar "_verity_slice_tmp_9") body

theorem actual_statement :
    (ImportedCreationPrefixFrames.imported.model.functions.head?.map
      fun fn => fn.body[61]?) = some (some statement) := by rfl

/-- Execute the actual complete dynamic-array loop, including its initial index
binding for count zero. The entire world is the derived physical copier world. -/
theorem execute (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (base tail count : Nat) (coherent : Coherent state.world)
    (heldBase : lookupValue state.bindings "_verity_slice_tmp_10" = base)
    (heldTail : lookupValue state.bindings "_verity_slice_tmp_11" = tail)
    (heldCount : lookupValue state.bindings "_verity_slice_tmp_9" = count)
    (pointers : base + 32 * count ≤ tail)
    (sources : ∀ i < count, ImportedAbiArray.sourceAt state.world base i + 128 ≤ tail)
    (budget : tail + 32 + 128 * count ≤ 2^64 - 1) :
    execStmt oracle fields state statement = .continue (runElements state base tail count) := by
  have executed := run_loop oracle fields state base tail count coherent heldBase heldTail
    pointers sources budget count 0 (by omega)
  simp only [statement, execStmt, evalExpr, heldCount]
  change execForEachLoop "_verity_slice_tmp_13" (fun current => execStmtList oracle fields current body)
    (runElements state base tail 0) 0 count = _
  simpa only [Nat.zero_add] using executed

/-- Every byte of every actual output element is read from the ORIGINAL
loop-entry struct selected by its ORIGINAL pointer-array word. -/
theorem output_bytes (state : DenoteState) (base tail count : Nat)
    (sources : ∀ i < count, ImportedAbiArray.sourceAt state.world base i + 128 ≤ tail)
    (index : Fin count) (offset : Fin 128) :
    (runElements state base tail count).world.physicalByte (tail + 32 + 128 * index.val + offset.val) =
      state.world.physicalByte (ImportedAbiArray.sourceAt state.world base index.val + offset.val) := by
  rw [world_eq]
  exact ImportedAbiArray.element_bytes state.world base (tail + 32) count
    (fun i live => by have := sources i live; omega) index offset

/-- All bytes outside the complete dynamic element region are preserved. -/
theorem output_frame (state : DenoteState) (base tail count query : Nat)
    (outside : query < tail + 32 ∨ tail + 32 + 128 * count ≤ query) :
    (runElements state base tail count).world.physicalByte query = state.world.physicalByte query := by
  rw [world_eq]
  exact ImportedAbiArray.frame _ _ _ _ _ outside

end Contracts.SolidityImportSmoke.ImportedCreationArrayLoop

import Compiler.Proofs.IRGeneration.ImportedAbiWords
import Contracts.SolidityImportSmoke.ImportedCreationArrayAllocation

namespace Contracts.SolidityImportSmoke.ImportedCreationArrayElement
open Compiler.CompilationModel Denote DenoteMemory PhysicalMemory
open Compiler.Proofs.IRGeneration

def pointerExpr : Expr := .add (.localVar "_verity_slice_tmp_10")
  (.mul (.localVar "_verity_slice_tmp_13") (.literal 32))
def sourceExpr (lane : Nat) : Expr := .add (.localVar "_verity_slice_tmp_14") (.literal lane)
def destinationExpr (lane : Nat) : Expr := .add
  (.add (.localVar "_verity_slice_tmp_11") (.literal 32))
  (.add (.literal lane) (.mul (.localVar "_verity_slice_tmp_13") (.literal 128)))
def copyStmt (lane : Nat) : Stmt := .mstore (destinationExpr lane) (.mload (sourceExpr lane))
def body : List Stmt := [.letVar "_verity_slice_tmp_14" (.mload pointerExpr),
  copyStmt 0, copyStmt 32, copyStmt 64, copyStmt 96]

theorem actual_loop :
    (ImportedCreationPrefixFrames.imported.model.functions.head?.map
      fun fn => fn.body[61]?) = some (some (.forEach "_verity_slice_tmp_13"
        (.localVar "_verity_slice_tmp_9") body)) := by rfl

/-- Resolve the actual pointer-array address with all arithmetic wrap ruled out. -/
theorem pointer_evaluated (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (base index : Nat)
    (heldBase : lookupValue state.bindings "_verity_slice_tmp_10" = base)
    (heldIndex : lookupValue state.bindings "_verity_slice_tmp_13" = index)
    (bound : base + index * 32 < Verity.Core.Uint256.modulus) :
    evalExpr oracle fields state pointerExpr = some (base + index * 32) := by
  have a : base < Verity.Core.Uint256.modulus := by omega
  have b : index < Verity.Core.Uint256.modulus := by omega
  have c : index * 32 < Verity.Core.Uint256.modulus := by omega
  simp only [pointerExpr, evalExpr, heldBase, heldIndex]
  change some ((base % Verity.Core.Uint256.modulus +
    (index % Verity.Core.Uint256.modulus * 32) % Verity.Core.Uint256.modulus % Verity.Core.Uint256.modulus) %
      Verity.Core.Uint256.modulus) = _
  rw [Nat.mod_eq_of_lt a, Nat.mod_eq_of_lt b, Nat.mod_eq_of_lt c,
    Nat.mod_eq_of_lt c, Nat.mod_eq_of_lt bound]

/-- The source is the word actually loaded from the pointer array. -/
theorem pointer_step (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (base index : Nat)
    (heldBase : lookupValue state.bindings "_verity_slice_tmp_10" = base)
    (heldIndex : lookupValue state.bindings "_verity_slice_tmp_13" = index)
    (bound : base + index * 32 < Verity.Core.Uint256.modulus) :
    execStmt oracle fields state (.letVar "_verity_slice_tmp_14" (.mload pointerExpr)) =
      .continue { state with bindings := (bindValue state.bindings "_verity_slice_tmp_14"
        (state.world.memory (base + index * 32)).val) } := by
  have resolved := pointer_evaluated oracle fields state base index heldBase heldIndex bound
  simp only [execStmt, evalExpr, resolved]
  rfl

/-- Resolve both actual lane addresses before executing a physical word copy. -/
theorem addresses (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (source tail index lane : Nat)
    (heldSource : lookupValue state.bindings "_verity_slice_tmp_14" = source)
    (heldTail : lookupValue state.bindings "_verity_slice_tmp_11" = tail)
    (heldIndex : lookupValue state.bindings "_verity_slice_tmp_13" = index)
    (sourceBound : source + lane < Verity.Core.Uint256.modulus)
    (destBound : tail + 32 + (lane + index * 128) < Verity.Core.Uint256.modulus) :
    evalExpr oracle fields state (sourceExpr lane) = some (source + lane) ∧
    evalExpr oracle fields state (destinationExpr lane) = some (tail + 32 + (lane + index * 128)) := by
  have s : source < Verity.Core.Uint256.modulus := by omega
  have t : tail < Verity.Core.Uint256.modulus := by omega
  have l : lane < Verity.Core.Uint256.modulus := by omega
  have i : index < Verity.Core.Uint256.modulus := by omega
  have m : index * 128 < Verity.Core.Uint256.modulus := by omega
  have a : tail + 32 < Verity.Core.Uint256.modulus := by omega
  have b : lane + index * 128 < Verity.Core.Uint256.modulus := by omega
  have normalized : wordNormalize lane = lane := Nat.mod_eq_of_lt l
  constructor
  · simp only [sourceExpr, evalExpr, heldSource, normalized]
    change some ((source % Verity.Core.Uint256.modulus + lane % Verity.Core.Uint256.modulus) % Verity.Core.Uint256.modulus) = _
    rw [Nat.mod_eq_of_lt s, Nat.mod_eq_of_lt l, Nat.mod_eq_of_lt sourceBound]
  · simp only [destinationExpr, evalExpr, heldTail, heldIndex, normalized]
    change some (((tail % Verity.Core.Uint256.modulus + 32) % Verity.Core.Uint256.modulus % Verity.Core.Uint256.modulus +
      (lane % Verity.Core.Uint256.modulus + (index % Verity.Core.Uint256.modulus * 128) % Verity.Core.Uint256.modulus % Verity.Core.Uint256.modulus) %
        Verity.Core.Uint256.modulus % Verity.Core.Uint256.modulus) % Verity.Core.Uint256.modulus) = _
    rw [Nat.mod_eq_of_lt t, Nat.mod_eq_of_lt l, Nat.mod_eq_of_lt i, Nat.mod_eq_of_lt m, Nat.mod_eq_of_lt m,
      Nat.mod_eq_of_lt a, Nat.mod_eq_of_lt a, Nat.mod_eq_of_lt b, Nat.mod_eq_of_lt b,
      Nat.mod_eq_of_lt destBound]

/-- One real encoder lane executes to its complete32-byte snapshot-copy world. -/
theorem lane_step (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (source tail index lane : Nat) (coherent : Coherent state.world)
    (heldSource : lookupValue state.bindings "_verity_slice_tmp_14" = source)
    (heldTail : lookupValue state.bindings "_verity_slice_tmp_11" = tail)
    (heldIndex : lookupValue state.bindings "_verity_slice_tmp_13" = index)
    (sourceBound : source + lane < Verity.Core.Uint256.modulus)
    (destBound : tail + 32 + (lane + index * 128) < Verity.Core.Uint256.modulus) :
    execStmt oracle fields state (copyStmt lane) = .continue
      { state with world := (state.world.copyPhysicalBytes state.world.physicalByte
        (tail + 32 + (lane + index * 128)) (source + lane) 32) } := by
  obtain ⟨read, write⟩ := addresses oracle fields state source tail index lane
    heldSource heldTail heldIndex sourceBound destBound
  exact ImportedAbiWordCopy.executed oracle fields state (sourceExpr lane) (destinationExpr lane)
    (source + lane) (tail + 32 + (lane + index * 128)) coherent read write

/-- The intermediate worlds retain full physical expansion and word views. -/
def afterLane (state : DenoteState) (source tail index lane : Nat) : DenoteState :=
  { state with world := (state.world.copyPhysicalBytes state.world.physicalByte
      (tail + 32 + (lane + index * 128)) (source + lane) 32) }

theorem afterLane_coherent (state : DenoteState) (source tail index lane : Nat) :
    Coherent (afterLane state source tail index lane).world := by
  exact copyPhysicalMemory_coherent _ _ _ _ _

def fourLanes (state : DenoteState) (source tail index : Nat) : DenoteState :=
  afterLane (afterLane (afterLane (afterLane state source tail index 0)
    source tail index 32) source tail index 64) source tail index 96

/-- Execute all four actual stores. Each word is loaded at its real execution
point, so this law remains sound even with overlapping source/destination. -/
theorem execute_lanes (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (source tail index : Nat) (coherent : Coherent state.world)
    (heldSource : lookupValue state.bindings "_verity_slice_tmp_14" = source)
    (heldTail : lookupValue state.bindings "_verity_slice_tmp_11" = tail)
    (heldIndex : lookupValue state.bindings "_verity_slice_tmp_13" = index)
    (sourceBound : source + 96 < Verity.Core.Uint256.modulus)
    (destBound : tail + 32 + (96 + index * 128) < Verity.Core.Uint256.modulus) :
    execStmtList oracle fields state [copyStmt 0, copyStmt 32, copyStmt 64, copyStmt 96] =
      .continue (fourLanes state source tail index) := by
  let a := afterLane state source tail index 0
  let b := afterLane a source tail index 32
  let c := afterLane b source tail index 64
  have h0 := lane_step oracle fields state source tail index 0 coherent heldSource heldTail heldIndex
    (by omega) (by omega)
  have h1 := lane_step oracle fields a source tail index 32 (afterLane_coherent state source tail index 0) heldSource heldTail heldIndex
    (by omega) (by omega)
  have h2 := lane_step oracle fields b source tail index 64 (afterLane_coherent a source tail index 32) heldSource heldTail heldIndex
    (by omega) (by omega)
  have h3 := lane_step oracle fields c source tail index 96 (afterLane_coherent b source tail index 64) heldSource heldTail heldIndex
    sourceBound destBound
  change execStmt oracle fields state (copyStmt 0) = .continue a at h0
  change execStmt oracle fields a (copyStmt 32) = .continue b at h1
  change execStmt oracle fields b (copyStmt 64) = .continue c at h2
  simp only [execStmtList, h0, h1, h2, h3]
  rfl

/-- Execute one complete actual iteration: load its pointer from the array,
then copy four words. No target world or output bytes are hypotheses. -/
theorem execute_body (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (base tail index : Nat) (coherent : Coherent state.world)
    (heldBase : lookupValue state.bindings "_verity_slice_tmp_10" = base)
    (heldTail : lookupValue state.bindings "_verity_slice_tmp_11" = tail)
    (heldIndex : lookupValue state.bindings "_verity_slice_tmp_13" = index)
    (pointerBound : base + index * 32 < Verity.Core.Uint256.modulus)
    (sourceBound : (state.world.memory (base + index * 32)).val + 96 < Verity.Core.Uint256.modulus)
    (destBound : tail + 32 + (96 + index * 128) < Verity.Core.Uint256.modulus) :
    execStmtList oracle fields state body = .continue (fourLanes
      { state with bindings := (bindValue state.bindings "_verity_slice_tmp_14"
        (state.world.memory (base + index * 32)).val) }
      (state.world.memory (base + index * 32)).val tail index) := by
  have loaded := pointer_step oracle fields state base index heldBase heldIndex pointerBound
  have copied := execute_lanes oracle fields
    { state with bindings := (bindValue state.bindings "_verity_slice_tmp_14"
        (state.world.memory (base + index * 32)).val) }
    (state.world.memory (base + index * 32)).val tail index coherent
    (SolidityImport.lookup_bind_same ..)
    (by simpa only [SolidityImport.lookup_bind_other _ "_verity_slice_tmp_14" "_verity_slice_tmp_11" _ (by decide)] using heldTail)
    (by simpa only [SolidityImport.lookup_bind_other _ "_verity_slice_tmp_14" "_verity_slice_tmp_13" _ (by decide)] using heldIndex)
    sourceBound destBound
  simpa only [body, execStmtList, loaded] using copied

/-- One bounded intermediate copy step avoids expanding nested physical worlds. -/
theorem afterLane_world_step (state : DenoteState) (initial : Verity.ContractState)
    (source tail index count : Nat)
    (prior : state.world = ImportedAbiWords.copyWords initial source (tail + 32 + index * 128) count) :
    (afterLane state source tail index (32 * count)).world =
      ImportedAbiWords.copyWords initial source (tail + 32 + index * 128) (count + 1) := by
  change state.world.copyPhysicalBytes state.world.physicalByte
    (tail + 32 + (32 * count + index * 128)) (source + 32 * count) 32 = _
  rw [prior]
  have address : tail + 32 + (32 * count + index * 128) =
    tail + 32 + index * 128 + 32 * count := by omega
  rw [address]
  rfl

/-- The four executed lane worlds equal the sequential physical copier. -/
theorem fourLanes_world (state : DenoteState) (source tail index : Nat) :
    (fourLanes state source tail index).world =
      ImportedAbiWords.copyWords state.world source (tail + 32 + index * 128) 4 := by
  have h0 := afterLane_world_step state state.world source tail index 0 rfl
  have h1 := afterLane_world_step (afterLane state source tail index 0)
    state.world source tail index 1 h0
  have h2 := afterLane_world_step (afterLane (afterLane state source tail index 0)
    source tail index 32) state.world source tail index 2 h1
  exact afterLane_world_step (afterLane (afterLane (afterLane state source tail index 0)
    source tail index 32) source tail index 64) state.world source tail index 3 h2

/-- The complete actual element result is the ORIGINAL128-byte struct snapshot
under explicit separation of its source and destination, rather than four
assumed desired word values. -/
theorem element_bytes (state : DenoteState) (source tail index : Nat)
    (separate : source + 128 ≤ tail + 32 + index * 128 ∨
      tail + 32 + index * 128 + 128 ≤ source) (offset : Fin 128) :
    (fourLanes state source tail index).world.physicalByte (tail + 32 + index * 128 + offset.val) =
      state.world.physicalByte (source + offset.val) := by
  rw [fourLanes_world]
  exact ImportedAbiWords.copied state.world source (tail + 32 + index * 128) 4 separate offset

/-- Outside the actual128-byte element destination, all bytes are unchanged. -/
theorem element_frame (state : DenoteState) (source tail index query : Nat)
    (outside : query < tail + 32 + index * 128 ∨ tail + 32 + index * 128 + 128 ≤ query) :
    (fourLanes state source tail index).world.physicalByte query = state.world.physicalByte query := by
  rw [fourLanes_world]
  exact ImportedAbiWords.frame state.world source (tail + 32 + index * 128) 4 query outside

/-- Actual pointer load plus all stores yield every original struct byte and
preserve every byte outside this element. The pointer value is read from the
input state; neither a poststate nor an output-byte oracle is supplied. -/
theorem execute_snapshot (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (base source tail index : Nat) (coherent : Coherent state.world)
    (heldBase : lookupValue state.bindings "_verity_slice_tmp_10" = base)
    (heldTail : lookupValue state.bindings "_verity_slice_tmp_11" = tail)
    (heldIndex : lookupValue state.bindings "_verity_slice_tmp_13" = index)
    (loaded : (state.world.memory (base + index * 32)).val = source)
    (pointerBound : base + index * 32 < Verity.Core.Uint256.modulus)
    (sourceBound : source + 96 < Verity.Core.Uint256.modulus)
    (destBound : tail + 32 + (96 + index * 128) < Verity.Core.Uint256.modulus)
    (separate : source + 128 ≤ tail + 32 + index * 128 ∨
      tail + 32 + index * 128 + 128 ≤ source) :
    ∃ final, execStmtList oracle fields state body = .continue final ∧
      (∀ offset : Fin 128, final.world.physicalByte (tail + 32 + index * 128 + offset.val) =
        state.world.physicalByte (source + offset.val)) ∧
      (∀ query, query < tail + 32 + index * 128 ∨ tail + 32 + index * 128 + 128 ≤ query →
        final.world.physicalByte query = state.world.physicalByte query) := by
  have executed := execute_body oracle fields state base tail index coherent heldBase heldTail heldIndex
    pointerBound (by simpa only [loaded] using sourceBound) destBound
  rw [loaded] at executed
  let ready := { state with bindings := bindValue state.bindings "_verity_slice_tmp_14" source }
  refine ⟨fourLanes ready source tail index, executed, ?_, ?_⟩
  · exact element_bytes ready source tail index separate
  · exact element_frame ready source tail index

end Contracts.SolidityImportSmoke.ImportedCreationArrayElement

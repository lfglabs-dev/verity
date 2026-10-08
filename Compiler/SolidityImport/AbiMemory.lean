import Verity.Core.Model.Denote
import Compiler.SolidityImport.AbiByteLanes
import Compiler.SolidityImport.AbiEncoding
import Compiler.SolidityImport.Proofs
import Compiler.SolidityImport.LoopInvariants

namespace Compiler.CompilationModel.Denote

/-- Read a byte from the encoder's aligned word grid, in EVM big-endian order.
This observation is restricted to the aligned representation; it does not
assert that arbitrary overlapping Denote stores have byte-memory semantics. -/
def abiMemoryByte (memory : Nat → Verity.Core.Uint256) (address : Nat) : Nat :=
  (memory (address / 32 * 32)).val / 256^(31 - address % 32) % 256

/-- An actual successful `mstore` preserves every different word-grid cell. -/
theorem execStmt_mstore_memory_frame (oracle : DenoteOracle) (fields : List Field)
    (before after : DenoteState) (offset value : Expr) (destination address : Nat)
    (evaluated : evalExpr oracle fields before offset = some destination)
    (outside : address ≠ destination)
    (executed : execStmt oracle fields before (.mstore offset value) = .continue after) :
    after.world.memory address = before.world.memory address := by
  simp only [execStmt, evaluated] at executed
  cases result : evalExpr oracle fields before value with
  | none => simp [result] at executed
  | some word =>
      simp only [result, StmtOutcome.continue.injEq] at executed
      cases executed
      simp [outside]

/-- Lift the statement frame rule to bytes in other aligned words. -/
theorem execStmt_mstore_byte_frame (oracle : DenoteOracle) (fields : List Field)
    (before after : DenoteState) (offset value : Expr) (destination address : Nat)
    (evaluated : evalExpr oracle fields before offset = some destination)
    (outside : address / 32 * 32 ≠ destination)
    (executed : execStmt oracle fields before (.mstore offset value) = .continue after) :
    abiMemoryByte after.world.memory address = abiMemoryByte before.world.memory address := by
  unfold abiMemoryByte
  rw [execStmt_mstore_memory_frame oracle fields before after offset value destination
    (address / 32 * 32) evaluated outside executed]

/-- A fresh allocation starting beyond a live slice cannot alias any word
containing a byte of that slice. The bound includes the whole prior allocation. -/
theorem fresh_allocation_byte_frame (base size fresh index : Nat)
    (separated : base + size ≤ fresh) (inside : index < size) :
    (base + index) / 32 * 32 ≠ fresh := by
  have lower : (base + index) / 32 * 32 ≤ base + index := Nat.div_mul_le_self _ _
  omega

/-- Mathematical memory update performed by the aligned byte-copy step.
The generated statement still needs an evaluation lemma connecting its shifts
and bindings to this update. -/
def abiInsertByte (memory : Nat → Verity.Core.Uint256) (address byte : Nat) :
    Nat → Verity.Core.Uint256 :=
  fun cell => if cell = address / 32 * 32 then
    Verity.Core.Uint256.ofNat (SolidityImport.AbiByteLanes.insert
      (memory cell).val byte (31 - address % 32)) else memory cell

theorem abiInsertByte_word (memory : Nat → Verity.Core.Uint256) (address byte : Nat)
    (empty : abiMemoryByte memory address = 0) (bounded : byte < 256) :
    (abiInsertByte memory address byte (address / 32 * 32)).val =
      SolidityImport.AbiByteLanes.insert (memory (address / 32 * 32)).val
        byte (31 - address % 32) := by
  have wordBound : (memory (address / 32 * 32)).val < 256^32 := by
    simpa [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS]
      using (memory (address / 32 * 32)).isLt
  have laneBound : 31 - address % 32 < 32 := by omega
  simp only [abiInsertByte, if_pos rfl, Verity.Core.Uint256.val_ofNat]
  change _ % 256^32 = _
  exact SolidityImport.AbiByteLanes.insertion_modulus _ _ _ wordBound laneBound empty bounded

theorem abiInsertByte_read (memory : Nat → Verity.Core.Uint256) (address byte : Nat)
    (empty : abiMemoryByte memory address = 0) (bounded : byte < 256) :
    abiMemoryByte (abiInsertByte memory address byte) address = byte := by
  unfold abiMemoryByte
  rw [abiInsertByte_word memory address byte empty bounded]
  exact SolidityImport.AbiByteLanes.inserted_byte _ _ _ empty bounded

/-- Byte insertion preserves every other address, even within the same word. -/
theorem abiInsertByte_frame (memory : Nat → Verity.Core.Uint256) (address byte other : Nat)
    (empty : abiMemoryByte memory address = 0) (bounded : byte < 256)
    (different : other ≠ address) :
    abiMemoryByte (abiInsertByte memory address byte) other = abiMemoryByte memory other := by
  by_cases grid : other / 32 * 32 = address / 32 * 32
  · have lanes : 31 - other % 32 ≠ 31 - address % 32 := by
      have first := Nat.mod_lt other (by decide : 0 < 32)
      have second := Nat.mod_lt address (by decide : 0 < 32)
      omega
    unfold abiMemoryByte
    rw [grid, abiInsertByte_word memory address byte empty bounded]
    exact SolidityImport.AbiByteLanes.other_byte_preserved _ _ _ _ empty bounded lanes
  · simp [abiMemoryByte, abiInsertByte, grid]

/-- Exact prefix invariant: copied bytes equal the source snapshot, and every
other byte still equals the initial memory. -/
def AbiCopyPrefix (initial memory : Nat → Verity.Core.Uint256)
    (bytes : Nat → Nat) (destination count : Nat) : Prop :=
  ∀ address, abiMemoryByte memory address =
    if destination ≤ address ∧ address < destination + count then
      bytes (address - destination) else abiMemoryByte initial address

theorem abiCopyPrefix_zero (initial : Nat → Verity.Core.Uint256)
    (bytes : Nat → Nat) (destination : Nat) :
    AbiCopyPrefix initial initial bytes destination 0 := by
  intro address
  simp only [Nat.add_zero]
  rw [if_neg (by omega)]

theorem abiCopyPrefix_step (initial memory : Nat → Verity.Core.Uint256)
    (bytes : Nat → Nat) (destination count : Nat)
    (copied : AbiCopyPrefix initial memory bytes destination count)
    (zero : abiMemoryByte initial (destination + count) = 0)
    (bounded : bytes count < 256) :
    AbiCopyPrefix initial (abiInsertByte memory (destination + count) (bytes count))
      bytes destination (count + 1) := by
  have empty : abiMemoryByte memory (destination + count) = 0 := by
    rw [copied, if_neg (by omega)]
    exact zero
  intro address
  by_cases current : address = destination + count
  · subst address
    rw [abiInsertByte_read memory _ _ empty bounded, if_pos (by omega)]
    simp
  · rw [abiInsertByte_frame memory _ _ address empty bounded current, copied]
    have same : (destination ≤ address ∧ address < destination + count) ↔
        (destination ≤ address ∧ address < destination + (count + 1)) := by omega
    simp only [same]

/-- Finite mathematical copy on the aligned representation. -/
def abiCopyBytes (initial : Nat → Verity.Core.Uint256) (bytes : Nat → Nat)
    (destination : Nat) : Nat → (Nat → Verity.Core.Uint256)
  | 0 => initial
  | count + 1 => abiInsertByte (abiCopyBytes initial bytes destination count)
      (destination + count) (bytes count)

/-- Exact bytes and the complete outside frame for any finite copied prefix.
This theorem concerns the mathematical update; generated-body equivalence
remains a separate obligation. -/
theorem abiCopyBytes_correct (initial : Nat → Verity.Core.Uint256)
    (bytes : Nat → Nat) (destination count : Nat)
    (zero : ∀ index, index < count → abiMemoryByte initial (destination + index) = 0)
    (bounded : ∀ index, index < count → bytes index < 256) :
    AbiCopyPrefix initial (abiCopyBytes initial bytes destination count) bytes destination count := by
  induction count with
  | zero => exact abiCopyPrefix_zero initial bytes destination
  | succ count ih =>
      exact abiCopyPrefix_step initial _ bytes destination count
        (ih (fun index inside => zero index (by omega))
          (fun index inside => bounded index (by omega)))
        (zero count (by omega)) (bounded count (by omega))

/-- Execute the copy store once its address and insertion expression have
been evaluated. This preserves the whole state apart from memory, and relates
the actual statement executor to the mathematical byte update. -/
theorem execStmt_mstore_abiInsertByte (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (offset value : Expr) (address byte : Nat)
    (resolvedOffset : evalExpr oracle fields state offset = some (address / 32 * 32))
    (resolvedValue : evalExpr oracle fields state value = some
      (SolidityImport.AbiByteLanes.insert (state.world.memory (address / 32 * 32)).val
        byte (31 - address % 32))) :
    execStmt oracle fields state (.mstore offset value) = .continue
      { state with world := { state.world with
          memory := abiInsertByte state.world.memory address byte } } := by
  simp only [execStmt, resolvedOffset, resolvedValue]
  congr 1
  congr 1
  congr 1
  funext cell
  by_cases same : cell = address / 32 * 32
  · subst cell
    rfl
  · simp [abiInsertByte, same]

/-- The actual copy store extends the exact prefix invariant, under explicit
expression-evaluation obligations. No assumption equates the output memory. -/
theorem execStmt_mstore_abiCopyPrefix (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (initial : Nat → Verity.Core.Uint256)
    (bytes : Nat → Nat) (destination count : Nat) (offset value : Expr)
    (copied : AbiCopyPrefix initial state.world.memory bytes destination count)
    (zero : abiMemoryByte initial (destination + count) = 0)
    (bounded : bytes count < 256)
    (resolvedOffset : evalExpr oracle fields state offset = some ((destination + count) / 32 * 32))
    (resolvedValue : evalExpr oracle fields state value = some
      (SolidityImport.AbiByteLanes.insert
        (state.world.memory ((destination + count) / 32 * 32)).val
        (bytes count) (31 - (destination + count) % 32))) :
    ∃ after, execStmt oracle fields state (.mstore offset value) = .continue after ∧
      AbiCopyPrefix initial after.world.memory bytes destination (count + 1) := by
  refine ⟨_, execStmt_mstore_abiInsertByte oracle fields state offset value
    (destination + count) (bytes count) resolvedOffset resolvedValue, ?_⟩
  exact abiCopyPrefix_step initial state.world.memory bytes destination count copied zero bounded

/-- Generated word addressing computes the exact floor-to-word offset without
modular wrap, for every EVM-sized index. -/
theorem evalExpr_byteWordOffset (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (index : Expr) (value : Nat)
    (evaluated : evalExpr oracle fields state index = some value)
    (bounded : value < Verity.Core.Uint256.modulus) :
    evalExpr oracle fields state (SolidityImport.AbiEncoding.byteWordOffset index) =
      some (value / 32 * 32) := by
  have quotient : value / 32 < Verity.Core.Uint256.modulus :=
    lt_of_le_of_lt (Nat.div_le_self _ _) bounded
  have product : value / 32 * 32 < Verity.Core.Uint256.modulus :=
    lt_of_le_of_lt (Nat.div_mul_le_self _ _) bounded
  simp only [SolidityImport.AbiEncoding.byteWordOffset, evalExpr, evaluated,
    Option.bind_some]
  change some ((((value % Verity.Core.Uint256.modulus / 32) %
    Verity.Core.Uint256.modulus) % Verity.Core.Uint256.modulus * 32) % Verity.Core.Uint256.modulus) = _
  rw [Nat.mod_eq_of_lt bounded, Nat.mod_eq_of_lt quotient, Nat.mod_eq_of_lt quotient, Nat.mod_eq_of_lt product]


/-- The generated subtraction computes the byte lane exactly, without wrap. -/
theorem evalExpr_byteLane (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (index : Expr) (value : Nat)
    (evaluated : evalExpr oracle fields state index = some value)
    (bounded : value < Verity.Core.Uint256.modulus) :
    evalExpr oracle fields state (SolidityImport.AbiEncoding.byteLane index) =
      some (value % 32) := by
  have word := evalExpr_byteWordOffset oracle fields state index value evaluated bounded
  have product : value / 32 * 32 < Verity.Core.Uint256.modulus :=
    lt_of_le_of_lt (Nat.div_mul_le_self _ _) bounded
  change evalExpr oracle fields state
    (.sub index (SolidityImport.AbiEncoding.byteWordOffset index)) = _
  rw [evalExpr, evaluated, word]
  change some (((Verity.Core.Uint256.ofNat value) -
    (Verity.Core.Uint256.ofNat (value / 32 * 32))).val) = _
  have noWrap : (Verity.Core.Uint256.ofNat (value / 32 * 32)).val ≤
      (Verity.Core.Uint256.ofNat value).val := by
    simpa only [Verity.Core.Uint256.val_ofNat, Nat.mod_eq_of_lt bounded,
      Nat.mod_eq_of_lt product] using Nat.div_mul_le_self value 32
  rw [Verity.Core.Uint256.sub_eq_of_le noWrap]
  simp only [Verity.Core.Uint256.val_ofNat, Nat.mod_eq_of_lt bounded,
    Nat.mod_eq_of_lt product]
  congr 1
  omega

/-- Exact big-endian shift distance used by the generated copy body. -/
theorem evalExpr_byteShift (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (index : Expr) (value : Nat)
    (evaluated : evalExpr oracle fields state index = some value)
    (bounded : value < Verity.Core.Uint256.modulus) :
    evalExpr oracle fields state (.mul (.literal 8)
      (.sub (.literal 31) (SolidityImport.AbiEncoding.byteLane index))) =
        some (8 * (31 - value % 32)) := by
  have lane := evalExpr_byteLane oracle fields state index value evaluated bounded
  have small : value % 32 < 32 := Nat.mod_lt _ (by decide)
  have laneBound : value % 32 < Verity.Core.Uint256.modulus := by
    have : 32 < Verity.Core.Uint256.modulus := by decide
    omega
  have subtraction : evalExpr oracle fields state
      (.sub (.literal 31) (SolidityImport.AbiEncoding.byteLane index)) =
        some (31 - value % 32) := by
    rw [evalExpr, lane]
    change some (((Verity.Core.Uint256.ofNat 31) -
      (Verity.Core.Uint256.ofNat (value % 32))).val) = _
    have ordered : (Verity.Core.Uint256.ofNat (value % 32)).val ≤
        (Verity.Core.Uint256.ofNat 31).val := by
      change (value % 32) % Verity.Core.Uint256.modulus ≤ 31
      rw [Nat.mod_eq_of_lt laneBound]
      omega
    rw [Verity.Core.Uint256.sub_eq_of_le ordered]
    change some (31 - (value % 32) % Verity.Core.Uint256.modulus) = _
    rw [Nat.mod_eq_of_lt laneBound]
  rw [evalExpr, subtraction]
  change some ((8 * ((31 - value % 32) % Verity.Core.Uint256.modulus)) %
    Verity.Core.Uint256.modulus) = _
  have distance : 31 - value % 32 < Verity.Core.Uint256.modulus := by
    have : 31 < Verity.Core.Uint256.modulus := by decide
    omega
  have bits : 8 * (31 - value % 32) < Verity.Core.Uint256.modulus := by
    have : 256 < Verity.Core.Uint256.modulus := by decide
    omega
  rw [Nat.mod_eq_of_lt distance, Nat.mod_eq_of_lt bits]

/-- Actual SHR/AND evaluation extracts the selected byte, including each
Uint256 coercion and normalization performed by Denote. -/
theorem evalExpr_extractByte (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (shift word : Expr) (lane value : Nat)
    (shiftEval : evalExpr oracle fields state shift = some (8 * lane))
    (wordEval : evalExpr oracle fields state word = some value)
    (laneBound : lane < 32) (valueBound : value < Verity.Core.Uint256.modulus) :
    evalExpr oracle fields state (.bitAnd (.shr shift word) (.literal 255)) =
      some (value / 256^lane % 256) := by
  have shiftBound : 8 * lane < Verity.Core.Uint256.modulus := by
    have : 256 < Verity.Core.Uint256.modulus := by decide
    omega
  have shiftedBound : value >>> (8 * lane) < Verity.Core.Uint256.modulus :=
    lt_of_le_of_lt (Nat.shiftRight_le _ _) valueBound
  simp only [evalExpr, shiftEval, wordEval]
  change some (((((value % Verity.Core.Uint256.modulus) >>>
    ((8 * lane) % Verity.Core.Uint256.modulus)) % Verity.Core.Uint256.modulus %
      Verity.Core.Uint256.modulus) &&& 255) % Verity.Core.Uint256.modulus) = _
  rw [Nat.mod_eq_of_lt valueBound, Nat.mod_eq_of_lt shiftBound,
    Nat.mod_eq_of_lt shiftedBound, Nat.mod_eq_of_lt shiftedBound,
    SolidityImport.AbiByteLanes.shift_mask_byte]
  have byteBound : value / 256^lane % 256 < Verity.Core.Uint256.modulus := by
    have := Nat.mod_lt (value / 256^lane) (by decide : 0 < 256)
    have : 256 < Verity.Core.Uint256.modulus := by decide
    omega
  rw [Nat.mod_eq_of_lt byteBound]

/-- Actual SHL/add evaluates to insertion into an empty byte lane without
losing information to any of Denote's intermediate word normalizations. -/
theorem evalExpr_insertByte (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (word shift byteExpr : Expr) (value lane byte : Nat)
    (wordEval : evalExpr oracle fields state word = some value)
    (shiftEval : evalExpr oracle fields state shift = some (8 * lane))
    (byteEval : evalExpr oracle fields state byteExpr = some byte)
    (valueBound : value < 256^32) (laneBound : lane < 32)
    (byteBound : byte < 256) (empty : value / 256^lane % 256 = 0) :
    evalExpr oracle fields state (.add word (.shl shift byteExpr)) =
      some (SolidityImport.AbiByteLanes.insert value byte lane) := by
  have bound := SolidityImport.AbiByteLanes.insertion_bounded value byte lane
    valueBound laneBound empty byteBound
  have total : value + 256^lane * byte < Verity.Core.Uint256.modulus := bound
  have valueSmall : value < Verity.Core.Uint256.modulus := valueBound
  have byteSmall : byte < Verity.Core.Uint256.modulus := by
    have : 256 < Verity.Core.Uint256.modulus := by decide
    omega
  have shiftSmall : 8 * lane < Verity.Core.Uint256.modulus := by
    have : 256 < Verity.Core.Uint256.modulus := by decide
    omega
  have placed : 256^lane * byte < Verity.Core.Uint256.modulus := by omega
  simp only [evalExpr, wordEval, shiftEval, byteEval]
  change some (((value % Verity.Core.Uint256.modulus) +
    (((byte % Verity.Core.Uint256.modulus) <<< ((8 * lane) % Verity.Core.Uint256.modulus)) %
      Verity.Core.Uint256.modulus % Verity.Core.Uint256.modulus)) %
        Verity.Core.Uint256.modulus) = _
  rw [Nat.mod_eq_of_lt valueSmall, Nat.mod_eq_of_lt byteSmall,
    Nat.mod_eq_of_lt shiftSmall, SolidityImport.AbiByteLanes.shift_byte,
    Nat.mod_eq_of_lt placed, Nat.mod_eq_of_lt placed, Nat.mod_eq_of_lt total]
  rfl

/-- The concrete copy-store expression implements the mathematical update.
Only source bindings and the already computed aligned destination are inputs;
shift, load, insertion arithmetic and store semantics are discharged here. -/
theorem execStmt_copyStore (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (position address byteExpr : Expr) (offset byte : Nat)
    (positionEval : evalExpr oracle fields state position = some offset)
    (addressEval : evalExpr oracle fields state address = some (offset / 32 * 32))
    (byteEval : evalExpr oracle fields state byteExpr = some byte)
    (offsetBound : offset < Verity.Core.Uint256.modulus)
    (byteBound : byte < 256) (empty : abiMemoryByte state.world.memory offset = 0) :
    execStmt oracle fields state (.mstore address (.add (.mload address)
      (.shl (.mul (.literal 8) (.sub (.literal 31)
        (SolidityImport.AbiEncoding.byteLane position))) byteExpr))) =
      .continue { state with world := { state.world with
        memory := abiInsertByte state.world.memory offset byte } } := by
  apply execStmt_mstore_abiInsertByte oracle fields state _ _ offset byte addressEval
  apply evalExpr_insertByte oracle fields state _ _ _ _ (31 - offset % 32) byte
  · simp only [evalExpr, addressEval]
    rfl
  · exact evalExpr_byteShift oracle fields state position offset positionEval offsetBound
  · exact byteEval
  · exact (state.world.memory (offset / 32 * 32)).isLt
  · omega
  · exact byteBound
  · exact empty

/-- Exact address addition under the allocator's nonwrapping bound. -/
theorem evalExpr_add_bounded (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (left right : Expr) (a b : Nat)
    (leftEval : evalExpr oracle fields state left = some a)
    (rightEval : evalExpr oracle fields state right = some b)
    (bounded : a + b < Verity.Core.Uint256.modulus) :
    evalExpr oracle fields state (.add left right) = some (a + b) := by
  have aBound : a < Verity.Core.Uint256.modulus := by omega
  have bBound : b < Verity.Core.Uint256.modulus := by omega
  rw [evalExpr, leftEval, rightEval]
  change some (((a % Verity.Core.Uint256.modulus) +
    (b % Verity.Core.Uint256.modulus)) % Verity.Core.Uint256.modulus) = _
  rw [Nat.mod_eq_of_lt aBound, Nat.mod_eq_of_lt bBound, Nat.mod_eq_of_lt bounded]

/-- An aligned allocation's relative word grid is the global word grid. -/
theorem abi_word_grid (base index : Nat) (aligned : base % 32 = 0) :
    base + index / 32 * 32 = (base + index) / 32 * 32 := by
  omega

/-- Generated base-plus-word-offset addressing reaches the byte's actual cell. -/
theorem evalExpr_byteAddress (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (baseExpr indexExpr : Expr) (base index : Nat)
    (baseEval : evalExpr oracle fields state baseExpr = some base)
    (indexEval : evalExpr oracle fields state indexExpr = some index)
    (aligned : base % 32 = 0) (bounded : base + index < Verity.Core.Uint256.modulus) :
    evalExpr oracle fields state (.add baseExpr
      (SolidityImport.AbiEncoding.byteWordOffset indexExpr)) =
        some ((base + index) / 32 * 32) := by
  have indexBound : index < Verity.Core.Uint256.modulus := by omega
  have cellBound : base + index / 32 * 32 < Verity.Core.Uint256.modulus := by
    have := Nat.div_mul_le_self index 32
    omega
  rw [evalExpr_add_bounded oracle fields state _ _ base (index / 32 * 32)
    baseEval (evalExpr_byteWordOffset oracle fields state indexExpr index indexEval indexBound)
    cellBound, abi_word_grid base index aligned]

/-- The complete generated source-read expression reads the intended byte
from any aligned allocation, rather than assuming unaligned memory semantics. -/
theorem evalExpr_copySourceByte (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (source indexExpr : Expr) (base index : Nat)
    (sourceEval : evalExpr oracle fields state source = some base)
    (indexEval : evalExpr oracle fields state indexExpr = some index)
    (aligned : base % 32 = 0) (bounded : base + index < Verity.Core.Uint256.modulus) :
    evalExpr oracle fields state (.bitAnd
      (.shr (.mul (.literal 8) (.sub (.literal 31)
        (SolidityImport.AbiEncoding.byteLane indexExpr)))
        (.mload (.add source (SolidityImport.AbiEncoding.byteWordOffset indexExpr))))
      (.literal 255)) = some (abiMemoryByte state.world.memory (base + index)) := by
  have indexBound : index < Verity.Core.Uint256.modulus := by omega
  have address := evalExpr_byteAddress oracle fields state source indexExpr base index
    sourceEval indexEval aligned bounded
  have load : evalExpr oracle fields state
      (.mload (.add source (SolidityImport.AbiEncoding.byteWordOffset indexExpr))) =
        some (state.world.memory ((base + index) / 32 * 32)).val := by
    rw [evalExpr, address]
    rfl
  have extracted := evalExpr_extractByte oracle fields state _ _ (31 - index % 32) _
    (evalExpr_byteShift oracle fields state indexExpr index indexEval indexBound) load
    (by omega) (state.world.memory ((base + index) / 32 * 32)).isLt
  simpa only [abiMemoryByte, Nat.add_mod, aligned, Nat.zero_add, Nat.mod_mod] using extracted

/-- The destination-relative shift in the emitted store selects the same
lane as the absolute address when the destination allocation is aligned. -/
theorem execStmt_relativeCopyStore (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (position address byteExpr : Expr) (base offset byte : Nat)
    (positionEval : evalExpr oracle fields state position = some offset)
    (addressEval : evalExpr oracle fields state address = some ((base + offset) / 32 * 32))
    (byteEval : evalExpr oracle fields state byteExpr = some byte)
    (aligned : base % 32 = 0) (offsetBound : base + offset < Verity.Core.Uint256.modulus)
    (byteBound : byte < 256) (empty : abiMemoryByte state.world.memory (base + offset) = 0) :
    execStmt oracle fields state (.mstore address (.add (.mload address)
      (.shl (.mul (.literal 8) (.sub (.literal 31)
        (SolidityImport.AbiEncoding.byteLane position))) byteExpr))) =
      .continue { state with world := { state.world with
        memory := abiInsertByte state.world.memory (base + offset) byte } } := by
  have relativeBound : offset < Verity.Core.Uint256.modulus := by omega
  have lanes : (base + offset) % 32 = offset % 32 := by omega
  apply execStmt_mstore_abiInsertByte oracle fields state _ _ (base + offset) byte addressEval
  apply evalExpr_insertByte oracle fields state _ _ _ _ (31 - (base + offset) % 32) byte
  · simp only [evalExpr, addressEval]
    rfl
  · rw [lanes]
    exact evalExpr_byteShift oracle fields state position offset positionEval relativeBound
  · exact byteEval
  · exact (state.world.memory ((base + offset) / 32 * 32)).isLt
  · omega
  · exact byteBound
  · exact empty

/-- State after the two fresh temporary bindings emitted by byte copying. -/
def abiCopyTemporaries (state : DenoteState) (byteName addressName : String)
    (byte address : Nat) : DenoteState :=
  { state with bindings := bindValue (bindValue state.bindings byteName byte) addressName address }

/-- Compose both emitted lets and the concrete store. Evaluation hypotheses
are on the actual successive states, so a clobbered input binding cannot be
silently treated as unchanged. Freshness supplies the byte-binding frame. -/
theorem execStmtList_copyTemporaries (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (sourceByte addressExpr position : Expr)
    (byteName addressName : String) (base offset byte : Nat)
    (distinct : addressName ≠ byteName)
    (sourceEval : evalExpr oracle fields state sourceByte = some byte)
    (addressEval : evalExpr oracle fields
      { state with bindings := bindValue state.bindings byteName byte } addressExpr =
        some ((base + offset) / 32 * 32))
    (positionEval : evalExpr oracle fields
      (abiCopyTemporaries state byteName addressName byte ((base + offset) / 32 * 32)) position =
        some offset)
    (aligned : base % 32 = 0) (offsetBound : base + offset < Verity.Core.Uint256.modulus)
    (byteBound : byte < 256) (empty : abiMemoryByte state.world.memory (base + offset) = 0) :
    execStmtList oracle fields state [
      .letVar byteName sourceByte,
      .letVar addressName addressExpr,
      .mstore (.localVar addressName) (.add (.mload (.localVar addressName))
        (.shl (.mul (.literal 8) (.sub (.literal 31)
          (SolidityImport.AbiEncoding.byteLane position))) (.localVar byteName)))] =
      .continue { abiCopyTemporaries state byteName addressName byte
        ((base + offset) / 32 * 32) with world := { state.world with
          memory := abiInsertByte state.world.memory (base + offset) byte } } := by
  rw [SolidityImport.exec_let_cons, sourceEval]
  simp only
  rw [SolidityImport.exec_let_cons, addressEval]
  simp only
  rw [SolidityImport.exec_singleton]
  apply execStmt_relativeCopyStore oracle fields _ position _ _ base offset byte
  · exact positionEval
  · simp [evalExpr, SolidityImport.lookup_bind_same]
  · simp [evalExpr, SolidityImport.lookup_bind_other, SolidityImport.lookup_bind_same, distinct]
  · exact aligned
  · exact offsetBound
  · exact byteBound
  · exact empty

/-- Fresh copy temporaries preserve a source local's actual evaluation. -/
theorem evalExpr_local_copyTemporaries (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (byteName addressName name : String) (byte address : Nat)
    (byteFresh : byteName ≠ name) (addressFresh : addressName ≠ name) :
    evalExpr oracle fields (abiCopyTemporaries state byteName addressName byte address)
      (.localVar name) = evalExpr oracle fields state (.localVar name) := by
  simp [evalExpr, abiCopyTemporaries, SolidityImport.lookup_bind_other, byteFresh, addressFresh]

/-- The destination-relative start+index expression survives both temporary
bindings when their generated names are fresh. -/
theorem evalExpr_position_copyTemporaries (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (byteName addressName startName indexName : String)
    (byte address start index : Nat)
    (byteStart : byteName ≠ startName) (byteIndex : byteName ≠ indexName)
    (addressStart : addressName ≠ startName) (addressIndex : addressName ≠ indexName)
    (startEval : evalExpr oracle fields state (.localVar startName) = some start)
    (indexEval : evalExpr oracle fields state (.localVar indexName) = some index)
    (bounded : start + index < Verity.Core.Uint256.modulus) :
    evalExpr oracle fields (abiCopyTemporaries state byteName addressName byte address)
      (.add (.localVar startName) (.localVar indexName)) = some (start + index) := by
  apply evalExpr_add_bounded oracle fields _ _ _ start index
  · rw [evalExpr_local_copyTemporaries oracle fields state byteName addressName startName
      byte address byteStart addressStart]
    exact startEval
  · rw [evalExpr_local_copyTemporaries oracle fields state byteName addressName indexName
      byte address byteIndex addressIndex]
    exact indexEval
  · exact bounded

/-- The address initializer remains exact after binding the extracted byte.
Freshness is required for all three locals it reads. -/
theorem evalExpr_address_afterByte (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (byteName destinationName startName indexName : String)
    (byte destination start index : Nat)
    (freshDestination : byteName ≠ destinationName)
    (freshStart : byteName ≠ startName) (freshIndex : byteName ≠ indexName)
    (destinationEval : evalExpr oracle fields state (.localVar destinationName) = some destination)
    (startEval : evalExpr oracle fields state (.localVar startName) = some start)
    (indexEval : evalExpr oracle fields state (.localVar indexName) = some index)
    (aligned : destination % 32 = 0)
    (bounded : destination + (start + index) < Verity.Core.Uint256.modulus) :
    evalExpr oracle fields { state with bindings := bindValue state.bindings byteName byte }
      (.add (.localVar destinationName) (SolidityImport.AbiEncoding.byteWordOffset
        (.add (.localVar startName) (.localVar indexName)))) =
          some ((destination + (start + index)) / 32 * 32) := by
  apply evalExpr_byteAddress oracle fields _ _ _ destination (start + index)
  · simpa only [evalExpr, SolidityImport.lookup_bind_other _ _ _ _ freshDestination]
      using destinationEval
  · apply evalExpr_add_bounded oracle fields _ _ _ start index
    · simpa only [evalExpr, SolidityImport.lookup_bind_other _ _ _ _ freshStart] using startEval
    · simpa only [evalExpr, SolidityImport.lookup_bind_other _ _ _ _ freshIndex] using indexEval
    · omega
  · exact aligned
  · exact bounded

/-- Extract the actual emitted loop body without maintaining a second lowering. -/
def abiGeneratedCopyBody (source destination start index byte address : String) : List Stmt :=
  match SolidityImport.AbiEncoding.copyBytes (.localVar source) (.localVar destination)
      (.localVar start) (.literal 0) index byte address with
  | .forEach _ _ body => body
  | _ => []

/-- One complete actual emitted iteration, including both lets, aligned source
read and destination store. No premise assumes an expression's post-binding
value: freshness and input bindings discharge those obligations. -/
theorem execStmtList_generatedCopyBody (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (sourceName destinationName startName indexName byteName addressName : String)
    (source destination start index : Nat)
    (distinct : addressName ≠ byteName)
    (byteDestination : byteName ≠ destinationName)
    (byteStart : byteName ≠ startName) (byteIndex : byteName ≠ indexName)
    (addressStart : addressName ≠ startName) (addressIndex : addressName ≠ indexName)
    (sourceEval : evalExpr oracle fields state (.localVar sourceName) = some source)
    (destinationEval : evalExpr oracle fields state (.localVar destinationName) = some destination)
    (startEval : evalExpr oracle fields state (.localVar startName) = some start)
    (indexEval : evalExpr oracle fields state (.localVar indexName) = some index)
    (sourceAligned : source % 32 = 0) (destinationAligned : destination % 32 = 0)
    (sourceBound : source + index < Verity.Core.Uint256.modulus)
    (destinationBound : destination + (start + index) < Verity.Core.Uint256.modulus)
    (empty : abiMemoryByte state.world.memory (destination + (start + index)) = 0) :
    let byte := abiMemoryByte state.world.memory (source + index)
    execStmtList oracle fields state
      (abiGeneratedCopyBody sourceName destinationName startName indexName byteName addressName) =
        .continue { abiCopyTemporaries state byteName addressName byte
          ((destination + (start + index)) / 32 * 32) with world := { state.world with
            memory := abiInsertByte state.world.memory (destination + (start + index)) byte } } := by
  dsimp only
  unfold abiGeneratedCopyBody SolidityImport.AbiEncoding.copyBytes
  apply execStmtList_copyTemporaries oracle fields state _ _ _ byteName addressName
    destination (start + index) _ distinct
  · exact evalExpr_copySourceByte oracle fields state _ _ source index sourceEval indexEval
      sourceAligned sourceBound
  · exact evalExpr_address_afterByte oracle fields state byteName destinationName startName indexName
      _ destination start index byteDestination byteStart byteIndex destinationEval startEval indexEval
      destinationAligned destinationBound
  · apply evalExpr_position_copyTemporaries oracle fields state byteName addressName startName indexName
      _ _ start index byteStart byteIndex addressStart addressIndex startEval indexEval
    omega
  · exact destinationAligned
  · exact destinationBound
  · exact Nat.mod_lt _ (by decide)
  · exact empty

/-- A copied prefix leaves the entire disjoint source slice unchanged, in
either address order. This is the source-snapshot fact required by the loop. -/
theorem abiCopyPrefix_source (initial memory : Nat → Verity.Core.Uint256)
    (bytes : Nat → Nat) (source destination size count index : Nat)
    (copied : AbiCopyPrefix initial memory bytes destination count)
    (progressBound : count ≤ size) (inside : index < size)
    (disjoint : source + size ≤ destination ∨ destination + size ≤ source) :
    abiMemoryByte memory (source + index) = abiMemoryByte initial (source + index) := by
  rw [copied, if_neg]
  rcases disjoint with before | after <;> omega

/-- A copy step reading the CURRENT source memory advances the invariant
whose target bytes are the INITIAL source snapshot. Nonoverlap, rather than
an assumed immutable source, justifies this conversion. -/
theorem abiCopyPrefix_live_step (initial memory : Nat → Verity.Core.Uint256)
    (source destination size count : Nat)
    (copied : AbiCopyPrefix initial memory
      (fun index => abiMemoryByte initial (source + index)) destination count)
    (inside : count < size)
    (disjoint : source + size ≤ destination ∨ destination + size ≤ source)
    (zero : abiMemoryByte initial (destination + count) = 0) :
    AbiCopyPrefix initial
      (abiInsertByte memory (destination + count) (abiMemoryByte memory (source + count)))
      (fun index => abiMemoryByte initial (source + index)) destination (count + 1) := by
  rw [abiCopyPrefix_source initial memory _ source destination size count count copied
    (by omega) inside disjoint]
  exact abiCopyPrefix_step initial memory _ destination count copied zero
    (Nat.mod_lt _ (by decide))

/-- Stable input names and values for a generated byte-copy loop. -/
structure AbiCopyInputs where
  sourceName : String
  destinationName : String
  startName : String
  source : Nat
  destination : Nat
  start : Nat

/-- Loop iterations must retain all three buffer descriptors. -/
def AbiCopyInputs.Holds (inputs : AbiCopyInputs) (state : DenoteState) : Prop :=
  lookupValue state.bindings inputs.sourceName = inputs.source ∧
  lookupValue state.bindings inputs.destinationName = inputs.destination ∧
  lookupValue state.bindings inputs.startName = inputs.start

/-- A fresh name cannot shadow any persistent loop input. -/
def AbiCopyInputs.Fresh (inputs : AbiCopyInputs) (name : String) : Prop :=
  name ≠ inputs.sourceName ∧ name ≠ inputs.destinationName ∧ name ≠ inputs.startName

theorem abiCopyInputs_bind (inputs : AbiCopyInputs) (state : DenoteState)
    (name : String) (value : Nat) (held : inputs.Holds state) (fresh : inputs.Fresh name) :
    inputs.Holds { state with bindings := bindValue state.bindings name value } := by
  rcases held with ⟨source, destination, start⟩
  rcases fresh with ⟨sourceFresh, destinationFresh, startFresh⟩
  simpa [AbiCopyInputs.Holds, SolidityImport.lookup_bind_other,
    sourceFresh, destinationFresh, startFresh] using And.intro source (And.intro destination start)

/-- Combined byte-prefix and persistent-input invariant used by the actual loop. -/
def AbiCopyLoopInvariant (inputs : AbiCopyInputs)
    (initial : Nat → Verity.Core.Uint256) (count : Nat) (state : DenoteState) : Prop :=
  inputs.Holds state ∧ AbiCopyPrefix initial state.world.memory
    (fun index => abiMemoryByte initial (inputs.source + index))
    (inputs.destination + inputs.start) count

/-- Binding the executor's index preserves the complete loop invariant when
its name is fresh. The normalized index value need not be assumed equal yet. -/
theorem abiCopyLoopInvariant_bind (inputs : AbiCopyInputs)
    (initial : Nat → Verity.Core.Uint256) (count : Nat) (state : DenoteState)
    (name : String) (value : Nat) (held : AbiCopyLoopInvariant inputs initial count state)
    (fresh : inputs.Fresh name) :
    AbiCopyLoopInvariant inputs initial count
      { state with bindings := bindValue state.bindings name value } := by
  exact ⟨abiCopyInputs_bind inputs state name value held.1 fresh, held.2⟩

/-- Both emitted temporary lets and the byte store preserve persistent inputs. -/
theorem abiCopyInputs_afterStore (inputs : AbiCopyInputs) (state : DenoteState)
    (byteName addressName : String) (byte address position : Nat)
    (held : inputs.Holds state) (byteFresh : inputs.Fresh byteName)
    (addressFresh : inputs.Fresh addressName) :
    inputs.Holds { abiCopyTemporaries state byteName addressName byte address with
      world := { state.world with memory := abiInsertByte state.world.memory position byte } } := by
  exact abiCopyInputs_bind inputs _ addressName address
    (abiCopyInputs_bind inputs state byteName byte held byteFresh) addressFresh

/-- One actual generated iteration preserves the combined loop invariant. -/
theorem abiCopyLoopInvariant_step (oracle : DenoteOracle) (fields : List Field)
    (inputs : AbiCopyInputs) (initial : Nat → Verity.Core.Uint256)
    (state : DenoteState) (indexName byteName addressName : String) (size count : Nat)
    (held : AbiCopyLoopInvariant inputs initial count state)
    (byteFresh : inputs.Fresh byteName) (addressFresh : inputs.Fresh addressName)
    (distinct : addressName ≠ byteName) (byteIndex : byteName ≠ indexName)
    (addressIndex : addressName ≠ indexName)
    (indexEval : evalExpr oracle fields state (.localVar indexName) = some count)
    (sourceAligned : inputs.source % 32 = 0) (destinationAligned : inputs.destination % 32 = 0)
    (sourceBound : inputs.source + count < Verity.Core.Uint256.modulus)
    (destinationBound : inputs.destination + (inputs.start + count) < Verity.Core.Uint256.modulus)
    (inside : count < size)
    (disjoint : inputs.source + size ≤ inputs.destination + inputs.start ∨
      inputs.destination + inputs.start + size ≤ inputs.source)
    (zero : abiMemoryByte initial (inputs.destination + inputs.start + count) = 0) :
    ∃ after, execStmtList oracle fields state
      (abiGeneratedCopyBody inputs.sourceName inputs.destinationName inputs.startName
        indexName byteName addressName) = .continue after ∧
      AbiCopyLoopInvariant inputs initial (count + 1) after := by
  have empty : abiMemoryByte state.world.memory (inputs.destination + (inputs.start + count)) = 0 := by
    rw [← Nat.add_assoc, held.2, if_neg (by omega)]
    exact zero
  have executed := execStmtList_generatedCopyBody oracle fields state
    inputs.sourceName inputs.destinationName inputs.startName indexName byteName addressName
    inputs.source inputs.destination inputs.start count distinct byteFresh.2.1 byteFresh.2.2
    byteIndex addressFresh.2.2 addressIndex
    (congrArg some held.1.1) (congrArg some held.1.2.1) (congrArg some held.1.2.2)
    indexEval sourceAligned destinationAligned sourceBound destinationBound empty
  refine ⟨_, executed, ?_⟩
  constructor
  · exact abiCopyInputs_afterStore inputs state byteName addressName _ _ _ held.1 byteFresh addressFresh
  · simpa only [abiCopyTemporaries, Nat.add_assoc] using
      abiCopyPrefix_live_step initial state.world.memory inputs.source
        (inputs.destination + inputs.start) size count held.2 inside disjoint zero

/-- The actual loop executor copies the full slice and cannot take any early
exit under the stated finite-memory, freshness and disjointness conditions. -/
theorem execForEachLoop_copy (oracle : DenoteOracle) (fields : List Field)
    (inputs : AbiCopyInputs) (state : DenoteState)
    (indexName byteName addressName : String) (size : Nat)
    (held : inputs.Holds state)
    (indexFresh : inputs.Fresh indexName) (byteFresh : inputs.Fresh byteName)
    (addressFresh : inputs.Fresh addressName)
    (distinct : addressName ≠ byteName) (byteIndex : byteName ≠ indexName)
    (addressIndex : addressName ≠ indexName)
    (sourceAligned : inputs.source % 32 = 0) (destinationAligned : inputs.destination % 32 = 0)
    (sourceBound : inputs.source + size < Verity.Core.Uint256.modulus)
    (destinationBound : inputs.destination + (inputs.start + size) < Verity.Core.Uint256.modulus)
    (disjoint : inputs.source + size ≤ inputs.destination + inputs.start ∨
      inputs.destination + inputs.start + size ≤ inputs.source)
    (zero : ∀ index, index < size →
      abiMemoryByte state.world.memory (inputs.destination + inputs.start + index) = 0) :
    LoopOutcomePost (AbiCopyLoopInvariant inputs state.world.memory size) (fun _ => False)
      (execForEachLoop indexName
        (fun s => execStmtList oracle fields s (abiGeneratedCopyBody inputs.sourceName
          inputs.destinationName inputs.startName indexName byteName addressName)) state 0 size) := by
  have step : ∀ index before, index < size → AbiCopyLoopInvariant inputs state.world.memory index before →
      LoopOutcomePost (AbiCopyLoopInvariant inputs state.world.memory (index + 1)) (fun _ => False)
        (execStmtList oracle fields
          { before with bindings := bindValue before.bindings indexName (wordNormalize index) }
          (abiGeneratedCopyBody inputs.sourceName inputs.destinationName inputs.startName
            indexName byteName addressName)) := by
    intro index before inside invariant
    have indexBound : index < Verity.Core.Uint256.modulus := by omega
    have evaluated : evalExpr oracle fields
        { before with bindings := bindValue before.bindings indexName (wordNormalize index) }
        (.localVar indexName) = some index := by
      simp only [evalExpr, SolidityImport.lookup_bind_same]
      change some (index % Verity.Core.Uint256.modulus) = some index
      rw [Nat.mod_eq_of_lt indexBound]
    obtain ⟨after, executed, preserved⟩ := abiCopyLoopInvariant_step oracle fields inputs
      state.world.memory _ indexName byteName addressName size index
      (abiCopyLoopInvariant_bind inputs _ index before indexName _ invariant indexFresh)
      byteFresh addressFresh distinct byteIndex addressIndex evaluated
      sourceAligned destinationAligned (by omega) (by omega) inside disjoint (zero index inside)
    rw [executed]
    exact preserved
  simpa only [Nat.zero_add] using execForEachLoop_bounded_invariant indexName
    (fun s => execStmtList oracle fields s (abiGeneratedCopyBody inputs.sourceName
      inputs.destinationName inputs.startName indexName byteName addressName)) size
    (AbiCopyLoopInvariant inputs state.world.memory) (fun _ => False) step size 0 state
    (by omega) ⟨held, abiCopyPrefix_zero _ _ _⟩


/-- Correctness of the actual emitted copyBytes statement, including count
evaluation and the executor's initial index binding (also for an empty copy). -/
theorem execStmt_copyBytes (oracle : DenoteOracle) (fields : List Field)
    (inputs : AbiCopyInputs) (state : DenoteState) (sizeExpr : Expr)
    (indexName byteName addressName : String) (size : Nat)
    (sizeEval : evalExpr oracle fields state sizeExpr = some size)
    (held : inputs.Holds state)
    (indexFresh : inputs.Fresh indexName) (byteFresh : inputs.Fresh byteName)
    (addressFresh : inputs.Fresh addressName)
    (distinct : addressName ≠ byteName) (byteIndex : byteName ≠ indexName)
    (addressIndex : addressName ≠ indexName)
    (sourceAligned : inputs.source % 32 = 0) (destinationAligned : inputs.destination % 32 = 0)
    (sourceBound : inputs.source + size < Verity.Core.Uint256.modulus)
    (destinationBound : inputs.destination + (inputs.start + size) < Verity.Core.Uint256.modulus)
    (disjoint : inputs.source + size ≤ inputs.destination + inputs.start ∨
      inputs.destination + inputs.start + size ≤ inputs.source)
    (zero : ∀ index, index < size →
      abiMemoryByte state.world.memory (inputs.destination + inputs.start + index) = 0) :
    ∃ after, execStmt oracle fields state (SolidityImport.AbiEncoding.copyBytes
      (.localVar inputs.sourceName) (.localVar inputs.destinationName) (.localVar inputs.startName)
      sizeExpr indexName byteName addressName) = .continue after ∧
      AbiCopyLoopInvariant inputs state.world.memory size after := by
  have result := execForEachLoop_copy oracle fields inputs
    { state with bindings := bindValue state.bindings indexName (wordNormalize 0) }
    indexName byteName addressName size
    (abiCopyInputs_bind inputs state indexName _ held indexFresh) indexFresh byteFresh addressFresh
    distinct byteIndex addressIndex sourceAligned destinationAligned sourceBound destinationBound disjoint zero
  have actual : LoopOutcomePost (AbiCopyLoopInvariant inputs state.world.memory size) (fun _ => False)
      (execStmt oracle fields state (SolidityImport.AbiEncoding.copyBytes
        (.localVar inputs.sourceName) (.localVar inputs.destinationName) (.localVar inputs.startName)
        sizeExpr indexName byteName addressName)) := by
    simpa only [SolidityImport.AbiEncoding.copyBytes, execStmt, sizeEval, abiGeneratedCopyBody] using result
  cases executed : execStmt oracle fields state (SolidityImport.AbiEncoding.copyBytes
      (.localVar inputs.sourceName) (.localVar inputs.destinationName) (.localVar inputs.startName)
      sizeExpr indexName byteName addressName) with
  | «continue» after => exact ⟨after, rfl, by simpa [executed, LoopOutcomePost] using actual⟩
  | stop after => simp [executed, LoopOutcomePost] at actual
  | «return» value after => simp [executed, LoopOutcomePost] at actual
  | revert => simp [executed, LoopOutcomePost] at actual
  | revertWithData bytes => simp [executed, LoopOutcomePost] at actual

/-- Word-grid specification for the allocator's output clearing pass. -/
def abiZeroWords (memory : Nat → Verity.Core.Uint256) (base count : Nat) :
    Nat → Verity.Core.Uint256 :=
  fun cell => if base ≤ cell ∧ cell < base + 32 * count ∧ cell % 32 = 0 then 0 else memory cell

/-- Clearing the aligned word range establishes every byte's zero precondition. -/
theorem abiZeroWords_byte (memory : Nat → Verity.Core.Uint256) (base count index : Nat)
    (aligned : base % 32 = 0) (inside : index < 32 * count) :
    abiMemoryByte (abiZeroWords memory base count) (base + index) = 0 := by
  have cell : base ≤ (base + index) / 32 * 32 ∧
      (base + index) / 32 * 32 < base + 32 * count ∧
      ((base + index) / 32 * 32) % 32 = 0 := by omega
  simp [abiMemoryByte, abiZeroWords, cell]

/-- Word-grid clearing preserves every byte outside the allocated range. -/
theorem abiZeroWords_frame (memory : Nat → Verity.Core.Uint256) (base count address : Nat)
    (aligned : base % 32 = 0) (outside : address < base ∨ base + 32 * count ≤ address) :
    abiMemoryByte (abiZeroWords memory base count) address = abiMemoryByte memory address := by
  have cell : ¬ (base ≤ address / 32 * 32 ∧ address / 32 * 32 < base + 32 * count ∧
      (address / 32 * 32) % 32 = 0) := by omega
  simp only [abiMemoryByte, abiZeroWords, if_neg cell]

theorem abiZeroWords_zero (memory : Nat → Verity.Core.Uint256) (base : Nat) :
    abiZeroWords memory base 0 = memory := by
  funext cell
  simp [abiZeroWords]
  omega

/-- One aligned zero store extends the cleared prefix by exactly one word. -/
theorem abiZeroWords_succ (memory : Nat → Verity.Core.Uint256) (base count : Nat)
    (aligned : base % 32 = 0) :
    (fun cell => if cell = base + 32 * count then 0 else abiZeroWords memory base count cell) =
      abiZeroWords memory base (count + 1) := by
  funext cell
  by_cases current : cell = base + 32 * count
  · subst cell
    have inside : base ≤ base + 32 * count ∧
        base + 32 * count < base + 32 * (count + 1) ∧ (base + 32 * count) % 32 = 0 := by omega
    simp only [if_pos rfl, abiZeroWords, if_pos inside, if_true]
  · have same : (base ≤ cell ∧ cell < base + 32 * count ∧ cell % 32 = 0) ↔
        (base ≤ cell ∧ cell < base + 32 * (count + 1) ∧ cell % 32 = 0) := by omega
    simp only [if_neg current, abiZeroWords, same]

/-- Actual MSTORE zero at the next word realizes the clearing specification. -/
theorem execStmt_zeroWord (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (initial : Nat → Verity.Core.Uint256) (address : Expr) (base count : Nat)
    (evaluated : evalExpr oracle fields state address = some (base + 32 * count))
    (cleared : state.world.memory = abiZeroWords initial base count) (aligned : base % 32 = 0) :
    execStmt oracle fields state (.mstore address (.literal 0)) =
      .continue { state with world := { state.world with memory := abiZeroWords initial base (count + 1) } } := by
  simp only [execStmt, evaluated, evalExpr]
  congr 1
  congr 1
  congr 1
  change (fun cell => if cell = base + 32 * count then 0 else state.world.memory cell) = _
  rw [cleared, abiZeroWords_succ initial base count aligned]

/-- Generated word-count multiplication is exact under its word bound. -/
theorem evalExpr_wordStride (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (indexExpr : Expr) (index : Nat)
    (evaluated : evalExpr oracle fields state indexExpr = some index)
    (bounded : 32 * index < Verity.Core.Uint256.modulus) :
    evalExpr oracle fields state (.mul indexExpr (.literal 32)) = some (32 * index) := by
  have indexBound : index < Verity.Core.Uint256.modulus := by omega
  simp only [evalExpr, evaluated]
  change some (((index % Verity.Core.Uint256.modulus) * 32) % Verity.Core.Uint256.modulus) = _
  rw [Nat.mod_eq_of_lt indexBound, Nat.mul_comm index 32, Nat.mod_eq_of_lt bounded]

/-- Complete emitted zero-store body, including base and stride evaluation. -/
theorem execStmt_zeroWordBody (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (initial : Nat → Verity.Core.Uint256)
    (baseName indexName : String) (base index : Nat)
    (baseEval : lookupValue state.bindings baseName = base)
    (indexEval : lookupValue state.bindings indexName = index)
    (bounded : base + 32 * index < Verity.Core.Uint256.modulus)
    (cleared : state.world.memory = abiZeroWords initial base index) (aligned : base % 32 = 0) :
    execStmt oracle fields state (.mstore
      (.add (.localVar baseName) (.mul (.localVar indexName) (.literal 32))) (.literal 0)) =
      .continue { state with world := { state.world with memory := abiZeroWords initial base (index + 1) } } := by
  apply execStmt_zeroWord oracle fields state initial _ base index _ cleared aligned
  apply evalExpr_add_bounded oracle fields state (.localVar baseName)
    (.mul (.localVar indexName) (.literal 32)) base (32 * index) (congrArg some baseEval)
  · exact evalExpr_wordStride oracle fields state (.localVar indexName) index (congrArg some indexEval) (by omega)
  · exact bounded

/-- Clearing-loop invariant records the base binding and the entire memory
function, so every untouched cell is preserved as well as every cleared word. -/
def AbiClearInvariant (initial : Nat → Verity.Core.Uint256) (baseName : String)
    (base count : Nat) (state : DenoteState) : Prop :=
  lookupValue state.bindings baseName = base ∧ state.world.memory = abiZeroWords initial base count

/-- Actual bounded clearing-loop executor, including all index rebindings. -/
theorem execForEachLoop_clear (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (baseName indexName : String) (base count : Nat)
    (held : lookupValue state.bindings baseName = base) (fresh : indexName ≠ baseName)
    (aligned : base % 32 = 0) (bounded : base + 32 * count < Verity.Core.Uint256.modulus) :
    LoopOutcomePost (AbiClearInvariant state.world.memory baseName base count) (fun _ => False)
      (execForEachLoop indexName (fun s => execStmtList oracle fields s
        [.mstore (.add (.localVar baseName) (.mul (.localVar indexName) (.literal 32))) (.literal 0)])
        state 0 count) := by
  have step : ∀ index before, index < count → AbiClearInvariant state.world.memory baseName base index before →
      LoopOutcomePost (AbiClearInvariant state.world.memory baseName base (index + 1)) (fun _ => False)
        (execStmtList oracle fields
          { before with bindings := bindValue before.bindings indexName (wordNormalize index) }
          [.mstore (.add (.localVar baseName) (.mul (.localVar indexName) (.literal 32))) (.literal 0)]) := by
    intro index before inside invariant
    have indexBound : index < Verity.Core.Uint256.modulus := by omega
    have baseEval : lookupValue (bindValue before.bindings indexName (wordNormalize index)) baseName = base := by
      rw [SolidityImport.lookup_bind_other _ _ _ _ fresh]
      exact invariant.1
    have indexEval : lookupValue (bindValue before.bindings indexName (wordNormalize index)) indexName = index := by
      rw [SolidityImport.lookup_bind_same]
      change index % Verity.Core.Uint256.modulus = index
      exact Nat.mod_eq_of_lt indexBound
    rw [SolidityImport.exec_singleton, execStmt_zeroWordBody oracle fields
      { before with bindings := bindValue before.bindings indexName (wordNormalize index) } state.world.memory
      baseName indexName base index baseEval indexEval (by omega) invariant.2 aligned]
    exact ⟨baseEval, rfl⟩
  simpa only [Nat.zero_add] using execForEachLoop_bounded_invariant indexName
    (fun s => execStmtList oracle fields s
      [.mstore (.add (.localVar baseName) (.mul (.localVar indexName) (.literal 32))) (.literal 0)]) count
    (AbiClearInvariant state.world.memory baseName base) (fun _ => False) step count 0 state
    (by omega) ⟨held, by rw [abiZeroWords_zero]⟩

/-- Actual clearing forEach, with count evaluation and initial index binding. -/
theorem execStmt_clearWords (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (baseName indexName : String) (countExpr : Expr) (base count : Nat)
    (countEval : evalExpr oracle fields state countExpr = some count)
    (held : lookupValue state.bindings baseName = base) (fresh : indexName ≠ baseName)
    (aligned : base % 32 = 0) (bounded : base + 32 * count < Verity.Core.Uint256.modulus) :
    ∃ after, execStmt oracle fields state (.forEach indexName countExpr
      [.mstore (.add (.localVar baseName) (.mul (.localVar indexName) (.literal 32))) (.literal 0)]) =
        .continue after ∧ AbiClearInvariant state.world.memory baseName base count after := by
  have initial : lookupValue (bindValue state.bindings indexName (wordNormalize 0)) baseName = base := by
    rw [SolidityImport.lookup_bind_other _ _ _ _ fresh]
    exact held
  have result := execForEachLoop_clear oracle fields
    { state with bindings := bindValue state.bindings indexName (wordNormalize 0) }
    baseName indexName base count initial fresh aligned bounded
  have actual : LoopOutcomePost (AbiClearInvariant state.world.memory baseName base count) (fun _ => False)
      (execStmt oracle fields state (.forEach indexName countExpr
        [.mstore (.add (.localVar baseName) (.mul (.localVar indexName) (.literal 32))) (.literal 0)])) := by
    simpa only [execStmt, countEval] using result
  cases executed : execStmt oracle fields state (.forEach indexName countExpr
      [.mstore (.add (.localVar baseName) (.mul (.localVar indexName) (.literal 32))) (.literal 0)]) with
  | «continue» after => exact ⟨after, rfl, by simpa [executed, LoopOutcomePost] using actual⟩
  | stop after => simp [executed, LoopOutcomePost] at actual
  | «return» value after => simp [executed, LoopOutcomePost] at actual
  | revert => simp [executed, LoopOutcomePost] at actual
  | revertWithData bytes => simp [executed, LoopOutcomePost] at actual

/-- Rounded word allocation covers exactly the payload plus fewer than32
padding bytes, including zero-length buffers. -/
theorem abiRoundedSize_bounds (size : Nat) :
    size ≤ 32 * ((size + 31) / 32) ∧ 32 * ((size + 31) / 32) < size + 32 := by
  omega

/-- Actual generated word count, with the rounding addition checked not to wrap. -/
theorem evalExpr_roundedCount (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (sizeExpr : Expr) (size : Nat)
    (evaluated : evalExpr oracle fields state sizeExpr = some size)
    (bounded : size + 31 < Verity.Core.Uint256.modulus) :
    evalExpr oracle fields state (.div (.add sizeExpr (.literal 31)) (.literal 32)) =
      some ((size + 31) / 32) := by
  have added := evalExpr_add_bounded oracle fields state sizeExpr (.literal 31) size 31
    evaluated (by rfl) bounded
  rw [evalExpr, added]
  change some (((size + 31) % Verity.Core.Uint256.modulus / 32) % Verity.Core.Uint256.modulus) = _
  have quotient : (size + 31) / 32 < Verity.Core.Uint256.modulus :=
    lt_of_le_of_lt (Nat.div_le_self _ _) bounded
  rw [Nat.mod_eq_of_lt bounded, Nat.mod_eq_of_lt quotient]

/-- Actual generated rounded byte allocation, with every coercion accounted for. -/
theorem evalExpr_roundedSize (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (sizeExpr : Expr) (size : Nat)
    (evaluated : evalExpr oracle fields state sizeExpr = some size)
    (bounded : size + 31 < Verity.Core.Uint256.modulus) :
    evalExpr oracle fields state
      (.mul (.div (.add sizeExpr (.literal 31)) (.literal 32)) (.literal 32)) =
        some (32 * ((size + 31) / 32)) := by
  apply evalExpr_wordStride oracle fields state _ _
    (evalExpr_roundedCount oracle fields state sizeExpr size evaluated bounded)
  have := (abiRoundedSize_bounds size).2
  omega

/-- The exact rounded clearing statement used by packedBuffer establishes
zero for every requested payload byte and preserves all bytes outside allocation. -/
theorem execStmt_clearPackedBytes (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (baseName indexName : String) (sizeExpr : Expr) (base size : Nat)
    (sizeEval : evalExpr oracle fields state sizeExpr = some size)
    (held : lookupValue state.bindings baseName = base) (fresh : indexName ≠ baseName)
    (aligned : base % 32 = 0) (sizeBound : size + 31 < Verity.Core.Uint256.modulus)
    (allocationBound : base + 32 * ((size + 31) / 32) < Verity.Core.Uint256.modulus) :
    ∃ after, execStmt oracle fields state
      (.forEach indexName (.div (.add sizeExpr (.literal 31)) (.literal 32))
        [.mstore (.add (.localVar baseName) (.mul (.localVar indexName) (.literal 32))) (.literal 0)]) =
        .continue after ∧ lookupValue after.bindings baseName = base ∧
      (∀ index, index < size → abiMemoryByte after.world.memory (base + index) = 0) ∧
      (∀ address, address < base ∨ base + 32 * ((size + 31) / 32) ≤ address →
        abiMemoryByte after.world.memory address = abiMemoryByte state.world.memory address) := by
  obtain ⟨after, executed, result⟩ := execStmt_clearWords oracle fields state baseName indexName
    _ base ((size + 31) / 32) (evalExpr_roundedCount oracle fields state sizeExpr size sizeEval sizeBound)
    held fresh aligned allocationBound
  refine ⟨after, executed, result.1, ?_, ?_⟩
  · intro index inside
    rw [result.2]
    apply abiZeroWords_byte _ base _ index aligned
    have := (abiRoundedSize_bounds size).1
    omega
  · intro address outside
    rw [result.2]
    exact abiZeroWords_frame _ base _ address aligned outside

/-- Exact successful reserve prefix. The size is evaluated after the base
binding, so callers must prove freshness rather than assuming unchanged locals. -/
theorem execStmtList_reserve (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (baseName endName : String) (sizeExpr : Expr) (base size : Nat)
    (pointer : (state.world.memory 64).val = base) (distinct : endName ≠ baseName)
    (sizeEval : evalExpr oracle fields
      { state with bindings := bindValue state.bindings baseName base } sizeExpr = some size)
    (bounded : base + size ≤ 2^64 - 1) :
    execStmtList oracle fields state (SolidityImport.AbiEncoding.reserve baseName endName sizeExpr) =
      .continue { state with
        bindings := bindValue (bindValue state.bindings baseName base) endName (base + size)
        world := { state.world with memory := fun cell =>
          if cell = 64 then Verity.Core.Uint256.ofNat (base + size) else state.world.memory cell } } := by
  have read : evalExpr oracle fields state (.mload (.literal 64)) = some base := by
    change some (state.world.memory 64).val = some base
    rw [pointer]
  have wordBound : base + size < Verity.Core.Uint256.modulus := by
    have : 2^64 - 1 < Verity.Core.Uint256.modulus := by decide
    omega
  have sum := evalExpr_add_bounded oracle fields
    { state with bindings := bindValue state.bindings baseName base }
    (.localVar baseName) sizeExpr base size
    (by simp [evalExpr, SolidityImport.lookup_bind_same]) sizeEval wordBound
  unfold SolidityImport.AbiEncoding.reserve
  rw [SolidityImport.exec_let_cons, read]
  simp only
  rw [SolidityImport.exec_let_cons, sum]
  simp only
  simp [execStmtList, execStmt, evalExpr, SolidityImport.lookup_bind_same,
    SolidityImport.lookup_bind_other, distinct, boolWord, wordNormalize,
    Verity.Core.Uint256.ofNat, Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS,
    bounded]

/-- Exceeding the allocator's64-bit bound produces the exact panic payload,
not a generic failure. The addition is nonwrapping in this guard case. -/
theorem execStmtList_reserve_oversized (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (baseName endName : String) (sizeExpr : Expr) (base size : Nat)
    (pointer : (state.world.memory 64).val = base)
    (sizeEval : evalExpr oracle fields
      { state with bindings := bindValue state.bindings baseName base } sizeExpr = some size)
    (wordBound : base + size < Verity.Core.Uint256.modulus)
    (oversized : 2^64 - 1 < base + size) :
    execStmtList oracle fields state (SolidityImport.AbiEncoding.reserve baseName endName sizeExpr) =
      .revertWithData (panicBytes 0x41) := by
  have read : evalExpr oracle fields state (.mload (.literal 64)) = some base := by
    change some (state.world.memory 64).val = some base
    rw [pointer]
  have sum := evalExpr_add_bounded oracle fields
    { state with bindings := bindValue state.bindings baseName base }
    (.localVar baseName) sizeExpr base size
    (by simp [evalExpr, SolidityImport.lookup_bind_same]) sizeEval wordBound
  unfold SolidityImport.AbiEncoding.reserve
  rw [SolidityImport.exec_let_cons, read]
  simp only
  rw [SolidityImport.exec_let_cons, sum]
  simp only
  have rejected : ¬ base + size ≤ 2^64 - 1 := by omega
  simp [execStmtList, execStmt, evalExpr, SolidityImport.lookup_bind_same,
    boolWord, wordNormalize, Verity.Core.Uint256.ofNat, Verity.Core.Uint256.modulus,
    Verity.Core.UINT256_MODULUS, rejected]

/-- Full emitted packedBuffer sequence: reserve followed by rounded clearing.
The memory result explicitly includes the free-pointer update; no frame claim
silently discards that write. -/
theorem execStmtList_packedBuffer (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (baseName endName indexName sizeName : String) (base size : Nat)
    (pointer : (state.world.memory 64).val = base)
    (sizeValue : lookupValue state.bindings sizeName = size)
    (distinct : endName ≠ baseName) (baseFresh : baseName ≠ sizeName)
    (endFresh : endName ≠ sizeName) (indexFresh : indexName ≠ baseName)
    (aligned : base % 32 = 0) (bounded : base + 32 * ((size + 31) / 32) ≤ 2^64 - 1) :
    ∃ after, execStmtList oracle fields state
      (SolidityImport.AbiEncoding.packedBuffer baseName endName indexName (.localVar sizeName)) =
        .continue after ∧ lookupValue after.bindings baseName = base ∧
      after.world.memory = abiZeroWords
        (fun cell => if cell = 64 then Verity.Core.Uint256.ofNat (base + 32 * ((size + 31) / 32))
          else state.world.memory cell) base ((size + 31) / 32) := by
  let count := (size + 31) / 32
  let reserved : DenoteState := { state with
    bindings := bindValue (bindValue state.bindings baseName base) endName (base + 32 * count)
    world := { state.world with memory := fun cell =>
      if cell = 64 then Verity.Core.Uint256.ofNat (base + 32 * count) else state.world.memory cell } }
  have sizeBound : size + 31 < Verity.Core.Uint256.modulus := by
    have := (abiRoundedSize_bounds size).1
    have : 2^64 + 31 < Verity.Core.Uint256.modulus := by decide
    omega
  have sizeAfterBase : evalExpr oracle fields
      { state with bindings := bindValue state.bindings baseName base } (.localVar sizeName) = some size := by
    simp [evalExpr, SolidityImport.lookup_bind_other, baseFresh, sizeValue]
  have allocation := execStmtList_reserve oracle fields state baseName endName
    (.mul (.div (.add (.localVar sizeName) (.literal 31)) (.literal 32)) (.literal 32)) base
    (32 * count) pointer distinct
    (evalExpr_roundedSize oracle fields _ _ size sizeAfterBase sizeBound) bounded
  have sizeAfter : evalExpr oracle fields reserved (.localVar sizeName) = some size := by
    simp [reserved, evalExpr, SolidityImport.lookup_bind_other, endFresh, baseFresh, sizeValue]
  have baseAfter : lookupValue reserved.bindings baseName = base := by
    simp [reserved, SolidityImport.lookup_bind_other, SolidityImport.lookup_bind_same, distinct]
  have wordBound : base + 32 * count < Verity.Core.Uint256.modulus := by
    have : 2^64 - 1 < Verity.Core.Uint256.modulus := by decide
    omega
  obtain ⟨after, cleared, result⟩ := execStmt_clearWords oracle fields reserved baseName indexName
    _ base count (evalExpr_roundedCount oracle fields reserved _ size sizeAfter sizeBound)
    baseAfter indexFresh aligned wordBound
  refine ⟨after, ?_, result.1, result.2⟩
  unfold SolidityImport.AbiEncoding.packedBuffer
  rw [SolidityImport.exec_append, allocation]
  exact (SolidityImport.exec_singleton oracle fields reserved _).trans cleared

/-- Adding two bounded words across the modulus produces an end below base,
which is exactly what reserve's second guard rejects. -/
theorem abiReserve_wrapBelow (base size : Nat)
    (baseBound : base < Verity.Core.Uint256.modulus)
    (sizeBound : size < Verity.Core.Uint256.modulus)
    (wrapped : Verity.Core.Uint256.modulus ≤ base + size) :
    (base + size) % Verity.Core.Uint256.modulus < base := by
  rw [Nat.mod_eq_sub_mod wrapped]
  have remainder : base + size - Verity.Core.Uint256.modulus < Verity.Core.Uint256.modulus := by omega
  rw [Nat.mod_eq_of_lt remainder]
  omega

/-- The wrapped-addition allocation case is rejected with exact panic bytes. -/
theorem execStmtList_reserve_wrapped (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (baseName endName : String) (sizeExpr : Expr) (base size : Nat)
    (pointer : (state.world.memory 64).val = base) (distinct : endName ≠ baseName)
    (sizeEval : evalExpr oracle fields
      { state with bindings := bindValue state.bindings baseName base } sizeExpr = some size)
    (sizeBound : size < Verity.Core.Uint256.modulus)
    (wrapped : Verity.Core.Uint256.modulus ≤ base + size) :
    execStmtList oracle fields state (SolidityImport.AbiEncoding.reserve baseName endName sizeExpr) =
      .revertWithData (panicBytes 0x41) := by
  have baseBound : base < Verity.Core.Uint256.modulus := pointer ▸ (state.world.memory 64).isLt
  have below := abiReserve_wrapBelow base size baseBound sizeBound wrapped
  have rejected : ¬ base ≤ (base + size) % Verity.Core.Uint256.modulus := by omega
  have read : evalExpr oracle fields state (.mload (.literal 64)) = some base := by
    change some (state.world.memory 64).val = some base
    rw [pointer]
  have sum : evalExpr oracle fields
      { state with bindings := bindValue state.bindings baseName base } (.add (.localVar baseName) sizeExpr) =
        some ((base + size) % Verity.Core.Uint256.modulus) := by
    simp only [evalExpr, SolidityImport.lookup_bind_same, sizeEval]
    change some (((base % Verity.Core.Uint256.modulus) + (size % Verity.Core.Uint256.modulus)) %
      Verity.Core.Uint256.modulus) = _
    rw [Nat.mod_eq_of_lt baseBound, Nat.mod_eq_of_lt sizeBound]
  unfold SolidityImport.AbiEncoding.reserve
  rw [SolidityImport.exec_let_cons, read]
  simp only
  rw [SolidityImport.exec_let_cons, sum]
  simp only
  by_cases limit : (base + size) % Verity.Core.Uint256.modulus ≤ 2^64 - 1 <;>
    simp only [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS] at limit rejected <;>
    simp [execStmtList, execStmt, evalExpr, SolidityImport.lookup_bind_same,
      SolidityImport.lookup_bind_other, distinct, boolWord, wordNormalize,
      Verity.Core.Uint256.ofNat, Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS,
      limit, rejected]

end Compiler.CompilationModel.Denote

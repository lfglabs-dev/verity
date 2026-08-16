import Compiler.Proofs.MappingSlot
import Compiler.CompilationModel.ExpressionCompile
import Compiler.CompilationModel.StorageWrites
import Compiler.Proofs.IRGeneration.SourceSemantics
import Compiler.Proofs.IRGeneration.GenericInduction.Main
import Compiler.CodegenCommon
import Verity.Core.Model.Types

namespace Compiler.Proofs.Storage

open Compiler.Proofs
open Compiler.Proofs.IRGeneration
open Compiler Compiler.CompilationModel Compiler.Yul

/-- Stable identity used to separate the storage of distinct contracts. -/
abbrev ContractId := Nat

/-- A canonical EVM storage word. -/
abbrev Word := IRStorageWord

/-- Canonical, contract-indexed Solidity storage, addressed by 32-byte slot keys. -/
abbrev SolidityStorage := ContractId → ByteArray → Word

/-- The canonical byte pointer for a Solidity mapping entry. Solidity hashes the
    ABI word for the key followed by the ABI word for the mapping's base slot. -/
def mappingSlotPointer (baseSlot key : Nat) : ByteArray :=
  KeccakEngine.keccak256 (abiEncodeMappingSlot baseSlot key)

/-- Every pointer constructed for a mapping entry carries the canonical Solidity
    ABI preimage `(key, baseSlot)`. This is the usable preimage direction and does
    not postulate injectivity of Keccak. -/
theorem mappingSlot_preimage (baseSlot key : Nat) :
    ∃ preimage : ByteArray,
      preimage = abiEncodeMappingSlot baseSlot key ∧
      mappingSlotPointer baseSlot key = KeccakEngine.keccak256 preimage := by
  exact ⟨abiEncodeMappingSlot baseSlot key, rfl, rfl⟩

/-- Structurally interpret the emitted `mappingSlot` helper. Matching every
    statement keeps the bridge sensitive to the two stores' order and addresses,
    as well as the hash range. -/
def compiledMappingSlotPointer
    (stmt : Compiler.Yul.YulStmt) (scratchBase baseSlot key : Nat) : Option ByteArray :=
  match stmt with
  | .funcDef "mappingSlot" ["baseSlot", "key"] ["slot"] [
      .exprStmt (.call "mstore" [.lit keyPtr, .ident "key"]),
      .exprStmt (.call "mstore" [.lit slotPtr, .ident "baseSlot"]),
      .assign "slot" (.call "keccak256" [.lit hashPtr, .lit hashSize])] =>
      if keyPtr == scratchBase && slotPtr == scratchBase + 32 &&
          hashPtr == scratchBase && hashSize == 64 then
        some (KeccakEngine.keccak256 (abiEncodeMappingSlot baseSlot key))
      else
        none
  | _ => none

/-- The emitted `mappingSlot` helper computes the canonical Solidity mapping
    pointer. Any change to its line-by-line Yul shape is observable here. -/
theorem compiledMappingSlotPointer_eq_mappingSlotPointer
    (scratchBase baseSlot key : Nat) :
    compiledMappingSlotPointer
        (Compiler.CodegenCommon.mappingSlotFuncAt scratchBase)
        scratchBase baseSlot key =
      some (mappingSlotPointer baseSlot key) := by
  simp [compiledMappingSlotPointer, Compiler.CodegenCommon.mappingSlotFuncAt,
    mappingSlotPointer]

/-- The pointer returned by the emitted helper is the same mapping slot used by
    source evaluation through `abstractMappingSlot`. -/
theorem mappingSlotPointer_eq_abstractMappingSlot (baseSlot key : Nat) :
    EvmYul.fromByteArrayBigEndian (mappingSlotPointer baseSlot key) =
      Compiler.Proofs.abstractMappingSlot baseSlot key := by
  rfl

/-- Synthetic mapping field used to expose the executable source mapping case. -/
def mappingSlotBridgeField (baseSlot : Nat) : Compiler.CompilationModel.Field :=
  { name := "__mapping_slot_bridge",
    ty := .mappingTyped (.simple .uint256), slot := some baseSlot }

/-- A slot-reflecting world makes a source read return its actual storage slot. -/
def mappingSlotBridgeState : SourceSemantics.RuntimeState :=
  { world := Verity.defaultState.withStorageChannel (fun _ => fun slot => slot),
    bindings := [] }

/-- A source mapping expression evaluated in a slot-reflecting world exposes
    the exact slot passed to `readFieldWord`. -/
def sourceMappingSlotRead (baseSlot key : Nat) : Option Nat :=
  SourceSemantics.evalExpr [mappingSlotBridgeField baseSlot] mappingSlotBridgeState
    (.mapping "__mapping_slot_bridge" (.literal key))

/-- The emitted helper's decoded result is precisely the slot consumed by the
    executable source mapping-read case. This joins the generated helper and
    `evalExpr` through `abstractMappingSlot`, rather than merely unfolding two
    copies of the Keccak definition. -/
theorem compiledMappingSlotPointer_eq_sourceMappingSlotRead
    (scratchBase baseSlot key : Nat) (hkey : key < Compiler.Constants.evmModulus) :
    Option.map EvmYul.fromByteArrayBigEndian
        (compiledMappingSlotPointer
          (Compiler.CodegenCommon.mappingSlotFuncAt scratchBase)
          scratchBase baseSlot key) =
      sourceMappingSlotRead baseSlot key := by
  rw [compiledMappingSlotPointer_eq_mappingSlotPointer,
    Option.map_some, mappingSlotPointer_eq_abstractMappingSlot]
  have hfield : Compiler.CompilationModel.findFieldWithResolvedSlot
      [mappingSlotBridgeField baseSlot] "__mapping_slot_bridge" =
      some (mappingSlotBridgeField baseSlot, baseSlot) := by
    rfl
  unfold sourceMappingSlotRead
  rw [SourceSemantics.evalExpr]
  simp only [SourceSemantics.evalExpr]
  rw [hfield]
  simp [mappingSlotBridgeField, mappingSlotBridgeState, SourceSemantics.readFieldWord,
    Verity.ContractState.storage_withStorageChannel, SourceSemantics.wordNormalize]
  change Compiler.Proofs.solidityMappingSlot baseSlot key =
    Compiler.Proofs.solidityMappingSlot baseSlot
      (key % Compiler.Constants.evmModulus) % Compiler.Constants.evmModulus
  rw [Nat.mod_eq_of_lt (Compiler.Proofs.solidityMappingSlot_lt_evmModulus
    baseSlot (key % Compiler.Constants.evmModulus))]
  rw [Nat.mod_eq_of_lt hkey]

/-- Reading a mapping key uses the pointer returned by the emitted `mappingSlot`
    helper, and decoding that same pointer yields the slot consumed by the
    executable source evaluator. -/
theorem mappingSlot_of_key (storage : SolidityStorage) (id : ContractId)
    (scratchBase baseSlot key : Nat) (hkey : key < Compiler.Constants.evmModulus) :
    Option.map (storage id)
        (compiledMappingSlotPointer
          (Compiler.CodegenCommon.mappingSlotFuncAt scratchBase)
          scratchBase baseSlot key) =
        some (storage id (mappingSlotPointer baseSlot key)) ∧
      Option.map EvmYul.fromByteArrayBigEndian
        (compiledMappingSlotPointer
          (Compiler.CodegenCommon.mappingSlotFuncAt scratchBase)
          scratchBase baseSlot key) =
        sourceMappingSlotRead baseSlot key := by
  constructor
  · rw [compiledMappingSlotPointer_eq_mappingSlotPointer, Option.map_some]
  · exact compiledMappingSlotPointer_eq_sourceMappingSlotRead scratchBase baseSlot key hkey

/-- Mask for a packed Solidity field of `width` low-order bits. -/
def packedMask (width : Nat) : Nat := 2 ^ width - 1

/-- Yul's `and(shr(offset, sload(pointer)), mask)` interpretation. -/
def yulReadPackedWord (word : Word) (offset width : Nat) : Word :=
  IRStorageWord.ofNat ((word.toNat / 2 ^ offset) % 2 ^ width)

/-- Synthetic scalar field used to expose the packed-storage compiler branch. -/
def packedReadBridgeField (offset width : Nat) : Compiler.CompilationModel.Field :=
  { name := "__packed_read_bridge", ty := .uint256, slot := some 0,
    packedBits := some { offset := offset, width := width } }

/-- Interpret the exact packed-storage expression emitted by
    `compileExprWithInternals`. The deliberately structural match makes changes
    to the emitted operator order, offset, load, slot, or mask observable here. -/
def isCompiledPackedReadExpr : Compiler.Yul.YulExpr → Nat → Nat → Bool
  | .call "and" [.call "shr" [.lit shift, .call "sload" [.lit 0]], .lit mask],
      offset, width => shift == offset && mask == packedMask width
  | _, _, _ => false

def compiledPackedRead (word : Word) (offset width : Nat) : Word :=
  let emitted := Compiler.CompilationModel.compileExprWithInternals
      [packedReadBridgeField offset width] .calldata []
      (.storage "__packed_read_bridge")
  match emitted with
  | .ok expr =>
      if isCompiledPackedReadExpr expr offset width then yulReadPackedWord word offset width
      else IRStorageWord.ofNat 0
  | .error _ => IRStorageWord.ofNat 0

/-- The helper for a Yul packed read is the interpretation of the real compiler
    path in `ExpressionCompile.lean`. -/
theorem yulReadPackedWord_eq_compiledExpr (word : Word) (offset width : Nat)
    (hwidth : width ≤ 256) :
    yulReadPackedWord word offset width = compiledPackedRead word offset width := by
  have hfield :
      Compiler.CompilationModel.findFieldWithResolvedSlot
        [packedReadBridgeField offset width] "__packed_read_bridge" =
        some (packedReadBridgeField offset width, 0) := by
    rfl
  have hmapping :
      Compiler.CompilationModel.isMapping
        [packedReadBridgeField offset width] "__packed_read_bridge" = false := by
    rfl
  have hcompile :
      Compiler.CompilationModel.compileExprWithInternals
          [packedReadBridgeField offset width] .calldata []
          (.storage "__packed_read_bridge") =
        .ok (.call "and"
          [.call "shr" [.lit offset, .call "sload" [.lit 0]],
            .lit (packedMask width)]) := by
    simp only [Compiler.CompilationModel.compileExprWithInternals, hmapping,
      Bool.false_eq_true, if_false, hfield]
    by_cases hlt : width < 256
    · simp [packedReadBridgeField, Compiler.CompilationModel.packedMaskNat,
        Nat.not_le.mpr hlt, packedMask]
      change Except.ok _ = Except.ok _
      rfl
    · have heq : width = 256 := Nat.le_antisymm hwidth (Nat.le_of_not_gt hlt)
      subst width
      simp [packedReadBridgeField, Compiler.CompilationModel.packedMaskNat, packedMask]
      change Except.ok _ = Except.ok _
      rfl
  unfold compiledPackedRead
  rw [hcompile]
  simp [isCompiledPackedReadExpr]

/-! ### The executable source packed read

`yulReadPackedWord_eq_compiledExpr` pins the compiler end of a packed read.
The definitions below pin the source end against the *executable* evaluator
`SourceSemantics.evalExpr`, so `sourceReadPackedWord` is a consequence of the
evaluator the rest of the source semantics runs on, rather than a restatement
of the Yul model. -/

/-- The source expression compiled and evaluated by the bridge. Keeping this as
    the same `Expr.storage` value on both sides prevents the proof from silently
    comparing two different evaluator/compiler cases. -/
def packedReadBridgeSourceExpr : Compiler.CompilationModel.Expr :=
  .storage "__packed_read_bridge"

/-- Structural predicate on the source IR: `e` is a struct-member read whose
    resolved member is packed at exactly `offset`/`width`. This is the shape the
    executable evaluator dispatches on, so a change to the member placement or to
    the expression constructor is observable here. -/
def isSourcePackedRead (fields : List Compiler.CompilationModel.Field)
    (e : Compiler.CompilationModel.Expr) (offset width : Nat) : Bool :=
  match e with
  | .storage fieldName =>
      match Compiler.CompilationModel.findFieldWithResolvedSlot fields fieldName with
      | some (field, _) =>
          match field.packedBits with
          | some packed => packed.offset == offset && packed.width == width
          | none => false
      | none => false
  | _ => false

/-- A runtime state holding `word` in every storage slot, so the bridge observes
    the packed extraction itself rather than slot arithmetic. -/
def packedReadBridgeState (word : Word) : SourceSemantics.RuntimeState :=
  { world := Verity.defaultState.withStorageChannel
      (fun _ => fun _ => Verity.Core.Uint256.ofNat word.toNat),
    bindings := [] }

/-- The packed read performed by the executable source evaluator. -/
def sourceEvalPackedRead (word : Word) (offset width : Nat) : Option Nat :=
  if isSourcePackedRead [packedReadBridgeField offset width]
      packedReadBridgeSourceExpr offset width then
    SourceSemantics.evalExpr [packedReadBridgeField offset width]
      (packedReadBridgeState word) packedReadBridgeSourceExpr
  else
    none

/-- Source-level extraction of a packed field, read off the executable source
    evaluator instead of restating the Yul model. -/
def sourceReadPackedWord (word : Word) (offset width : Nat) : Word :=
  match sourceEvalPackedRead word offset width with
  | some value => IRStorageWord.ofNat value
  | none => IRStorageWord.ofNat 0

private theorem land_packedMaskNat (x : Nat) (packed : Compiler.CompilationModel.PackedBits)
    (hx : x < 2 ^ 256) :
    Nat.land x (Compiler.CompilationModel.packedMaskNat packed) = x % 2 ^ packed.width := by
  unfold Compiler.CompilationModel.packedMaskNat
  by_cases hw : packed.width ≥ 256
  · have h256 : (2 : Nat) ^ 256 ≤ 2 ^ packed.width := Nat.pow_le_pow_right (by decide) hw
    have heq : Compiler.CompilationModel.uint256Modulus - 1 = 2 ^ 256 - 1 := rfl
    have hand : Nat.land x (2 ^ 256 - 1) = x % 2 ^ 256 := Nat.and_two_pow_sub_one_eq_mod x 256
    rw [if_pos hw, heq, hand, Nat.mod_eq_of_lt hx,
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hx h256)]
  · rw [if_neg hw]
    exact Nat.and_two_pow_sub_one_eq_mod x packed.width

private theorem packedMaskNat_lt (packed : Compiler.CompilationModel.PackedBits) :
    Compiler.CompilationModel.packedMaskNat packed < 2 ^ 256 := by
  have hmod : Compiler.CompilationModel.uint256Modulus = 2 ^ 256 := rfl
  have hpos : (0 : Nat) < 2 ^ 256 := by positivity
  unfold Compiler.CompilationModel.packedMaskNat
  by_cases hw : packed.width ≥ 256
  · rw [if_pos hw, hmod]; omega
  · rw [if_neg hw]
    have hle : (2 : Nat) ^ packed.width ≤ 2 ^ 256 := Nat.pow_le_pow_right (by decide) (by omega)
    have hp : (0 : Nat) < 2 ^ packed.width := by positivity
    omega

private theorem uint256_packed_extract (raw : Nat)
    (packed : Compiler.CompilationModel.PackedBits)
    (hraw : raw < 2 ^ 256) (hoffset : packed.offset < 256) :
    (Verity.Core.Uint256.and
        (Verity.Core.Uint256.shr (Verity.Core.Uint256.ofNat packed.offset)
          (Verity.Core.Uint256.ofNat raw))
        (Verity.Core.Uint256.ofNat
          (Compiler.CompilationModel.packedMaskNat packed))).val
      = (raw / 2 ^ packed.offset) % 2 ^ packed.width := by
  have hbig : (256 : Nat) < 2 ^ 256 := by norm_num
  have hoff : packed.offset < 2 ^ 256 := Nat.lt_trans hoffset hbig
  have hdiv : raw / 2 ^ packed.offset < 2 ^ 256 :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hraw
  show Nat.land ((raw % 2 ^ 256) >>> (packed.offset % 2 ^ 256) % 2 ^ 256)
      (Compiler.CompilationModel.packedMaskNat packed % 2 ^ 256) % 2 ^ 256
    = (raw / 2 ^ packed.offset) % 2 ^ packed.width
  rw [Nat.mod_eq_of_lt hraw, Nat.mod_eq_of_lt hoff, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt hdiv, Nat.mod_eq_of_lt (packedMaskNat_lt packed),
    land_packedMaskNat _ packed hdiv,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le _ _) hdiv)]

/-- The bridge expression really is a source packed read at `offset`/`width`. -/
theorem isSourcePackedRead_bridge (offset width : Nat) :
    isSourcePackedRead [packedReadBridgeField offset width]
      packedReadBridgeSourceExpr offset width = true := by
  have hfield :
      Compiler.CompilationModel.findFieldWithResolvedSlot
        [packedReadBridgeField offset width] "__packed_read_bridge" =
        some (packedReadBridgeField offset width, 0) := by
    rfl
  unfold isSourcePackedRead
  dsimp only [packedReadBridgeSourceExpr]
  rw [hfield]
  simp [packedReadBridgeField]

/-- The compiler's packed read agrees with the packed read the executable source
    evaluator performs. Changing the emitted operand order, mask or offset breaks
    the left-hand side; changing the evaluator's `and`/`shr`/mask breaks the right.
    -/
theorem compiledPackedRead_eq_sourceEvalPackedRead (word : Word) (offset width : Nat)
    (hoffset : offset < 256) (hwidth : width ≤ 256) :
    sourceEvalPackedRead word offset width =
      some (compiledPackedRead word offset width).toNat := by
  have hraw : word.toNat % Verity.Core.Uint256.modulus < 2 ^ 256 :=
    Nat.mod_lt _ Verity.Core.Uint256.modulus_pos
  have heval : SourceSemantics.evalExpr [packedReadBridgeField offset width]
      (packedReadBridgeState word) packedReadBridgeSourceExpr =
      some (Verity.Core.Uint256.and
        (Verity.Core.Uint256.shr (Verity.Core.Uint256.ofNat offset)
          (Verity.Core.Uint256.ofNat (word.toNat % Verity.Core.Uint256.modulus)))
        (Verity.Core.Uint256.ofNat
          (Compiler.CompilationModel.packedMaskNat { offset := offset, width := width }))).val := by
    have hfield :
        Compiler.CompilationModel.findFieldWithResolvedSlot
          [packedReadBridgeField offset width] "__packed_read_bridge" =
          some (packedReadBridgeField offset width, 0) := by
      rfl
    unfold packedReadBridgeSourceExpr
    rw [SourceSemantics.evalExpr, hfield]
    simp [packedReadBridgeField, packedReadBridgeState,
      Verity.ContractState.storage_withStorageChannel,
      SourceSemantics.readFieldWord, SourceSemantics.wordNormalize]
  have hextract := uint256_packed_extract (word.toNat % Verity.Core.Uint256.modulus)
    { offset := offset, width := width } hraw hoffset
  rw [← yulReadPackedWord_eq_compiledExpr word offset width hwidth]
  unfold sourceEvalPackedRead
  rw [if_pos (isSourcePackedRead_bridge offset width), heval, hextract]
  have hword : word.toNat % Verity.Core.Uint256.modulus = word.toNat :=
    Nat.mod_eq_of_lt (IRStorageWord.toNat_lt_size word)
  have hsize : (word.toNat / 2 ^ offset) % 2 ^ width < EvmYul.UInt256.size :=
    Nat.lt_of_le_of_lt (Nat.mod_le _ _)
      (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (IRStorageWord.toNat_lt_size word))
  rw [hword, yulReadPackedWord, IRStorageWord.toNat_ofNat, Nat.mod_eq_of_lt hsize]

/-- A source packed-word read produces the same word as the corresponding Yul
    `sload`/`shr`/`and` sequence. The left-hand side now runs the executable
    source evaluator, so this is a real bridge rather than a restatement. -/
theorem sourceRead_of_packedWord (word : Word) (offset width : Nat)
    (hoffset : offset < 256) (hwidth : width ≤ 256) :
    sourceReadPackedWord word offset width = yulReadPackedWord word offset width := by
  unfold sourceReadPackedWord
  rw [compiledPackedRead_eq_sourceEvalPackedRead word offset width hoffset hwidth,
    ← yulReadPackedWord_eq_compiledExpr word offset width hwidth]
  exact IRStorageWord.ofNat_toNat _

/-- The reverse bridge lets a Yul packed-word read be interpreted as the source
    read of the same Solidity field. -/
theorem packedWord_of_sourceRead (word : Word) (offset width : Nat)
    (hoffset : offset < 256) (hwidth : width ≤ 256) :
    yulReadPackedWord word offset width = sourceReadPackedWord word offset width := by
  exact (sourceRead_of_packedWord word offset width hoffset hwidth).symm

/-- One canonical source storage delta. A list represents sequential writes. -/
structure StorageWrite where
  contract : ContractId
  slot : ByteArray
  value : Word

abbrev StorageDiff := List StorageWrite

/-- Apply source storage writes in program order. Later writes to a slot win. -/
def applyStateRewrite (diff : StorageDiff) (storage : SolidityStorage) : SolidityStorage :=
  diff.foldl (fun current write contract slot =>
    if contract = write.contract ∧ slot = write.slot then write.value
    else current contract slot) storage

/-- Apply a single canonical source storage write. -/
def applyStorageWrite (write : StorageWrite) (storage : SolidityStorage) : SolidityStorage :=
  fun contract slot =>
    if contract = write.contract ∧ slot = write.slot then write.value
    else storage contract slot

theorem applyStateRewrite_cons (write : StorageWrite) (writes : StorageDiff)
    (storage : SolidityStorage) :
    applyStateRewrite (write :: writes) storage =
      applyStateRewrite writes (applyStorageWrite write storage) := rfl

/-! ### Interpreting the emitted `sstore` calls

`applyStateRewrite` is the source-side state transformer. The definitions below
recover the same transformer by pattern-matching the Yul that
`Compiler/CompilationModel/StorageWrites.lean` actually emits for a storage
assignment, so the two are related by a proof rather than by an alias. -/

/-- Synthetic single-slot storage field used to expose the real `sstore`
    lowering in `compileSetStorage`. -/
def sstoreBridgeField (slot : Nat) : Compiler.CompilationModel.Field :=
  { name := "__sstore_bridge", ty := .uint256, slot := some slot }

/-- The statements the real compiler emits for a plain single-slot store. -/
def compiledSstoreStmts (slot value : Nat) : List Compiler.Yul.YulStmt :=
  match Compiler.CompilationModel.compileSetStorage
      [sstoreBridgeField slot] .calldata "__sstore_bridge" (.literal value) with
  | .ok stmts => stmts
  | .error _ => []

/-- The emitted lowering is exactly one `sstore(slot, value)` call. Any change to
    the statement shape, the store builtin or the slot operand is observable here. -/
theorem compiledSstoreStmts_eq (slot value : Nat) :
    compiledSstoreStmts slot value =
      [.exprStmt (.call "sstore" [.lit slot,
        .lit (value % Compiler.CompilationModel.uint256Modulus)])] := by
  have hfield : Compiler.CompilationModel.findFieldWithResolvedSlot
      [({ name := "__sstore_bridge", ty := .uint256, slot := some slot } :
          Compiler.CompilationModel.Field)] "__sstore_bridge"
      = some ({ name := "__sstore_bridge", ty := .uint256, slot := some slot }, slot) := rfl
  simp only [compiledSstoreStmts, Compiler.CompilationModel.compileSetStorage,
    sstoreBridgeField, Compiler.CompilationModel.isMapping, hfield,
    Compiler.CompilationModel.compileExprWithInternals]
  rfl

/-- The canonical Yul slot literal denoted by a source storage write. -/
def writeSlotLit (write : StorageWrite) : Nat :=
  EvmYul.fromByteArrayBigEndian write.slot

/-- A source diff is executable as one Yul contract invocation only when every
    write belongs to that contract and every key has the canonical EVM width. -/
def ValidSstoreDiff (currentContract : ContractId) (diff : StorageDiff) : Prop :=
  ∀ write ∈ diff, write.contract = currentContract ∧ write.slot.size = 32

/-- The `sstore` sequence the compiler emits for a whole valid source storage
    diff. The contract and canonical-key checks are deliberately retained in
    the program boundary instead of being reconstructed after decoding slots. -/
def compiledSstoreProgram (currentContract : ContractId) (diff : StorageDiff) :
    List Compiler.Yul.YulStmt :=
  diff.flatMap fun write =>
    if write.contract == currentContract && write.slot.size == 32 then
      compiledSstoreStmts (writeSlotLit write) write.value.toNat
    else []

/-- Structurally interpret emitted Yul statements as storage updates. Each
    statement must be exactly the `sstore(slot, value)` call that
    `compileSetStorage` emits for the corresponding source write; any other
    statement shape, slot operand or value operand leaves storage untouched. -/
def compiledYulSstores :
    ContractId → List Compiler.Yul.YulStmt → StorageDiff → SolidityStorage → SolidityStorage
  | currentContract, .exprStmt (.call "sstore" [.lit slot, .lit value]) :: stmts,
      write :: writes, storage =>
      if write.contract == currentContract && write.slot.size == 32 &&
          slot == writeSlotLit write &&
          value == write.value.toNat % Compiler.CompilationModel.uint256Modulus then
        compiledYulSstores currentContract stmts writes (applyStorageWrite write storage)
      else storage
  | _, _, _, storage => storage

/-- Canonical interpretation of the equivalent sequence of Yul `sstore` calls:
    walk the statements the compiler emits for `diff` and apply each store. -/
def applyYulSstores (currentContract : ContractId) (diff : StorageDiff)
    (storage : SolidityStorage) : SolidityStorage :=
  compiledYulSstores currentContract (compiledSstoreProgram currentContract diff) diff storage

theorem applyYulSstores_eq_compiledYulSstores (currentContract : ContractId)
    (diff : StorageDiff) (storage : SolidityStorage) :
    applyYulSstores currentContract diff storage =
      compiledYulSstores currentContract (compiledSstoreProgram currentContract diff) diff storage :=
  rfl

/-- The emitted `sstore` sequence, structurally interpreted, performs exactly the
    canonical source storage rewrite. -/
theorem applyYulSstores_eq_applyStateRewrite (currentContract : ContractId)
    (diff : StorageDiff) (storage : SolidityStorage)
    (hvalid : ValidSstoreDiff currentContract diff) :
    applyYulSstores currentContract diff storage = applyStateRewrite diff storage := by
  unfold applyYulSstores
  induction diff generalizing storage with
  | nil => rfl
  | cons write writes ih =>
      have hhead := hvalid write (by simp)
      have htail : ValidSstoreDiff currentContract writes := by
        intro tail hmem
        exact hvalid tail (by simp [hmem])
      have hprog : compiledSstoreProgram currentContract (write :: writes) =
          .exprStmt (.call "sstore" [.lit (writeSlotLit write),
              .lit (write.value.toNat % Compiler.CompilationModel.uint256Modulus)]) ::
            compiledSstoreProgram currentContract writes := by
        simp [compiledSstoreProgram, hhead.1, hhead.2, compiledSstoreStmts_eq]
      rw [hprog, applyStateRewrite_cons]
      simp only [compiledYulSstores, hhead.1, hhead.2, beq_self_eq_true,
        Bool.and_self, if_true]
      exact ih (applyStorageWrite write storage) htail

/-- A storage key whose width makes big-endian decoding injective on the
    projection surface. -/
abbrev CanonicalStorageKey := { slot : ByteArray // slot.size = 32 }

/-- Storage observations are exposed only at canonical EVM-width keys. -/
abbrev CanonicalSolidityStorage := ContractId → CanonicalStorageKey → Word

/-- Restrict an abstract byte-array-addressed storage to canonical queries. -/
def canonicalStorageProjection (storage : SolidityStorage) : CanonicalSolidityStorage :=
  fun contract slot => storage contract slot.1

/-- Internal byte-array view used while applying source rewrites. The public
    projection below prevents non-canonical aliases from being queried. -/
private def irStorageView (currentContract : ContractId) (state : IRState) :
    SolidityStorage :=
  fun contract slot =>
    if contract = currentContract then
      state.storage (IRStorageSlot.ofNat (EvmYul.fromByteArrayBigEndian slot))
    else 0

/-- Project live IR storage onto canonical 32-byte keys only. -/
def irStorageProjection (currentContract : ContractId) (state : IRState) :
    CanonicalSolidityStorage :=
  canonicalStorageProjection (irStorageView currentContract state)

/-- Project the source runtime storage of one executing contract through the
    same `encodeStorageAt` view used by `runtimeStateMatchesIR`. -/
private def sourceStorageView (fields : List Field) (currentContract : ContractId)
    (runtime : SourceSemantics.RuntimeState) : SolidityStorage :=
  fun contract slot =>
    if contract = currentContract then
      IRStorageWord.ofNat (SourceSemantics.encodeStorageAt fields runtime.world
        (IRStorageSlot.ofNat (EvmYul.fromByteArrayBigEndian slot)).toNat)
    else 0

/-- Project source runtime storage onto canonical 32-byte keys only. -/
def sourceStorageProjection (fields : List Field) (currentContract : ContractId)
    (runtime : SourceSemantics.RuntimeState) : CanonicalSolidityStorage :=
  canonicalStorageProjection (sourceStorageView fields currentContract runtime)

/-- The storage conjunct of `runtimeStateMatchesIR`, expressed on the canonical
    contract/key storage surface consumed by state rewrites. -/
theorem runtimeStateMatchesIR_storageProjections_eq
    (fields : List Field) (currentContract : ContractId)
    (runtime : SourceSemantics.RuntimeState) (state : IRState)
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state) :
    irStorageProjection currentContract state =
      sourceStorageProjection fields currentContract runtime := by
  funext contract slot
  by_cases hcontract : contract = currentContract
  · simp only [irStorageProjection, sourceStorageProjection, canonicalStorageProjection,
      irStorageView, sourceStorageView, hcontract, if_true]
    rw [hruntime.1]
  · simp [irStorageProjection, sourceStorageProjection, canonicalStorageProjection,
      irStorageView, sourceStorageView, hcontract]

/-- A valid compiled/source rewrite preserves the live runtime/IR storage
    relation, projected onto the canonical contract/key surface. The premise is
    the actual `runtimeStateMatchesIR` invariant rather than an unrelated
    equality between two abstract storages. -/
theorem applyStateRewrite_preserves_canonicalStorageRel
    (fields : List Field) (currentContract : ContractId) (diff : StorageDiff)
    (runtime : SourceSemantics.RuntimeState) (state : IRState)
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state)
    (hvalid : ValidSstoreDiff currentContract diff) :
    canonicalStorageProjection (applyYulSstores currentContract diff
        (irStorageView currentContract state)) =
      canonicalStorageProjection (applyStateRewrite diff
        (sourceStorageView fields currentContract runtime)) := by
  have hviews : irStorageView currentContract state =
      sourceStorageView fields currentContract runtime := by
    funext contract slot
    by_cases hcontract : contract = currentContract
    · simp only [irStorageView, sourceStorageView, hcontract, if_true]
      rw [hruntime.1]
    · simp [irStorageView, sourceStorageView, hcontract]
  rw [applyYulSstores_eq_applyStateRewrite currentContract diff _ hvalid]
  rw [hviews]

/-! ### Canonical storage preservation for compiled statement lists -/

/-- Expose the real single-slot mapping-write compiler branch with literal key
    and value operands. -/
def compiledMappingSstoreStmts (baseSlot key : Nat) (value : Word) : List YulStmt :=
  match compileMappingSlotWrite [mappingSlotBridgeField baseSlot]
      "__mapping_slot_bridge" (.lit key) (.lit value.toNat) "mapping bridge" with
  | .ok stmts => stmts
  | .error _ => []

/-- Structurally interpret the mapping `sstore` emitted by
    `compileMappingSlotWrite`.  The helper body, outer statement shape, emitted
    base/key operands, and emitted value all remain observable. -/
def interpretCompiledMappingSstore
    (helper : YulStmt) (scratchBase currentContract : Nat)
    (stmt : YulStmt) (storage : SolidityStorage) : SolidityStorage :=
  match stmt with
  | .exprStmt (.call "sstore"
      [.call "mappingSlot" [.lit emittedBaseSlot, .lit emittedKey], .lit emittedValue]) =>
      match compiledMappingSlotPointer helper scratchBase emittedBaseSlot emittedKey with
      | some pointer => applyStorageWrite
          { contract := currentContract, slot := pointer,
            value := IRStorageWord.ofNat emittedValue } storage
      | none => storage
  | _ => storage

/-- The actual mapping-slot `sstore` emitted by `compileMappingSlotWrite` is the
    canonical source update. -/
theorem compiledMappingSstore_eq_canonicalSstore
    (scratchBase currentContract baseSlot key : Nat) (value : Word)
    (storage : SolidityStorage) :
    compiledMappingSstoreStmts baseSlot key value =
        [.exprStmt (.call "sstore"
          [.call "mappingSlot" [.lit baseSlot, .lit key], .lit value.toNat])] ∧
      interpretCompiledMappingSstore
          (Compiler.CodegenCommon.mappingSlotFuncAt scratchBase)
          scratchBase currentContract
          (.exprStmt (.call "sstore"
            [.call "mappingSlot" [.lit baseSlot, .lit key], .lit value.toNat])) storage =
        applyStorageWrite
          { contract := currentContract,
            slot := mappingSlotPointer baseSlot key,
            value := value } storage := by
  constructor
  · rfl
  · simp [interpretCompiledMappingSstore,
      compiledMappingSlotPointer_eq_mappingSlotPointer, IRStorageWord.ofNat_toNat]

/-- Exact statement-list preservation for the legacy compile shape.  The result
    relation contains `runtimeStateMatchesIR`, whose first conjunct equates the
    compiled storage with the executable source semantics' encoded storage.
    Unlike a freestanding storage-diff statement, this theorem is tied to the
    actual compilation and executions of `fn.body`. -/
theorem compilerStmtList_obeys_canonical_storage
    (runtimeContract : IRContract)
    (model : CompilationModel)
    (fn : FunctionSpec)
    (bodyStmts : List YulStmt)
    (helperFuel : Nat)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (state : IRState)
    (bindings : List (String × Nat))
    (extraFuel : Nat)
    (hextraFuel : sizeOf bodyStmts - bodyStmts.length ≤ extraFuel)
    (hfuelPos : 0 < helperFuel)
    (hnormalized : SourceSemantics.effectiveFields model = model.fields)
    (hnoEvents : model.events = [])
    (hnoErrors : model.errors = [])
    (hnoAdtTypes : model.adtTypes = [])
    (hhelperFree : StmtListHelperFreeStepInterface
      (SourceSemantics.effectiveFields model) (fn.params.map (·.name)) fn.body)
    (hcall : StmtListDirectInternalHelperCallStepInterface
      runtimeContract model (SourceSemantics.effectiveFields model)
      (fn.params.map (·.name)) fn.body)
    (hassign : StmtListDirectInternalHelperAssignStepInterface
      runtimeContract model (SourceSemantics.effectiveFields model)
      (fn.params.map (·.name)) fn.body)
    (hexpr : StmtListExprInternalHelperStepInterface
      runtimeContract model (SourceSemantics.effectiveFields model)
      (fn.params.map (·.name)) fn.body)
    (hstruct : StmtListStructuralInternalHelperStepInterface
      runtimeContract model (SourceSemantics.effectiveFields model)
      (fn.params.map (·.name)) fn.body)
    (hresidual : StmtListResidualHelperSurfaceStepInterface
      runtimeContract model (SourceSemantics.effectiveFields model)
      (fn.params.map (·.name)) fn.body)
    (hlegacy : StmtListHelperFreeCompiledLegacyCompatible
      (SourceSemantics.effectiveFields model) (fn.params.map (·.name)) fn.body)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) model.adtTypes fn.body = Except.ok bodyStmts)
    (hscope : FunctionBody.scopeNamesPresent (fn.params.map (·.name)) bindings)
    (hbounded : FunctionBody.bindingsBounded bindings)
    (hstateRuntime : FunctionBody.runtimeStateMatchesIR
      (SourceSemantics.effectiveFields model)
      { world := SourceSemantics.withTransactionContext initialWorld tx
        bindings := []
        selector := tx.functionSelector }
      state)
    (hstateBindings : FunctionBody.bindingsExactlyMatchIRVars bindings state)
    (hnoInternalFunctions : runtimeContract.internalFunctions = []) :
    SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal
      runtimeContract model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel := by
  exact
    supported_function_body_correct_from_exact_state_generic_finer_split_internal_helper_surface_steps_and_helper_ir
      runtimeContract model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel
      hextraFuel hfuelPos hnormalized hnoEvents hnoErrors hnoAdtTypes hhelperFree
      hcall hassign hexpr hstruct hresidual hlegacy hbodyCompile hscope hbounded
      hstateRuntime hstateBindings hnoInternalFunctions

/-- Spec-functions-aware exact statement-list preservation.  All four Phase 1C
    helper interfaces are assembled into the proof of the relation between the
    actual helper-aware source and compiled executions. -/
theorem compilerStmtListWithInternals_obeys_canonical_storage
    (runtimeContract : IRContract)
    (model : CompilationModel)
    (fn : FunctionSpec)
    (bodyStmts : List YulStmt)
    (helperFuel : Nat)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (state : IRState)
    (bindings : List (String × Nat))
    (extraFuel : Nat)
    (hextraFuel : sizeOf bodyStmts - bodyStmts.length ≤ extraFuel)
    (hfuelPos : 0 < helperFuel)
    (hnormalized : SourceSemantics.effectiveFields model = model.fields)
    (hnoEvents : model.events = [])
    (hnoErrors : model.errors = [])
    (hnoAdtTypes : model.adtTypes = [])
    (hhelperFree : StmtListHelperFreeStepInterfaceWithInternals
      runtimeContract model (SourceSemantics.effectiveFields model)
      (fn.params.map (·.name)) fn.body)
    (hcall : StmtListDirectInternalHelperCallStepInterfaceWithInternals
      runtimeContract model (SourceSemantics.effectiveFields model)
      (fn.params.map (·.name)) fn.body)
    (hassign : StmtListDirectInternalHelperAssignStepInterfaceWithInternals
      runtimeContract model (SourceSemantics.effectiveFields model)
      (fn.params.map (·.name)) fn.body)
    (hexpr : StmtListExprInternalHelperStepInterfaceWithInternals
      runtimeContract model (SourceSemantics.effectiveFields model)
      (fn.params.map (·.name)) fn.body)
    (hstruct : StmtListStructuralInternalHelperStepInterfaceWithInternals
      runtimeContract model (SourceSemantics.effectiveFields model)
      (fn.params.map (·.name)) fn.body)
    (hresidual : StmtListResidualHelperSurfaceStepInterfaceWithInternals
      runtimeContract model (SourceSemantics.effectiveFields model)
      (fn.params.map (·.name)) fn.body)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) model.adtTypes fn.body model.functions =
          Except.ok bodyStmts)
    (hscope : FunctionBody.scopeNamesPresent (fn.params.map (·.name)) bindings)
    (hbounded : FunctionBody.bindingsBounded bindings)
    (hstateRuntime : FunctionBody.runtimeStateMatchesIR
      (SourceSemantics.effectiveFields model)
      { world := SourceSemantics.withTransactionContext initialWorld tx
        bindings := []
        selector := tx.functionSelector }
      state)
    (hstateBindings : FunctionBody.bindingsExactlyMatchIRVars bindings state) :
    SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal
      runtimeContract model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel := by
  exact
    supported_function_body_correct_from_exact_state_generic_split_helper_steps_and_helper_ir_with_internals
      runtimeContract model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel
      hextraFuel hfuelPos hnormalized hnoEvents hnoErrors hnoAdtTypes hhelperFree
      hcall hassign hexpr hstruct hresidual hbodyCompile hscope hbounded
      hstateRuntime hstateBindings

end Compiler.Proofs.Storage

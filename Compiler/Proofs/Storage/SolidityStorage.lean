import Compiler.Proofs.MappingSlot
import Compiler.CompilationModel.ExpressionCompile
import Compiler.CompilationModel.StorageWrites
import Compiler.Proofs.IRGeneration.SourceSemantics
import Compiler.CodegenCommon
import Verity.Core.Model.Types

namespace Compiler.Proofs.Storage

open Compiler.Proofs
open Compiler.Proofs.IRGeneration

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

/-- Reading a mapping key is precisely reading its canonical Keccak pointer. -/
theorem mappingSlot_of_key (storage : SolidityStorage) (id : ContractId)
    (baseSlot key : Nat) :
    storage id (mappingSlotPointer baseSlot key) =
      storage id (KeccakEngine.keccak256 (abiEncodeMappingSlot baseSlot key)) := by
  rfl

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

/-- Struct member carrying the packed placement under test. -/
def packedReadBridgeMember (offset width : Nat) : Compiler.CompilationModel.StructMember :=
  { name := "value", wordOffset := 0, packed := some { offset := offset, width := width } }

/-- Storage field whose struct value carries that packed member. -/
def packedReadBridgeStructField (offset width : Nat) : Compiler.CompilationModel.Field :=
  { name := "__packed_read_bridge_struct",
    ty := .mappingStruct .uint256 [packedReadBridgeMember offset width],
    slot := some 0 }

/-- The source expression that drives the packed branch of `evalExpr`. -/
def packedReadBridgeSourceExpr : Compiler.CompilationModel.Expr :=
  .structMember "__packed_read_bridge_struct" (.literal 0) "value"

/-- Structural predicate on the source IR: `e` is a struct-member read whose
    resolved member is packed at exactly `offset`/`width`. This is the shape the
    executable evaluator dispatches on, so a change to the member placement or to
    the expression constructor is observable here. -/
def isSourcePackedRead (fields : List Compiler.CompilationModel.Field)
    (e : Compiler.CompilationModel.Expr) (offset width : Nat) : Bool :=
  match e with
  | .structMember field _ memberName =>
      match Compiler.CompilationModel.findStructMembers fields field with
      | some members =>
          match Compiler.CompilationModel.findStructMember members memberName with
          | some member =>
              match member.packed with
              | some packed => packed.offset == offset && packed.width == width
              | none => false
          | none => false
      | none => false
  | _ => false

/-- A runtime state holding `word` in every storage slot, so the bridge observes
    the packed extraction itself rather than slot arithmetic. -/
def packedReadBridgeState (word : Word) : SourceSemantics.RuntimeState :=
  { world := { Verity.defaultState with
                storage := fun _ => Verity.Core.Uint256.ofNat word.toNat },
    bindings := [] }

/-- The packed read performed by the executable source evaluator. -/
def sourceEvalPackedRead (word : Word) (offset width : Nat) : Option Nat :=
  if isSourcePackedRead [packedReadBridgeStructField offset width]
      packedReadBridgeSourceExpr offset width then
    SourceSemantics.evalExpr [packedReadBridgeStructField offset width]
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
    isSourcePackedRead [packedReadBridgeStructField offset width]
      packedReadBridgeSourceExpr offset width = true := by
  simp [isSourcePackedRead, packedReadBridgeSourceExpr, packedReadBridgeStructField,
    packedReadBridgeMember, Compiler.CompilationModel.findStructMembers,
    Compiler.CompilationModel.findStructMember]

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
  have heval : SourceSemantics.evalExpr [packedReadBridgeStructField offset width]
      (packedReadBridgeState word) packedReadBridgeSourceExpr =
      some (Verity.Core.Uint256.and
        (Verity.Core.Uint256.shr (Verity.Core.Uint256.ofNat offset)
          (Verity.Core.Uint256.ofNat (word.toNat % Verity.Core.Uint256.modulus)))
        (Verity.Core.Uint256.ofNat
          (Compiler.CompilationModel.packedMaskNat { offset := offset, width := width }))).val :=
    rfl
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

/-- The `sstore` sequence the compiler emits for a whole source storage diff. -/
def compiledSstoreProgram (diff : StorageDiff) : List Compiler.Yul.YulStmt :=
  diff.flatMap fun write => compiledSstoreStmts (writeSlotLit write) write.value.toNat

/-- Structurally interpret emitted Yul statements as storage updates. Each
    statement must be exactly the `sstore(slot, value)` call that
    `compileSetStorage` emits for the corresponding source write; any other
    statement shape, slot operand or value operand leaves storage untouched. -/
def compiledYulSstores :
    List Compiler.Yul.YulStmt → StorageDiff → SolidityStorage → SolidityStorage
  | .exprStmt (.call "sstore" [.lit slot, .lit value]) :: stmts, write :: writes, storage =>
      if slot == writeSlotLit write &&
          value == write.value.toNat % Compiler.CompilationModel.uint256Modulus then
        compiledYulSstores stmts writes (applyStorageWrite write storage)
      else storage
  | _, _, storage => storage

/-- Canonical interpretation of the equivalent sequence of Yul `sstore` calls:
    walk the statements the compiler emits for `diff` and apply each store. -/
def applyYulSstores (diff : StorageDiff) (storage : SolidityStorage) : SolidityStorage :=
  compiledYulSstores (compiledSstoreProgram diff) diff storage

theorem applyYulSstores_eq_compiledYulSstores (diff : StorageDiff) (storage : SolidityStorage) :
    applyYulSstores diff storage =
      compiledYulSstores (compiledSstoreProgram diff) diff storage := rfl

/-- The emitted `sstore` sequence, structurally interpreted, performs exactly the
    canonical source storage rewrite. -/
theorem applyYulSstores_eq_applyStateRewrite (diff : StorageDiff) (storage : SolidityStorage) :
    applyYulSstores diff storage = applyStateRewrite diff storage := by
  unfold applyYulSstores
  induction diff generalizing storage with
  | nil => rfl
  | cons write writes ih =>
      have hprog : compiledSstoreProgram (write :: writes) =
          .exprStmt (.call "sstore" [.lit (writeSlotLit write),
              .lit (write.value.toNat % Compiler.CompilationModel.uint256Modulus)]) ::
            compiledSstoreProgram writes := by
        simp [compiledSstoreProgram, compiledSstoreStmts_eq]
      rw [hprog, applyStateRewrite_cons]
      simp only [compiledYulSstores, beq_self_eq_true, Bool.and_self, if_true]
      exact ih (applyStorageWrite write storage)

end Compiler.Proofs.Storage

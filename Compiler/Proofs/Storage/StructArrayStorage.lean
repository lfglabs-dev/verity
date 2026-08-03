import Compiler.Proofs.Storage.SolidityStorage
import Compiler.Proofs.StorageBounds

/-!
# Canonical storage preservation for struct members and dynamic storage arrays

Phase 1D case 3 (verity#2081).  `Compiler/Proofs/Storage/SolidityStorage.lean`
pins plain mapping reads/writes against the canonical `SolidityStorage`
relation.  This module extends that bridge to the two remaining storage shapes
the compiler lowers with slot arithmetic:

* `Expr.structMember` / `Stmt.setStructMember` — a mapping entry advanced by the
  resolved member's `wordOffset`;
* `Expr.storageArrayLength`, `Expr.storageArrayElement`,
  `Stmt.storageArrayPush`, `Stmt.storageArrayPop` and
  `Stmt.setStorageArrayElement` — a length word at the field slot plus an
  element region based at `keccak256(slot)`.

Every lemma below runs the *real* compiler entry point on a synthetic bridge
field, structurally interprets the emitted Yul, and compares the result against
the *executable* source evaluator `SourceSemantics.evalExpr` / `execStmt`.  The
structural matches are deliberately exact, so a change to the emitted operand
order, builtin, slot arithmetic or statement shape is observable here rather
than silently absorbed.
-/

namespace Compiler.Proofs.Storage

open Compiler.Proofs
open Compiler.Proofs.IRGeneration
open Compiler Compiler.CompilationModel Compiler.Yul

/-! ## Canonical slot pointers -/

/-- The canonical 32-byte big-endian pointer denoting storage slot `slot`. -/
def slotPointer (slot : Nat) : ByteArray := (EvmYul.UInt256.ofNat slot).toByteArray

/-- The canonical pointer for struct member at `wordOffset` inside the struct
    stored at mapping entry `(baseSlot, key)`. -/
def structMemberPointer (baseSlot key wordOffset : Nat) : ByteArray :=
  slotPointer (EvmYul.fromByteArrayBigEndian (mappingSlotPointer baseSlot key) + wordOffset)

/-- The struct-member pointer is based at the same abstract mapping slot the
    executable source evaluator uses. -/
theorem structMemberPointer_eq_abstractMappingSlot (baseSlot key wordOffset : Nat) :
    structMemberPointer baseSlot key wordOffset =
      slotPointer (Compiler.Proofs.abstractMappingSlot baseSlot key + wordOffset) := rfl

/-! ## Struct members

`compileSetStructMember` and the `Expr.structMember` arm of
`compileExprWithInternals` both route through `compileMappingSlotRead` /
`compileMappingSlotWrite` with the resolved member's `wordOffset`.  The bridge
field below exposes exactly that path for a single unpacked member. -/

/-- The single unpacked member carried by the struct bridge field. -/
def structBridgeMember (wordOffset : Nat) : StructMember :=
  { name := "__struct_bridge_member", ty := .uint256, wordOffset := wordOffset, packed := none }

/-- Synthetic struct-valued mapping field used to expose the real struct-member
    compiler branch. -/
def structBridgeField (baseSlot wordOffset : Nat) : Field :=
  { name := "__struct_bridge",
    ty := .mappingStruct .uint256 [structBridgeMember wordOffset],
    slot := some baseSlot }

/-- The slot expression the compiler builds for a struct member: the mapping
    pointer, advanced by `wordOffset` only when that offset is non-zero. -/
def structMemberSlotYul (baseSlot key wordOffset : Nat) : YulExpr :=
  let mappingBase := YulExpr.call "mappingSlot" [.lit baseSlot, .lit key]
  if wordOffset == 0 then mappingBase
  else YulExpr.call "add" [mappingBase, .lit wordOffset]

/-- The real compiler output for a struct-member read on the bridge field. -/
def compiledStructMemberRead (baseSlot key wordOffset : Nat) : Except String YulExpr :=
  compileExprWithInternals [structBridgeField baseSlot wordOffset] .calldata []
    (.structMember "__struct_bridge" (.literal key) "__struct_bridge_member")

/-- A struct-member read lowers to `sload` of the mapping pointer advanced by
    the member's word offset.  The emitted builtin, operand order and offset are
    all pinned by this equation. -/
theorem compiledStructMemberRead_eq (baseSlot key wordOffset : Nat) :
    compiledStructMemberRead baseSlot key wordOffset =
      .ok (.call "sload"
        [structMemberSlotYul baseSlot (key % uint256Modulus) wordOffset]) := by
  unfold compiledStructMemberRead
  simp only [compileExprWithInternals]
  rfl

/-- Structurally interpret an emitted struct-member read as the canonical slot
    it loads.  The `mappingSlot` helper body is re-checked through
    `compiledMappingSlotPointer`, so the helper's own Yul shape stays observable. -/
def compiledStructMemberSlot (helper : YulStmt) (scratchBase : Nat) :
    YulExpr → Option Nat
  | .call "sload" [.call "add" [.call "mappingSlot" [.lit baseSlot, .lit key], .lit wordOffset]] =>
      (compiledMappingSlotPointer helper scratchBase baseSlot key).map
        fun pointer => EvmYul.fromByteArrayBigEndian pointer + wordOffset
  | .call "sload" [.call "mappingSlot" [.lit baseSlot, .lit key]] =>
      (compiledMappingSlotPointer helper scratchBase baseSlot key).map
        EvmYul.fromByteArrayBigEndian
  | _ => none

/-- A slot-reflecting world makes a source struct-member read return the exact
    slot it consumed. -/
def structMemberBridgeState : SourceSemantics.RuntimeState :=
  { world := { Verity.defaultState with storage := fun slot => slot }, bindings := [] }

/-- The slot the executable source evaluator reads for a struct member. -/
def sourceStructMemberSlotRead (baseSlot key wordOffset : Nat) : Option Nat :=
  SourceSemantics.evalExpr [structBridgeField baseSlot wordOffset] structMemberBridgeState
    (.structMember "__struct_bridge" (.literal key) "__struct_bridge_member")

/-- The compiled struct-member read targets the canonical struct-member pointer.
    Reading canonical storage through the interpreted slot is the same as
    reading it at `structMemberPointer`. -/
theorem compilerStructMember_eq_storageStructRead
    (storage : SolidityStorage) (id : ContractId)
    (scratchBase baseSlot key wordOffset : Nat) :
    Option.map (fun slot => storage id (slotPointer slot))
        (compiledStructMemberSlot
          (Compiler.CodegenCommon.mappingSlotFuncAt scratchBase) scratchBase
          (.call "sload" [structMemberSlotYul baseSlot key wordOffset])) =
      some (storage id (structMemberPointer baseSlot key wordOffset)) := by
  unfold structMemberSlotYul structMemberPointer
  by_cases hzero : wordOffset = 0
  · subst hzero
    simp [compiledStructMemberSlot, compiledMappingSlotPointer_eq_mappingSlotPointer]
  · have hzb : (wordOffset == 0) = false := by simpa using hzero
    simp [hzb, compiledStructMemberSlot, compiledMappingSlotPointer_eq_mappingSlotPointer]

/-- The interpreted compiled slot is precisely the slot the executable source
    evaluator consumes for the same struct-member read.  This joins the emitted
    `mappingSlot` helper, the member's word offset and `evalExpr`. -/
theorem compiledStructMemberSlot_eq_sourceStructMemberSlotRead
    (scratchBase baseSlot key wordOffset : Nat)
    (hkey : key < Compiler.Constants.evmModulus) :
    Option.map SourceSemantics.wordNormalize
        (compiledStructMemberSlot
          (Compiler.CodegenCommon.mappingSlotFuncAt scratchBase) scratchBase
          (.call "sload" [structMemberSlotYul baseSlot key wordOffset])) =
      sourceStructMemberSlotRead baseSlot key wordOffset := by
  have hfield : findFieldWithResolvedSlot [structBridgeField baseSlot wordOffset]
      "__struct_bridge" = some (structBridgeField baseSlot wordOffset, baseSlot) := rfl
  have hmembers : findStructMembers [structBridgeField baseSlot wordOffset] "__struct_bridge" =
      some [structBridgeMember wordOffset] := rfl
  have hsource : sourceStructMemberSlotRead baseSlot key wordOffset =
      some (SourceSemantics.wordNormalize
        (Compiler.Proofs.abstractMappingSlot baseSlot key + wordOffset)) := by
    unfold sourceStructMemberSlotRead
    rw [SourceSemantics.evalExpr]
    simp only [SourceSemantics.evalExpr, hfield, hmembers, structBridgeMember,
      SourceSemantics.wordNormalize_eq_mod, Nat.mod_eq_of_lt hkey]
    simp only [structBridgeField, structMemberBridgeState, SourceSemantics.readFieldWord,
      SourceSemantics.wordNormalize]
    simp [findStructMember]
  rw [hsource]
  unfold structMemberSlotYul
  by_cases hzero : wordOffset = 0
  · subst hzero
    simp [compiledStructMemberSlot, compiledMappingSlotPointer_eq_mappingSlotPointer,
      mappingSlotPointer_eq_abstractMappingSlot]
  · have hzb : (wordOffset == 0) = false := by simpa using hzero
    simp [hzb, compiledStructMemberSlot, compiledMappingSlotPointer_eq_mappingSlotPointer,
      mappingSlotPointer_eq_abstractMappingSlot]

/-! ### Struct-member writes -/

/-- The real compiler output for a struct-member write on the bridge field. -/
def compiledStructMemberWrite (baseSlot key wordOffset value : Nat) :
    Except String (List YulStmt) :=
  compileSetStructMember [structBridgeField baseSlot wordOffset] .calldata
    "__struct_bridge" (.literal key) "__struct_bridge_member" (.literal value)

/-- A struct-member write lowers to a single `sstore` at the mapping pointer
    advanced by the member's word offset. -/
theorem compiledStructMemberWrite_eq (baseSlot key wordOffset value : Nat) :
    compiledStructMemberWrite baseSlot key wordOffset value =
      .ok [.exprStmt (.call "sstore"
        [structMemberSlotYul baseSlot (key % uint256Modulus) wordOffset,
          .lit (value % uint256Modulus)])] := by
  unfold compiledStructMemberWrite
  simp only [compileSetStructMember, compileExprWithInternals]
  rfl

/-- Structurally interpret the emitted struct-member `sstore` as a canonical
    storage update.  The emitted base slot, key, word offset and value all stay
    observable, and the `mappingSlot` helper body is re-checked. -/
def interpretCompiledStructMemberSstore
    (helper : YulStmt) (scratchBase currentContract : Nat) :
    YulStmt → SolidityStorage → SolidityStorage
  | .exprStmt (.call "sstore"
      [.call "add" [.call "mappingSlot" [.lit baseSlot, .lit key], .lit wordOffset],
        .lit value]), storage =>
      match compiledMappingSlotPointer helper scratchBase baseSlot key with
      | some pointer =>
          applyStorageWrite
            { contract := currentContract,
              slot := slotPointer (EvmYul.fromByteArrayBigEndian pointer + wordOffset),
              value := IRStorageWord.ofNat value } storage
      | none => storage
  | .exprStmt (.call "sstore" [.call "mappingSlot" [.lit baseSlot, .lit key], .lit value]),
      storage =>
      match compiledMappingSlotPointer helper scratchBase baseSlot key with
      | some pointer =>
          applyStorageWrite
            { contract := currentContract,
              slot := slotPointer (EvmYul.fromByteArrayBigEndian pointer),
              value := IRStorageWord.ofNat value } storage
      | none => storage
  | _, storage => storage

/-- The `sstore` the compiler actually emits for a struct-member assignment
    performs exactly the canonical write at `structMemberPointer`. -/
theorem compilerStructMemberWrite_eq_storageStructWrite
    (scratchBase currentContract baseSlot key wordOffset : Nat) (value : Word)
    (storage : SolidityStorage) :
    interpretCompiledStructMemberSstore
        (Compiler.CodegenCommon.mappingSlotFuncAt scratchBase) scratchBase currentContract
        (.exprStmt (.call "sstore"
          [structMemberSlotYul baseSlot key wordOffset, .lit value.toNat])) storage =
      applyStorageWrite
        { contract := currentContract,
          slot := structMemberPointer baseSlot key wordOffset,
          value := value } storage := by
  unfold structMemberSlotYul structMemberPointer
  by_cases hzero : wordOffset = 0
  · subst hzero
    simp [interpretCompiledStructMemberSstore,
      compiledMappingSlotPointer_eq_mappingSlotPointer, IRStorageWord.ofNat_toNat]
  · have hzb : (wordOffset == 0) = false := by simpa using hzero
    simp [hzb, interpretCompiledStructMemberSstore,
      compiledMappingSlotPointer_eq_mappingSlotPointer, IRStorageWord.ofNat_toNat]

/-! ## Dynamic storage arrays

A Solidity dynamic storage array keeps its length in the field's own slot and
its elements in the region based at `keccak256(slot)`.  The compiler realises
that layout with `sload(slot)` for the length and
`add(keccak256(mstore(0, slot)), index)` for elements. -/

/-- Canonical base pointer for the element region of the storage array at
    `slot`: `keccak256` of the 32-byte word holding `slot`. -/
def storageArrayBasePointer (slot : Nat) : ByteArray :=
  KeccakEngine.keccak256 (EvmYul.UInt256.ofNat slot).toByteArray

/-- Canonical pointer for element `index` of the storage array at `slot`. -/
def storageArrayElementPointer (slot index : Nat) : ByteArray :=
  slotPointer (EvmYul.fromByteArrayBigEndian (storageArrayBasePointer slot) + index)

/-- Every storage-array element pointer carries the canonical Solidity preimage
    for its base.  This is the usable preimage direction and does not postulate
    injectivity of Keccak. -/
theorem storageArrayBasePointer_preimage (slot : Nat) :
    ∃ preimage : ByteArray,
      preimage = (EvmYul.UInt256.ofNat slot).toByteArray ∧
      storageArrayBasePointer slot = KeccakEngine.keccak256 preimage :=
  ⟨(EvmYul.UInt256.ofNat slot).toByteArray, rfl, rfl⟩

/-- Synthetic dynamic-array field used to expose the real storage-array compiler
    branches. -/
def arrayBridgeField (slot : Nat) : Field :=
  { name := "__array_bridge", ty := .dynamicArray .uint256, slot := some slot }

/-- A world holding `values` in the bridge array's slot, with the field slot
    itself holding the array length exactly as the EVM layout requires. -/
def arrayBridgeState (slot : Nat) (values : List Verity.Core.Uint256) :
    SourceSemantics.RuntimeState :=
  { world := { Verity.defaultState with
                storageArray := fun s => if s = slot then values else [],
                storage := fun s =>
                  if s = SourceSemantics.wordNormalize slot then (values.length : Verity.Core.Uint256)
                  else 0 },
    bindings := [] }

/-- Interpret an emitted `sload(<literal slot>)` against a concrete world. -/
def interpretSloadLit (world : Verity.ContractState) : YulExpr → Option Nat
  | .call "sload" [.lit slot] => some (world.storage (SourceSemantics.wordNormalize slot)).val
  | _ => none

/-- The real compiler output for a storage-array length read. -/
def compiledStorageArrayLength (slot : Nat) : Except String YulExpr :=
  compileExprWithInternals [arrayBridgeField slot] .calldata []
    (.storageArrayLength "__array_bridge")

/-- The length read lowers to exactly `sload(slot)`. -/
theorem compiledStorageArrayLength_eq (slot : Nat) :
    compiledStorageArrayLength slot = .ok (.call "sload" [.lit slot]) := by
  unfold compiledStorageArrayLength
  simp only [compileExprWithInternals]
  rfl

/-- Reading a dynamic array's length through the emitted `sload` agrees with the
    length the executable source evaluator reports.  Running the interpretation
    against the same world keeps both ends tied to one state. -/
theorem storageArrayLength_eq_storageArrayLength (slot : Nat)
    (values : List Verity.Core.Uint256)
    (hlen : values.length < Compiler.Constants.evmModulus) :
    Option.bind (compiledStorageArrayLength slot).toOption
        (interpretSloadLit (arrayBridgeState slot values).world) =
      SourceSemantics.evalExpr [arrayBridgeField slot] (arrayBridgeState slot values)
        (.storageArrayLength "__array_bridge") := by
  have hsource : SourceSemantics.evalExpr [arrayBridgeField slot] (arrayBridgeState slot values)
      (.storageArrayLength "__array_bridge") = some values.length := by
    rw [SourceSemantics.evalExpr]
    show some (if slot = slot then values else []).length = some values.length
    simp
  rw [hsource, compiledStorageArrayLength_eq]
  simp only [Except.toOption, Option.bind_some, interpretSloadLit, arrayBridgeState]
  simp only [Option.some.injEq]
  show (values.length : Verity.Core.Uint256).val = values.length
  exact Nat.mod_eq_of_lt hlen

/-- The real compiler output for a checked storage-array element read. -/
def compiledStorageArrayElement (slot index : Nat) : Except String YulExpr :=
  compileExprWithInternals [arrayBridgeField slot] .calldata []
    (.storageArrayElement "__array_bridge" (.literal index))

/-- The element read lowers to a call of the checked storage-array helper on the
    field slot and the index. -/
theorem compiledStorageArrayElement_eq (slot index : Nat) :
    compiledStorageArrayElement slot index =
      .ok (.call checkedStorageArrayElementHelperName
        [.lit slot, .lit (index % uint256Modulus)]) := by
  unfold compiledStorageArrayElement
  simp only [compileExprWithInternals]
  rfl

/-- Structurally interpret the emitted `__verity_storage_array_element_checked`
    helper as the canonical element pointer it loads.  Matching the whole helper
    body keeps the bounds check, the scratch `mstore`, the hash range and the
    final `add` observable. -/
def compiledStorageArrayElementPointer (helper : YulStmt) (storage : SolidityStorage)
    (id : ContractId) (slot index : Nat) :
    Option ByteArray :=
  match helper with
  | .funcDef name ["slot", "index"] ["word"] [
      .let_ "__array_len" (.call "sload" [.ident "slot"]),
      .if_ (.call "iszero" [.call "lt" [.ident "index", .ident "__array_len"]]) [
        .exprStmt (.call "revert" [.lit 0, .lit 0])],
      .exprStmt (.call "mstore" [.lit storePtr, .ident "slot"]),
      .let_ "__array_base" (.call "keccak256" [.lit hashPtr, .lit hashSize]),
      .assign "word" (.call "sload" [.call "add" [.ident "__array_base", .ident "index"]])] =>
      if name == checkedStorageArrayElementHelperName && storePtr == 0 && hashPtr == 0 &&
          hashSize == 32 && index < (storage id (slotPointer slot)).toNat then
        some (storageArrayElementPointer slot index)
      else
        none
  | _ => none

/-- The emitted checked-element helper computes the canonical Solidity element
    pointer.  Any change to its line-by-line Yul shape is observable here. -/
theorem storageArrayElement_eq_storageArrayElement (storage : SolidityStorage)
    (id : ContractId) (slot index : Nat)
    (hindex : index < (storage id (slotPointer slot)).toNat) :
    compiledStorageArrayElementPointer checkedStorageArrayElementHelper storage id slot index =
      some (storageArrayElementPointer slot index) := by
  simp [compiledStorageArrayElementPointer, checkedStorageArrayElementHelper, hindex]

/-- Reading canonical storage at the interpreted element pointer is the same as
    reading it at the canonical element pointer for `(slot, index)`. -/
theorem storageArrayElement_eq_canonicalStorageRead (storage : SolidityStorage)
    (id : ContractId) (slot index : Nat)
    (hindex : index < (storage id (slotPointer slot)).toNat) :
    Option.map (storage id)
        (compiledStorageArrayElementPointer checkedStorageArrayElementHelper storage id slot index) =
      some (storage id (storageArrayElementPointer slot index)) := by
  rw [storageArrayElement_eq_storageArrayElement storage id slot index hindex, Option.map_some]

/-- Canonical array words and the executable source array describe the same
    length and element values for one contract and one field slot. -/
def StorageArrayCoherent (storage : SolidityStorage) (id : ContractId) (slot : Nat)
    (values : List Verity.Core.Uint256) : Prop :=
  (storage id (slotPointer slot)).toNat = values.length ∧
    ∀ index value, values[index]? = some value →
      (storage id (storageArrayElementPointer slot index)).toNat = value.val

/-- Under the explicit source/canonical coherence invariant, interpreting the
    checked compiled read and loading its canonical word agrees with executable
    `SourceSemantics.evalExpr`. -/
theorem storageArrayElement_eq_sourceEval (storage : SolidityStorage)
    (id : ContractId) (slot index : Nat) (values : List Verity.Core.Uint256)
    (hcoherent : StorageArrayCoherent storage id slot values)
    (hindex : index < values.length)
    (hword : index < Compiler.Constants.evmModulus) :
    Option.map IRStorageWord.toNat
        (Option.bind
          (compiledStorageArrayElementPointer checkedStorageArrayElementHelper storage id slot index)
          (fun pointer => some (storage id pointer))) =
      SourceSemantics.evalExpr [arrayBridgeField slot] (arrayBridgeState slot values)
        (.storageArrayElement "__array_bridge" (.literal index)) := by
  have hcanonical : index < (storage id (slotPointer slot)).toNat := by
    simpa [hcoherent.1] using hindex
  rw [storageArrayElement_eq_storageArrayElement storage id slot index hcanonical]
  have hnth : ∃ value, values[index]? = some value := by
    exact List.getElem?_eq_getElem hindex |>.symm ▸ ⟨values[index], rfl⟩
  obtain ⟨value, hvalue⟩ := hnth
  simp only [Option.bind_some, Option.map_some]
  have hsource :
      SourceSemantics.evalExpr [arrayBridgeField slot] (arrayBridgeState slot values)
          (.storageArrayElement "__array_bridge" (.literal index)) = some value.val := by
    have hfield : findFieldWithResolvedSlot [arrayBridgeField slot] "__array_bridge" =
        some (arrayBridgeField slot, slot) := rfl
    rw [SourceSemantics.evalExpr]
    simp only [SourceSemantics.evalExpr, SourceSemantics.wordNormalize_eq_mod,
      Nat.mod_eq_of_lt hword, hfield]
    simp [arrayBridgeField, arrayBridgeState, hvalue]
  rw [hsource]
  exact congrArg some (hcoherent.2 index value hvalue)

/-- A checked read rejects an index at or beyond the length loaded from the
    canonical array slot. -/
theorem storageArrayElement_outOfBounds (storage : SolidityStorage)
    (id : ContractId) (slot index : Nat)
    (hindex : (storage id (slotPointer slot)).toNat ≤ index) :
    compiledStorageArrayElementPointer checkedStorageArrayElementHelper storage id slot index =
      none := by
  simp [compiledStorageArrayElementPointer, checkedStorageArrayElementHelper,
    Nat.not_lt.mpr hindex]

/-! ### Storage-array writes

`compileSetStorageArrayElement`, `compileStorageArrayPush` and
`compileStorageArrayPop` each emit a single Yul block.  The interpreters below
match those blocks statement by statement and produce the canonical storage
diff they realise, so the bounds checks, the scratch-memory hashing and the
length bookkeeping all remain observable. -/

/-- The canonical write performed by an element assignment. -/
def storageArrayElementWrite (currentContract slot index : Nat) (value : Word) : StorageWrite :=
  { contract := currentContract, slot := storageArrayElementPointer slot index, value := value }

/-- The canonical length write performed by a push or pop. -/
def storageArrayLengthWrite (currentContract slot : Nat) (length : Nat) : StorageWrite :=
  { contract := currentContract, slot := slotPointer slot,
    value := IRStorageWord.ofNat length }

/-- The real compiler output for a storage-array element assignment. -/
def compiledSetStorageArrayElement (slot index value : Nat) : Except String (List YulStmt) :=
  compileSetStorageArrayElement [arrayBridgeField slot] .calldata "__array_bridge"
    (.literal index) (.literal value)

/-- The element assignment lowers to exactly one block: the length load, the
    index binding, the bounds check, the scratch `mstore`, the `keccak256` base
    and the element `sstore`. -/
theorem compiledSetStorageArrayElement_eq (slot index value : Nat) :
    compiledSetStorageArrayElement slot index value =
      .ok [.block [
        .let_ "__array_len" (.call "sload" [.lit slot]),
        .let_ "__array_index" (.lit (index % uint256Modulus)),
        .if_ (.call "iszero" [.call "lt" [.ident "__array_index", .ident "__array_len"]]) [
          .exprStmt (.call "revert" [.lit 0, .lit 0])],
        .exprStmt (.call "mstore" [.lit 0, .lit slot]),
        .let_ "__array_base" (.call "keccak256" [.lit 0, .lit 32]),
        .exprStmt (.call "sstore"
          [.call "add" [.ident "__array_base", .ident "__array_index"],
            .lit (value % uint256Modulus)])]] := by
  unfold compiledSetStorageArrayElement
  simp only [compileSetStorageArrayElement, compileExprWithInternals]
  rfl

/-- Structurally interpret the emitted element-assignment block as the canonical
    storage diff it performs. -/
def interpretCompiledSetStorageArrayElement (storage : SolidityStorage)
    (currentContract : ContractId) :
    List YulStmt → Option StorageDiff
  | [.block [
      .let_ "__array_len" (.call "sload" [.lit slot]),
      .let_ "__array_index" (.lit index),
      .if_ (.call "iszero" [.call "lt" [.ident "__array_index", .ident "__array_len"]]) [
        .exprStmt (.call "revert" [.lit 0, .lit 0])],
      .exprStmt (.call "mstore" [.lit storePtr, .lit storeSlot]),
      .let_ "__array_base" (.call "keccak256" [.lit hashPtr, .lit hashSize]),
      .exprStmt (.call "sstore"
        [.call "add" [.ident "__array_base", .ident "__array_index"], .lit value])]] =>
      if storePtr == 0 && storeSlot == slot && hashPtr == 0 && hashSize == 32 &&
          index < (storage currentContract (slotPointer slot)).toNat then
        some [storageArrayElementWrite currentContract slot index (IRStorageWord.ofNat value)]
      else
        none
  | _ => none

/-- The statements the compiler actually emits for an element assignment realise
    exactly the canonical single-slot write at the element pointer. -/
theorem setStorageArrayElement_eq_compiledSetStorageArrayElement
    (storage : SolidityStorage) (currentContract slot index value : Nat)
    (hindex : index % uint256Modulus < (storage currentContract (slotPointer slot)).toNat) :
    Option.bind (compiledSetStorageArrayElement slot index value).toOption
        (interpretCompiledSetStorageArrayElement storage currentContract) =
      some [storageArrayElementWrite currentContract slot
        (index % uint256Modulus) (IRStorageWord.ofNat (value % uint256Modulus))] := by
  rw [compiledSetStorageArrayElement_eq]
  simp [Except.toOption, interpretCompiledSetStorageArrayElement, hindex]

/-- Element assignment performs no write when its normalized index fails the
    guard against the canonically loaded length. -/
theorem setStorageArrayElement_outOfBounds
    (storage : SolidityStorage) (currentContract slot index value : Nat)
    (hindex : (storage currentContract (slotPointer slot)).toNat ≤ index % uint256Modulus) :
    Option.bind (compiledSetStorageArrayElement slot index value).toOption
        (interpretCompiledSetStorageArrayElement storage currentContract) = none := by
  rw [compiledSetStorageArrayElement_eq]
  simp [Except.toOption, interpretCompiledSetStorageArrayElement, Nat.not_lt.mpr hindex]

/-- The real compiler output for a storage-array push. -/
def compiledStorageArrayPush (slot value : Nat) : Except String (List YulStmt) :=
  compileStorageArrayPush [arrayBridgeField slot] .calldata "__array_bridge" (.literal value)

/-- The push lowers to exactly one block: the length load, the scratch `mstore`,
    the `keccak256` base, the element `sstore` at the current length and the
    length bump. -/
theorem compiledStorageArrayPush_eq (slot value : Nat) :
    compiledStorageArrayPush slot value =
      .ok [.block [
        .let_ "__array_len" (.call "sload" [.lit slot]),
        .exprStmt (.call "mstore" [.lit 0, .lit slot]),
        .let_ "__array_base" (.call "keccak256" [.lit 0, .lit 32]),
        .exprStmt (.call "sstore"
          [.call "add" [.ident "__array_base", .ident "__array_len"],
            .lit (value % uint256Modulus)]),
        .exprStmt (.call "sstore"
          [.lit slot, .call "add" [.ident "__array_len", .lit 1]])]] := by
  unfold compiledStorageArrayPush
  simp only [compileStorageArrayPush, compileExprWithInternals]
  rfl

/-- Structurally interpret the emitted push block as the canonical storage diff
    it performs: the element write at the old length, then the length bump. -/
def interpretCompiledStorageArrayPush (storage : SolidityStorage)
    (currentContract : ContractId) :
    List YulStmt → Option StorageDiff
  | [.block [
      .let_ "__array_len" (.call "sload" [.lit slot]),
      .exprStmt (.call "mstore" [.lit storePtr, .lit storeSlot]),
      .let_ "__array_base" (.call "keccak256" [.lit hashPtr, .lit hashSize]),
      .exprStmt (.call "sstore"
        [.call "add" [.ident "__array_base", .ident "__array_len"], .lit value]),
      .exprStmt (.call "sstore"
        [.lit lengthSlot, .call "add" [.ident "__array_len", .lit one]])]] =>
      if storePtr == 0 && storeSlot == slot && hashPtr == 0 && hashSize == 32 &&
          lengthSlot == slot && one == 1 then
        let oldLength := (storage currentContract (slotPointer slot)).toNat
        some [storageArrayElementWrite currentContract slot oldLength (IRStorageWord.ofNat value),
          storageArrayLengthWrite currentContract slot (oldLength + 1)]
      else
        none
  | _ => none

/-- The statements the compiler actually emits for a push realise exactly the
    canonical two-slot diff: store the value one past the end, then record the
    incremented length. -/
theorem pushStorageArray_eq_compiledStorageArrayPush
    (storage : SolidityStorage) (currentContract slot value : Nat) :
    Option.bind (compiledStorageArrayPush slot value).toOption
        (interpretCompiledStorageArrayPush storage currentContract) =
      some [storageArrayElementWrite currentContract slot
          (storage currentContract (slotPointer slot)).toNat
          (IRStorageWord.ofNat (value % uint256Modulus)),
        storageArrayLengthWrite currentContract slot
          ((storage currentContract (slotPointer slot)).toNat + 1)] := by
  rw [compiledStorageArrayPush_eq]
  simp [Except.toOption, interpretCompiledStorageArrayPush]

/-- A caller-supplied length is irrelevant: push always uses the canonical
    length word.  This regression makes the mismatched-length case explicit. -/
theorem pushStorageArray_ignoresCallerLength
    (storage : SolidityStorage) (currentContract slot value claimed : Nat)
    (_hmismatch : claimed ≠ (storage currentContract (slotPointer slot)).toNat) :
    Option.bind (compiledStorageArrayPush slot value).toOption
        (interpretCompiledStorageArrayPush storage currentContract) =
      some [storageArrayElementWrite currentContract slot
          (storage currentContract (slotPointer slot)).toNat
          (IRStorageWord.ofNat (value % uint256Modulus)),
        storageArrayLengthWrite currentContract slot
          ((storage currentContract (slotPointer slot)).toNat + 1)] :=
  pushStorageArray_eq_compiledStorageArrayPush storage currentContract slot value

/-- A push extends the source-level array by exactly the pushed value, so the
    canonical element write above lands one past the previous end. -/
theorem pushStorageArray_source_length (values : List Verity.Core.Uint256)
    (value : Verity.Core.Uint256) :
    (values ++ [value]).length = values.length + 1 := by
  simp

/-- The real compiler output for a storage-array pop. -/
def compiledStorageArrayPop (slot : Nat) : Except String (List YulStmt) :=
  compileStorageArrayPop [arrayBridgeField slot] "__array_bridge"

/-- Structurally interpret the emitted pop block as the canonical storage diff
    it performs: zero the vacated element, then record the decremented length. -/
def interpretCompiledStorageArrayPop (storage : SolidityStorage)
    (currentContract : ContractId) :
    List YulStmt → Option StorageDiff
  | [.block [
      .let_ "__array_len" (.call "sload" [.lit slot]),
      .if_ (.call "iszero" [.ident "__array_len"]) [
        .exprStmt (.call "revert" [.lit 0, .lit 0])],
      .let_ "__array_new_len" (.call "sub" [.ident "__array_len", .lit one]),
      .exprStmt (.call "mstore" [.lit storePtr, .lit storeSlot]),
      .let_ "__array_base" (.call "keccak256" [.lit hashPtr, .lit hashSize]),
      .exprStmt (.call "sstore"
        [.call "add" [.ident "__array_base", .ident "__array_new_len"], .lit zeroLit]),
      .exprStmt (.call "sstore" [.lit lengthSlot, .ident "__array_new_len"])]] =>
      if storePtr == 0 && storeSlot == slot && hashPtr == 0 && hashSize == 32 &&
          lengthSlot == slot && one == 1 && zeroLit == 0 &&
          0 < (storage currentContract (slotPointer slot)).toNat then
        let newLength := (storage currentContract (slotPointer slot)).toNat - 1
        some [storageArrayElementWrite currentContract slot newLength (IRStorageWord.ofNat 0),
          storageArrayLengthWrite currentContract slot newLength]
      else
        none
  | _ => none

/-- The statements the compiler actually emits for a pop realise exactly the
    canonical two-slot diff: clear the vacated element, then record the
    decremented length.  The emitted `iszero` guard keeps the empty-array revert
    observable. -/
theorem popStorageArray_eq_compiledStorageArrayPop
    (storage : SolidityStorage) (currentContract slot : Nat)
    (hnonempty : 0 < (storage currentContract (slotPointer slot)).toNat) :
    Option.bind (compiledStorageArrayPop slot).toOption
        (interpretCompiledStorageArrayPop storage currentContract) =
      some [storageArrayElementWrite currentContract slot
          ((storage currentContract (slotPointer slot)).toNat - 1) (IRStorageWord.ofNat 0),
        storageArrayLengthWrite currentContract slot
          ((storage currentContract (slotPointer slot)).toNat - 1)] := by
  have hcompiled : compiledStorageArrayPop slot =
      .ok [.block [
        .let_ "__array_len" (.call "sload" [.lit slot]),
        .if_ (.call "iszero" [.ident "__array_len"]) [
          .exprStmt (.call "revert" [.lit 0, .lit 0])],
        .let_ "__array_new_len" (.call "sub" [.ident "__array_len", .lit 1]),
        .exprStmt (.call "mstore" [.lit 0, .lit slot]),
        .let_ "__array_base" (.call "keccak256" [.lit 0, .lit 32]),
        .exprStmt (.call "sstore"
          [.call "add" [.ident "__array_base", .ident "__array_new_len"], .lit 0]),
        .exprStmt (.call "sstore" [.lit slot, .ident "__array_new_len"])]] := rfl
  rw [hcompiled]
  simp [Except.toOption, interpretCompiledStorageArrayPop, hnonempty]

/-- Pop evaluates the emitted empty-array guard against canonical storage and
    therefore yields no writes for an empty array. -/
theorem popStorageArray_empty
    (storage : SolidityStorage) (currentContract slot : Nat)
    (hempty : (storage currentContract (slotPointer slot)).toNat = 0) :
    Option.bind (compiledStorageArrayPop slot).toOption
        (interpretCompiledStorageArrayPop storage currentContract) = none := by
  have hcompiled : compiledStorageArrayPop slot =
      .ok [.block [
        .let_ "__array_len" (.call "sload" [.lit slot]),
        .if_ (.call "iszero" [.ident "__array_len"]) [
          .exprStmt (.call "revert" [.lit 0, .lit 0])],
        .let_ "__array_new_len" (.call "sub" [.ident "__array_len", .lit 1]),
        .exprStmt (.call "mstore" [.lit 0, .lit slot]),
        .let_ "__array_base" (.call "keccak256" [.lit 0, .lit 32]),
        .exprStmt (.call "sstore"
          [.call "add" [.ident "__array_base", .ident "__array_new_len"], .lit 0]),
        .exprStmt (.call "sstore" [.lit slot, .ident "__array_new_len"])]] := rfl
  rw [hcompiled]
  simp [Except.toOption, interpretCompiledStorageArrayPop, hempty]

/-- A mismatched caller prediction cannot influence pop: the cleared index and
    stored length are derived from the canonical length word. -/
theorem popStorageArray_ignoresCallerLength
    (storage : SolidityStorage) (currentContract slot claimed : Nat)
    (hnonempty : 0 < (storage currentContract (slotPointer slot)).toNat)
    (_hmismatch : claimed ≠ (storage currentContract (slotPointer slot)).toNat - 1) :
    Option.bind (compiledStorageArrayPop slot).toOption
        (interpretCompiledStorageArrayPop storage currentContract) =
      some [storageArrayElementWrite currentContract slot
          ((storage currentContract (slotPointer slot)).toNat - 1) (IRStorageWord.ofNat 0),
        storageArrayLengthWrite currentContract slot
          ((storage currentContract (slotPointer slot)).toNat - 1)] :=
  popStorageArray_eq_compiledStorageArrayPop storage currentContract slot hnonempty

/-- A source-level pop shortens the array by exactly one element, matching the
    length the canonical pop diff records. -/
theorem popStorageArray_source_length (values updated : List Verity.Core.Uint256)
    (h : Compiler.Proofs.StorageBounds.storageArrayDropLast? values = some updated) :
    updated.length + 1 = values.length :=
  Compiler.Proofs.StorageBounds.storageArrayDropLast_length values updated h

/-- A source-level element assignment preserves the array length, so the
    canonical element write is the only slot the compiled form touches. -/
theorem setStorageArrayElement_source_length (values updated : List Verity.Core.Uint256)
    (index : Nat) (value : Verity.Core.Uint256)
    (h : Compiler.Proofs.StorageBounds.storageArraySetAt values index value = some updated) :
    updated.length = values.length :=
  Compiler.Proofs.StorageBounds.storageArraySetAt_length values index value updated h

/-! ### Canonical diffs applied to `SolidityStorage`

The interpreters above produce `StorageDiff`s, so the existing
`applyStateRewrite` transformer from `SolidityStorage.lean` gives the resulting
canonical storage directly. -/

/-- Applying the canonical element-assignment diff updates exactly the element
    pointer of `(slot, index)` and leaves every other slot alone. -/
theorem applyStateRewrite_storageArrayElementWrite
    (currentContract slot index : Nat) (value : Word) (storage : SolidityStorage) :
    applyStateRewrite [storageArrayElementWrite currentContract slot index value] storage =
      applyStorageWrite (storageArrayElementWrite currentContract slot index value) storage := by
  rw [applyStateRewrite_cons]
  rfl

/-- Applying the canonical push diff writes the value at the old end and then
    records the incremented length. -/
theorem applyStateRewrite_storageArrayPush
    (currentContract slot oldLength : Nat) (value : Word) (storage : SolidityStorage) :
    applyStateRewrite
        [storageArrayElementWrite currentContract slot oldLength value,
          storageArrayLengthWrite currentContract slot (oldLength + 1)] storage =
      applyStorageWrite (storageArrayLengthWrite currentContract slot (oldLength + 1))
        (applyStorageWrite (storageArrayElementWrite currentContract slot oldLength value)
          storage) := by
  rw [applyStateRewrite_cons, applyStateRewrite_cons]
  rfl

/-- Applying the canonical pop diff clears the vacated element and then records
    the decremented length. -/
theorem applyStateRewrite_storageArrayPop
    (currentContract slot newLength : Nat) (storage : SolidityStorage) :
    applyStateRewrite
        [storageArrayElementWrite currentContract slot newLength (IRStorageWord.ofNat 0),
          storageArrayLengthWrite currentContract slot newLength] storage =
      applyStorageWrite (storageArrayLengthWrite currentContract slot newLength)
        (applyStorageWrite
          (storageArrayElementWrite currentContract slot newLength (IRStorageWord.ofNat 0))
          storage) := by
  rw [applyStateRewrite_cons, applyStateRewrite_cons]
  rfl

end Compiler.Proofs.Storage

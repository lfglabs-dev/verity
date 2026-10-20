import Lean
import Verity.Macro.Syntax
import Verity.Macro.Types

namespace Verity.Macro

open Lean
open Lean.Elab.Command

set_option hygiene false

def storageTypeFromSyntax
    (newtypes : Array NewtypeDecl)
    (structDecls : Array StructDecl := #[])
    (adtDecls : Array AdtDecl := #[])
    (ty : Term) : CommandElabM StorageType := do
  let keyTypeFromSyntax (stx : Term) : CommandElabM MappingKeyType := do
    match stx with
    | `(term| Address) => pure .address
    | `(term| Uint256) => pure .uint256
    | `(term| Bytes32) => pure .bytes32
    | _ => throwErrorAt stx "unsupported mapping key type; expected Address, Uint256, or Bytes32"

  let structMemberFromSyntax (stx : TSyntax `verityStructMember) : CommandElabM StructMemberDecl := do
    match stx with
    | `(verityStructMember| $name:ident @word $wordOffset:num) =>
        pure {
          name := toString name.getId
          wordOffset := ← natFromSyntax wordOffset
        }
    | `(verityStructMember| $name:ident : $memberTy:term @word $wordOffset:num) =>
        pure {
          name := toString name.getId
          ty := ← valueTypeFromSyntax newtypes structDecls adtDecls memberTy
          wordOffset := ← natFromSyntax wordOffset
        }
    | `(verityStructMember| $name:ident @word $wordOffset:num packed($offset:num,$width:num)) =>
        pure {
          name := toString name.getId
          wordOffset := ← natFromSyntax wordOffset
          packed := some (← natFromSyntax offset, ← natFromSyntax width)
        }
    | `(verityStructMember| $name:ident : $memberTy:term @word $wordOffset:num packed($offset:num,$width:num)) =>
        pure {
          name := toString name.getId
          ty := ← valueTypeFromSyntax newtypes structDecls adtDecls memberTy
          wordOffset := ← natFromSyntax wordOffset
          packed := some (← natFromSyntax offset, ← natFromSyntax width)
        }
    | _ => throwErrorAt stx "invalid struct member declaration"

  let rec storageStructMemberElementWords (memberName : String) : ValueType → CommandElabM Nat
    | .uint256 | .int256 | .uint8 | .uint16 | .uintN _ | .intN _ | .bytesN _ | .address | .bool | .bytes32 => pure 1
    | .newtype _ baseType => storageStructMemberElementWords memberName baseType
    | .enum _ _ => pure 1
    | .fixedArray elemTy size => do
        let elemWords ← storageStructMemberElementWords memberName elemTy
        pure (elemWords * size)
    | other =>
        throwErrorAt ty
          s!"mapping struct member '{memberName}' has unsupported storage type {repr other}; expected a word-like type or FixedArray of word-like types"

  let rec expandStructMemberDecl (memberPrefix : String) (baseOffset : Nat) (memberTy : ValueType)
      (packed : Option (Nat × Nat)) : CommandElabM (List StructMemberDecl) := do
    match memberTy with
    | .newtype _ baseType =>
        expandStructMemberDecl memberPrefix baseOffset baseType packed
    | .enum _ _ =>
        pure [{ name := memberPrefix, ty := memberTy, wordOffset := baseOffset, packed := packed }]
    | .fixedArray elemTy size => do
        if packed.isSome then
          throwErrorAt ty s!"mapping struct fixed-array member '{memberPrefix}' cannot be packed"
        let elemWords ← storageStructMemberElementWords memberPrefix elemTy
        let nested ← (List.range size).mapM fun idx =>
          expandStructMemberDecl s!"{memberPrefix}[{idx}]" (baseOffset + idx * elemWords) elemTy none
        pure nested.flatten
    | .uint256 | .int256 | .uint8 | .uint16 | .uintN _ | .intN _ | .bytesN _ | .address | .bool | .bytes32 =>
        pure [{ name := memberPrefix, ty := memberTy, wordOffset := baseOffset, packed := packed }]
    | other =>
        throwErrorAt ty
          s!"mapping struct member '{memberPrefix}' has unsupported storage type {repr other}; expected a word-like type or FixedArray of word-like types"

  let expandStructMembers (members : Array StructMemberDecl) : CommandElabM (List StructMemberDecl) := do
    let expanded ← members.mapM fun member =>
      expandStructMemberDecl member.name member.wordOffset member.ty member.packed
    pure expanded.toList.flatten

  let storageArrayElemTypeFromValueType (elemTy : ValueType) : CommandElabM Compiler.CompilationModel.StorageArrayElemType :=
    match elemTy with
    | .uint256 => pure .uint256
    | .address => pure .address
    | .bool => pure .bool
    | .bytes32 => pure .bytes32
    | _ =>
        throwErrorAt ty
          s!"storage dynamic arrays currently support only one-word elements (Uint256, Address, Bool, Bytes32) on the macro path, got {reprStr (ValueType.array elemTy)}"

  let (arrowArgs, arrowResult) ← collectArrowChainTypes ty
  if !arrowArgs.isEmpty then
    match (← valueTypeFromSyntax newtypes structDecls adtDecls arrowResult) with
    | .uint256 =>
        let keyTypes ← arrowArgs.mapM keyTypeFromSyntax
        match keyTypes with
        | [.address] => pure .mappingAddressToUint256
        | [.uint256] => pure .mappingUintToUint256
        | [.address, .address] => pure .mapping2AddressToAddressToUint256
        | _ => pure (.mappingChain keyTypes)
    | .enum name memberCount =>
        let keyTypes ← arrowArgs.mapM keyTypeFromSyntax
        match keyTypes with
        | [.address] => pure (.mappingAddressToEnum name memberCount)
        | [.uint256] => pure (.mappingUintToEnum name memberCount)
        | [.address, .address] => pure (.mapping2AddressToAddressToEnum name memberCount)
        | _ => pure (.mappingChainEnum keyTypes name memberCount)
    | _ =>
        throwErrorAt ty "unsupported mapping value type; expected Uint256 or an enum"
  else
    match ty with
  | `(term| MappingStruct($keyTy:term,[ $[$members:verityStructMember],* ])) =>
      pure <| .mappingStruct
        (← keyTypeFromSyntax keyTy)
        (← expandStructMembers (← members.mapM structMemberFromSyntax))
  | `(term| MappingStruct2($outerKey:term,$innerKey:term,[ $[$members:verityStructMember],* ])) =>
      pure <| .mappingStruct2
        (← keyTypeFromSyntax outerKey)
        (← keyTypeFromSyntax innerKey)
        (← expandStructMembers (← members.mapM structMemberFromSyntax))
  | _ => do
      let vt ← valueTypeFromSyntax newtypes structDecls adtDecls ty
      match vt with
      | .array elemTy => pure (.dynamicArray (← storageArrayElemTypeFromValueType elemTy))
      | .fixedArray _ 0 =>
          throwErrorAt ty "storage fixed arrays must contain at least one element"
      | .tuple _ => throwErrorAt ty "storage fields cannot be Tuple; use mapping encodings"
      | .struct _ _ =>
          throwErrorAt ty
            "top-level named struct storage fields are not supported yet (#1758); flatten the struct into explicit scalar storage fields with fixed slots, or use MappingStruct/MappingStruct2 for struct-valued mappings"
      | _ => pure (.scalar vt)

def modelMappingKeyTypeTerm : MappingKeyType → CommandElabM Term
  | .address => `(Compiler.CompilationModel.MappingKeyType.address)
  | .uint256 => `(Compiler.CompilationModel.MappingKeyType.uint256)
  | .bytes32 => `(Compiler.CompilationModel.MappingKeyType.bytes32)

def storageTypeMappingKeyTypes? : StorageType → Option (List MappingKeyType)
  | .mappingAddressToUint256 => some [.address]
  | .mappingAddressToEnum _ _ => some [.address]
  | .mapping2AddressToAddressToUint256 => some [.address, .address]
  | .mapping2AddressToAddressToEnum _ _ => some [.address, .address]
  | .mappingUintToUint256 => some [.uint256]
  | .mappingUintToEnum _ _ => some [.uint256]
  | .mappingChain keyTypes => some keyTypes
  | .mappingChainEnum keyTypes _ _ => some keyTypes
  | _ => none

def storageTypeMappingDepth? (ty : StorageType) : Option Nat :=
  storageTypeMappingKeyTypes? ty |>.map List.length

def storageTypeMappingValueType? : StorageType → Option ValueType
  | .mappingAddressToEnum name memberCount | .mapping2AddressToAddressToEnum name memberCount
    | .mappingUintToEnum name memberCount | .mappingChainEnum _ name memberCount =>
      some (.enum name memberCount)
  | _ => none

def storageKeyTypeContractTerm : MappingKeyType → CommandElabM Term
  | .address => `(Address)
  | .uint256 => `(Uint256)
  | .bytes32 => `(Bytes32)

def modelStructMemberTerm (member : StructMemberDecl) : CommandElabM Term := do
  let packedTerm ←
    match member.packed with
    | none => `(none)
    | some (offset, width) =>
        `(some { offset := $(natTerm offset), width := $(natTerm width) })
  let memberTypeTerm ←
    match member.ty with
    | .uint256 | .int256 | .uint8 | .uintN _ | .intN _ | .bytesN _ | .enum _ _ =>
        `(Compiler.CompilationModel.StructMemberType.uint256)
    | .uint16 =>
        `(Compiler.CompilationModel.StructMemberType.uint16)
    | .address =>
        `(Compiler.CompilationModel.StructMemberType.address)
    | .bool =>
        `(Compiler.CompilationModel.StructMemberType.bool)
    | .bytes32 =>
        `(Compiler.CompilationModel.StructMemberType.bytes32)
    | _ =>
        throwError "mapping struct member '{member.name}' has unsupported type {repr member.ty}; expected Uint256, Uint16, Address, Bool, or Bytes32"
  `(Compiler.CompilationModel.StructMember.mk
      $(strTerm member.name)
      $memberTypeTerm
      $(natTerm member.wordOffset)
      $packedTerm)

def modelFieldTypeTerm (ty : StorageType) : CommandElabM Term :=
  match ty with
  | .scalar .uint256 => `(Compiler.CompilationModel.FieldType.uint256)
  | .scalar .int256 => `(Compiler.CompilationModel.FieldType.int256)
  | .scalar .uint8 => `(Compiler.CompilationModel.FieldType.uint256)
  | .scalar .uint16 => `(Compiler.CompilationModel.FieldType.uint256)
  | .scalar (.uintN _) => `(Compiler.CompilationModel.FieldType.uint256)
  | .scalar (.intN _) => throwError "storage fields cannot use narrow integers yet; packed storage is tracked separately in #2060"
  | .scalar (.bytesN _) => throwError "storage fields cannot use fixed bytes yet; packed storage is tracked separately in #2060"
  | .scalar .address => `(Compiler.CompilationModel.FieldType.address)
  | .scalar .bytes32 => `(Compiler.CompilationModel.FieldType.uint256)
  | .scalar .bool => `(Compiler.CompilationModel.FieldType.uint256)
  | .scalar .string => throwError "storage fields cannot be String; use Uint256 encoding"
  | .scalar .bytes => throwError "storage fields cannot be Bytes; use Uint256 encoding"
  | .scalar (.array _) => throwError "storage fields cannot be Array; use mapping encodings"
  | .scalar (.fixedArray (.uintN 128) size) => do
      if size == 0 then
        throwError "storage fixed arrays must contain at least one element"
      `(Compiler.CompilationModel.FieldType.fixedArrayUint128 $(natTerm size))
  | .scalar (.fixedArray _ _) => throwError "storage fixed arrays currently support only Uint128 elements"
  | .scalar (.tuple _) => throwError "storage fields cannot be Tuple; use mapping encodings"
  | .scalar (.struct _ _) =>
      throwError
        "top-level named struct storage fields are not supported yet (#1758); flatten the struct into explicit scalar storage fields with fixed slots, or use MappingStruct/MappingStruct2 for struct-valued mappings"
  | .scalar .unit => throwError "storage fields cannot be Unit"
  | .scalar (.newtype _ baseType) => modelFieldTypeTerm (.scalar baseType)  -- Erased to base type
  | .scalar (.enum _ _) => `(Compiler.CompilationModel.FieldType.uint256)
  | .scalar (.adt name maxFields) =>
      `(Compiler.CompilationModel.FieldType.adt $(Lean.quote name) $(Lean.quote maxFields))
  | .dynamicArray .uint256 => `(Compiler.CompilationModel.FieldType.dynamicArray Compiler.CompilationModel.StorageArrayElemType.uint256)
  | .dynamicArray .address => `(Compiler.CompilationModel.FieldType.dynamicArray Compiler.CompilationModel.StorageArrayElemType.address)
  | .dynamicArray .bool => `(Compiler.CompilationModel.FieldType.dynamicArray Compiler.CompilationModel.StorageArrayElemType.bool)
  | .dynamicArray .uint8 => `(Compiler.CompilationModel.FieldType.dynamicArray Compiler.CompilationModel.StorageArrayElemType.uint8)
  | .dynamicArray .bytes32 => `(Compiler.CompilationModel.FieldType.dynamicArray Compiler.CompilationModel.StorageArrayElemType.bytes32)
  | .mappingAddressToUint256 =>
      `(Compiler.CompilationModel.FieldType.mappingTyped
          (Compiler.CompilationModel.MappingType.simple Compiler.CompilationModel.MappingKeyType.address))
  | .mappingAddressToEnum _ _ =>
      `(Compiler.CompilationModel.FieldType.mappingTyped
          (Compiler.CompilationModel.MappingType.simple Compiler.CompilationModel.MappingKeyType.address))
  | .mapping2AddressToAddressToUint256 =>
      `(Compiler.CompilationModel.FieldType.mappingTyped
          (Compiler.CompilationModel.MappingType.nested
            Compiler.CompilationModel.MappingKeyType.address
            Compiler.CompilationModel.MappingKeyType.address))
  | .mapping2AddressToAddressToEnum _ _ =>
      `(Compiler.CompilationModel.FieldType.mappingTyped
          (Compiler.CompilationModel.MappingType.nested
            Compiler.CompilationModel.MappingKeyType.address
            Compiler.CompilationModel.MappingKeyType.address))
  | .mappingUintToUint256 =>
      `(Compiler.CompilationModel.FieldType.mappingTyped
          (Compiler.CompilationModel.MappingType.simple Compiler.CompilationModel.MappingKeyType.uint256))
  | .mappingUintToEnum _ _ =>
      `(Compiler.CompilationModel.FieldType.mappingTyped
          (Compiler.CompilationModel.MappingType.simple Compiler.CompilationModel.MappingKeyType.uint256))
  | .mappingChain keyTypes => do
      let keyTypeTerms := (← keyTypes.mapM modelMappingKeyTypeTerm).toArray
      `(Compiler.CompilationModel.FieldType.mappingTyped
          (Compiler.CompilationModel.MappingType.chain [ $[$keyTypeTerms],* ]))
  | .mappingChainEnum keyTypes _ _ => do
      let keyTypeTerms := (← keyTypes.mapM modelMappingKeyTypeTerm).toArray
      `(Compiler.CompilationModel.FieldType.mappingTyped
          (Compiler.CompilationModel.MappingType.chain [ $[$keyTypeTerms],* ]))
  | .mappingStruct keyType members => do
      let keyTypeTerm ← modelMappingKeyTypeTerm keyType
      let memberTerms := (← members.mapM modelStructMemberTerm).toArray
      `(Compiler.CompilationModel.FieldType.mappingStruct $keyTypeTerm [ $[$memberTerms],* ])
  | .mappingStruct2 outerKey innerKey members => do
      let outerKeyTerm ← modelMappingKeyTypeTerm outerKey
      let innerKeyTerm ← modelMappingKeyTypeTerm innerKey
      let memberTerms := (← members.mapM modelStructMemberTerm).toArray
      `(Compiler.CompilationModel.FieldType.mappingStruct2 $outerKeyTerm $innerKeyTerm [ $[$memberTerms],* ])

/-- Map a macro `ValueType` to its `CompilationModel.ScalarStorageType` descriptor (`#2417`). -/
partial def scalarStorageModelType? : ValueType → Option Compiler.CompilationModel.ScalarStorageType
  | .bool => some .bool
  | .uint8 => some .uint8
  | .uint16 => some .uint16
  | .uintN 32 => some .uint32
  | .uintN 64 => some .uint64
  | .uintN 96 => some .uint96
  | .uintN 128 => some .uint128
  | .uintN bits => some (.uintN bits)
  | .uint256 => some .uint256
  | .int256 => some .int256
  | .address => some .address
  | .bytes32 => some .bytes32
  | .enum _ _ => some .uint8
  | .newtype _ baseType => scalarStorageModelType? baseType
  | _ => none

/-- Storage bit width of a scalar `ValueType` in Solidity's 256-bit word layout (`#2417`). -/
def scalarStorageBitWidth? (ty : ValueType) : Option Nat :=
  (scalarStorageModelType? ty).map Compiler.CompilationModel.ScalarStorageType.bitWidth

/-- Construct a `PackedSlotField` descriptor from a `StorageFieldDecl` when the field
    carries `packedBits` or is a narrow sub-word scalar (`#2417`, `#1993`). -/
def packedSlotFieldFromDecl? (decl : StorageFieldDecl) :
    Option Compiler.CompilationModel.PackedSlotField :=
  match decl.ty, decl.packedBits with
  | .scalar vt, some (offset, width) =>
      let scalarTy := (scalarStorageModelType? vt).getD (.uintN width)
      some
        (Compiler.CompilationModel.PackedSlotField.mk
          decl.name
          decl.slotNum
          { offset := offset, width := width }
          scalarTy
          decl.isTransient)
  | .scalar vt, none =>
      match scalarStorageModelType? vt with
      | some scalarTy =>
          if scalarTy.isSubWord then
            some
              (Compiler.CompilationModel.PackedSlotField.mk
                decl.name
                decl.slotNum
                { offset := 0, width := scalarTy.bitWidth }
                scalarTy
                decl.isTransient)
          else
            none
      | none => none
  | _, _ => none

/-- Compute the per-element storage word stride of a `FixedArray` element type (`#2417`). -/
partial def fixedArrayElementWordStride? : ValueType → Option Nat
  | .uint256 | .int256 | .uint8 | .uint16 | .uintN _ | .intN _ | .bytesN _
  | .address | .bool | .bytes32 | .enum _ _ =>
      some 1
  | .newtype _ baseType =>
      fixedArrayElementWordStride? baseType
  | .adt _ maxFields =>
      some (1 + maxFields)
  | .fixedArray elemTy size =>
      (fixedArrayElementWordStride? elemTy).map (· * size)
  | .struct _ fields =>
      fields.foldlM
        (fun acc (_, fty) => do
          let w ← fixedArrayElementWordStride? fty
          pure (acc + w))
        0
  | _ => none

/-- Construct a `FixedArrayLayoutDescriptor` for a `ValueType.fixedArray` storage declaration
    with multi-slot stride and optional trailing `__gap` slots (`#2417`, `#2420`). -/
def fixedArrayLayoutDescriptor?
    (baseSlot : Nat) (ty : ValueType) (gapSlots : Nat := 0) :
    Option Compiler.CompilationModel.FixedArrayLayoutDescriptor :=
  match ty with
  | .fixedArray elemTy size => do
      let stride ← fixedArrayElementWordStride? elemTy
      pure
        { baseSlot := baseSlot
          size := size
          elemStride := stride
          gapSlots := gapSlots }
  | _ => none

/-- Shift a `StorageFieldDecl` by a relative `parentSlotOffset` and optional ERC-7201
    `namespaceRoot?` modulo `evmModulus` (`#2420`). -/
def applyStorageFieldRelativeOffset
    (parentSlotOffset : Nat)
    (namespaceRoot? : Option Nat := none)
    (decl : StorageFieldDecl) : StorageFieldDecl :=
  let rel : Compiler.CompilationModel.RelativeSlotOffset :=
    { namespaceRoot? := namespaceRoot?
      parentSlotOffset := parentSlotOffset
      localSlot := decl.slotNum }
  { decl with slotNum := rel.resolvedSlot }

/-! ## Compile-Time Storage Slot & ERC-7201 Collision Detection -/

/-- A contiguous bit-range `[offset, offset + width)` within a 256-bit storage `slot`.
    A full-word storage slot is represented with `offset := 0` and `width := 256`. -/
structure PackedRange where
  «slot» : Nat
  offset : Nat := 0
  width : Nat := 256
  deriving DecidableEq, Repr, BEq

/-- Construct a `PackedRange` inside an ERC-7201 namespace rooted at `namespaceRoot`. -/
def erc7201SlotRange
    (namespaceRoot localSlot : Nat)
    (offset : Nat := 0)
    (width : Nat := 256) : PackedRange :=
  { «slot» := (namespaceRoot + localSlot) % Compiler.Constants.evmModulus
    offset := offset
    width := width }

/-- Check whether two `PackedRange` descriptors overlap in the same 256-bit storage slot. -/
def packedRangesOverlap (a b : PackedRange) : Bool :=
  decide (a.slot = b.slot ∧ a.offset < b.offset + b.width ∧ b.offset < a.offset + a.width)

/-- Find the first entry in `rest` whose `PackedRange` overlaps `rangeA`. -/
def findOverlappingEntry (nameA : String) (rangeA : PackedRange) :
    List (String × PackedRange) → Option (String × String × Nat)
  | [] => none
  | (nameB, rangeB) :: tail =>
      if packedRangesOverlap rangeA rangeB then
        some (nameA, nameB, rangeA.slot)
      else
        findOverlappingEntry nameA rangeA tail

theorem findOverlappingEntry_eq_none_iff (nameA : String) (rangeA : PackedRange)
    (rest : List (String × PackedRange)) :
    findOverlappingEntry nameA rangeA rest = none ↔
      ∀ entry ∈ rest, packedRangesOverlap rangeA entry.2 = false := by
  induction rest with
  | nil => simp [findOverlappingEntry]
  | cons hd tl ih =>
    rcases hd with ⟨nameB, rangeB⟩
    simp only [findOverlappingEntry, List.mem_cons, forall_eq_or_imp]
    split <;> rename_i h
    · simp [h]
    · simp [h, ih]

/-- Return the first colliding pair `(fieldA, fieldB, slot)` in `ranges`, or `none`
    when all storage ranges are pairwise disjoint. -/
def firstStorageLayoutConflict : List (String × PackedRange) → Option (String × String × Nat)
  | [] => none
  | (nameA, rangeA) :: rest =>
      match findOverlappingEntry nameA rangeA rest with
      | some conflict => some conflict
      | none => firstStorageLayoutConflict rest

/-- Soundness and completeness of `firstStorageLayoutConflict`: it returns `none`
    if and only if all entries in `ranges` are pairwise non-overlapping. -/
theorem firstStorageLayoutConflict_eq_none_iff (ranges : List (String × PackedRange)) :
    firstStorageLayoutConflict ranges = none ↔
      ranges.Pairwise (fun a b => packedRangesOverlap a.2 b.2 = false) := by
  induction ranges with
  | nil => simp [firstStorageLayoutConflict]
  | cons hd tl ih =>
    rcases hd with ⟨nameA, rangeA⟩
    simp only [firstStorageLayoutConflict]
    rw [List.pairwise_cons, ← findOverlappingEntry_eq_none_iff nameA rangeA tl, ← ih]
    cases findOverlappingEntry nameA rangeA tl <;> simp

/-- Extract the occupied `PackedRange` of a `StorageFieldDecl`. -/
def packedRangeOfStorageField (decl : StorageFieldDecl) : PackedRange :=
  match decl.packedBits with
  | some (offset, width) => { «slot» := decl.slotNum, offset := offset, width := width }
  | none => { «slot» := decl.slotNum, offset := 0, width := 256 }

/-- Collect `(name, PackedRange)` descriptors for persistent or transient fields. -/
def storageFieldPackedRanges
    (fields : Array StorageFieldDecl)
    (isTransient : Bool := false) : List (String × PackedRange) :=
  fields.toList.filterMap fun decl =>
    if decl.isTransient == isTransient then
      some (decl.name, packedRangeOfStorageField decl)
    else
      none

/-- Elaboration guard for `verity_contract` rejecting overlapping storage slot/bitfield layouts. -/
def ensureCollisionFreeStorageLayout
    (ranges : List (String × PackedRange))
    (ref? : Option Syntax := none) : CommandElabM Unit := do
  if let some (fieldA, fieldB, slotNum) := firstStorageLayoutConflict ranges then
    let msg := s!"storage layout collision at slot {slotNum} between '{fieldA}' and '{fieldB}'"
    match ref? with
    | some ref => throwErrorAt ref msg
    | none => throwError msg

/-- Validate both persistent and transient storage field declarations for slot/bitfield collisions. -/
def ensureCollisionFreeStorageFields (fields : Array StorageFieldDecl) : CommandElabM Unit := do
  ensureCollisionFreeStorageLayout (storageFieldPackedRanges fields false)
  ensureCollisionFreeStorageLayout (storageFieldPackedRanges fields true)

end Verity.Macro

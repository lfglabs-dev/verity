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
    | .uint256 | .int256 | .uint16 | .address | .bool | .bytes32 => pure 1
    | .newtype _ baseType => storageStructMemberElementWords memberName baseType
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
    | .fixedArray elemTy size => do
        if packed.isSome then
          throwErrorAt ty s!"mapping struct fixed-array member '{memberPrefix}' cannot be packed"
        let elemWords ← storageStructMemberElementWords memberPrefix elemTy
        let nested ← (List.range size).mapM fun idx =>
          expandStructMemberDecl s!"{memberPrefix}[{idx}]" (baseOffset + idx * elemWords) elemTy none
        pure nested.flatten
    | .uint256 | .int256 | .uint16 | .address | .bool | .bytes32 =>
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
    match arrowResult with
    | `(term| Uint256) =>
        let keyTypes ← arrowArgs.mapM keyTypeFromSyntax
        match keyTypes with
        | [.address] => pure .mappingAddressToUint256
        | [.uint256] => pure .mappingUintToUint256
        | [.address, .address] => pure .mapping2AddressToAddressToUint256
        | _ => pure (.mappingChain keyTypes)
    | _ =>
        throwErrorAt ty "unsupported mapping value type; expected Uint256"
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
  | .mapping2AddressToAddressToUint256 => some [.address, .address]
  | .mappingUintToUint256 => some [.uint256]
  | .mappingChain keyTypes => some keyTypes
  | _ => none

def storageTypeMappingDepth? (ty : StorageType) : Option Nat :=
  storageTypeMappingKeyTypes? ty |>.map List.length

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
    | .uint256 | .int256 | .uint8 =>
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
  | .scalar .int256 => `(Compiler.CompilationModel.FieldType.uint256)
  | .scalar .uint8 => throwError "storage fields cannot be Uint8; use Uint256 encoding"
  | .scalar .uint16 => `(Compiler.CompilationModel.FieldType.uint256)
  | .scalar (.uintN _) => `(Compiler.CompilationModel.FieldType.uint256)
  | .scalar (.intN _) => throwError "storage fields cannot use narrow integers yet; packed storage is tracked separately in #2060"
  | .scalar (.bytesN _) => throwError "storage fields cannot use fixed bytes yet; packed storage is tracked separately in #2060"
  | .scalar .address => `(Compiler.CompilationModel.FieldType.address)
  | .scalar .bytes32 => throwError "storage fields cannot be Bytes32; use Uint256 encoding"
  | .scalar .bool => throwError "storage fields cannot be Bool; use Uint256 (0/1) encoding"
  | .scalar .string => throwError "storage fields cannot be String; use Uint256 encoding"
  | .scalar .bytes => throwError "storage fields cannot be Bytes; use Uint256 encoding"
  | .scalar (.array _) => throwError "storage fields cannot be Array; use mapping encodings"
  | .scalar (.fixedArray (.uintN 128) size) =>
      `(Compiler.CompilationModel.FieldType.fixedArrayUint128 $(natTerm size))
  | .scalar (.fixedArray _ _) => throwError "storage fixed arrays currently support only Uint128 elements"
  | .scalar (.tuple _) => throwError "storage fields cannot be Tuple; use mapping encodings"
  | .scalar (.struct _ _) =>
      throwError
        "top-level named struct storage fields are not supported yet (#1758); flatten the struct into explicit scalar storage fields with fixed slots, or use MappingStruct/MappingStruct2 for struct-valued mappings"
  | .scalar .unit => throwError "storage fields cannot be Unit"
  | .scalar (.newtype _ baseType) => modelFieldTypeTerm (.scalar baseType)  -- Erased to base type
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
  | .mapping2AddressToAddressToUint256 =>
      `(Compiler.CompilationModel.FieldType.mappingTyped
          (Compiler.CompilationModel.MappingType.nested
            Compiler.CompilationModel.MappingKeyType.address
            Compiler.CompilationModel.MappingKeyType.address))
  | .mappingUintToUint256 =>
      `(Compiler.CompilationModel.FieldType.mappingTyped
          (Compiler.CompilationModel.MappingType.simple Compiler.CompilationModel.MappingKeyType.uint256))
  | .mappingChain keyTypes => do
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

end Verity.Macro

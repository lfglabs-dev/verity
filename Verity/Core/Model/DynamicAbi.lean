import Compiler.CompilationModel.AbiTypeLayout
import Verity.Core.Uint256
import Verity.Core.Model.Constants

namespace Compiler.CompilationModel

namespace DynamicAbi

def wordNormalize (n : Nat) : Nat :=
  ((n : Verity.Core.Uint256) : Nat)

def uint8Modulus : Nat := 2 ^ 8

def selectorWord (selector : Nat) : Nat :=
  (selector % Compiler.Constants.selectorModulus) * (2 ^ Compiler.Constants.selectorShift)

def calldataloadWord (selector : Nat) (calldata : List Nat) (offset : Nat) : Nat :=
  if offset = 0 then
    selectorWord selector
  else if offset < 4 then
    0
  else
    let p := offset - 4
    let q := p / 32
    let r := p % 32
    if r = 0 then
      calldata.getD q 0 % Compiler.Constants.evmModulus
    else
      let hi := calldata.getD q 0 % Compiler.Constants.evmModulus
      let lo := calldata.getD (q + 1) 0 % Compiler.Constants.evmModulus
      ((hi % (2 ^ (8 * (32 - r)))) * (2 ^ (8 * r)) + lo / (2 ^ (8 * (32 - r)))) %
        Compiler.Constants.evmModulus

def decodeSupportedParamWord (ty : ParamType) (word : Nat) : Option Nat :=
  let word := wordNormalize word
  match ty with
  | .uint256 | .int256 | .bytes32 => some word
  | .uint8 => some (word &&& (uint8Modulus - 1))
  | .uint16 => some (word &&& (2^16 - 1))
  | .address => some (word &&& Compiler.Constants.addressMask)
  | .bool => some (if word = 0 then 0 else 1)
  | _ => none

def bindSupportedParams (params : List Param) (args : List Nat) :
    Option (List (String × Nat)) :=
  match params, args with
  | [], _ => some []
  | _ :: _, [] => none
  | param :: rest, arg :: restArgs => do
      let value ← decodeSupportedParamWord param.ty arg
      let bindings ← bindSupportedParams rest restArgs
      pure ((param.name, value) :: bindings)

def dynamicArrayBinding? (bindings : List (String × Nat)) (name : String) :
    Option (Nat × Nat) := do
  let dataOffset ← lookupBinding? bindings s!"{name}_data_offset"
  let length ← lookupBinding? bindings s!"{name}_length"
  some (dataOffset, length)
where
  lookupBinding? (bindings : List (String × Nat)) (name : String) : Option Nat :=
    bindings.find? (fun entry => entry.1 == name) |>.map Prod.snd

def externalCalldataSize (calldata : List Nat) : Nat :=
  4 + 32 * calldata.length

def externalWordAt? (selector : Nat) (calldata : List Nat) (byteOffset : Nat) :
    Option Nat :=
  if 4 ≤ byteOffset ∧ byteOffset + 32 ≤ externalCalldataSize calldata then
    some (calldataloadWord selector calldata byteOffset)
  else
    none

def arrayElementDynamicHeadOffset? (selector : Nat) (calldata : List Nat)
    (dataOffset length index : Nat) : Option Nat := do
  if index < length then
    let offsetTableBytes := length * 32
    let elementRelOffset ← externalWordAt? selector calldata (dataOffset + index * 32)
    if elementRelOffset < offsetTableBytes then
      none
    else
      let elementHead := dataOffset + elementRelOffset
      if elementHead + 32 ≤ externalCalldataSize calldata then
        some elementHead
      else
        none
  else
    none

def arrayElementDynamicWord? (selector : Nat) (calldata : List Nat)
    (dataOffset length index wordOffset : Nat) : Option Nat := do
  let elementHead ← arrayElementDynamicHeadOffset? selector calldata dataOffset length index
  externalWordAt? selector calldata (elementHead + wordOffset * 32)

def arrayElementDynamicMemberLength? (selector : Nat) (calldata : List Nat)
    (dataOffset length index wordOffset : Nat) : Option Nat := do
  let elementHead ← arrayElementDynamicHeadOffset? selector calldata dataOffset length index
  let memberRelOffset ← externalWordAt? selector calldata (elementHead + wordOffset * 32)
  let memberDataPos := elementHead + memberRelOffset
  externalWordAt? selector calldata memberDataPos

def arrayElementDynamicMemberDataOffset? (selector : Nat) (calldata : List Nat)
    (dataOffset length index wordOffset : Nat) : Option Nat := do
  let elementHead ← arrayElementDynamicHeadOffset? selector calldata dataOffset length index
  let memberRelOffset ← externalWordAt? selector calldata (elementHead + wordOffset * 32)
  let memberDataPos := elementHead + memberRelOffset
  if memberDataPos + 32 ≤ externalCalldataSize calldata then
    some (memberDataPos + 32)
  else
    none

def arrayElementDynamicMemberElement? (selector : Nat) (calldata : List Nat)
    (dataOffset length index wordOffset innerIndex : Nat) : Option Nat := do
  let memberLength ←
    arrayElementDynamicMemberLength? selector calldata dataOffset length index wordOffset
  if innerIndex < memberLength then
    let memberDataOffset ←
      arrayElementDynamicMemberDataOffset? selector calldata dataOffset length index wordOffset
    externalWordAt? selector calldata (memberDataOffset + innerIndex * 32)
  else
    none

inductive DynamicPayloadShape where
  | bytesLike
  | array (elementStrideWords : Nat)
  deriving Repr, DecidableEq

def DynamicPayloadShape.fitsLength (shape : DynamicPayloadShape)
    (length tailRemaining : Nat) : Bool :=
  match shape with
  | .bytesLike => length ≤ tailRemaining
  | .array elementStrideWords =>
      length ≤ tailRemaining / (32 * Nat.max 1 elementStrideWords)

structure LengthPrefixedDynamicParam where
  relativeOffset : Nat
  absoluteOffset : Nat
  length : Nat
  tailHeadEnd : Nat
  tailRemaining : Nat
  dataOffset : Nat
  deriving Repr, DecidableEq

def decodeLengthPrefixedDynamicParam? (selector : Nat) (calldata : List Nat)
    (shape : DynamicPayloadShape) (headSize baseOffset headOffset : Nat) :
    Option LengthPrefixedDynamicParam := do
  let relativeOffset ← externalWordAt? selector calldata headOffset
  if relativeOffset < headSize then
    none
  else
    let absoluteOffset := baseOffset + relativeOffset
    if absoluteOffset + 32 > externalCalldataSize calldata then
      none
    else
      let length ← externalWordAt? selector calldata absoluteOffset
      let tailHeadEnd := absoluteOffset + 32
      let tailRemaining := externalCalldataSize calldata - tailHeadEnd
      if shape.fitsLength length tailRemaining then
        some
          { relativeOffset := relativeOffset
            absoluteOffset := absoluteOffset
            length := length
            tailHeadEnd := tailHeadEnd
            tailRemaining := tailRemaining
            dataOffset := tailHeadEnd }
      else
        none

def decodeDynamicTupleParamDataOffset? (selector : Nat) (calldata : List Nat)
    (headSize baseOffset headOffset : Nat) : Option Nat := do
  let relativeOffset ← externalWordAt? selector calldata headOffset
  if relativeOffset < headSize then
    none
  else
    let absoluteOffset := baseOffset + relativeOffset
    if absoluteOffset + 32 ≤ externalCalldataSize calldata then
      some absoluteOffset
    else
      none

private def externalDynamicPayloadShape? : ParamType → Option DynamicPayloadShape
  | .bytes | .string => some .bytesLike
  | .array elemTy =>
      let strideWords :=
        if isDynamicParamType elemTy then
          1
        else
          Nat.max 1 (paramHeadSize elemTy / 32)
      some (.array strideWords)
  | _ => none

private def dynamicParamBindings (name : String)
    (decoded : LengthPrefixedDynamicParam) :
    List (String × Nat) :=
  [ (s!"{name}_offset", decoded.relativeOffset)
  , (s!"{name}_abs_offset", decoded.absoluteOffset)
  , (s!"{name}_length", decoded.length)
  , (s!"{name}_tail_head_end", decoded.tailHeadEnd)
  , (s!"{name}_tail_remaining", decoded.tailRemaining)
  , (s!"{name}_data_offset", decoded.dataOffset) ]

private def dynamicTupleParamBindings (name : String) (relativeOffset absoluteOffset : Nat) :
    List (String × Nat) :=
  [ (s!"{name}_offset", relativeOffset)
  , (s!"{name}_abs_offset", absoluteOffset)
  , (s!"{name}_data_offset", absoluteOffset) ]

def bindExternalParam (selector : Nat) (calldata : List Nat)
    (headSize baseOffset headOffset : Nat) (param : Param) :
    Option (List (String × Nat)) :=
  match decodeSupportedParamWord param.ty =<< externalWordAt? selector calldata headOffset with
  | some value => some [(param.name, value)]
  | none =>
      match externalDynamicPayloadShape? param.ty with
      | some shape => do
          let decoded ←
            decodeLengthPrefixedDynamicParam? selector calldata shape headSize baseOffset headOffset
          some (dynamicParamBindings param.name decoded)
      | none =>
          if isDynamicParamType param.ty then do
            let relativeOffset ← externalWordAt? selector calldata headOffset
            let absoluteOffset ←
              decodeDynamicTupleParamDataOffset? selector calldata headSize baseOffset headOffset
            some (dynamicTupleParamBindings param.name relativeOffset absoluteOffset)
          else
            none

def bindExternalParamsFrom (selector : Nat) (calldata : List Nat)
    (headSize baseOffset : Nat) : List Param → Nat → Option (List (String × Nat))
  | [], _ => some []
  | param :: rest, headOffset => do
      let here ← bindExternalParam selector calldata headSize baseOffset headOffset param
      let tail ← bindExternalParamsFrom selector calldata headSize baseOffset rest
        (headOffset + paramHeadSize param.ty)
      some (here ++ tail)

def bindExternalParams (selector : Nat) (params : List Param) (calldata : List Nat) :
    Option (List (String × Nat)) :=
  if params.length ≤ calldata.length then
    match bindSupportedParams params calldata with
    | some bindings => some bindings
    | none =>
        let headSize := paramHeadSizeList (params.map (·.ty))
        bindExternalParamsFrom selector calldata headSize 4 params 4
  else
    none

end DynamicAbi

end Compiler.CompilationModel

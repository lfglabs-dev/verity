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

/-- ABI coder v2 validation of one head word: `cleaned` is the type's cleanup of
`word` (solc's `cleanup_t_<type>`); the word is a valid encoding iff cleanup is
the identity on it (solc's `validator_revert_t_<type>`), else decoding fails. -/
def validatedWord (cleaned word : Nat) : Option Nat :=
  if cleaned = word then some cleaned else none

@[simp] theorem validatedWord_self (word : Nat) : validatedWord word word = some word := by
  simp [validatedWord]

theorem validatedWord_of_eq {cleaned word : Nat} (h : cleaned = word) :
    validatedWord cleaned word = some word := by
  subst h
  exact validatedWord_self cleaned

theorem validatedWord_eq_some_iff {cleaned word value : Nat} :
    validatedWord cleaned word = some value ↔ cleaned = word ∧ cleaned = value := by
  unfold validatedWord
  by_cases h : cleaned = word <;> simp [h]

theorem validatedWord_eq_none_iff {cleaned word : Nat} :
    validatedWord cleaned word = none ↔ cleaned ≠ word := by
  unfold validatedWord
  by_cases h : cleaned = word <;> simp [h]

/-- Strict ABI decoding of a scalar head word: a word that is not a valid
encoding of `ty` (high bits set for `address`/`uintN`, low bits set for
`bytesN`, not sign-extended for `intN`, not 0/1 for `bool`) fails. -/
def decodeSupportedParamWord (ty : ParamType) (word : Nat) : Option Nat :=
  let word := wordNormalize word
  match ty with
  | .uint256 | .int256 | .bytes32 => some word
  | .uint8 => validatedWord (word &&& (uint8Modulus - 1)) word
  | .uint16 => validatedWord (word &&& (2^16 - 1)) word
  | .uintN bits => validatedWord (word &&& (2 ^ bits - 1)) word
  | .intN bits => validatedWord
      (Verity.Core.Uint256.signextend
        (Verity.Core.Uint256.ofNat (bits / 8 - 1))
        (Verity.Core.Uint256.ofNat word)).val word
  | .bytesN bytes => validatedWord
      (word &&& ((2 ^ (8 * bytes) - 1) * 2 ^ (8 * (32 - bytes)))) word
  | .address => validatedWord (word &&& Compiler.Constants.addressMask) word
  | .bool => validatedWord (if word = 0 then 0 else 1) word
  | _ => none

/-- Non-validating scalar decoding: the type's cleanup of the word, as bound to
a static tuple member (`Compiler.genScalarCleanLoad`; solc validates members of
a calldata composite only at their read). -/
def cleanSupportedParamWord (ty : ParamType) (word : Nat) : Option Nat :=
  let word := wordNormalize word
  match ty with
  | .uint256 | .int256 | .bytes32 => some word
  | .uint8 => some (word &&& (uint8Modulus - 1))
  | .uint16 => some (word &&& (2^16 - 1))
  | .uintN bits => some (word &&& (2 ^ bits - 1))
  | .intN bits => some
      (Verity.Core.Uint256.signextend
        (Verity.Core.Uint256.ofNat (bits / 8 - 1))
        (Verity.Core.Uint256.ofNat word)).val
  | .bytesN bytes => some
      (word &&& ((2 ^ (8 * bytes) - 1) * 2 ^ (8 * (32 - bytes))))
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

/-- Semantics of the checked single-word calldata-array helper.  Out-of-range
indices fail (the generated helper reverts); in-range indices read the ABI word
at `dataOffset + 32 * index`. -/
def arrayElement? (selector : Nat) (calldata : List Nat)
    (dataOffset length index : Nat) : Option Nat :=
  if index < length then
    some (calldataloadWord selector calldata (dataOffset + index * 32))
  else
    none

/-- The first byte of a `calldataload`, matching Yul `byte(0,
calldataload(offset))`. -/
def calldataByte (selector : Nat) (calldata : List Nat) (offset : Nat) : Nat :=
  calldataloadWord selector calldata offset / (2 ^ 248) % 256

/-- Byte-for-byte equality over two calldata regions.  This is the functional
counterpart of `dynamicBytesEqCalldataHelper`; unequal lengths short-circuit to
`false`. -/
def dynamicBytesEqCalldata (selector : Nat) (calldata : List Nat)
    (lhsOffset lhsLength rhsOffset rhsLength : Nat) : Bool :=
  lhsLength = rhsLength &&
    (List.range lhsLength).all (fun index =>
      calldataByte selector calldata (lhsOffset + index) =
        calldataByte selector calldata (rhsOffset + index))

@[simp] theorem arrayElement?_index_oob
    (selector : Nat) (calldata : List Nat) (dataOffset length index : Nat)
    (h : length ≤ index) :
    arrayElement? selector calldata dataOffset length index = none := by
  simp [arrayElement?, Nat.not_lt.mpr h]

@[simp] theorem arrayElement?_index_in_bounds
    (selector : Nat) (calldata : List Nat) (dataOffset length index : Nat)
    (h : index < length) :
    arrayElement? selector calldata dataOffset length index =
      some (calldataloadWord selector calldata (dataOffset + index * 32)) := by
  simp [arrayElement?, h]

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
  | .array elemTy => some (.array (dynamicArrayElementStrideWords elemTy))
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

/-- Static tuple fields use the same recursive indexed names and word offsets
as `Compiler.genStaticTypeLoads`, binding each member's cleanup without
validation (`cleanSupportedParamWord`). Unsupported leaves and missing words fail;
this helper does not manufacture bindings for dynamic data or fixed arrays. -/
def bindStaticTupleType (selector : Nat) (calldata : List Nat)
    (name : String) (ty : ParamType) (offset : Nat) :
    Option (List (String × Nat)) :=
  match ty with
  | .tuple elemTys =>
      let rec go (tys : List ParamType) (index current : Nat) :
          Option (List (String × Nat)) :=
        match tys with
        | [] => some []
        | elemTy :: rest => do
            let here ← bindStaticTupleType selector calldata s!"{name}_{index}" elemTy current
            let tail ← go rest (index + 1) (current + paramHeadSize elemTy)
            some (here ++ tail)
        termination_by sizeOf tys
      go elemTys 0 offset
  | _ => do
      let word ← externalWordAt? selector calldata offset
      let value ← cleanSupportedParamWord ty word
      some [(name, value)]
termination_by sizeOf ty

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
            match param.ty with
            | .tuple _ => bindStaticTupleType selector calldata param.name param.ty headOffset
            | _ => none

def bindExternalParamsFrom (selector : Nat) (calldata : List Nat)
    (headSize baseOffset : Nat) : List Param → Nat → Option (List (String × Nat))
  | [], _ => some []
  | param :: rest, headOffset => do
      let here ← bindExternalParam selector calldata headSize baseOffset headOffset param
      let tail ← bindExternalParamsFrom selector calldata headSize baseOffset rest
        (headOffset + paramHeadSize param.ty)
      some (here ++ tail)

/-- The semantic counterpart of the compiler's length-prefixed dynamic
calldata loader for a `bytes` parameter.  Given the same checked head word,
tail length word, and byte-tail bound that the generated loader establishes,
the dispatcher binds exactly its six loader locals.

This is intentionally a one-parameter refinement boundary: the next dispatch
slice composes it with `execIRStmts` for `genDynamicParamLoads`, then lifts it
over the parameter list. -/
theorem bindExternalParam_bytes_refines_dynamic_loader
    {selector : Nat} {calldata : List Nat}
    {headSize baseOffset headOffset relativeOffset length : Nat} {name : String}
    (hhead : externalWordAt? selector calldata headOffset = some relativeOffset)
    (hheadBound : headSize ≤ relativeOffset)
    (htailBound : baseOffset + relativeOffset + 32 ≤ externalCalldataSize calldata)
    (hlength : externalWordAt? selector calldata (baseOffset + relativeOffset) = some length)
    (hpayloadBound :
      length ≤ externalCalldataSize calldata - (baseOffset + relativeOffset + 32)) :
    bindExternalParam selector calldata headSize baseOffset headOffset
      { name := name, ty := ParamType.bytes } =
      some
        [ (s!"{name}_offset", relativeOffset)
        , (s!"{name}_abs_offset", baseOffset + relativeOffset)
        , (s!"{name}_length", length)
        , (s!"{name}_tail_head_end", baseOffset + relativeOffset + 32)
        , (s!"{name}_tail_remaining",
            externalCalldataSize calldata - (baseOffset + relativeOffset + 32))
        , (s!"{name}_data_offset", baseOffset + relativeOffset + 32) ] := by
  have hnotTailOutOfBounds : ¬ baseOffset + relativeOffset + 32 > externalCalldataSize calldata := by
    omega
  have hnotHeadInTail : ¬ relativeOffset < headSize := by
    omega
  have hdecodeBytes : decodeSupportedParamWord ParamType.bytes =<< some relativeOffset = none := rfl
  simp [bindExternalParam, externalDynamicPayloadShape?,
    decodeLengthPrefixedDynamicParam?, DynamicPayloadShape.fitsLength,
    dynamicParamBindings, hhead, hdecodeBytes, hnotHeadInTail, hnotTailOutOfBounds, hlength,
    hpayloadBound]

/-- The single-word scalar parameter types: `bindExternalParam` binds them
through `decodeSupportedParamWord` alone. -/
def ScalarHeadParamType : ParamType → Prop
  | .uint256 | .int256 | .uint8 | .uint16 | .uintN _ | .intN _ | .bytesN _
  | .address | .bool | .bytes32 => True
  | _ => False

/-- On the scalar branch, `bindExternalParam` is the decoded ABI head word: it
fails exactly when the head word is missing or not a valid encoding. -/
theorem bindExternalParam_eq_map_of_scalar
    {selector : Nat} {calldata : List Nat} {headSize baseOffset headOffset : Nat}
    {param : Param} (hscalar : ScalarHeadParamType param.ty) :
    bindExternalParam selector calldata headSize baseOffset headOffset param =
      (decodeSupportedParamWord param.ty =<< externalWordAt? selector calldata headOffset).map
        (fun value => [(param.name, value)]) := by
  unfold bindExternalParam
  cases decodeSupportedParamWord param.ty =<< externalWordAt? selector calldata headOffset with
  | some value => rfl
  | none =>
      obtain ⟨name, ty⟩ := param
      cases ty <;> simp_all [ScalarHeadParamType, externalDynamicPayloadShape?,
        isDynamicParamType]

/-- On the scalar branch a successful `bindExternalParam` is exactly the decoded
ABI head word. -/
theorem bindExternalParam_scalar_eq_some_inv
    {selector : Nat} {calldata : List Nat} {headSize baseOffset headOffset : Nat}
    {param : Param} {bindings : List (String × Nat)}
    (hscalar : ScalarHeadParamType param.ty)
    (hbind : bindExternalParam selector calldata headSize baseOffset headOffset param =
      some bindings) :
    ∃ word value,
      externalWordAt? selector calldata headOffset = some word ∧
        decodeSupportedParamWord param.ty word = some value ∧
        bindings = [(param.name, value)] := by
  rw [bindExternalParam_eq_map_of_scalar hscalar] at hbind
  cases hword : externalWordAt? selector calldata headOffset with
  | none =>
      rw [hword, show (decodeSupportedParamWord param.ty =<< (none : Option Nat)) = none
        from rfl] at hbind
      simp at hbind
  | some word =>
      rw [hword, show (decodeSupportedParamWord param.ty =<< some word) =
        decodeSupportedParamWord param.ty word from rfl] at hbind
      cases hvalue : decodeSupportedParamWord param.ty word with
      | none => simp [hvalue] at hbind
      | some value =>
          simp only [hvalue, Option.map_some, Option.some.injEq] at hbind
          exact ⟨word, value, rfl, hvalue, hbind.symm⟩

/-- Inversion for the length-prefixed decoder at an arbitrary payload shape: a
successful decode pins every field of the result and certifies the head, tail
and shape-specific payload bounds. -/
private theorem decodeLengthPrefixedDynamicParam?_eq_some_inv
    {selector : Nat} {calldata : List Nat} {shape : DynamicPayloadShape}
    {headSize baseOffset headOffset : Nat} {decoded : LengthPrefixedDynamicParam}
    (hdec : decodeLengthPrefixedDynamicParam? selector calldata shape
      headSize baseOffset headOffset = some decoded) :
    externalWordAt? selector calldata headOffset = some decoded.relativeOffset ∧
      headSize ≤ decoded.relativeOffset ∧
      baseOffset + decoded.relativeOffset + 32 ≤ externalCalldataSize calldata ∧
      externalWordAt? selector calldata (baseOffset + decoded.relativeOffset) =
        some decoded.length ∧
      shape.fitsLength decoded.length
        (externalCalldataSize calldata - (baseOffset + decoded.relativeOffset + 32)) ∧
      decoded.absoluteOffset = baseOffset + decoded.relativeOffset ∧
      decoded.tailHeadEnd = baseOffset + decoded.relativeOffset + 32 ∧
      decoded.tailRemaining =
        externalCalldataSize calldata - (baseOffset + decoded.relativeOffset + 32) ∧
      decoded.dataOffset = baseOffset + decoded.relativeOffset + 32 := by
  unfold decodeLengthPrefixedDynamicParam? at hdec
  cases hro : externalWordAt? selector calldata headOffset with
  | none => simp [hro] at hdec
  | some relativeOffset =>
      cases hlen : externalWordAt? selector calldata (baseOffset + relativeOffset) <;>
        by_cases hlt : relativeOffset < headSize <;>
        by_cases hgt : baseOffset + relativeOffset + 32 > externalCalldataSize calldata <;>
        simp_all [Option.bind_eq_bind, Option.bind]
      obtain ⟨hfit, rfl⟩ := hdec
      exact ⟨rfl, hlt, hgt, hlen, hfit, rfl, rfl, rfl, rfl⟩

/-- A successful binding of a length-prefixed dynamic parameter comes from a
successful length-prefixed decode, and the bindings are its six loader locals. -/
private theorem bindExternalParam_lengthPrefixed_eq_some_inv
    {selector : Nat} {calldata : List Nat} {headSize baseOffset headOffset : Nat}
    {param : Param} {shape : DynamicPayloadShape} {bindings : List (String × Nat)}
    (hword : ∀ word, decodeSupportedParamWord param.ty word = none)
    (hshape : externalDynamicPayloadShape? param.ty = some shape)
    (hbind : bindExternalParam selector calldata headSize baseOffset headOffset param =
      some bindings) :
    ∃ decoded, decodeLengthPrefixedDynamicParam? selector calldata shape
        headSize baseOffset headOffset = some decoded ∧
      bindings = dynamicParamBindings param.name decoded := by
  have hdecode :
      decodeSupportedParamWord param.ty =<< externalWordAt? selector calldata headOffset =
        none := by
    cases externalWordAt? selector calldata headOffset <;> first | rfl | exact hword _
  unfold bindExternalParam at hbind
  rw [hdecode, hshape] at hbind
  cases hdec : decodeLengthPrefixedDynamicParam? selector calldata shape
      headSize baseOffset headOffset with
  | none => simp [hdec] at hbind
  | some decoded => exact ⟨decoded, rfl, by simpa [hdec] using hbind.symm⟩

/-- A successful binding of a length-prefixed dynamic parameter is exactly the
six loader locals, certified by the head, tail and shape-specific payload bounds. -/
private theorem bindExternalParam_lengthPrefixed_eq_some_loader_inv
    {selector : Nat} {calldata : List Nat} {headSize baseOffset headOffset : Nat} {param : Param}
    {shape : DynamicPayloadShape} {bindings : List (String × Nat)}
    (hword : ∀ word, decodeSupportedParamWord param.ty word = none)
    (hshape : externalDynamicPayloadShape? param.ty = some shape)
    (hbind : bindExternalParam selector calldata headSize baseOffset headOffset param =
      some bindings) :
    ∃ relativeOffset length,
      externalWordAt? selector calldata headOffset = some relativeOffset ∧
        headSize ≤ relativeOffset ∧
        baseOffset + relativeOffset + 32 ≤ externalCalldataSize calldata ∧
        externalWordAt? selector calldata (baseOffset + relativeOffset) = some length ∧
        shape.fitsLength length
          (externalCalldataSize calldata - (baseOffset + relativeOffset + 32)) ∧
        bindings =
          [ (s!"{param.name}_offset", relativeOffset)
          , (s!"{param.name}_abs_offset", baseOffset + relativeOffset)
          , (s!"{param.name}_length", length)
          , (s!"{param.name}_tail_head_end", baseOffset + relativeOffset + 32)
          , (s!"{param.name}_tail_remaining",
              externalCalldataSize calldata - (baseOffset + relativeOffset + 32))
          , (s!"{param.name}_data_offset", baseOffset + relativeOffset + 32) ] := by
  obtain ⟨decoded, hdec, rfl⟩ := bindExternalParam_lengthPrefixed_eq_some_inv hword hshape hbind
  obtain ⟨hro, hhead, htail, hlen, hfit, habs, hend, hrem, hdata⟩ :=
    decodeLengthPrefixedDynamicParam?_eq_some_inv hdec
  exact ⟨_, _, hro, hhead, htail, hlen, hfit, by rw [dynamicParamBindings, habs, hend, hrem, hdata]⟩

/-- Inversion for the length-prefixed `bytes`-like decoder: a successful decode
pins every field of the result and certifies the three bounds the generated
loader checks at runtime. -/
theorem decodeLengthPrefixedDynamicParam?_bytesLike_eq_some_inv
    {selector : Nat} {calldata : List Nat} {headSize baseOffset headOffset : Nat}
    {decoded : LengthPrefixedDynamicParam}
    (hdec : decodeLengthPrefixedDynamicParam? selector calldata DynamicPayloadShape.bytesLike
      headSize baseOffset headOffset = some decoded) :
    externalWordAt? selector calldata headOffset = some decoded.relativeOffset ∧
      headSize ≤ decoded.relativeOffset ∧
      baseOffset + decoded.relativeOffset + 32 ≤ externalCalldataSize calldata ∧
      externalWordAt? selector calldata (baseOffset + decoded.relativeOffset) =
        some decoded.length ∧
      decoded.length ≤
        externalCalldataSize calldata - (baseOffset + decoded.relativeOffset + 32) ∧
      decoded.absoluteOffset = baseOffset + decoded.relativeOffset ∧
      decoded.tailHeadEnd = baseOffset + decoded.relativeOffset + 32 ∧
      decoded.tailRemaining =
        externalCalldataSize calldata - (baseOffset + decoded.relativeOffset + 32) ∧
      decoded.dataOffset = baseOffset + decoded.relativeOffset + 32 := by
  obtain ⟨hro, hheadBound, htailBound, hlen, hfit, habs, htailHead, htailRem, hdata⟩ :=
    decodeLengthPrefixedDynamicParam?_eq_some_inv hdec
  exact ⟨hro, hheadBound, htailBound, hlen,
    by simpa [DynamicPayloadShape.fitsLength] using hfit, habs, htailHead, htailRem, hdata⟩

/-- Converse of `bindExternalParam_bytes_refines_dynamic_loader`: a successful
`bytes` binding is exactly the six loader locals, and it certifies the bounds
the generated loader enforces.  The IR-execution refinement consumes this to
discharge the loader's revert guards from binder success alone. -/
theorem bindExternalParam_bytes_eq_some_inv
    {selector : Nat} {calldata : List Nat}
    {headSize baseOffset headOffset : Nat} {name : String}
    {bindings : List (String × Nat)}
    (hbind : bindExternalParam selector calldata headSize baseOffset headOffset
      { name := name, ty := ParamType.bytes } = some bindings) :
    ∃ relativeOffset length,
      externalWordAt? selector calldata headOffset = some relativeOffset ∧
        headSize ≤ relativeOffset ∧
        baseOffset + relativeOffset + 32 ≤ externalCalldataSize calldata ∧
        externalWordAt? selector calldata (baseOffset + relativeOffset) = some length ∧
        length ≤ externalCalldataSize calldata - (baseOffset + relativeOffset + 32) ∧
        bindings =
          [ (s!"{name}_offset", relativeOffset)
          , (s!"{name}_abs_offset", baseOffset + relativeOffset)
          , (s!"{name}_length", length)
          , (s!"{name}_tail_head_end", baseOffset + relativeOffset + 32)
          , (s!"{name}_tail_remaining",
              externalCalldataSize calldata - (baseOffset + relativeOffset + 32))
          , (s!"{name}_data_offset", baseOffset + relativeOffset + 32) ] := by
  simpa [DynamicPayloadShape.fitsLength] using
    bindExternalParam_lengthPrefixed_eq_some_loader_inv (fun _ => rfl) rfl hbind

/-- `string` and `bytes` bind identically. The ABI encodes both as a relative
tail offset in the head area and a length-prefixed payload in the tail; the two
types differ only in the textual signature that feeds the selector hash, never
in the encoding of an argument block. Every `string` fact below is therefore
routed through the `bytes` lemmas rather than reproved (verity#2085). -/
theorem bindExternalParam_string_eq_bytes
    (selector : Nat) (calldata : List Nat)
    (headSize baseOffset headOffset : Nat) (name : String) :
    bindExternalParam selector calldata headSize baseOffset headOffset
        { name := name, ty := ParamType.string } =
      bindExternalParam selector calldata headSize baseOffset headOffset
        { name := name, ty := ParamType.bytes } := by
  unfold bindExternalParam
  cases externalWordAt? selector calldata headOffset <;> rfl

/-- The `string` counterpart of `bindExternalParam_bytes_refines_dynamic_loader`:
the same checked head word, tail length word and payload bound make the
dispatcher bind the same six loader locals. -/
theorem bindExternalParam_string_refines_dynamic_loader
    {selector : Nat} {calldata : List Nat}
    {headSize baseOffset headOffset relativeOffset length : Nat} {name : String}
    (hhead : externalWordAt? selector calldata headOffset = some relativeOffset)
    (hheadBound : headSize ≤ relativeOffset)
    (htailBound : baseOffset + relativeOffset + 32 ≤ externalCalldataSize calldata)
    (hlength : externalWordAt? selector calldata (baseOffset + relativeOffset) = some length)
    (hpayloadBound :
      length ≤ externalCalldataSize calldata - (baseOffset + relativeOffset + 32)) :
    bindExternalParam selector calldata headSize baseOffset headOffset
      { name := name, ty := ParamType.string } =
      some
        [ (s!"{name}_offset", relativeOffset)
        , (s!"{name}_abs_offset", baseOffset + relativeOffset)
        , (s!"{name}_length", length)
        , (s!"{name}_tail_head_end", baseOffset + relativeOffset + 32)
        , (s!"{name}_tail_remaining",
            externalCalldataSize calldata - (baseOffset + relativeOffset + 32))
        , (s!"{name}_data_offset", baseOffset + relativeOffset + 32) ] := by
  rw [bindExternalParam_string_eq_bytes]
  exact bindExternalParam_bytes_refines_dynamic_loader hhead hheadBound htailBound hlength
    hpayloadBound

/-- Converse of `bindExternalParam_string_refines_dynamic_loader`, mirroring
`bindExternalParam_bytes_eq_some_inv`: a successful `string` binding is exactly
the six loader locals and certifies the bounds the generated loader checks. -/
theorem bindExternalParam_string_eq_some_inv
    {selector : Nat} {calldata : List Nat}
    {headSize baseOffset headOffset : Nat} {name : String}
    {bindings : List (String × Nat)}
    (hbind : bindExternalParam selector calldata headSize baseOffset headOffset
      { name := name, ty := ParamType.string } = some bindings) :
    ∃ relativeOffset length,
      externalWordAt? selector calldata headOffset = some relativeOffset ∧
        headSize ≤ relativeOffset ∧
        baseOffset + relativeOffset + 32 ≤ externalCalldataSize calldata ∧
        externalWordAt? selector calldata (baseOffset + relativeOffset) = some length ∧
        length ≤ externalCalldataSize calldata - (baseOffset + relativeOffset + 32) ∧
        bindings =
          [ (s!"{name}_offset", relativeOffset)
          , (s!"{name}_abs_offset", baseOffset + relativeOffset)
          , (s!"{name}_length", length)
          , (s!"{name}_tail_head_end", baseOffset + relativeOffset + 32)
          , (s!"{name}_tail_remaining",
              externalCalldataSize calldata - (baseOffset + relativeOffset + 32))
          , (s!"{name}_data_offset", baseOffset + relativeOffset + 32) ] := by
  rw [bindExternalParam_string_eq_bytes] at hbind
  exact bindExternalParam_bytes_eq_some_inv hbind

/-! ### Dynamic arrays

`T[]` shares the `bytes` head/tail skeleton — a relative tail offset in the head
area, a length word at the tail head — but its length counts *elements*, not
bytes.  The payload bound therefore divides the remaining tail by the element
stride, which is exactly the `div` the emitter puts in the generated guard
(verity#2085). -/

/-- Inversion for the length-prefixed array decoder, mirroring
`decodeLengthPrefixedDynamicParam?_bytesLike_eq_some_inv` with the strided
payload bound. -/
theorem decodeLengthPrefixedDynamicParam?_array_eq_some_inv
    {selector : Nat} {calldata : List Nat}
    {headSize baseOffset headOffset strideWords : Nat}
    {decoded : LengthPrefixedDynamicParam}
    (hdec : decodeLengthPrefixedDynamicParam? selector calldata
      (DynamicPayloadShape.array strideWords) headSize baseOffset headOffset = some decoded) :
    externalWordAt? selector calldata headOffset = some decoded.relativeOffset ∧
      headSize ≤ decoded.relativeOffset ∧
      baseOffset + decoded.relativeOffset + 32 ≤ externalCalldataSize calldata ∧
      externalWordAt? selector calldata (baseOffset + decoded.relativeOffset) =
        some decoded.length ∧
      decoded.length ≤
        (externalCalldataSize calldata - (baseOffset + decoded.relativeOffset + 32)) /
          (32 * Nat.max 1 strideWords) ∧
      decoded.absoluteOffset = baseOffset + decoded.relativeOffset ∧
      decoded.tailHeadEnd = baseOffset + decoded.relativeOffset + 32 ∧
      decoded.tailRemaining =
        externalCalldataSize calldata - (baseOffset + decoded.relativeOffset + 32) ∧
      decoded.dataOffset = baseOffset + decoded.relativeOffset + 32 := by
  obtain ⟨hro, hheadBound, htailBound, hlen, hfit, habs, htailHead, htailRem, hdata⟩ :=
    decodeLengthPrefixedDynamicParam?_eq_some_inv hdec
  exact ⟨hro, hheadBound, htailBound, hlen,
    by simpa [DynamicPayloadShape.fitsLength] using hfit, habs, htailHead, htailRem, hdata⟩

/-- The array counterpart of `bindExternalParam_bytes_refines_dynamic_loader`:
given the head word, tail length word and strided payload bound the generated
loader checks, the dispatcher binds the same six loader locals. -/
theorem bindExternalParam_array_refines_dynamic_loader
    {selector : Nat} {calldata : List Nat}
    {headSize baseOffset headOffset relativeOffset length : Nat} {name : String}
    {elemTy : ParamType}
    (hhead : externalWordAt? selector calldata headOffset = some relativeOffset)
    (hheadBound : headSize ≤ relativeOffset)
    (htailBound : baseOffset + relativeOffset + 32 ≤ externalCalldataSize calldata)
    (hlength : externalWordAt? selector calldata (baseOffset + relativeOffset) = some length)
    (hpayloadBound :
      length ≤ (externalCalldataSize calldata - (baseOffset + relativeOffset + 32)) /
        (32 * dynamicArrayElementStrideWords elemTy)) :
    bindExternalParam selector calldata headSize baseOffset headOffset
      { name := name, ty := ParamType.array elemTy } =
      some
        [ (s!"{name}_offset", relativeOffset)
        , (s!"{name}_abs_offset", baseOffset + relativeOffset)
        , (s!"{name}_length", length)
        , (s!"{name}_tail_head_end", baseOffset + relativeOffset + 32)
        , (s!"{name}_tail_remaining",
            externalCalldataSize calldata - (baseOffset + relativeOffset + 32))
        , (s!"{name}_data_offset", baseOffset + relativeOffset + 32) ] := by
  have hnotTailOutOfBounds :
      ¬ baseOffset + relativeOffset + 32 > externalCalldataSize calldata := by omega
  have hnotHeadInTail : ¬ relativeOffset < headSize := by omega
  have hdecodeArray :
      decodeSupportedParamWord (ParamType.array elemTy) =<< some relativeOffset = none := rfl
  simp [bindExternalParam, externalDynamicPayloadShape?,
    decodeLengthPrefixedDynamicParam?, DynamicPayloadShape.fitsLength,
    dynamicParamBindings, hhead, hdecodeArray, hnotHeadInTail, hnotTailOutOfBounds, hlength,
    hpayloadBound]

/-- Converse of `bindExternalParam_array_refines_dynamic_loader`: a successful
array binding is exactly the six loader locals and certifies the bounds the
generated loader enforces, including the strided payload bound. -/
theorem bindExternalParam_array_eq_some_inv
    {selector : Nat} {calldata : List Nat}
    {headSize baseOffset headOffset : Nat} {name : String} {elemTy : ParamType}
    {bindings : List (String × Nat)}
    (hbind : bindExternalParam selector calldata headSize baseOffset headOffset
      { name := name, ty := ParamType.array elemTy } = some bindings) :
    ∃ relativeOffset length,
      externalWordAt? selector calldata headOffset = some relativeOffset ∧
        headSize ≤ relativeOffset ∧
        baseOffset + relativeOffset + 32 ≤ externalCalldataSize calldata ∧
        externalWordAt? selector calldata (baseOffset + relativeOffset) = some length ∧
        length ≤ (externalCalldataSize calldata - (baseOffset + relativeOffset + 32)) /
          (32 * dynamicArrayElementStrideWords elemTy) ∧
        bindings =
          [ (s!"{name}_offset", relativeOffset)
          , (s!"{name}_abs_offset", baseOffset + relativeOffset)
          , (s!"{name}_length", length)
          , (s!"{name}_tail_head_end", baseOffset + relativeOffset + 32)
          , (s!"{name}_tail_remaining",
              externalCalldataSize calldata - (baseOffset + relativeOffset + 32))
          , (s!"{name}_data_offset", baseOffset + relativeOffset + 32) ] := by
  simpa [DynamicPayloadShape.fitsLength] using
    bindExternalParam_lengthPrefixed_eq_some_loader_inv (fun _ => rfl) rfl hbind

/-! ### Dynamic composites without a length word

A `struct` with dynamic members, and a fixed-size array of such structs, are
encoded as a relative tail offset whose target is the composite's own head area:
no length word, so the loader binds three locals instead of six.  Both shapes go
through the same branch of `bindExternalParam`, keyed on the compiler's
`isLengthPrefixedDynamicShape` (verity#2085). -/

private theorem decodeSupportedParamWord_eq_none_of_dynamic {ty : ParamType}
    (hdynamic : isDynamicParamType ty = true) (word : Nat) :
    decodeSupportedParamWord ty word = none := by
  cases ty <;> simp_all [decodeSupportedParamWord, isDynamicParamType]

private theorem externalDynamicPayloadShape?_eq_none_of_not_lengthPrefixed {ty : ParamType}
    (hnotLengthPrefixed : isLengthPrefixedDynamicShape ty = false) :
    externalDynamicPayloadShape? ty = none := by
  cases ty <;> simp_all [isLengthPrefixedDynamicShape, externalDynamicPayloadShape?]

/-- Inversion for the length-word-free dynamic decoder: a successful decode pins
the absolute offset and certifies the two bounds the generated loader checks. -/
theorem decodeDynamicTupleParamDataOffset?_eq_some_inv
    {selector : Nat} {calldata : List Nat} {headSize baseOffset headOffset absoluteOffset : Nat}
    (hdec : decodeDynamicTupleParamDataOffset? selector calldata headSize baseOffset headOffset
      = some absoluteOffset) :
    ∃ relativeOffset,
      externalWordAt? selector calldata headOffset = some relativeOffset ∧
        headSize ≤ relativeOffset ∧
        baseOffset + relativeOffset + 32 ≤ externalCalldataSize calldata ∧
        absoluteOffset = baseOffset + relativeOffset := by
  unfold decodeDynamicTupleParamDataOffset? at hdec
  cases hro : externalWordAt? selector calldata headOffset with
  | none => rw [hro] at hdec; simp at hdec
  | some relativeOffset =>
      rw [hro] at hdec
      simp only [Option.bind_eq_bind, Option.bind] at hdec
      by_cases hlt : relativeOffset < headSize
      · simp [hlt] at hdec
      · rw [if_neg hlt] at hdec
        by_cases hfit : baseOffset + relativeOffset + 32 ≤ externalCalldataSize calldata
        · rw [if_pos hfit] at hdec
          exact ⟨relativeOffset, rfl, by omega, hfit, by simpa using hdec.symm⟩
        · rw [if_neg hfit] at hdec
          simp at hdec

/-- The dispatcher binds the three loader locals of a length-word-free dynamic
composite from the same head word and tail bound the generated loader checks. -/
theorem bindExternalParam_dynamicComposite_refines_dynamic_loader
    {selector : Nat} {calldata : List Nat}
    {headSize baseOffset headOffset relativeOffset : Nat} {name : String} {ty : ParamType}
    (hdynamic : isDynamicParamType ty = true)
    (hnotLengthPrefixed : isLengthPrefixedDynamicShape ty = false)
    (hhead : externalWordAt? selector calldata headOffset = some relativeOffset)
    (hheadBound : headSize ≤ relativeOffset)
    (htailBound : baseOffset + relativeOffset + 32 ≤ externalCalldataSize calldata) :
    bindExternalParam selector calldata headSize baseOffset headOffset
      { name := name, ty := ty } =
      some
        [ (s!"{name}_offset", relativeOffset)
        , (s!"{name}_abs_offset", baseOffset + relativeOffset)
        , (s!"{name}_data_offset", baseOffset + relativeOffset) ] := by
  have hnotHeadInTail : ¬ relativeOffset < headSize := by omega
  have hoff :
      decodeDynamicTupleParamDataOffset? selector calldata headSize baseOffset headOffset =
        some (baseOffset + relativeOffset) := by
    unfold decodeDynamicTupleParamDataOffset?
    rw [hhead]
    simp only [Option.bind_eq_bind, Option.bind]
    rw [if_neg hnotHeadInTail, if_pos htailBound]
  have hdec : decodeSupportedParamWord ty =<< some relativeOffset = none :=
    decodeSupportedParamWord_eq_none_of_dynamic hdynamic relativeOffset
  unfold bindExternalParam
  rw [hhead, hdec,
    externalDynamicPayloadShape?_eq_none_of_not_lengthPrefixed hnotLengthPrefixed,
    if_pos hdynamic]
  simp only [hoff, Option.bind_eq_bind, Option.bind, dynamicTupleParamBindings]

/-- Converse of `bindExternalParam_dynamicComposite_refines_dynamic_loader`: a
successful binding is exactly the three loader locals and certifies the two
bounds the generated loader enforces. -/
theorem bindExternalParam_dynamicComposite_eq_some_inv
    {selector : Nat} {calldata : List Nat}
    {headSize baseOffset headOffset : Nat} {name : String} {ty : ParamType}
    {bindings : List (String × Nat)}
    (hdynamic : isDynamicParamType ty = true)
    (hnotLengthPrefixed : isLengthPrefixedDynamicShape ty = false)
    (hbind : bindExternalParam selector calldata headSize baseOffset headOffset
      { name := name, ty := ty } = some bindings) :
    ∃ relativeOffset,
      externalWordAt? selector calldata headOffset = some relativeOffset ∧
        headSize ≤ relativeOffset ∧
        baseOffset + relativeOffset + 32 ≤ externalCalldataSize calldata ∧
        bindings =
          [ (s!"{name}_offset", relativeOffset)
          , (s!"{name}_abs_offset", baseOffset + relativeOffset)
          , (s!"{name}_data_offset", baseOffset + relativeOffset) ] := by
  have hdecode :
      decodeSupportedParamWord ty =<< externalWordAt? selector calldata headOffset = none := by
    cases externalWordAt? selector calldata headOffset with
    | none => rfl
    | some word => exact decodeSupportedParamWord_eq_none_of_dynamic hdynamic word
  unfold bindExternalParam at hbind
  rw [hdecode, externalDynamicPayloadShape?_eq_none_of_not_lengthPrefixed hnotLengthPrefixed,
    if_pos hdynamic] at hbind
  cases hro : externalWordAt? selector calldata headOffset with
  | none => rw [hro] at hbind; simp at hbind
  | some relativeOffset =>
      rw [hro] at hbind
      simp only [Option.bind_eq_bind, Option.bind] at hbind
      cases hoff : decodeDynamicTupleParamDataOffset? selector calldata headSize baseOffset
          headOffset with
      | none => rw [hoff] at hbind; simp at hbind
      | some absoluteOffset =>
          rw [hoff] at hbind
          simp only [Option.some.injEq] at hbind
          obtain ⟨ro, hro', hheadBound, htailBound, habs⟩ :=
            decodeDynamicTupleParamDataOffset?_eq_some_inv hoff
          have hroEq : ro = relativeOffset := by rw [hro] at hro'; simpa using hro'.symm
          subst hroEq
          refine ⟨ro, rfl, hheadBound, htailBound, ?_⟩
          rw [← hbind, habs]
          simp [dynamicTupleParamBindings]

/-- Witness that one external ABI parameter is accepted by `bindExternalParam`
at a particular absolute head offset. -/
def ExternalParamBindingWitness
    (selector : Nat) (calldata : List Nat)
    (headSize baseOffset headOffset : Nat)
    (param : Param) : Prop :=
  ∃ bindings,
    bindExternalParam selector calldata headSize baseOffset headOffset param =
      some bindings

/-- One `ExternalParamBindingWitness` per parameter, using the exact ABI head
offset progression consumed by `bindExternalParamsFrom`. -/
inductive ExternalParamBindingWitnessesFrom
    (selector : Nat) (calldata : List Nat)
    (headSize baseOffset : Nat) : List Param → Nat → Prop where
  | nil (headOffset : Nat) :
      ExternalParamBindingWitnessesFrom selector calldata headSize baseOffset [] headOffset
  | cons {param : Param} {rest : List Param} {headOffset : Nat}
      (head :
        ExternalParamBindingWitness selector calldata headSize baseOffset headOffset param)
      (tail :
        ExternalParamBindingWitnessesFrom selector calldata headSize baseOffset rest
          (headOffset + paramHeadSize param.ty)) :
      ExternalParamBindingWitnessesFrom selector calldata headSize baseOffset
        (param :: rest) headOffset

theorem bindExternalParamsFrom_some_of_witnesses
    {selector : Nat} {calldata : List Nat} {headSize baseOffset : Nat}
    {params : List Param} {headOffset : Nat}
    (h :
      ExternalParamBindingWitnessesFrom selector calldata headSize baseOffset params headOffset) :
    ∃ bindings,
      bindExternalParamsFrom selector calldata headSize baseOffset params headOffset =
        some bindings := by
  induction h with
  | nil headOffset =>
      exact ⟨[], rfl⟩
  | cons head tail ih =>
      rcases head with ⟨here, hhere⟩
      rcases ih with ⟨there, hthere⟩
      exact ⟨here ++ there, by
        simp [bindExternalParamsFrom, hhere, hthere]⟩

/-- Static tuples now expand through the indexed static decoder rather than
falling through to the unsupported-parameter result. This equation pins the
actual public binder branch; it is not a solc equivalence theorem. -/
theorem bindExternalParam_staticTuple_arm
    {selector : Nat} {calldata : List Nat} {headSize baseOffset headOffset : Nat}
    {name : String} {elemTys : List ParamType}
    (hstatic : isDynamicParamTypeList elemTys = false) :
    bindExternalParam selector calldata headSize baseOffset headOffset
      { name := name, ty := ParamType.tuple elemTys } =
        bindStaticTupleType selector calldata name (.tuple elemTys) headOffset := by
  have hdecode :
      decodeSupportedParamWord (ParamType.tuple elemTys) =<<
        externalWordAt? selector calldata headOffset = none := by
    cases externalWordAt? selector calldata headOffset <;> rfl
  unfold bindExternalParam
  rw [hdecode]
  simp [externalDynamicPayloadShape?, isDynamicParamType, hstatic]

/-- Static fixed arrays are not expanded by the current semantic
external-parameter binder. This documents the remaining gap without claiming
support for every static composite constructor. -/
theorem bindExternalParam_staticFixedArray_eq_none
    {selector : Nat} {calldata : List Nat} {headSize baseOffset headOffset : Nat}
    {name : String} {elemTy : ParamType} {size : Nat}
    (hstatic : isDynamicParamType elemTy = false) :
    bindExternalParam selector calldata headSize baseOffset headOffset
      { name := name, ty := ParamType.fixedArray elemTy size } = none := by
  have hdecode :
      decodeSupportedParamWord (ParamType.fixedArray elemTy size) =<<
        externalWordAt? selector calldata headOffset = none := by
    cases externalWordAt? selector calldata headOffset <;> rfl
  unfold bindExternalParam
  rw [hdecode]
  simp [externalDynamicPayloadShape?, isDynamicParamType, hstatic]

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

theorem wordNormalize_mod (n : Nat) :
    wordNormalize (n % Compiler.Constants.evmModulus) = wordNormalize n := by
  show n % Compiler.Constants.evmModulus % Compiler.Constants.evmModulus =
    n % Compiler.Constants.evmModulus
  exact Nat.mod_mod _ _

theorem decodeSupportedParamWord_mod (ty : ParamType) (word : Nat) :
    decodeSupportedParamWord ty (word % Compiler.Constants.evmModulus) =
      decodeSupportedParamWord ty word := by
  simp only [decodeSupportedParamWord, wordNormalize_mod]

/-- At an aligned in-range head offset the external word is the calldata word
(reduced mod 2^256). -/
private theorem externalWordAt?_aligned_mod {selector : Nat} {calldata : List Nat} {idx : Nat}
    (hidx : idx < calldata.length) :
    externalWordAt? selector calldata (4 + 32 * idx) =
      some (calldata.getD idx 0 % Compiler.Constants.evmModulus) := by
  have hbound : 4 ≤ 4 + 32 * idx ∧ 4 + 32 * idx + 32 ≤ externalCalldataSize calldata := by
    simp only [externalCalldataSize]
    omega
  have hword : calldataloadWord selector calldata (4 + 32 * idx) =
      calldata.getD idx 0 % Compiler.Constants.evmModulus := by
    have h4 : ¬ 4 + 32 * idx < 4 := by omega
    simp [calldataloadWord, h4]
  simp only [externalWordAt?, hbound, and_self, ↓reduceIte, hword]

theorem paramHeadSize_of_scalarHead {ty : ParamType} (hscalar : ScalarHeadParamType ty) :
    paramHeadSize ty = 32 := by
  cases ty <;> simp_all [ScalarHeadParamType, paramHeadSize]

/-- For scalar head parameters covered by the calldata, the external binder
fails whenever the word-by-word scalar binder does: a word that is not a valid
encoding of its type is rejected on both paths. -/
theorem bindExternalParamsFrom_scalar_eq_none
    (selector : Nat) (calldata : List Nat) (headSize baseOffset : Nat) :
    ∀ (params : List Param) (idx : Nat),
      (∀ param ∈ params, ScalarHeadParamType param.ty) →
      idx + params.length ≤ calldata.length →
      bindSupportedParams params (calldata.drop idx) = none →
      bindExternalParamsFrom selector calldata headSize baseOffset params (4 + 32 * idx) = none
  | [], _, _, _, hnone => by simp [bindSupportedParams] at hnone
  | param :: rest, idx, hscalar, hlen, hnone => by
      have hhead := hscalar param (by simp)
      have hidx : idx < calldata.length := by simp at hlen; omega
      rw [List.drop_eq_getElem_cons hidx] at hnone
      have hget : calldata[idx] = calldata.getD idx 0 := by
        simp [List.getElem?_eq_getElem hidx]
      rw [hget] at hnone
      simp only [bindExternalParamsFrom, bindExternalParam_eq_map_of_scalar hhead,
        externalWordAt?_aligned_mod hidx, paramHeadSize_of_scalarHead hhead]
      rw [show (decodeSupportedParamWord param.ty =<<
          some (calldata.getD idx 0 % Compiler.Constants.evmModulus)) =
          decodeSupportedParamWord param.ty (calldata.getD idx 0) from
        decodeSupportedParamWord_mod _ _]
      cases hdec : decodeSupportedParamWord param.ty (calldata.getD idx 0) with
      | none => rfl
      | some value =>
          have hrest : bindSupportedParams rest (calldata.drop (idx + 1)) = none := by
            cases h : bindSupportedParams rest (calldata.drop (idx + 1)) with
            | none => rfl
            | some bs => simp [bindSupportedParams, hdec, h, -List.getD_eq_getElem?_getD] at hnone
          have ih := bindExternalParamsFrom_scalar_eq_none selector calldata headSize baseOffset
            rest (idx + 1) (fun p hp => hscalar p (by simp [hp])) (by simp at hlen ⊢; omega) hrest
          rw [show 4 + 32 * idx + 32 = 4 + 32 * (idx + 1) by omega]
          simp [ih]

/-- Under scalar head parameters, the external binder fails whenever the
word-by-word scalar binder does. -/
theorem bindExternalParams_eq_none_of_bindSupportedParams_none
    (selector : Nat) {params : List Param} {args : List Nat}
    (hscalar : ∀ param ∈ params, ScalarHeadParamType param.ty)
    (hnone : bindSupportedParams params args = none) :
    bindExternalParams selector params args = none := by
  unfold bindExternalParams
  by_cases hlen : params.length ≤ args.length
  · rw [if_pos hlen, hnone]
    simpa using bindExternalParamsFrom_scalar_eq_none selector args _ 4 params 0 hscalar
      (by simpa using hlen) (by simpa using hnone)
  · rw [if_neg hlen]

end DynamicAbi

end Compiler.CompilationModel

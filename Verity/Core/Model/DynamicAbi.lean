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

/-- On the scalar branch — where `decodeSupportedParamWord` is total — a
successful `bindExternalParam` is exactly the decoded ABI head word. -/
theorem bindExternalParam_scalar_eq_some_inv
    {selector : Nat} {calldata : List Nat} {headSize baseOffset headOffset : Nat}
    {param : Param} {bindings : List (String × Nat)}
    (htotal : ∀ w : Nat, ∃ v, decodeSupportedParamWord param.ty w = some v)
    (hbind : bindExternalParam selector calldata headSize baseOffset headOffset param =
      some bindings) :
    ∃ word value,
      externalWordAt? selector calldata headOffset = some word ∧
        decodeSupportedParamWord param.ty word = some value ∧
        bindings = [(param.name, value)] := by
  cases hword : externalWordAt? selector calldata headOffset with
  | some word =>
      obtain ⟨value, hvalue⟩ := htotal word
      unfold bindExternalParam at hbind
      rw [hword] at hbind
      -- `Option.bind` on `some` reduces definitionally, so `hvalue` retypes directly.
      have hred : decodeSupportedParamWord param.ty =<< some word = some value := hvalue
      rw [hred] at hbind
      have hbind' : some [(param.name, value)] = some bindings := hbind
      exact ⟨word, value, rfl, hvalue, (Option.some.inj hbind').symm⟩
  | none =>
      exfalso
      have hshape : ∀ shape,
          decodeLengthPrefixedDynamicParam? selector calldata shape headSize baseOffset
            headOffset = none := by
        intro shape
        unfold decodeLengthPrefixedDynamicParam?
        rw [hword]
        rfl
      have hnone :
          bindExternalParam selector calldata headSize baseOffset headOffset param = none := by
        unfold bindExternalParam
        rw [hword]
        have hb : decodeSupportedParamWord param.ty =<< (none : Option Nat) = none := rfl
        rw [hb]
        cases hs : externalDynamicPayloadShape? param.ty with
        | some shape => simp [hshape shape]
        | none => by_cases hdyn : isDynamicParamType param.ty <;> simp [hdyn]
      rw [hnone] at hbind
      simp at hbind

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
  unfold decodeLengthPrefixedDynamicParam? at hdec
  cases hro : externalWordAt? selector calldata headOffset with
  | none => rw [hro] at hdec; simp at hdec
  | some relativeOffset =>
      rw [hro] at hdec
      simp only [Option.bind_eq_bind, Option.bind] at hdec
      by_cases hlt : relativeOffset < headSize
      · simp [hlt] at hdec
      · rw [if_neg hlt] at hdec
        by_cases hgt : baseOffset + relativeOffset + 32 > externalCalldataSize calldata
        · simp [hgt] at hdec
        · rw [if_neg hgt] at hdec
          cases hlen : externalWordAt? selector calldata (baseOffset + relativeOffset) with
          | none => rw [hlen] at hdec; simp at hdec
          | some length =>
              rw [hlen] at hdec
              simp only [DynamicPayloadShape.fitsLength] at hdec
              by_cases hfit :
                  length ≤ externalCalldataSize calldata - (baseOffset + relativeOffset + 32)
              · rw [if_pos (by simpa using hfit)] at hdec
                cases hdec
                refine ⟨rfl, ?_, ?_, hlen, hfit, rfl, rfl, rfl, rfl⟩
                · show headSize ≤ relativeOffset
                  omega
                · show baseOffset + relativeOffset + 32 ≤ externalCalldataSize calldata
                  omega
              · rw [if_neg (by simpa using hfit)] at hdec
                simp at hdec

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
  have hdecode :
      decodeSupportedParamWord ParamType.bytes =<<
        externalWordAt? selector calldata headOffset = none := by
    cases externalWordAt? selector calldata headOffset <;> rfl
  unfold bindExternalParam at hbind
  rw [hdecode] at hbind
  simp only [externalDynamicPayloadShape?] at hbind
  cases hdec : decodeLengthPrefixedDynamicParam? selector calldata
      DynamicPayloadShape.bytesLike headSize baseOffset headOffset with
  | none => rw [hdec] at hbind; simp at hbind
  | some decoded =>
      rw [hdec] at hbind
      simp only [Option.bind_eq_bind, Option.bind, Option.some.injEq] at hbind
      obtain ⟨hro, hheadBound, htailBound, hlen, hfit, habs, htailHead, htailRem, hdata⟩ :=
        decodeLengthPrefixedDynamicParam?_bytesLike_eq_some_inv hdec
      refine ⟨decoded.relativeOffset, decoded.length,
        hro, hheadBound, htailBound, hlen, hfit, ?_⟩
      rw [← hbind]
      unfold dynamicParamBindings
      rw [habs, htailHead, htailRem, hdata]

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

/-- Static tuples are not expanded by the current semantic external-parameter
binder. Generated loaders can emit member bindings for static tuples, but
`bindExternalParam` only binds scalar heads and dynamic-shape metadata today. -/
theorem bindExternalParam_staticTuple_eq_none
    {selector : Nat} {calldata : List Nat} {headSize baseOffset headOffset : Nat}
    {name : String} {elemTys : List ParamType}
    (hstatic : isDynamicParamTypeList elemTys = false) :
    bindExternalParam selector calldata headSize baseOffset headOffset
      { name := name, ty := ParamType.tuple elemTys } = none := by
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

end DynamicAbi

end Compiler.CompilationModel

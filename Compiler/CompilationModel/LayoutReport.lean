import Compiler.CompilationModel.Types
import Compiler.CompilationModel.AbiHelpers
import Compiler.CompilationModel.LayoutValidation
import Compiler.Json

namespace Compiler.CompilationModel

open Compiler.Json

private def jsonNat (n : Nat) : String :=
  toString n

private def jsonOption (render : α → String) : Option α → String
  | some value => render value
  | none => "null"

private def mappingKeyTypeString : MappingKeyType → String
  | .address => "address"
  | .uint256 => "uint256"
  | .bytes32 => "bytes32"

private def structMemberTypeString : StructMemberType → String
  | .uint256 => "uint256"
  | .uint16 => "uint16"
  | .address => "address"
  | .bool => "bool"
  | .bytes32 => "bytes32"

private def mappingKeysJson (keys : List MappingKeyType) : String :=
  jsonArray (keys.map (fun keyType => jsonString (mappingKeyTypeString keyType)))

private def packedBitsJson (packed : PackedBits) : String :=
  jsonObject [
    ("offset", jsonNat packed.offset),
    ("width", jsonNat packed.width)
  ]

private def structMemberJson (member : StructMember) : String :=
  jsonObject [
    ("name", jsonString member.name),
    ("type", jsonString (structMemberTypeString member.ty)),
    ("wordOffset", jsonNat member.wordOffset),
    ("packedBits", jsonOption packedBitsJson member.packed)
  ]

private def fieldTypeJson : FieldType → String
  | .uint256 =>
      jsonObject [("kind", jsonString "uint256")]
  | .address =>
      jsonObject [("kind", jsonString "address")]
  | .fixedArrayUint128 size =>
      jsonObject [("kind", jsonString "fixedArrayUint128"), ("size", jsonNat size)]
  | .adt name maxFields =>
      jsonObject [
        ("kind", jsonString "adt"),
        ("name", jsonString name),
        ("maxFields", jsonNat maxFields)
      ]
  | .dynamicArray elemType =>
      jsonObject [
        ("kind", jsonString "dynamicArray"),
        ("elemType", jsonString (paramTypeToSolidityString (storageArrayElemTypeToParamType elemType)))
      ]
  | .mappingTyped mt =>
      jsonObject [
        ("kind", jsonString "mapping"),
        ("keys", mappingKeysJson (mappingTypeKeyTypes mt)),
        ("valueKind", jsonString "uint256")
      ]
  | .mappingStruct keyType members =>
      jsonObject [
        ("kind", jsonString "mappingStruct"),
        ("keys", jsonArray [jsonString (mappingKeyTypeString keyType)]),
        ("members", jsonArray (members.map structMemberJson))
      ]
  | .mappingStruct2 outer inner members =>
      jsonObject [
        ("kind", jsonString "mappingStruct"),
        ("keys", jsonArray [jsonString (mappingKeyTypeString outer), jsonString (mappingKeyTypeString inner)]),
        ("members", jsonArray (members.map structMemberJson))
      ]

private def reservedSlotRangeJson (range : ReservedSlotRange) : String :=
  jsonObject [
    ("start", jsonNat range.start),
    ("end", jsonNat range.end_)
  ]

private def slotAliasRangeJson (range : SlotAliasRange) : String :=
  jsonObject [
    ("sourceStart", jsonNat range.sourceStart),
    ("sourceEnd", jsonNat range.sourceEnd),
    ("targetStart", jsonNat range.targetStart)
  ]

private def fieldLocationKind (field : Field) : String :=
  if field.isTransient then "transient" else "persistent"

private def fieldWriteSlots (field : Field) (bases : List Nat) : List Nat :=
  let words := match field.ty with
    | .fixedArrayUint128 size => max 1 ((size + 1) / 2)
    | _ => 1
  dedupNatPreserve <| bases.flatMap fun base =>
    (List.range words).map fun offset =>
      (base + offset) % Compiler.Constants.evmModulus

private def fieldJson (declaredField effectiveField : Field) (idx : Nat) : String :=
  let canonicalSlot := declaredField.slot.getD idx
  let effectiveAliasSlots := effectiveField.aliasSlots
  jsonObject [
    ("name", jsonString declaredField.name),
    ("declaredSlot", jsonOption jsonNat declaredField.slot),
    ("canonicalSlot", jsonNat canonicalSlot),
    ("declaredAliasSlots", jsonArray (declaredField.aliasSlots.map jsonNat)),
    ("effectiveAliasSlots", jsonArray (effectiveAliasSlots.map jsonNat)),
    ("writeSlots", jsonArray ((fieldWriteSlots declaredField (canonicalSlot :: effectiveAliasSlots)).map jsonNat)),
    ("type", fieldTypeJson declaredField.ty),
    ("packedBits", jsonOption packedBitsJson declaredField.packedBits),
    ("isTransient", if declaredField.isTransient then "true" else "false"),
    ("locationKind", jsonString (fieldLocationKind declaredField))
  ]

private def immutableJson (imm : ImmutableSpec) : String :=
  jsonObject [
    ("name", jsonString imm.name),
    ("type", jsonString (paramTypeToSolidityString imm.ty)),
    ("storageFootprint", jsonNat 0),
    ("kind", jsonString "bytecodeImmutable")
  ]

/-! ### Storage families and non-alias certificate (#1966)

Each storage field becomes a "family" — the set of storage locations the
field can occupy at runtime. Plain scalars occupy a single declared slot;
mapping families occupy keccak-derived locations parameterised by their
key shape; nested mapping families nest a second keccak; mapping-struct
families add a bounded word offset to the keccak base. The certificate
records the *derivation kind*, the *root slot*, the *keccak preimage
shape* (when applicable), and any *struct-offset range*, so a downstream
proof obligation can replace the global keccak-injectivity boundary with
local per-family obligations and machine-checkable claims for the
finite, declared subset. -/

private def familyKindString : FieldType → String
  | .uint256 | .address | .adt _ _ => "scalar"
  | .fixedArrayUint128 _ => "fixedArray"
  | .dynamicArray _ => "dynamicArray"
  | .mappingTyped mt =>
      if (mappingTypeKeyTypes mt).length ≥ 2 then "nestedMapping" else "mapping"
  | .mappingStruct _ _ => "mappingStruct"
  | .mappingStruct2 _ _ _ => "nestedMappingStruct"

/-- Symbolic keccak preimage description used as the per-family
    non-collision justification. `null` for plain scalars, where
    non-alias reduces to declared-slot distinctness. -/
private def familyKeccakPreimage : FieldType → Nat → String
  | .uint256, _ | .address, _ | .adt _ _, _ | .fixedArrayUint128 _, _ => "null"
  | .dynamicArray _, slot =>
      -- elements at keccak256(rootSlot) + i
      jsonString s!"keccak256(slot={slot})"
  | .mappingTyped mt, slot =>
      let keys := mappingTypeKeyTypes mt
      let keyStr := String.intercalate ", " (keys.map mappingKeyTypeString)
      if keys.length ≥ 2 then
        jsonString s!"keccak256(innerKey || keccak256(outerKey || slot={slot})) [keys: {keyStr}]"
      else
        jsonString s!"keccak256(key || slot={slot}) [keys: {keyStr}]"
  | .mappingStruct keyType _, slot =>
      jsonString s!"keccak256(key || slot={slot}) + wordOffset [keys: {mappingKeyTypeString keyType}]"
  | .mappingStruct2 outerKey innerKey _, slot =>
      jsonString s!"keccak256(innerKey || keccak256(outerKey || slot={slot})) + wordOffset [keys: {mappingKeyTypeString outerKey}, {mappingKeyTypeString innerKey}]"

/-- Maximum struct word offset for mapping-struct families, or `null`. -/
private def familyStructWordRange : FieldType → String
  | .mappingStruct _ members | .mappingStruct2 _ _ members =>
      let maxOffset := members.foldl (fun acc m => Nat.max acc m.wordOffset) 0
      jsonObject [("min", jsonNat 0), ("maxInclusive", jsonNat maxOffset)]
  | _ => "null"

private def storageFamilyJson (declaredField : Field) (idx : Nat) : String :=
  let canonicalSlot := declaredField.slot.getD idx
  jsonObject [
    ("name", jsonString declaredField.name),
    ("locationKind", jsonString (fieldLocationKind declaredField)),
    ("kind", jsonString (familyKindString declaredField.ty)),
    ("rootSlot", jsonNat canonicalSlot),
    ("keccakPreimage", familyKeccakPreimage declaredField.ty canonicalSlot),
    ("structWordRange", familyStructWordRange declaredField.ty)
  ]

/-- Pairwise non-alias claim: an unordered pair of family names paired
    with a *justification* the obligation discharger should use:

    - `distinctScalarSlots`  — both are scalar families whose *effective
      write slot sets* (canonical slot ∪ `aliasSlots` ∪
      `slotAliasRanges`-derived aliases) are disjoint; the claim is a
      closed-form finite decision the proof side discharges with `decide`.
    - `writeSetsOverlap`     — both are scalar families but their
      effective write slot sets intersect; this is a real aliasing
      conflict the certificate must surface rather than silently assert
      `distinctScalarSlots` for (Bugbot #1967).
    - `keccakDomainScalar`   — one is keccak-derived, the other a scalar
      at a declared slot < 2^32 (say); the claim assumes keccak digest >
      maxDeclaredSlot, which is a standard preimage assumption.
    - `keccakPreimageDistinct` — both are keccak-derived families; the
      claim assumes keccak256 is injective on the disjoint preimage
      shapes (the per-family `keccakPreimage` strings differ).
    - `sameFamilyDistinctKey` — same family, different keys: assumes
      keccak256 injectivity on keys.

    The compiler-side artifact emits the claims as data; the proof side
    discharges them via either a `decide`/`native_decide` lemma (for the
    finite scalar subset) or a named local keccak assumption. -/
private def isKeccakDerivedFamily : FieldType → Bool
  | .uint256 | .address | .adt _ _ | .fixedArrayUint128 _ => false
  | _ => true

/-- Effective scalar write slot set for a single field: the declared/derived
    canonical slot union the field's own `aliasSlots` and any
    `slotAliasRanges`-derived aliases. This is the set of storage words the
    field *actually writes to* at runtime, so it is the set the pairwise
    non-alias certificate must compare against. -/
private def effectiveScalarWriteSlots
    (f : Field) (idx : Nat) (aliasRanges : List SlotAliasRange) : List Nat :=
  let canonical := f.slot.getD idx
  let mergedAliases := dedupNatPreserve
    (f.aliasSlots ++ derivedAliasSlotsForSource canonical aliasRanges)
  fieldWriteSlots f (canonical :: mergedAliases)

/-- Predicate: do two scalar fields share any effective write slot?
    Two scalars only truly non-alias when their effective write slot sets
    are disjoint; the declared slots alone are insufficient because
    `aliasSlots` and `slotAliasRanges` can still fold them onto the same
    canonical word. -/
private def scalarWriteSetsOverlap
    (a b : Field) (idxA idxB : Nat) (aliasRanges : List SlotAliasRange) : Bool :=
  if a.isTransient != b.isTransient then false
  else
    let writeA := effectiveScalarWriteSlots a idxA aliasRanges
    let writeB := effectiveScalarWriteSlots b idxB aliasRanges
    writeA.any (fun s => writeB.contains s)

/-- Justification for a pairwise non-alias claim. Both the family kinds and
    the effective scalar write sets feed into the choice: when two scalar
    families have overlapping write slot sets the certificate must report a
    real aliasing conflict (`writeSetsOverlap`) rather than assert a
    decidable `distinctScalarSlots` claim the proof side would happily
    discharge. -/
private def nonAliasJustification
    (a b : Field) (idxA idxB : Nat) (aliasRanges : List SlotAliasRange) : String :=
  let aKeccak := isKeccakDerivedFamily a.ty
  let bKeccak := isKeccakDerivedFamily b.ty
  if !aKeccak && !bKeccak then
    if scalarWriteSetsOverlap a b idxA idxB aliasRanges then
      "writeSetsOverlap"
    else
      "distinctScalarSlots"
  else if aKeccak && bKeccak then "keccakPreimageDistinct"
  else "keccakDomainScalar"

private def nonAliasClaimJson (a b : Field) (idxA idxB : Nat)
    (aliasRanges : List SlotAliasRange) : String :=
  let slotA := a.slot.getD idxA
  let slotB := b.slot.getD idxB
  let writeA := effectiveScalarWriteSlots a idxA aliasRanges
  let writeB := effectiveScalarWriteSlots b idxB aliasRanges
  jsonObject [
    ("a", jsonString a.name),
    ("b", jsonString b.name),
    ("aSlot", jsonNat slotA),
    ("bSlot", jsonNat slotB),
    ("aLocationKind", jsonString (fieldLocationKind a)),
    ("bLocationKind", jsonString (fieldLocationKind b)),
    ("aWriteSlots", jsonArray (writeA.map jsonNat)),
    ("bWriteSlots", jsonArray (writeB.map jsonNat)),
    ("justification", jsonString (nonAliasJustification a b idxA idxB aliasRanges))
  ]

/-- Build the list of unordered pairwise non-alias claims for a contract. -/
private def nonAliasClaimsJson (fields : List Field)
    (aliasRanges : List SlotAliasRange) : List String :=
  let indexed := fields.zipIdx
  let rec go : List (Field × Nat) → List (Field × Nat) → List String
    | [], _ => []
    | (a, ai) :: rest, _all =>
        let here := rest.map (fun (b, bi) => nonAliasClaimJson a b ai bi aliasRanges)
        here ++ go rest _all
  go indexed indexed

/-- Render a machine-readable storage layout report for upgrade/layout auditing.

    Includes the per-contract `storageFamilies` and `nonAliasClaims` sections
    (#1966) so reviewers can replace a global keccak-injectivity boundary
    with per-family local obligations and decide the declared-scalar subset
    by finite case analysis. -/
def emitLayoutReportJson (specs : List CompilationModel) : String :=
  jsonObject [
    ("contracts", jsonArray (specs.map contractJson))
  ]
where
  contractJson (spec : CompilationModel) : String :=
    let effectiveFields := applySlotAliasRanges spec.fields spec.slotAliasRanges
    let fieldsJson :=
      (spec.fields.zip effectiveFields).zipIdx.map fun ((declaredField, effectiveField), idx) =>
        fieldJson declaredField effectiveField idx
    let familiesJson :=
      spec.fields.zipIdx.map fun (declaredField, idx) =>
        storageFamilyJson declaredField idx
    let claimsJson := nonAliasClaimsJson spec.fields spec.slotAliasRanges
    let nsField := match spec.storageNamespace with
      | some ns => jsonString (toString ns)
      | none => "null"
    jsonObject [
      ("contract", jsonString spec.name),
      ("storageNamespace", nsField),
      ("fields", jsonArray fieldsJson),
      ("immutables", jsonArray (spec.immutables.map immutableJson)),
      ("storageFamilies", jsonArray familiesJson),
      ("nonAliasClaims", jsonArray claimsJson),
      ("reservedSlotRanges", jsonArray (spec.reservedSlotRanges.map reservedSlotRangeJson)),
      ("slotAliasRanges", jsonArray (spec.slotAliasRanges.map slotAliasRangeJson))
    ]

end Compiler.CompilationModel

import Compiler.Proofs.IRGeneration.SupportedFragment
import Compiler.Proofs.IRGeneration.IRInterpreter
import Compiler.CompilationModel.AbiHelpers
import Compiler.CompilationModel.Dispatch
import Compiler.CompilationModel.UsageAnalysis
import Compiler.CompilationModel.SelectorInteropHelpers
import Compiler.TypedIRCompilerCorrectness

set_option linter.deprecated false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.CompilationModel

/-- ABI parameter types admitted by the first whole-contract Layer 2 fragment.
Only single-head-word scalars are included for the initial generic theorem. -/
def SupportedExternalScalarParamType : ParamType → Prop
  | .uint256 | .int256 | .uint8 | .uint16 | .uintN _ | .intN _ | .bytesN _
  | .address | .bytes32 | .bool => True
  | _ => False

/-- Side condition on a dynamic array's element type: the stride literal the
loader divides the remaining tail by must be representable as an EVM word.
Below `2 ^ 256` the emitted `div` agrees with `Nat` division, so the generated
revert guard and `DynamicPayloadShape.fitsLength` accept exactly the same
lengths; at or above it the emitted `div` would saturate to `0` and the two
would diverge. `dynamicArrayElementStrideWords` is positive, so this also rules
out the EVM's division-by-zero convention. -/
def ExternalArrayStrideFitsWord (elemTy : ParamType) : Prop :=
  32 * dynamicArrayElementStrideWords elemTy < Compiler.Constants.evmModulus

/-- ABI parameter types admitted by external dispatch, widened past the
single-head-word scalars to every dynamic parameter whose head contribution is a
single relative tail offset (verity#2085).

None of these is decodable by `decodeSupportedParamWord`: they have no
single-word value. Their head word is a relative tail offset, and the generated
calldata loader binds locals that `DynamicAbi.bindExternalParam` reproduces
semantically. Two shapes occur:

* Length-prefixed (`bytes`, `string`, `T[]`) — the offset points at a length
  word, and the loader binds six locals (`_offset`, `_abs_offset`, `_length`,
  `_tail_head_end`, `_tail_remaining`, `_data_offset`). `string` is encoded
  byte-for-byte like `bytes`, so it reuses the same loader and binder lemmas.
  Arrays additionally carry `ExternalArrayStrideFitsWord`.
* Length-word-free composites (a `tuple` with a dynamic member, or a
  `fixedArray` of such) — the offset points straight at the composite's own head
  area, and the loader binds three locals (`_offset`, `_abs_offset`,
  `_data_offset`).

*Statically* sized composites are deliberately excluded: their head is wider
than one word, so they would break `supportedExternalParamType_headSize_eq_32`,
and `bindExternalParam` returns `none` for them anyway. `newtypeOf` is excluded
for a different reason: the emitter erases it to its base type while the binder
does not, so admitting it would relate two different loaders.

Consumers that need an actual scalar head word — the native-backend
static-scalar bridge and the legacy Yul compatibility witnesses — keep requiring
`SupportedExternalScalarParamType`. -/
def SupportedExternalParamType : ParamType → Prop
  | .uint256 | .int256 | .uint8 | .uint16 | .uintN _ | .intN _ | .bytesN _
  | .address | .bytes32 | .bool | .bytes | .string => True
  | .array elemTy => ExternalArrayStrideFitsWord elemTy
  | .fixedArray elemTy _ => isDynamicParamType elemTy = true
  | .tuple elemTys => isDynamicParamTypeList elemTys = true
  | _ => False

theorem SupportedExternalParamType_of_scalar {ty : ParamType}
    (hscalar : SupportedExternalScalarParamType ty) :
    SupportedExternalParamType ty := by
  cases ty <;> simp [SupportedExternalScalarParamType] at hscalar <;>
    simp [SupportedExternalParamType]

theorem SupportedExternalParamType_bytes :
    SupportedExternalParamType ParamType.bytes := trivial

theorem SupportedExternalParamType_string :
    SupportedExternalParamType ParamType.string := trivial

theorem SupportedExternalParamType_array {elemTy : ParamType}
    (hstride : ExternalArrayStrideFitsWord elemTy) :
    SupportedExternalParamType (ParamType.array elemTy) := hstride

/-- Every single-word element type has stride `1`, so word arrays — `uint256[]`,
`address[]`, `bytes32[]`, … — are admitted unconditionally. -/
theorem SupportedExternalParamType_wordArray {elemTy : ParamType}
    (hword : isSingleWordStaticParamType elemTy = true) :
    SupportedExternalParamType (ParamType.array elemTy) := by
  show ExternalArrayStrideFitsWord elemTy
  rw [ExternalArrayStrideFitsWord,
    dynamicArrayElementStrideWords_eq_one_of_singleWordStatic hword]
  simp [Compiler.Constants.evmModulus]

theorem SupportedExternalParamType_dynamicFixedArray {elemTy : ParamType} {n : Nat}
    (hdynamic : isDynamicParamType elemTy = true) :
    SupportedExternalParamType (ParamType.fixedArray elemTy n) := hdynamic

theorem SupportedExternalParamType_dynamicTuple {elemTys : List ParamType}
    (hdynamic : isDynamicParamTypeList elemTys = true) :
    SupportedExternalParamType (ParamType.tuple elemTys) := hdynamic

/-- The widened admission set, as the case split every downstream
calldata-loading execution lemma performs. The composite constructors are named
individually rather than folded into one `isLengthPrefixedDynamicShape = false`
disjunct because `genSingleParamLoad` dispatches on the constructor. -/
theorem supportedExternalParamType_cases {ty : ParamType}
    (hsupported : SupportedExternalParamType ty) :
    SupportedExternalScalarParamType ty ∨
      ty = ParamType.bytes ∨
      ty = ParamType.string ∨
      (∃ elemTy, ty = ParamType.array elemTy ∧ ExternalArrayStrideFitsWord elemTy) ∨
      (∃ elemTy n, ty = ParamType.fixedArray elemTy n ∧ isDynamicParamType elemTy = true) ∨
      (∃ elemTys, ty = ParamType.tuple elemTys ∧ isDynamicParamTypeList elemTys = true) := by
  cases ty <;> simp [SupportedExternalParamType] at hsupported <;>
    simp_all [SupportedExternalScalarParamType]

/-- Widened parameter lists still have 32-byte ABI head words: every admitted
dynamic type contributes exactly one relative tail pointer to the head area. -/
theorem supportedExternalParamType_headSize_eq_32 {ty : ParamType}
    (hsupported : SupportedExternalParamType ty) : paramHeadSize ty = 32 := by
  cases ty <;> simp [SupportedExternalParamType] at hsupported <;>
    simp [paramHeadSize, isDynamicParamType, hsupported]

/-- Return profiles admitted by the first whole-contract Layer 2 fragment.
The initial theorem only targets zero-return or single-head-word-return entrypoints. -/
def SupportedExternalReturnProfile : List ParamType → Prop
  | [] => True
  | [ty] => SupportedExternalScalarParamType ty
  | _ => False

/-- Proof-side scalar-parameter predicate tied to the compiler's actual gating
function `isScalarParamType`. Mirrors the `eventParamScalarProofSupported` /
`eventParamScalarCompileSupported` pattern: instead of duplicating the case
list in the proof layer, the proof-side name delegates to the compile-side
Bool so the two cannot drift apart. The hand-restated `SupportedExternalScalarParamType`
Prop is retained for existing call sites; the agreement theorem
`SupportedExternalParamType_iff_externalParamScalarProofSupported` proves they
denote the same set of types. -/
def externalParamScalarProofSupported (ty : ParamType) : Bool :=
  isScalarParamType ty

/-- Compile-driven decision procedure for the widened external-parameter
admission set. The scalar half still delegates to the compiler's
`isScalarParamType`; the dynamic constructors admitted on top of it are named
explicitly, and their side conditions are phrased with the compiler's own
`dynamicArrayElementStrideWords` / `isDynamicParamType`, so any future
compiler-side change to dynamic-parameter routing shows up at the agreement
oracle below rather than drifting silently. -/
def externalParamProofSupported : ParamType → Bool
  | ParamType.bytes | ParamType.string => true
  | ParamType.array elemTy =>
      decide (32 * dynamicArrayElementStrideWords elemTy < Compiler.Constants.evmModulus)
  | ParamType.fixedArray elemTy _ => isDynamicParamType elemTy
  | ParamType.tuple elemTys => isDynamicParamTypeList elemTys
  | ty => isScalarParamType ty

/-- Proof-side scalar-return-profile predicate tied to the compiler's scalar
gating function. Encodes the "zero or one single-word return" envelope of
`SupportedExternalReturnProfile` while delegating the per-type decision to
the compiler's `isScalarParamType`. -/
def externalReturnProfileProofSupported : List ParamType → Bool
  | [] => true
  | [ty] => isScalarParamType ty
  | _ => false

def eventParamScalarProofSupported (ty : ParamType) : Bool :=
  eventParamScalarCompileSupported ty

def eventDefScalarProofSupported (eventDef : EventDef) : Bool :=
  eventDefScalarCompileSupported eventDef

/-- Proof-side catalog for source-shaped event declarations whose payloads are
handled by the compiler's ABI event encoder. This deliberately lives beside,
not inside, `eventEmissionProofSupported`: the existing semantic bridge still
requires scalar params because it proves exact word-by-word log execution.
All currently represented ABI `ParamType` constructors are source-shaped for
event declarations; per-statement validation still checks the stricter
argument-source requirements for dynamic payload copying/hashing. -/
def eventParamSourceShapeProofSupported (_ty : ParamType) : Bool := true

theorem eventParamSourceShapeProofSupported_of_scalar :
    ∀ {ty : ParamType},
      eventParamScalarProofSupported ty = true →
        eventParamSourceShapeProofSupported ty = true
  | _ty, _hsupport => rfl

/-- Agreement oracle: the hand-restated `SupportedExternalScalarParamType` Prop holds
iff the compile-driven `externalParamScalarProofSupported` Bool is `true`.
This is the meaning-preservation lemma for the conversion pattern: any future
relaxation/tightening of `isScalarParamType` becomes visible at the proof
boundary, instead of silently drifting from a hand-written enumeration. -/
theorem SupportedExternalParamType_iff_externalParamScalarProofSupported
    (ty : ParamType) :
    SupportedExternalScalarParamType ty ↔ externalParamScalarProofSupported ty = true := by
  cases ty <;>
    simp [SupportedExternalScalarParamType, externalParamScalarProofSupported,
      isScalarParamType]

/-- Agreement oracle for the widened admission set (verity#2085): the
hand-restated `SupportedExternalParamType` Prop holds iff the compile-driven
`externalParamProofSupported` Bool is `true`. -/
theorem SupportedExternalParamType_iff_externalParamProofSupported
    (ty : ParamType) :
    SupportedExternalParamType ty ↔ externalParamProofSupported ty = true := by
  cases ty <;>
    simp [SupportedExternalParamType, externalParamProofSupported, isScalarParamType,
      ExternalArrayStrideFitsWord]

/-- Agreement oracle for the return-profile shape. -/
theorem SupportedExternalReturnProfile_iff_externalReturnProfileProofSupported
    (returns : List ParamType) :
    SupportedExternalReturnProfile returns ↔
      externalReturnProfileProofSupported returns = true := by
  rcases returns with _ | ⟨ty, tail⟩
  · -- []
    simp [SupportedExternalReturnProfile, externalReturnProfileProofSupported]
  · rcases tail with _ | ⟨ty2, rest⟩
    · -- [ty]
      simp [SupportedExternalReturnProfile, externalReturnProfileProofSupported,
        SupportedExternalParamType_iff_externalParamScalarProofSupported,
        externalParamScalarProofSupported]
    · -- ty :: ty2 :: rest
      simp [SupportedExternalReturnProfile, externalReturnProfileProofSupported]

theorem eventDefScalarProofSupported_params_all
    {eventDef : EventDef}
    (hsupport : eventDefScalarProofSupported eventDef = true) :
    eventDef.params.all (fun param => eventParamScalarProofSupported param.ty) = true := by
  have hsplit :
      (∀ param ∈ eventDef.params, eventParamScalarProofSupported param.ty = true) ∧
        (eventDef.params.filter (fun param => param.kind == EventParamKind.indexed)).length ≤ 3 := by
    simpa [eventDefScalarProofSupported, eventDefScalarCompileSupported,
      eventParamScalarProofSupported, Bool.and_eq_true] using hsupport
  simpa using hsplit.1

theorem eventDefScalarProofSupported_indexed_length_le_three
    {eventDef : EventDef}
    (hsupport : eventDefScalarProofSupported eventDef = true) :
    (eventDef.params.filter (fun param => param.kind == EventParamKind.indexed)).length ≤ 3 := by
  have hsplit :
      (∀ param ∈ eventDef.params, eventParamScalarProofSupported param.ty = true) ∧
        (eventDef.params.filter (fun param => param.kind == EventParamKind.indexed)).length ≤ 3 := by
    simpa [eventDefScalarProofSupported, eventDefScalarCompileSupported,
      eventParamScalarProofSupported, Bool.and_eq_true] using hsupport
  exact hsplit.2

private theorem eventParamScalarProofSupported_eq_true_of_mem_all :
    ∀ {params : List EventParam} {param : EventParam},
      params.all (fun param => eventParamScalarProofSupported param.ty) = true →
        param ∈ params →
          eventParamScalarProofSupported param.ty = true
  | params, param, hall, hmem => by
      have hforall :
          ∀ candidate ∈ params, eventParamScalarProofSupported candidate.ty = true := by
        simpa using hall
      exact hforall param hmem

theorem eventParamScalarProofSupported_eq_true_of_eventDefScalarProofSupported
    {eventDef : EventDef}
    {param : EventParam}
    (hsupport : eventDefScalarProofSupported eventDef = true)
    (hmem : param ∈ eventDef.params) :
    eventParamScalarProofSupported param.ty = true :=
  eventParamScalarProofSupported_eq_true_of_mem_all
    (eventDefScalarProofSupported_params_all hsupport) hmem

theorem eventParamScalarProofSupported_eventIsDynamicType_eq_false :
    ∀ {ty : ParamType},
      eventParamScalarProofSupported ty = true →
        eventIsDynamicType ty = false
  | ty, hsupport => by
      cases ty <;>
        simp [eventParamScalarProofSupported, eventParamScalarCompileSupported,
          eventIsDynamicType, isDynamicParamType]
          at hsupport ⊢
      case newtypeOf name baseType =>
        have hbase :=
          eventParamScalarProofSupported_eventIsDynamicType_eq_false (ty := baseType) hsupport
        simpa [eventIsDynamicType] using hbase

theorem eventParamScalarProofSupported_eventHeadWordSize_eq_thirty_two :
    ∀ {ty : ParamType},
      eventParamScalarProofSupported ty = true →
        eventHeadWordSize ty = 32
  | ty, hsupport => by
      cases ty <;>
        simp [eventParamScalarProofSupported, eventParamScalarCompileSupported,
          eventHeadWordSize, paramHeadSize]
          at hsupport ⊢
      case newtypeOf name baseType =>
        have hbase :=
          eventParamScalarProofSupported_eventHeadWordSize_eq_thirty_two (ty := baseType) hsupport
        simpa [eventHeadWordSize] using hbase

theorem eventParamScalarProofSupported_ne_bytes
    {ty : ParamType}
    (hsupport : eventParamScalarProofSupported ty = true) :
    ty ≠ ParamType.bytes := by
  intro h; subst h; simp [eventParamScalarProofSupported,
    eventParamScalarCompileSupported] at hsupport

theorem eventParamScalarProofSupported_ne_string
    {ty : ParamType}
    (hsupport : eventParamScalarProofSupported ty = true) :
    ty ≠ ParamType.string := by
  intro h; subst h; simp [eventParamScalarProofSupported,
    eventParamScalarCompileSupported] at hsupport

theorem eventParamScalarProofSupported_ne_array
    {ty elemTy : ParamType}
    (hsupport : eventParamScalarProofSupported ty = true) :
    ty ≠ ParamType.array elemTy := by
  intro h; subst h; simp [eventParamScalarProofSupported,
    eventParamScalarCompileSupported] at hsupport

theorem eventParamScalarProofSupported_ne_fixedArray
    {ty elemTy : ParamType}
    {len : Nat}
    (hsupport : eventParamScalarProofSupported ty = true) :
    ty ≠ ParamType.fixedArray elemTy len := by
  intro h; subst h; simp [eventParamScalarProofSupported,
    eventParamScalarCompileSupported] at hsupport

theorem eventParamScalarProofSupported_ne_tuple
    {ty : ParamType}
    {members : List ParamType}
    (hsupport : eventParamScalarProofSupported ty = true) :
    ty ≠ ParamType.tuple members := by
  intro h; subst h; simp [eventParamScalarProofSupported,
    eventParamScalarCompileSupported] at hsupport

/-- Generous size ceiling on event scratch geometry. The compiled emit block
addresses scratch words with the wrapping `add` builtin, so the semantic
bridge needs every scratch word offset `k * 32` to stay strictly below
`2^256`; bounding the signature byte length and parameter count by `2^32`
keeps all offsets distinct mod `2^256` while admitting every realistic event. -/
def eventScratchSizeLimit : Nat := 2 ^ 32

def eventDefScratchBounded (eventDef : EventDef) : Bool :=
  decide ((bytesFromString (eventSignature eventDef)).length ≤ eventScratchSizeLimit) &&
    decide (eventDef.params.length ≤ eventScratchSizeLimit)

def eventDefSourceShapeProofSupported (eventDef : EventDef) : Bool :=
  eventDef.params.all (fun param => eventParamSourceShapeProofSupported param.ty) &&
    decide ((eventDef.params.filter (fun param => param.kind == EventParamKind.indexed)).length ≤ 3) &&
    eventDefScratchBounded eventDef

theorem eventDefSourceShapeProofSupported_of_scalar
    {eventDef : EventDef}
    (hscalar : eventDefScalarProofSupported eventDef = true)
    (hscratch : eventDefScratchBounded eventDef = true) :
    eventDefSourceShapeProofSupported eventDef = true := by
  have hparams :
      eventDef.params.all (fun param => eventParamSourceShapeProofSupported param.ty) = true := by
    apply List.all_eq_true.mpr
    intro param hmem
    exact eventParamSourceShapeProofSupported_of_scalar
      (eventParamScalarProofSupported_eq_true_of_eventDefScalarProofSupported hscalar hmem)
  have hindexed := eventDefScalarProofSupported_indexed_length_le_three hscalar
  simp [eventDefSourceShapeProofSupported, hparams, hscratch, hindexed]

private def dynamicTupleEventSmoke : EventDef :=
  { name := "CompositeEvent"
    params := [
      { name := "id", ty := .bytes32, kind := .indexed },
      { name := "payload", ty := .tuple [.uint256, .bytes], kind := .unindexed },
      { name := "values", ty := .array .uint256, kind := .unindexed },
      { name := "note", ty := .bytes, kind := .unindexed }
    ] }

private def staticStructEventSmoke : EventDef :=
  { name := "CreateMarket"
    params := [
      { name := "id", ty := .bytes32, kind := .indexed },
      { name := "market"
        ty := .tuple [.address, .address, .address, .address, .uint256]
        kind := .unindexed }
    ] }

private def indexedDynamicStructArrayEventSmoke : EventDef :=
  { name := "IndexedDynamicStructArray"
    params := [
      { name := "payload"
        ty := .array (.tuple [.uint256, .bytes])
        kind := .indexed }
    ] }

private def fixedArrayAndAdtEventSmoke : EventDef :=
  { name := "FixedArrayAndAdt"
    params := [
      { name := "fixed", ty := .fixedArray .address 2, kind := .indexed },
      { name := "choice", ty := .adt "Choice" 2, kind := .unindexed }
    ] }

example : eventDefSourceShapeProofSupported dynamicTupleEventSmoke = true := by
  rfl

example : eventDefSourceShapeProofSupported staticStructEventSmoke = true := by
  rfl

example :
    eventDefSourceShapeProofSupported indexedDynamicStructArrayEventSmoke = true := by
  rfl

example : eventDefSourceShapeProofSupported fixedArrayAndAdtEventSmoke = true := by
  rfl

/-- Event arguments admitted by the semantic bridge: atomic word-pure
expressions (literals, scope variables, transaction context). The compiled
emit block evaluates argument expressions *after* the signature words have
been stored into scratch memory, while source semantics resolves arguments
*before* the emit takes effect; atomic arguments cannot observe memory (or
the block-local scratch bindings), so the two evaluation points agree. -/
def exprEventArgAtomic : Expr → Bool
  | .literal _ | .param _ | .localVar _ | .caller | .contractAddress
  | .txOrigin | .msgValue | .blockTimestamp | .blockNumber | .chainid
  | .blobbasefee | .calldatasize => true
  | .immutable _ => false
  | _ => false

def eventEmissionProofSupported
    (events : List EventDef) (eventName : String) (args : List Expr) : Bool :=
  match events.find? (·.name == eventName) with
  | none => false
  | some eventDef =>
      eventDefScalarProofSupported eventDef &&
        decide (args.length = eventDef.params.length) &&
        eventDefScratchBounded eventDef &&
        args.all exprEventArgAtomic

theorem exists_eventDef_of_eventEmissionProofSupported
    {events : List EventDef}
    {eventName : String}
    {args : List Expr}
    (hsupport : eventEmissionProofSupported events eventName args = true) :
    ∃ eventDef,
      events.find? (·.name == eventName) = some eventDef ∧
      eventDefScalarProofSupported eventDef = true ∧
      args.length = eventDef.params.length := by
  unfold eventEmissionProofSupported at hsupport
  cases hfind : events.find? (fun x => x.name == eventName) with
  | none =>
      simp [hfind] at hsupport
  | some eventDef =>
      simp [hfind, Bool.and_eq_true] at hsupport
      exact ⟨eventDef, rfl, hsupport.1.1.1, hsupport.1.1.2⟩

theorem eventDefScratchBounded_of_eventEmissionProofSupported
    {events : List EventDef}
    {eventName : String}
    {args : List Expr}
    {eventDef : EventDef}
    (hsupport : eventEmissionProofSupported events eventName args = true)
    (hfind : events.find? (·.name == eventName) = some eventDef) :
    eventDefScratchBounded eventDef = true := by
  unfold eventEmissionProofSupported at hsupport
  rw [hfind] at hsupport
  simp [Bool.and_eq_true] at hsupport
  exact hsupport.1.2

theorem args_all_atomic_of_eventEmissionProofSupported
    {events : List EventDef}
    {eventName : String}
    {args : List Expr}
    (hsupport : eventEmissionProofSupported events eventName args = true) :
    args.all exprEventArgAtomic = true := by
  unfold eventEmissionProofSupported at hsupport
  cases hfind : events.find? (fun x => x.name == eventName) with
  | none => simp [hfind] at hsupport
  | some eventDef =>
      rw [hfind] at hsupport
      simp [Bool.and_eq_true] at hsupport
      simpa using hsupport.2

theorem eventEmissionProofSupported_find?_isSome
    {events : List EventDef}
    {eventName : String}
    {args : List Expr}
    (hsupport : eventEmissionProofSupported events eventName args = true) :
    (events.find? (·.name == eventName)).isSome = true := by
  rcases exists_eventDef_of_eventEmissionProofSupported hsupport with
    ⟨eventDef, hfind, _, _⟩
  simp [hfind]

theorem eventDefScalarProofSupported_eq_true_of_eventEmissionProofSupported
    {events : List EventDef}
    {eventName : String}
    {args : List Expr}
    {eventDef : EventDef}
    (hsupport : eventEmissionProofSupported events eventName args = true)
    (hfind : events.find? (·.name == eventName) = some eventDef) :
    eventDefScalarProofSupported eventDef = true := by
  rcases exists_eventDef_of_eventEmissionProofSupported hsupport with
    ⟨selected, hselected, hscalar, _⟩
  rw [hfind] at hselected
  injection hselected with heq
  subst heq
  exact hscalar

theorem eventParamScalarProofSupported_eq_true_of_eventEmissionProofSupported
    {events : List EventDef}
    {eventName : String}
    {args : List Expr}
    {eventDef : EventDef}
    {param : EventParam}
    (hsupport : eventEmissionProofSupported events eventName args = true)
    (hfind : events.find? (·.name == eventName) = some eventDef)
    (hmem : param ∈ eventDef.params) :
    eventParamScalarProofSupported param.ty = true :=
  eventParamScalarProofSupported_eq_true_of_eventDefScalarProofSupported
    (eventDefScalarProofSupported_eq_true_of_eventEmissionProofSupported hsupport hfind)
    hmem

theorem eventEmissionProofSupported_indexed_length_le_three
    {events : List EventDef}
    {eventName : String}
    {args : List Expr}
    {eventDef : EventDef}
    (hsupport : eventEmissionProofSupported events eventName args = true)
    (hfind : events.find? (·.name == eventName) = some eventDef) :
    (eventDef.params.filter (fun param => param.kind == EventParamKind.indexed)).length ≤ 3 :=
  eventDefScalarProofSupported_indexed_length_le_three
    (eventDefScalarProofSupported_eq_true_of_eventEmissionProofSupported hsupport hfind)

theorem eventEmissionProofSupported_args_length
    {events : List EventDef}
    {eventName : String}
    {args : List Expr}
    {eventDef : EventDef}
    (hsupport : eventEmissionProofSupported events eventName args = true)
    (hfind : events.find? (·.name == eventName) = some eventDef) :
    args.length = eventDef.params.length := by
  rcases exists_eventDef_of_eventEmissionProofSupported hsupport with
    ⟨selected, hselected, _, hlen⟩
  rw [hfind] at hselected
  injection hselected with heq
  subst heq
  exact hlen

theorem eventEmissionProofSupported_param_eventIsDynamicType_eq_false
    {events : List EventDef}
    {eventName : String}
    {args : List Expr}
    {eventDef : EventDef}
    {param : EventParam}
    (hsupport : eventEmissionProofSupported events eventName args = true)
    (hfind : events.find? (·.name == eventName) = some eventDef)
    (hmem : param ∈ eventDef.params) :
    eventIsDynamicType param.ty = false :=
  eventParamScalarProofSupported_eventIsDynamicType_eq_false
    (eventParamScalarProofSupported_eq_true_of_eventEmissionProofSupported
      hsupport hfind hmem)

theorem eventEmissionProofSupported_param_eventHeadWordSize_eq_thirty_two
    {events : List EventDef}
    {eventName : String}
    {args : List Expr}
    {eventDef : EventDef}
    {param : EventParam}
    (hsupport : eventEmissionProofSupported events eventName args = true)
    (hfind : events.find? (·.name == eventName) = some eventDef)
    (hmem : param ∈ eventDef.params) :
    eventHeadWordSize param.ty = 32 :=
  eventParamScalarProofSupported_eventHeadWordSize_eq_thirty_two
    (eventParamScalarProofSupported_eq_true_of_eventEmissionProofSupported
      hsupport hfind hmem)

theorem eventEmissionProofSupported_param_not_bytes
    {events : List EventDef}
    {eventName : String}
    {args : List Expr}
    {eventDef : EventDef}
    {param : EventParam}
    (hsupport : eventEmissionProofSupported events eventName args = true)
    (hfind : events.find? (·.name == eventName) = some eventDef)
    (hmem : param ∈ eventDef.params) :
    param.ty ≠ ParamType.bytes :=
  eventParamScalarProofSupported_ne_bytes
    (eventParamScalarProofSupported_eq_true_of_eventEmissionProofSupported
      hsupport hfind hmem)

theorem eventEmissionProofSupported_param_not_string
    {events : List EventDef}
    {eventName : String}
    {args : List Expr}
    {eventDef : EventDef}
    {param : EventParam}
    (hsupport : eventEmissionProofSupported events eventName args = true)
    (hfind : events.find? (·.name == eventName) = some eventDef)
    (hmem : param ∈ eventDef.params) :
    param.ty ≠ ParamType.string :=
  eventParamScalarProofSupported_ne_string
    (eventParamScalarProofSupported_eq_true_of_eventEmissionProofSupported
      hsupport hfind hmem)

theorem eventEmissionProofSupported_zippedWithSource_param_scalar
    {events : List EventDef}
    {eventName : String}
    {args : List Expr}
    {eventDef : EventDef}
    {α : Type}
    {compiledArgs : List α}
    {entry : EventParam × Expr × α}
    (hsupport : eventEmissionProofSupported events eventName args = true)
    (hfind : events.find? (·.name == eventName) = some eventDef)
    (hmem :
      entry ∈
        ((eventDef.params.zip args).zip compiledArgs |>.map
          (fun ((p, srcExpr), argExpr) => (p, srcExpr, argExpr)))) :
    eventParamScalarProofSupported entry.1.ty = true := by
  rcases entry with ⟨param, srcExpr, argExpr⟩
  simp only [List.mem_map] at hmem
  rcases hmem with ⟨sourceEntry, hsourceMem, hentry⟩
  rcases sourceEntry with ⟨paramArg, compiledArg⟩
  rcases paramArg with ⟨sourceParam, sourceExpr⟩
  cases hentry
  have hparamArgMem : (sourceParam, sourceExpr) ∈ eventDef.params.zip args := by
    exact (List.of_mem_zip hsourceMem).1
  have hparamMem : sourceParam ∈ eventDef.params := by
    exact (List.of_mem_zip hparamArgMem).1
  exact eventParamScalarProofSupported_eq_true_of_eventEmissionProofSupported
    hsupport hfind hparamMem

theorem eventEmissionProofSupported_zippedWithSource_eventIsDynamicType_eq_false
    {events : List EventDef}
    {eventName : String}
    {args : List Expr}
    {eventDef : EventDef}
    {α : Type}
    {compiledArgs : List α}
    {entry : EventParam × Expr × α}
    (hsupport : eventEmissionProofSupported events eventName args = true)
    (hfind : events.find? (·.name == eventName) = some eventDef)
    (hmem :
      entry ∈
        ((eventDef.params.zip args).zip compiledArgs |>.map
          (fun ((p, srcExpr), argExpr) => (p, srcExpr, argExpr)))) :
    eventIsDynamicType entry.1.ty = false :=
  eventParamScalarProofSupported_eventIsDynamicType_eq_false
    (eventEmissionProofSupported_zippedWithSource_param_scalar
      hsupport hfind hmem)

theorem eventEmissionProofSupported_zippedWithSource_eventHeadWordSize_eq_thirty_two
    {events : List EventDef}
    {eventName : String}
    {args : List Expr}
    {eventDef : EventDef}
    {α : Type}
    {compiledArgs : List α}
    {entry : EventParam × Expr × α}
    (hsupport : eventEmissionProofSupported events eventName args = true)
    (hfind : events.find? (·.name == eventName) = some eventDef)
    (hmem :
      entry ∈
        ((eventDef.params.zip args).zip compiledArgs |>.map
          (fun ((p, srcExpr), argExpr) => (p, srcExpr, argExpr)))) :
    eventHeadWordSize entry.1.ty = 32 :=
  eventParamScalarProofSupported_eventHeadWordSize_eq_thirty_two
    (eventEmissionProofSupported_zippedWithSource_param_scalar
      hsupport hfind hmem)

theorem eventEmissionProofSupported_zippedWithSource_unindexed_any_dynamic_false
    {events : List EventDef}
    {eventName : String}
    {args : List Expr}
    {eventDef : EventDef}
    {α : Type}
    (compiledArgs : List α)
    (hsupport : eventEmissionProofSupported events eventName args = true)
    (hfind : events.find? (·.name == eventName) = some eventDef) :
    ((((eventDef.params.zip args).zip compiledArgs |>.map
        (fun ((p, srcExpr), argExpr) => (p, srcExpr, argExpr))).filter
          (fun (p, _, _) => p.kind == EventParamKind.unindexed)).any
            (fun (p, _, _) => eventIsDynamicType p.ty)) = false := by
  apply List.any_eq_false.mpr
  intro entry hentry
  have hstatic :
      (match entry with
        | (p, _, _) => eventIsDynamicType p.ty) = false :=
    eventEmissionProofSupported_zippedWithSource_eventIsDynamicType_eq_false
      hsupport hfind (List.mem_filter.mp hentry).1
  simp [hstatic]

private theorem foldl_eventHeadWordSize_eq_thirty_two_mul_length
    {α : Type}
    {entries : List (EventParam × Expr × α)}
    (acc : Nat)
    (hhead :
      ∀ entry ∈ entries, eventHeadWordSize entry.1.ty = 32) :
    (entries.map (fun entry => eventHeadWordSize entry.1.ty)).foldl (· + ·) acc =
      acc + 32 * entries.length := by
  induction entries generalizing acc with
  | nil =>
      simp
  | cons entry rest ih =>
      have hentry : eventHeadWordSize entry.1.ty = 32 := hhead entry (by simp)
      have hrest :
          ∀ tailEntry ∈ rest, eventHeadWordSize tailEntry.1.ty = 32 := by
        intro tailEntry hmem
        exact hhead tailEntry (by simp [hmem])
      calc
        ((entry :: rest).map (fun entry => eventHeadWordSize entry.1.ty)).foldl (· + ·) acc
            = (rest.map (fun entry => eventHeadWordSize entry.1.ty)).foldl (· + ·)
                (acc + 32) := by simp [hentry]
        _ = (acc + 32) + 32 * rest.length := ih (acc + 32) hrest
        _ = acc + 32 * (entry :: rest).length := by
          simp [Nat.mul_succ, Nat.add_comm, Nat.add_assoc]

theorem eventEmissionProofSupported_zippedWithSource_unindexed_head_size
    {events : List EventDef}
    {eventName : String}
    {args : List Expr}
    {eventDef : EventDef}
    {α : Type}
    (compiledArgs : List α)
    (hsupport : eventEmissionProofSupported events eventName args = true)
    (hfind : events.find? (·.name == eventName) = some eventDef) :
    let zipped : List (EventParam × Expr × α) :=
      (eventDef.params.zip args).zip compiledArgs |>.map
        (fun ((p, srcExpr), argExpr) => (p, srcExpr, argExpr))
    let unindexed := zipped.filter (fun (p, _, _) => p.kind == EventParamKind.unindexed)
    (unindexed.map (fun (p, _, _) => eventHeadWordSize p.ty)).foldl (· + ·) 0 =
      32 * unindexed.length := by
  dsimp only
  simpa using
    foldl_eventHeadWordSize_eq_thirty_two_mul_length (α := α) (acc := 0)
      (entries :=
        (((eventDef.params.zip args).zip compiledArgs |>.map
          (fun ((p, srcExpr), argExpr) => (p, srcExpr, argExpr))).filter
            (fun (p, _, _) => p.kind == EventParamKind.unindexed)))
      (by
        intro entry hentry
        exact eventEmissionProofSupported_zippedWithSource_eventHeadWordSize_eq_thirty_two
          hsupport hfind (List.mem_filter.mp hentry).1)

theorem eventEmissionProofSupported_eventUnindexedHeadSize
    {events : List EventDef}
    {eventName : String}
    {args : List Expr}
    {eventDef : EventDef}
    (compiledArgs : List Compiler.Yul.YulExpr)
    (hsupport : eventEmissionProofSupported events eventName args = true)
    (hfind : events.find? (·.name == eventName) = some eventDef) :
    eventUnindexedHeadSize
        (eventUnindexedArgs (eventZippedWithSource eventDef args compiledArgs)) =
      32 * (eventUnindexedArgs (eventZippedWithSource eventDef args compiledArgs)).length := by
  simpa [eventUnindexedHeadSize, eventUnindexedArgs, eventZippedWithSource] using
    eventEmissionProofSupported_zippedWithSource_unindexed_head_size
      compiledArgs hsupport hfind

theorem eventEmissionProofSupported_eventHasUnindexedDynamicData_eq_false
    {events : List EventDef}
    {eventName : String}
    {args : List Expr}
    {eventDef : EventDef}
    (compiledArgs : List Compiler.Yul.YulExpr)
    (hsupport : eventEmissionProofSupported events eventName args = true)
    (hfind : events.find? (·.name == eventName) = some eventDef) :
    eventHasUnindexedDynamicData
        (eventUnindexedArgs (eventZippedWithSource eventDef args compiledArgs)) = false := by
  simpa [eventHasUnindexedDynamicData, eventUnindexedArgs, eventZippedWithSource] using
    eventEmissionProofSupported_zippedWithSource_unindexed_any_dynamic_false
      compiledArgs hsupport hfind

private theorem eventCompiledArgs_filter_kind_length_le_params_filter_kind
    {α : Type}
    (params : List EventParam)
    (args : List Expr)
    (compiledArgs : List α)
    (kind : EventParamKind) :
    ((List.filter
        (fun entry : EventParam × Expr × α => entry.1.kind == kind)
        (List.map
          (fun entry : (EventParam × Expr) × α => (entry.1.1, entry.1.2, entry.2))
          ((List.zip params args).zip compiledArgs))).length) ≤
      (params.filter (fun param => param.kind == kind)).length := by
  induction params generalizing args compiledArgs with
  | nil =>
      simp
  | cons param params ih =>
      cases args with
      | nil =>
          simp
      | cons arg args =>
          cases compiledArgs with
          | nil =>
              simp
          | cons compiledArg compiledArgs =>
              by_cases hkind : param.kind == kind
              · simp [hkind, ih args compiledArgs]
              · have htail := ih args compiledArgs
                simp [hkind]
                exact htail

theorem eventEmissionProofSupported_zippedWithSource_indexed_length_le_three
    {events : List EventDef}
    {eventName : String}
    {args : List Expr}
    {eventDef : EventDef}
    {α : Type}
    (compiledArgs : List α)
    (hsupport : eventEmissionProofSupported events eventName args = true)
    (hfind : events.find? (·.name == eventName) = some eventDef) :
    ((List.filter
        (fun entry : EventParam × Expr × α => entry.1.kind == EventParamKind.indexed)
        (List.map
          (fun entry : (EventParam × Expr) × α => (entry.1.1, entry.1.2, entry.2))
          ((List.zip eventDef.params args).zip compiledArgs))).length) ≤ 3 := by
  exact Nat.le_trans
    (eventCompiledArgs_filter_kind_length_le_params_filter_kind
      eventDef.params args compiledArgs EventParamKind.indexed)
    (eventEmissionProofSupported_indexed_length_le_three hsupport hfind)

theorem eventEmissionProofSupported_eventIndexedArgs_length_le_three
    {events : List EventDef}
    {eventName : String}
    {args : List Expr}
    {eventDef : EventDef}
    (compiledArgs : List Compiler.Yul.YulExpr)
    (hsupport : eventEmissionProofSupported events eventName args = true)
    (hfind : events.find? (·.name == eventName) = some eventDef) :
    (eventIndexedArgs (eventZippedWithSource eventDef args compiledArgs)).length ≤ 3 := by
  simpa [eventIndexedArgs, eventZippedWithSource] using
    eventEmissionProofSupported_zippedWithSource_indexed_length_le_three
      compiledArgs hsupport hfind

theorem eventLogFunction_mem_logBuiltins_of_le_three
    {indexedLength : Nat}
    (hle : indexedLength ≤ 3) :
    eventLogFunction indexedLength ∈ ["log1", "log2", "log3", "log4"] := by
  cases indexedLength with
  | zero =>
      simp [eventLogFunction]
  | succ n =>
      cases n with
      | zero =>
          simp [eventLogFunction]
      | succ n =>
          cases n with
          | zero =>
              simp [eventLogFunction]
          | succ n =>
              cases n with
              | zero =>
                  simp [eventLogFunction]
              | succ n =>
                  omega

theorem eventLogArgs_length
    (dataSizeExpr : Compiler.Yul.YulExpr)
    (indexedTopicParts : List (List Compiler.Yul.YulStmt × Compiler.Yul.YulExpr)) :
    (eventLogArgs dataSizeExpr indexedTopicParts).length =
      indexedTopicParts.length + 3 := by
  simp [eventLogArgs]

mutual
/-- Constructor body proofs are intentionally staged after initcode argument
decoding. Raw constructor calldata observations therefore remain outside the
current body-level support interface until the deploy-wrapper proof exists. -/
def exprTouchesUnsupportedConstructorRawCalldataSurface : Expr → Bool
  | .literal _ | .param _ | .immutable _ | .localVar _ | .caller | .contractAddress | .txOrigin
  | .chainid | .msgValue | .selfBalance | .baseFee | .gasPrice | .blockTimestamp | .blockNumber
  | .blobbasefee | .constructorArg _ | .returndataSize => false
  | .calldatasize => true
  | .storage _ | .storageAddr _ | .arrayLength _ | .memoryArrayLength _
  | .storageArrayLength _ => false
  | .logicalNot a | .bitNot a | .mload a | .tload a | .extcodesize a | .returndataOptionalBoolAt a =>
      exprTouchesUnsupportedConstructorRawCalldataSurface a
  | .calldataload _ =>
      true
  | .mapping _ a | .mappingWord _ a _ | .mappingPackedWord _ a _ _
  | .mappingUint _ a | .structMember _ a _ | .arrayElement _ a
  | .memoryArrayElement _ a
  | .arrayElementWord _ a _ _
  | .arrayElementDynamicWord _ a _
  | .arrayElementDynamicDataOffset _ a
  | .arrayElementDynamicMemberLength _ a _
  | .arrayElementDynamicMemberDataOffset _ a _
  | .storageArrayElement _ a =>
      exprTouchesUnsupportedConstructorRawCalldataSurface a
  | .paramDynamicMemberElement _ _ a =>
      exprTouchesUnsupportedConstructorRawCalldataSurface a
  | .arrayElementDynamicMemberElement _ a _ b =>
      exprTouchesUnsupportedConstructorRawCalldataSurface a ||
        exprTouchesUnsupportedConstructorRawCalldataSurface b
  | .add a b | .sub a b | .mul a b | .div a b | .mod a b
  | .eq a b | .ge a b | .gt a b | .lt a b | .le a b
  | .logicalAnd a b | .logicalOr a b | .shl a b | .shr a b
  | .bitAnd a b | .bitOr a b | .bitXor a b | .min a b | .max a b
  | .wMulDown a b | .wDivUp a b | .ceilDiv a b | .slt a b | .sgt a b
  | .sdiv a b | .smod a b | .sar a b | .byte a b | .signextend a b =>
      exprTouchesUnsupportedConstructorRawCalldataSurface a ||
        exprTouchesUnsupportedConstructorRawCalldataSurface b
  | .mapping2 _ a b | .mapping2Word _ a b _ | .structMember2 _ a b _ =>
      exprTouchesUnsupportedConstructorRawCalldataSurface a ||
        exprTouchesUnsupportedConstructorRawCalldataSurface b
  | .dynamicBytesEq _ _ => false
  | .ite c t e | .mulDivDown c t e | .mulDivUp c t e
  | .mulDiv512Down c t e | .mulDiv512Up c t e =>
      exprTouchesUnsupportedConstructorRawCalldataSurface c ||
        exprTouchesUnsupportedConstructorRawCalldataSurface t ||
        exprTouchesUnsupportedConstructorRawCalldataSurface e
  -- `paramDynamicHeadWord` reads the head section of an ABI-decoded
  -- parameter; like `param _` it does not touch raw calldata, so the
  -- constructor-arg precondition is unaffected.
  | .paramDynamicHeadWord _ _ | .paramDynamicStaticComposite _ _
  | .paramDynamicMemberLength _ _
  | .paramDynamicMemberDataOffset _ _ => false
  | .mappingChain _ keys | .internalCall _ keys | .externalCall _ keys =>
      exprListTouchesUnsupportedConstructorRawCalldataSurface keys
  | .intrinsic _ _ _ _ => true
  | .forkIfAtLeast _ thenExpr elseExpr =>
      exprTouchesUnsupportedConstructorRawCalldataSurface thenExpr ||
        exprTouchesUnsupportedConstructorRawCalldataSurface elseExpr
  | .keccak256 a b =>
      exprTouchesUnsupportedConstructorRawCalldataSurface a ||
        exprTouchesUnsupportedConstructorRawCalldataSurface b
  | .call g t v io is oo os =>
      exprTouchesUnsupportedConstructorRawCalldataSurface g ||
        exprTouchesUnsupportedConstructorRawCalldataSurface t ||
        exprTouchesUnsupportedConstructorRawCalldataSurface v ||
        exprTouchesUnsupportedConstructorRawCalldataSurface io ||
        exprTouchesUnsupportedConstructorRawCalldataSurface is ||
        exprTouchesUnsupportedConstructorRawCalldataSurface oo ||
        exprTouchesUnsupportedConstructorRawCalldataSurface os
  | .staticcall g t io is oo os | .delegatecall g t io is oo os =>
      exprTouchesUnsupportedConstructorRawCalldataSurface g ||
        exprTouchesUnsupportedConstructorRawCalldataSurface t ||
        exprTouchesUnsupportedConstructorRawCalldataSurface io ||
        exprTouchesUnsupportedConstructorRawCalldataSurface is ||
        exprTouchesUnsupportedConstructorRawCalldataSurface oo ||
        exprTouchesUnsupportedConstructorRawCalldataSurface os
  | .adtConstruct _ _ args =>
      exprListTouchesUnsupportedConstructorRawCalldataSurface args
  | .adtTag _ _ | .adtField _ _ _ _ _ => false

def exprListTouchesUnsupportedConstructorRawCalldataSurface : List Expr → Bool
  | [] => false
  | expr :: rest =>
      exprTouchesUnsupportedConstructorRawCalldataSurface expr ||
        exprListTouchesUnsupportedConstructorRawCalldataSurface rest

def stmtTouchesUnsupportedConstructorRawCalldataSurface : Stmt → Bool
  | .panicCode _ => false
  | .panic _ => false
  | .letVar _ value | .assignVar _ value | .setStorage _ value
  | .setStorageAddr _ value | .setImmutable _ value | .setStorageWord _ _ value
  | .require value _ | .return value
  | .storageArrayPush _ value =>
      exprTouchesUnsupportedConstructorRawCalldataSurface value
  | .returnCodeData pointer =>
      exprTouchesUnsupportedConstructorRawCalldataSurface pointer
  | .setMapping _ key value | .setMappingWord _ key _ value
  | .setMappingPackedWord _ key _ _ value | .setMappingUint _ key value
  | .setStructMember _ key _ value | .setStorageArrayElement _ key value
  | .mstore key value | .tstore key value  =>
      exprTouchesUnsupportedConstructorRawCalldataSurface key ||
        exprTouchesUnsupportedConstructorRawCalldataSurface value
  | .setMappingChain _ keys value =>
      exprListTouchesUnsupportedConstructorRawCalldataSurface keys ||
        exprTouchesUnsupportedConstructorRawCalldataSurface value
  | .setMapping2 _ key1 key2 value | .setMapping2Word _ key1 key2 _ value
  | .setStructMember2 _ key1 key2 _ value =>
      exprTouchesUnsupportedConstructorRawCalldataSurface key1 ||
        exprTouchesUnsupportedConstructorRawCalldataSurface key2 ||
        exprTouchesUnsupportedConstructorRawCalldataSurface value
  | .emit _ args | .internalCallAssign _ _ args | .internalCall _ args
  | .externalCallBind _ _ args | .tryExternalCallBind _ _ _ args =>
      exprListTouchesUnsupportedConstructorRawCalldataSurface args
  | .ite cond thenBranch elseBranch =>
      exprTouchesUnsupportedConstructorRawCalldataSurface cond ||
        stmtListTouchesUnsupportedConstructorRawCalldataSurface thenBranch ||
        stmtListTouchesUnsupportedConstructorRawCalldataSurface elseBranch
  | .forEach _ count body | .forEachSetBit _ count body =>
      exprTouchesUnsupportedConstructorRawCalldataSurface count ||
        stmtListTouchesUnsupportedConstructorRawCalldataSurface body
  | .requireError cond _ args =>
      exprTouchesUnsupportedConstructorRawCalldataSurface cond ||
        exprListTouchesUnsupportedConstructorRawCalldataSurface args
  | .revertError _ args =>
      exprListTouchesUnsupportedConstructorRawCalldataSurface args
  | .calldatacopy destOffset sourceOffset size
  | .returndataCopy destOffset sourceOffset size =>
      exprTouchesUnsupportedConstructorRawCalldataSurface destOffset ||
        exprTouchesUnsupportedConstructorRawCalldataSurface sourceOffset ||
        exprTouchesUnsupportedConstructorRawCalldataSurface size
  | .stop | .storageArrayPop _
  | .returnValues _ | .returnArray _ | .returnBytes _ | .returnStorageWords _
  | .revertEmpty | .revertReturndata
  | .rawLog _ _ _ | .ecm _ _ => false
  | .unsafeBlock _ _ | .unsafeYul _ | .matchAdt _ _ _ => true

def stmtListTouchesUnsupportedConstructorRawCalldataSurface : List Stmt → Bool
  | [] => false
  | stmt :: rest =>
      stmtTouchesUnsupportedConstructorRawCalldataSurface stmt ||
        stmtListTouchesUnsupportedConstructorRawCalldataSurface rest
end

/-- Scope exposed to the continuation of a helper-rich statement.  Branch
bindings of an `ite` are local to the branch in both source validation and Yul,
so unlike the compiler's conservative name inventory they must not be added to
the tail scope. -/
def stmtHelperRichNextScope (scope : List String) : Stmt → List String
  | .ite _ _ _ => scope
  | stmt => stmtNextScope scope stmt

/-- Selector-dispatched entrypoints in the same order used by `CompilationModel.compile`. -/
def selectorDispatchedFunctions (spec : CompilationModel) : List FunctionSpec :=
  spec.functions.filter (fun fn => !fn.isInternal && !isInteropEntrypointName fn.name)

/-- Parameter-profile interface for selector-dispatched entrypoints covered by the
current whole-contract theorem. -/
structure SupportedParamProfile (params : List Param) : Prop where
  namesNodup : (params.map (·.name)).Nodup
  supported : ∀ param ∈ params, SupportedExternalScalarParamType param.ty
  calldataThreshold : 4 + params.length * 32 < Compiler.Constants.evmModulus

/-- Return-profile interface for selector-dispatched entrypoints covered by the
current whole-contract theorem. -/
structure SupportedReturnProfile (fn : FunctionSpec) : Prop where
  resolved :
    ∃ resolvedReturns,
      functionReturns fn = Except.ok resolvedReturns ∧
        SupportedExternalReturnProfile resolvedReturns

/-- Pure expression forms still outside the current generic-induction core, even
before any richer contract surface is considered. This tracks proof-core gaps
rather than a semantic trust boundary. -/
def exprTouchesUnsupportedCoreSurface : Expr → Bool
  | .literal _ | .param _ | .caller | .contractAddress | .txOrigin
  | .chainid | .msgValue | .blockTimestamp | .blockNumber
  | .blobbasefee | .calldatasize | .returndataSize | .localVar _ | .constructorArg _
  | .arrayLength _ | .dynamicBytesEq _ _ => false
  | .immutable _ => true
  | .selfBalance | .baseFee | .gasPrice => true
  | .storage _ | .storageAddr _ => false
  | .add a b | .sub a b | .mul a b | .div a b | .mod a b
  | .eq a b | .ge a b | .gt a b | .lt a b | .le a b
  | .logicalAnd a b | .logicalOr a b
  | .shl a b | .shr a b =>
      exprTouchesUnsupportedCoreSurface a || exprTouchesUnsupportedCoreSurface b
  | .logicalNot a | .bitNot a => exprTouchesUnsupportedCoreSurface a
  | .bitAnd a b | .bitOr a b | .bitXor a b
  | .min a b | .max a b | .ceilDiv a b =>
      exprTouchesUnsupportedCoreSurface a || exprTouchesUnsupportedCoreSurface b
  | .ite a b c =>
      exprTouchesUnsupportedCoreSurface a || exprTouchesUnsupportedCoreSurface b ||
        exprTouchesUnsupportedCoreSurface c
  | .forkIfAtLeast _ _ _ => true
  | .wMulDown a b | .wDivUp a b =>
      exprTouchesUnsupportedCoreSurface a || exprTouchesUnsupportedCoreSurface b
  | .mulDivDown a b c | .mulDivUp a b c =>
      exprTouchesUnsupportedCoreSurface a || exprTouchesUnsupportedCoreSurface b ||
        exprTouchesUnsupportedCoreSurface c
  | .slt a b | .sgt a b | .sdiv a b | .smod a b | .sar a b | .byte a b | .signextend a b =>
      exprTouchesUnsupportedCoreSurface a || exprTouchesUnsupportedCoreSurface b
  | .mload a | .tload a | .calldataload a | .extcodesize a
  | .returndataOptionalBoolAt a => exprTouchesUnsupportedCoreSurface a
  | .keccak256 a b =>
      exprTouchesUnsupportedCoreSurface a || exprTouchesUnsupportedCoreSurface b
  | .arrayElement _ index => exprTouchesUnsupportedCoreSurface index
  -- The reserved `exp` builtin lane travels as `externalCall`, but it is pure
  -- arithmetic that lowers to the Yul `exp` builtin, so only its operands
  -- constrain the core surface. Every other `externalCall` stays excluded.
  | .externalCall name [base, exponent] =>
      if name == builtinExpName then
        exprTouchesUnsupportedCoreSurface base || exprTouchesUnsupportedCoreSurface exponent
      else true
  -- `mulDiv512Down/Up` (verity#1761) and `paramDynamicHeadWord` (verity#1832)
  -- are codegen-only additions whose runtime Yul helpers the current core
  -- proof framework does not model yet, so `SupportedSpec` continues to
  -- exclude contracts that use them.
  | .mapping _ _ | .mappingWord _ _ _ | .mappingPackedWord _ _ _ _
  | .mapping2 _ _ _ | .mapping2Word _ _ _ _ | .mappingUint _ _ | .mappingChain _ _
  | .structMember _ _ _ | .structMember2 _ _ _ _
  | .call _ _ _ _ _ _ _ | .staticcall _ _ _ _ _ _ | .delegatecall _ _ _ _ _ _
  | .externalCall _ _ | .internalCall _ _
  | .memoryArrayLength _
  | .memoryArrayElement _ _ | .arrayElementWord _ _ _ _
  | .arrayElementDynamicWord _ _ _
  | .arrayElementDynamicDataOffset _ _
  | .arrayElementDynamicMemberLength _ _ _
  | .arrayElementDynamicMemberDataOffset _ _ _
  | .arrayElementDynamicMemberElement _ _ _ _
  | .paramDynamicHeadWord _ _ | .paramDynamicStaticComposite _ _
  | .paramDynamicMemberLength _ _
  | .paramDynamicMemberDataOffset _ _ | .paramDynamicMemberElement _ _ _
  | .mulDiv512Down _ _ _ | .mulDiv512Up _ _ _
  | .storageArrayLength _ | .storageArrayElement _ _
  | .intrinsic _ _ _ _
  | .adtConstruct _ _ _ | .adtTag _ _ | .adtField _ _ _ _ _ => true

/-- Stateful expression surfaces not yet carried by the generic Layer 2 body
interface. These are the next storage/layout-style widening targets. -/
def exprTouchesUnsupportedStateSurface : Expr → Bool
  | .literal _ | .param _ | .immutable _ | .caller | .contractAddress | .txOrigin
  | .chainid | .msgValue | .selfBalance | .baseFee | .gasPrice | .blockTimestamp | .blockNumber
  | .localVar _ => false
  | .storage _ | .storageAddr _ => true
  | .mapping _ _ | .mappingWord _ _ _ | .mappingPackedWord _ _ _ _
  | .mapping2 _ _ _ | .mapping2Word _ _ _ _ | .mappingUint _ _ | .mappingChain _ _
  | .structMember _ _ _ | .structMember2 _ _ _ _
  | .storageArrayLength _ | .storageArrayElement _ _ => true
  | .add a b | .sub a b | .mul a b | .div a b | .sdiv a b | .mod a b | .smod a b
  | .bitAnd a b | .bitOr a b | .bitXor a b | .eq a b
  | .ge a b | .gt a b | .sgt a b | .lt a b | .slt a b | .le a b
  | .logicalAnd a b | .logicalOr a b =>
      exprTouchesUnsupportedStateSurface a || exprTouchesUnsupportedStateSurface b
  | .min a b | .max a b | .wMulDown a b | .wDivUp a b | .ceilDiv a b =>
      exprTouchesUnsupportedStateSurface a || exprTouchesUnsupportedStateSurface b
  | .bitNot a | .logicalNot a => exprTouchesUnsupportedStateSurface a
  | .ite cond thenVal elseVal =>
      exprTouchesUnsupportedStateSurface cond ||
        exprTouchesUnsupportedStateSurface thenVal ||
        exprTouchesUnsupportedStateSurface elseVal
  | .forkIfAtLeast _ thenExpr elseExpr =>
      exprTouchesUnsupportedStateSurface thenExpr ||
        exprTouchesUnsupportedStateSurface elseExpr
  | .shl a b | .shr a b | .sar a b | .byte a b | .signextend a b =>
      exprTouchesUnsupportedStateSurface a || exprTouchesUnsupportedStateSurface b
  | .mulDivDown a b c | .mulDivUp a b c
  | .mulDiv512Down a b c | .mulDiv512Up a b c =>
      exprTouchesUnsupportedStateSurface a || exprTouchesUnsupportedStateSurface b ||
        exprTouchesUnsupportedStateSurface c
  | .intrinsic _ _ _ _ => true
  | .keccak256 a b =>
      exprTouchesUnsupportedStateSurface a || exprTouchesUnsupportedStateSurface b
  -- The reserved `exp` builtin lane travels as `externalCall` but is pure
  -- arithmetic, so only its operands constrain the state surface.
  | .externalCall name [base, exponent] =>
      if name == builtinExpName then
        exprTouchesUnsupportedStateSurface base || exprTouchesUnsupportedStateSurface exponent
      else false
  | .constructorArg _ | .blobbasefee
  | .call _ _ _ _ _ _ _ | .staticcall _ _ _ _ _ _ | .delegatecall _ _ _ _ _ _
  | .calldatasize | .returndataSize
  | .externalCall _ _ | .internalCall _ _
  | .arrayLength _ | .memoryArrayLength _
  | .arrayElement _ _ | .memoryArrayElement _ _ | .arrayElementWord _ _ _ _
  | .arrayElementDynamicWord _ _ _
  | .arrayElementDynamicMemberLength _ _ _
  | .arrayElementDynamicDataOffset _ _
  | .arrayElementDynamicMemberDataOffset _ _ _
  | .arrayElementDynamicMemberElement _ _ _ _
  | .paramDynamicHeadWord _ _ | .paramDynamicStaticComposite _ _
  | .paramDynamicMemberLength _ _
  | .paramDynamicMemberDataOffset _ _ | .paramDynamicMemberElement _ _ _
  | .dynamicBytesEq _ _ => false
  | .mload a | .tload a | .calldataload a | .extcodesize a
  | .returndataOptionalBoolAt a => exprTouchesUnsupportedStateSurface a
  | .adtConstruct _ _ _ | .adtTag _ _ | .adtField _ _ _ _ _ => true

/-- Call-related surfaces that still sit outside the current generic Layer 2
body theorem: internal helper reuse, low-level calls, and foreign call hooks. -/
def exprTouchesUnsupportedCallSurface : Expr → Bool
  -- The reserved `exp` builtin lane travels as `externalCall` but lowers to the
  -- pure Yul `exp` builtin, so it introduces no call surface of its own.
  | .externalCall name [base, exponent] =>
      if name == builtinExpName then
        exprTouchesUnsupportedCallSurface base || exprTouchesUnsupportedCallSurface exponent
      else true
  | .internalCall _ _ | .externalCall _ _ => true
  | .call _ _ _ _ _ _ _ | .staticcall _ _ _ _ _ _ | .delegatecall _ _ _ _ _ _ => true
  | .literal _ | .param _ | .immutable _ | .caller | .contractAddress | .txOrigin
  | .chainid | .msgValue | .selfBalance | .baseFee | .gasPrice | .blockTimestamp | .blockNumber
  | .localVar _ | .storage _ | .storageAddr _
  | .constructorArg _ | .blobbasefee
  | .calldatasize | .returndataSize
  | .memoryArrayLength _
  | .paramDynamicHeadWord _ _ | .paramDynamicStaticComposite _ _
  | .paramDynamicMemberLength _ _
  | .paramDynamicMemberDataOffset _ _
  | .storageArrayLength _ => false
  | .paramDynamicMemberElement _ _ b =>
      exprTouchesUnsupportedCallSurface b
  | .mload a | .tload a | .calldataload a | .extcodesize a
  | .returndataOptionalBoolAt a => exprTouchesUnsupportedCallSurface a
  | .keccak256 a b =>
      exprTouchesUnsupportedCallSurface a || exprTouchesUnsupportedCallSurface b
  | .add a b | .sub a b | .mul a b | .div a b | .sdiv a b | .mod a b | .smod a b
  | .bitAnd a b | .bitOr a b | .bitXor a b | .eq a b
  | .ge a b | .gt a b | .sgt a b | .lt a b | .slt a b | .le a b
  | .logicalAnd a b | .logicalOr a b =>
      exprTouchesUnsupportedCallSurface a || exprTouchesUnsupportedCallSurface b
  | .min a b | .max a b | .wMulDown a b | .wDivUp a b | .ceilDiv a b =>
      exprTouchesUnsupportedCallSurface a || exprTouchesUnsupportedCallSurface b
  | .mapping _ b | .mappingUint _ b | .memoryArrayElement _ b
  | .arrayElementWord _ b _ _
  | .arrayElementDynamicWord _ b _
  | .storageArrayElement _ b =>
      exprTouchesUnsupportedCallSurface b
  | .arrayElementDynamicDataOffset _ b
  | .arrayElementDynamicMemberLength _ b _
  | .arrayElementDynamicMemberDataOffset _ b _ =>
      exprTouchesUnsupportedCallSurface b
  | .arrayElementDynamicMemberElement _ a _ b =>
      exprTouchesUnsupportedCallSurface a || exprTouchesUnsupportedCallSurface b
  | .mappingChain _ _ => true
  | .bitNot a | .logicalNot a | .mappingWord _ a _ | .mappingPackedWord _ a _ _
  | .structMember _ a _ => exprTouchesUnsupportedCallSurface a
  | .ite cond thenVal elseVal =>
      exprTouchesUnsupportedCallSurface cond ||
        exprTouchesUnsupportedCallSurface thenVal ||
        exprTouchesUnsupportedCallSurface elseVal
  | .forkIfAtLeast _ thenExpr elseExpr =>
      exprTouchesUnsupportedCallSurface thenExpr ||
        exprTouchesUnsupportedCallSurface elseExpr
  | .mapping2 _ a b | .mapping2Word _ a b _ | .structMember2 _ a b _ =>
      exprTouchesUnsupportedCallSurface a || exprTouchesUnsupportedCallSurface b
  | .mulDivDown a b c | .mulDivUp a b c
  | .mulDiv512Down a b c | .mulDiv512Up a b c =>
      exprTouchesUnsupportedCallSurface a ||
        exprTouchesUnsupportedCallSurface b ||
        exprTouchesUnsupportedCallSurface c
  | .shl a b | .shr a b | .sar a b | .byte a b | .signextend a b =>
      exprTouchesUnsupportedCallSurface a || exprTouchesUnsupportedCallSurface b
  | .arrayLength _ | .arrayElement _ _ | .dynamicBytesEq _ _ => true
  | .intrinsic _ _ _ _ => true
  | .adtConstruct _ _ _ | .adtTag _ _ | .adtField _ _ _ _ _ => true

/-- Internal helper-call surfaces not yet modeled compositionally in the current
generic whole-contract theorem. -/
def exprTouchesUnsupportedHelperSurface : Expr → Bool
  | .internalCall _ _ => true
  -- The reserved `exp` builtin lane now evaluates in the source semantics, so
  -- its operands have to be screened rather than ignored.
  | .externalCall name [base, exponent] =>
      if name == builtinExpName then
        exprTouchesUnsupportedHelperSurface base || exprTouchesUnsupportedHelperSurface exponent
      else false
  | .literal _ | .param _ | .immutable _ | .caller | .contractAddress | .txOrigin
  | .chainid | .msgValue | .selfBalance | .baseFee | .gasPrice | .blockTimestamp | .blockNumber
  | .localVar _ | .storage _ | .storageAddr _
  | .constructorArg _ | .blobbasefee
  | .calldatasize | .returndataSize
  | .memoryArrayLength _
  | .paramDynamicHeadWord _ _ | .paramDynamicStaticComposite _ _
  | .paramDynamicMemberLength _ _
  | .paramDynamicMemberDataOffset _ _
  | .storageArrayLength _ | .externalCall _ _ => false
  | .paramDynamicMemberElement _ _ b =>
      exprTouchesUnsupportedHelperSurface b
  | .mload a | .tload a | .calldataload a | .extcodesize a
  | .returndataOptionalBoolAt a => exprTouchesUnsupportedHelperSurface a
  | .keccak256 a b =>
      exprTouchesUnsupportedHelperSurface a || exprTouchesUnsupportedHelperSurface b
  | .call _ _ _ _ _ _ _ | .staticcall _ _ _ _ _ _ | .delegatecall _ _ _ _ _ _ => false
  | .add a b | .sub a b | .mul a b | .div a b | .sdiv a b | .mod a b | .smod a b
  | .bitAnd a b | .bitOr a b | .bitXor a b | .eq a b
  | .ge a b | .gt a b | .sgt a b | .lt a b | .slt a b | .le a b
  | .logicalAnd a b | .logicalOr a b =>
      exprTouchesUnsupportedHelperSurface a || exprTouchesUnsupportedHelperSurface b
  | .min a b | .max a b | .wMulDown a b | .wDivUp a b | .ceilDiv a b =>
      exprTouchesUnsupportedHelperSurface a || exprTouchesUnsupportedHelperSurface b
  | .mapping _ b | .mappingUint _ b | .memoryArrayElement _ b
  | .arrayElementWord _ b _ _
  | .arrayElementDynamicWord _ b _
  | .storageArrayElement _ b =>
      exprTouchesUnsupportedHelperSurface b
  | .arrayElementDynamicDataOffset _ b
  | .arrayElementDynamicMemberLength _ b _
  | .arrayElementDynamicMemberDataOffset _ b _ =>
      exprTouchesUnsupportedHelperSurface b
  | .arrayElementDynamicMemberElement _ a _ b =>
      exprTouchesUnsupportedHelperSurface a || exprTouchesUnsupportedHelperSurface b
  | .mappingChain _ _ => true
  | .bitNot a | .logicalNot a | .mappingWord _ a _ | .mappingPackedWord _ a _ _
  | .structMember _ a _ => exprTouchesUnsupportedHelperSurface a
  | .ite cond thenVal elseVal =>
      exprTouchesUnsupportedHelperSurface cond ||
        exprTouchesUnsupportedHelperSurface thenVal ||
        exprTouchesUnsupportedHelperSurface elseVal
  | .forkIfAtLeast _ thenExpr elseExpr =>
      exprTouchesUnsupportedHelperSurface thenExpr ||
        exprTouchesUnsupportedHelperSurface elseExpr
  | .mapping2 _ a b | .mapping2Word _ a b _ | .structMember2 _ a b _ =>
      exprTouchesUnsupportedHelperSurface a || exprTouchesUnsupportedHelperSurface b
  | .mulDivDown a b c | .mulDivUp a b c
  | .mulDiv512Down a b c | .mulDiv512Up a b c =>
      exprTouchesUnsupportedHelperSurface a ||
        exprTouchesUnsupportedHelperSurface b ||
        exprTouchesUnsupportedHelperSurface c
  | .shl a b | .shr a b | .sar a b | .byte a b | .signextend a b =>
      exprTouchesUnsupportedHelperSurface a || exprTouchesUnsupportedHelperSurface b
  | .arrayLength _ | .arrayElement _ _ | .dynamicBytesEq _ _ => true
  | .intrinsic _ _ _ _ => true
  | .adtConstruct _ _ _ | .adtTag _ _ | .adtField _ _ _ _ _ => true

def exprListTouchesUnsupportedHelperSurface : List Expr → Bool
  | [] => false
  | expr :: rest =>
      exprTouchesUnsupportedHelperSurface expr ||
        exprListTouchesUnsupportedHelperSurface rest

/-- Narrow helper-effect surface used by the exact helper-aware induction seam:
this tracks only genuine internal-helper execution, not the broader set of
still-unsupported expression shapes that currently share the coarse
`exprTouchesUnsupportedHelperSurface` approximation. -/
def exprTouchesInternalHelperSurface : Expr → Bool
  | .internalCall _ _ => true
  -- The reserved `exp` builtin lane now evaluates in the source semantics, so
  -- its operands have to be screened rather than ignored.
  | .externalCall name [base, exponent] =>
      if name == builtinExpName then
        exprTouchesInternalHelperSurface base || exprTouchesInternalHelperSurface exponent
      else false
  | .literal _ | .param _ | .immutable _ | .caller | .contractAddress | .txOrigin
  | .chainid | .msgValue | .selfBalance | .baseFee | .gasPrice | .blockTimestamp | .blockNumber
  | .localVar _ | .storage _ | .storageAddr _
  | .constructorArg _ | .blobbasefee
  | .calldatasize | .returndataSize
  | .arrayLength _
  | .memoryArrayLength _
  | .paramDynamicHeadWord _ _ | .paramDynamicStaticComposite _ _
  | .paramDynamicMemberLength _ _
  | .paramDynamicMemberDataOffset _ _
  | .storageArrayLength _ | .externalCall _ _ => false
  | .paramDynamicMemberElement _ _ b =>
      exprTouchesInternalHelperSurface b
  | .mload a | .tload a | .calldataload a | .extcodesize a
  | .returndataOptionalBoolAt a => exprTouchesInternalHelperSurface a
  | .keccak256 a b =>
      exprTouchesInternalHelperSurface a || exprTouchesInternalHelperSurface b
  | .call _ _ _ _ _ _ _ | .staticcall _ _ _ _ _ _ | .delegatecall _ _ _ _ _ _ => false
  | .add a b | .sub a b | .mul a b | .div a b | .sdiv a b | .mod a b | .smod a b
  | .bitAnd a b | .bitOr a b | .bitXor a b | .eq a b
  | .ge a b | .gt a b | .sgt a b | .lt a b | .slt a b | .le a b
  | .logicalAnd a b | .logicalOr a b =>
      exprTouchesInternalHelperSurface a || exprTouchesInternalHelperSurface b
  | .min a b | .max a b | .wMulDown a b | .wDivUp a b | .ceilDiv a b =>
      exprTouchesInternalHelperSurface a || exprTouchesInternalHelperSurface b
  | .mapping _ b | .mappingUint _ b | .arrayElement _ b | .memoryArrayElement _ b
  | .arrayElementWord _ b _ _
  | .arrayElementDynamicWord _ b _
  | .arrayElementDynamicDataOffset _ b
  | .arrayElementDynamicMemberLength _ b _
  | .arrayElementDynamicMemberDataOffset _ b _
  | .storageArrayElement _ b =>
      exprTouchesInternalHelperSurface b
  | .arrayElementDynamicMemberElement _ a _ b =>
      exprTouchesInternalHelperSurface a || exprTouchesInternalHelperSurface b
  | .mappingChain _ [] => false
  | .mappingChain field (k :: ks) =>
      exprTouchesInternalHelperSurface k || exprTouchesInternalHelperSurface (.mappingChain field ks)
  | .bitNot a | .logicalNot a | .mappingWord _ a _ | .mappingPackedWord _ a _ _
  | .structMember _ a _ => exprTouchesInternalHelperSurface a
  | .ite cond thenVal elseVal =>
      exprTouchesInternalHelperSurface cond ||
        exprTouchesInternalHelperSurface thenVal ||
        exprTouchesInternalHelperSurface elseVal
  | .forkIfAtLeast _ thenExpr elseExpr =>
      exprTouchesInternalHelperSurface thenExpr ||
        exprTouchesInternalHelperSurface elseExpr
  | .mapping2 _ a b | .mapping2Word _ a b _ | .structMember2 _ a b _ =>
      exprTouchesInternalHelperSurface a || exprTouchesInternalHelperSurface b
  | .mulDivDown a b c | .mulDivUp a b c
  | .mulDiv512Down a b c | .mulDiv512Up a b c =>
      exprTouchesInternalHelperSurface a ||
        exprTouchesInternalHelperSurface b ||
        exprTouchesInternalHelperSurface c
  | .shl a b | .shr a b | .sar a b | .byte a b | .signextend a b =>
      exprTouchesInternalHelperSurface a || exprTouchesInternalHelperSurface b
  | .dynamicBytesEq _ _ => false
  | .intrinsic _ _ _ _ => true
  | .adtConstruct _ _ _ | .adtTag _ _ | .adtField _ _ _ _ _ => true

/-- Foreign-call/library-hook surfaces still outside the current generic
whole-contract theorem. -/
def exprTouchesUnsupportedForeignSurface : Expr → Bool
  -- `pow`/`^` in the EDSL surfaces as `externalCall builtinExpName [b, e]`, but
  -- it carries no foreign behaviour: the compiler lowers it to the pure Yul
  -- `exp` builtin, and the source semantics evaluates it with
  -- `Uint256.powEff` (modular square-and-multiply, equal to `Uint256.pow`).
  -- Genuine foreign calls keep the blanket exclusion.
  | .externalCall name [base, exponent] =>
      if name == builtinExpName then
        exprTouchesUnsupportedForeignSurface base || exprTouchesUnsupportedForeignSurface exponent
      else true
  | .externalCall _ _ => true
  | .literal _ | .param _ | .immutable _ | .caller | .contractAddress | .txOrigin
  | .chainid | .msgValue | .selfBalance | .baseFee | .gasPrice | .blockTimestamp | .blockNumber
  | .localVar _ | .storage _ | .storageAddr _
  | .constructorArg _ | .blobbasefee
  | .calldatasize | .returndataSize
  | .arrayLength _
  | .memoryArrayLength _
  | .paramDynamicHeadWord _ _ | .paramDynamicStaticComposite _ _
  | .paramDynamicMemberLength _ _
  | .paramDynamicMemberDataOffset _ _
  | .storageArrayLength _ | .internalCall _ _ => false
  | .paramDynamicMemberElement _ _ b =>
      exprTouchesUnsupportedForeignSurface b
  | .keccak256 a b =>
      exprTouchesUnsupportedForeignSurface a || exprTouchesUnsupportedForeignSurface b
  | .mload a | .tload a | .calldataload a | .extcodesize a
  | .returndataOptionalBoolAt a => exprTouchesUnsupportedForeignSurface a
  | .call _ _ _ _ _ _ _ | .staticcall _ _ _ _ _ _ | .delegatecall _ _ _ _ _ _ => false
  | .add a b | .sub a b | .mul a b | .div a b | .sdiv a b | .mod a b | .smod a b
  | .bitAnd a b | .bitOr a b | .bitXor a b | .eq a b
  | .ge a b | .gt a b | .sgt a b | .lt a b | .slt a b | .le a b
  | .logicalAnd a b | .logicalOr a b =>
      exprTouchesUnsupportedForeignSurface a || exprTouchesUnsupportedForeignSurface b
  | .min a b | .max a b | .wMulDown a b | .wDivUp a b | .ceilDiv a b =>
      exprTouchesUnsupportedForeignSurface a || exprTouchesUnsupportedForeignSurface b
  | .mapping _ b | .mappingUint _ b | .arrayElement _ b | .memoryArrayElement _ b
  | .arrayElementWord _ b _ _
  | .arrayElementDynamicWord _ b _
  | .arrayElementDynamicMemberLength _ b _
  | .arrayElementDynamicDataOffset _ b
  | .arrayElementDynamicMemberDataOffset _ b _
  | .storageArrayElement _ b =>
      exprTouchesUnsupportedForeignSurface b
  | .arrayElementDynamicMemberElement _ a _ b =>
      exprTouchesUnsupportedForeignSurface a || exprTouchesUnsupportedForeignSurface b
  | .mappingChain _ _ => true
  | .bitNot a | .logicalNot a | .mappingWord _ a _ | .mappingPackedWord _ a _ _
  | .structMember _ a _ => exprTouchesUnsupportedForeignSurface a
  | .ite cond thenVal elseVal =>
      exprTouchesUnsupportedForeignSurface cond ||
        exprTouchesUnsupportedForeignSurface thenVal ||
        exprTouchesUnsupportedForeignSurface elseVal
  | .forkIfAtLeast _ thenExpr elseExpr =>
      exprTouchesUnsupportedForeignSurface thenExpr ||
        exprTouchesUnsupportedForeignSurface elseExpr
  | .mapping2 _ a b | .mapping2Word _ a b _ | .structMember2 _ a b _ =>
      exprTouchesUnsupportedForeignSurface a || exprTouchesUnsupportedForeignSurface b
  | .mulDivDown a b c | .mulDivUp a b c
  | .mulDiv512Down a b c | .mulDiv512Up a b c =>
      exprTouchesUnsupportedForeignSurface a ||
        exprTouchesUnsupportedForeignSurface b ||
        exprTouchesUnsupportedForeignSurface c
  | .shl a b | .shr a b | .sar a b | .byte a b | .signextend a b =>
      exprTouchesUnsupportedForeignSurface a || exprTouchesUnsupportedForeignSurface b
  | .dynamicBytesEq _ _ => false
  | .intrinsic _ _ _ _ => true
  | .adtConstruct _ _ _ | .adtTag _ _ | .adtField _ _ _ _ _ => true

/-- Low-level call/runtime-mechanic surfaces still outside the current generic
whole-contract theorem. -/
def exprTouchesUnsupportedLowLevelSurface : Expr → Bool
  | .call _ _ _ _ _ _ _ | .staticcall _ _ _ _ _ _ | .delegatecall _ _ _ _ _ _ => true
  -- The reserved `exp` builtin lane now evaluates in the source semantics, so
  -- its operands have to be screened rather than ignored.
  | .externalCall name [base, exponent] =>
      if name == builtinExpName then
        exprTouchesUnsupportedLowLevelSurface base || exprTouchesUnsupportedLowLevelSurface exponent
      else false
  | .literal _ | .param _ | .immutable _ | .caller | .contractAddress | .txOrigin
  | .chainid | .msgValue | .selfBalance | .baseFee | .gasPrice | .blockTimestamp | .blockNumber
  | .localVar _ | .storage _ | .storageAddr _
  | .constructorArg _ | .blobbasefee
  | .calldatasize | .returndataSize
  | .arrayLength _
  | .memoryArrayLength _
  | .paramDynamicHeadWord _ _ | .paramDynamicStaticComposite _ _
  | .paramDynamicMemberLength _ _
  | .paramDynamicMemberDataOffset _ _
  | .storageArrayLength _ | .internalCall _ _ | .externalCall _ _ => false
  | .paramDynamicMemberElement _ _ b =>
      exprTouchesUnsupportedLowLevelSurface b
  | .keccak256 a b =>
      exprTouchesUnsupportedLowLevelSurface a || exprTouchesUnsupportedLowLevelSurface b
  | .mload a | .tload a | .calldataload a | .extcodesize a
  | .returndataOptionalBoolAt a => exprTouchesUnsupportedLowLevelSurface a
  | .add a b | .sub a b | .mul a b | .div a b | .sdiv a b | .mod a b | .smod a b
  | .bitAnd a b | .bitOr a b | .bitXor a b | .eq a b
  | .ge a b | .gt a b | .sgt a b | .lt a b | .slt a b | .le a b
  | .logicalAnd a b | .logicalOr a b =>
      exprTouchesUnsupportedLowLevelSurface a || exprTouchesUnsupportedLowLevelSurface b
  | .min a b | .max a b | .wMulDown a b | .wDivUp a b | .ceilDiv a b =>
      exprTouchesUnsupportedLowLevelSurface a || exprTouchesUnsupportedLowLevelSurface b
  | .mapping _ b | .mappingUint _ b | .arrayElement _ b | .memoryArrayElement _ b
  | .arrayElementWord _ b _ _
  | .arrayElementDynamicWord _ b _
  | .arrayElementDynamicDataOffset _ b
  | .arrayElementDynamicMemberLength _ b _
  | .arrayElementDynamicMemberDataOffset _ b _
  | .storageArrayElement _ b =>
      exprTouchesUnsupportedLowLevelSurface b
  | .arrayElementDynamicMemberElement _ a _ b =>
      exprTouchesUnsupportedLowLevelSurface a || exprTouchesUnsupportedLowLevelSurface b
  | .mappingChain _ _ => true
  | .bitNot a | .logicalNot a | .mappingWord _ a _ | .mappingPackedWord _ a _ _
  | .structMember _ a _ => exprTouchesUnsupportedLowLevelSurface a
  | .ite cond thenVal elseVal =>
      exprTouchesUnsupportedLowLevelSurface cond ||
        exprTouchesUnsupportedLowLevelSurface thenVal ||
        exprTouchesUnsupportedLowLevelSurface elseVal
  | .forkIfAtLeast _ thenExpr elseExpr =>
      exprTouchesUnsupportedLowLevelSurface thenExpr ||
        exprTouchesUnsupportedLowLevelSurface elseExpr
  | .mapping2 _ a b | .mapping2Word _ a b _ | .structMember2 _ a b _ =>
      exprTouchesUnsupportedLowLevelSurface a || exprTouchesUnsupportedLowLevelSurface b
  | .mulDivDown a b c | .mulDivUp a b c
  | .mulDiv512Down a b c | .mulDiv512Up a b c =>
      exprTouchesUnsupportedLowLevelSurface a ||
        exprTouchesUnsupportedLowLevelSurface b ||
        exprTouchesUnsupportedLowLevelSurface c
  | .shl a b | .shr a b | .sar a b | .byte a b | .signextend a b =>
      exprTouchesUnsupportedLowLevelSurface a || exprTouchesUnsupportedLowLevelSurface b
  | .dynamicBytesEq _ _ => false
  | .intrinsic _ _ _ _ => true
  | .adtConstruct _ _ _ | .adtTag _ _ | .adtField _ _ _ _ _ => true

/-- Compatibility expression scan retained for the current generic-induction
proofs. This intentionally preserves the pre-interface split meaning so the
generic-induction boundary does not silently widen or tighten while the new
feature-local interfaces are introduced alongside it. -/
def exprTouchesUnsupportedContractSurface (expr : Expr) : Bool :=
  match expr with
  | .literal _ | .param _ | .caller | .contractAddress | .txOrigin
  | .chainid | .msgValue | .blockTimestamp | .blockNumber
  | .blobbasefee | .calldatasize | .returndataSize
  | .localVar _ | .constructorArg _ => false
  | .immutable _ => true
  | .selfBalance | .baseFee | .gasPrice => true
  | .storage _ | .storageAddr _ => true
  | .add a b | .sub a b | .mul a b | .div a b | .mod a b
  | .bitAnd a b | .bitOr a b | .bitXor a b | .eq a b
  | .ge a b | .gt a b | .lt a b | .le a b
  | .logicalAnd a b | .logicalOr a b
  | .shl a b | .shr a b | .slt a b | .sgt a b | .sdiv a b | .smod a b | .sar a b
  | .byte a b | .signextend a b =>
      exprTouchesUnsupportedContractSurface a || exprTouchesUnsupportedContractSurface b
  | .bitNot a | .logicalNot a => exprTouchesUnsupportedContractSurface a
  | .min a b | .max a b | .ceilDiv a b =>
      exprTouchesUnsupportedContractSurface a || exprTouchesUnsupportedContractSurface b
  | .ite a b c =>
      exprTouchesUnsupportedContractSurface a || exprTouchesUnsupportedContractSurface b ||
        exprTouchesUnsupportedContractSurface c
  | .forkIfAtLeast _ _ _ => true
  | .wMulDown a b | .wDivUp a b =>
      exprTouchesUnsupportedContractSurface a || exprTouchesUnsupportedContractSurface b
  | .mulDivDown a b c | .mulDivUp a b c =>
      exprTouchesUnsupportedContractSurface a || exprTouchesUnsupportedContractSurface b ||
        exprTouchesUnsupportedContractSurface c
  | .mload a | .tload a | .calldataload a | .extcodesize a
  | .returndataOptionalBoolAt a =>
      exprTouchesUnsupportedContractSurface a
  | .keccak256 a b =>
      exprTouchesUnsupportedContractSurface a || exprTouchesUnsupportedContractSurface b
  -- The reserved `exp` builtin lane travels as `externalCall` but is pure
  -- arithmetic lowered to the Yul `exp` builtin. Every other `externalCall`
  -- stays excluded below.
  | .externalCall name [base, exponent] =>
      if name == builtinExpName then
        exprTouchesUnsupportedContractSurface base ||
          exprTouchesUnsupportedContractSurface exponent
      else true
  | .mapping _ _ | .mappingWord _ _ _ | .mappingPackedWord _ _ _ _
  | .mapping2 _ _ _ | .mapping2Word _ _ _ _ | .mappingUint _ _ | .mappingChain _ _
  | .structMember _ _ _ | .structMember2 _ _ _ _
  | .call _ _ _ _ _ _ _ | .staticcall _ _ _ _ _ _ | .delegatecall _ _ _ _ _ _
  | .externalCall _ _ | .internalCall _ _
  | .arrayLength _ | .memoryArrayLength _
  | .arrayElement _ _ | .memoryArrayElement _ _ | .arrayElementWord _ _ _ _
  | .arrayElementDynamicWord _ _ _
  | .arrayElementDynamicDataOffset _ _
  | .arrayElementDynamicMemberLength _ _ _
  | .arrayElementDynamicMemberDataOffset _ _ _
  | .arrayElementDynamicMemberElement _ _ _ _
  | .paramDynamicHeadWord _ _ | .paramDynamicStaticComposite _ _
  | .paramDynamicMemberLength _ _
  | .paramDynamicMemberDataOffset _ _ | .paramDynamicMemberElement _ _ _
  | .mulDiv512Down _ _ _ | .mulDiv512Up _ _ _
  | .storageArrayLength _ | .storageArrayElement _ _
  | .dynamicBytesEq _ _ | .intrinsic _ _ _ _
  | .adtConstruct _ _ _ | .adtTag _ _ | .adtField _ _ _ _ _ => true

mutual
/-- Observable/effect-rich surfaces outside the current generic whole-contract
theorem: richer returns, logs, typed errors, and raw external effect hooks. -/
def stmtTouchesUnsupportedEffectSurface : Stmt → Bool
  | .panicCode _ => true
  | .panic _ => true
  | .requireError _ _ _ | .revertError _ _ | .returnValues _ | .returnArray _
  | .returnBytes _ | .returnStorageWords _ | .returnCodeData _ | .emit _ _ | .rawLog _ _ _
  | .externalCallBind _ _ _ | .tryExternalCallBind _ _ _ _ => true
  | .ecm mod _ => !(ecmPureHashing mod)
  | .setImmutable _ _ => true
  | .letVar _ _ | .assignVar _ _ | .setStorage _ _ | .setStorageAddr _ _
  | .setStorageWord _ _ _
  | .require _ _ | .return _ | .mstore _ _ | .tstore _ _ | .stop
  | .setMapping _ _ _ | .setMappingWord _ _ _ _
  | .setMappingPackedWord _ _ _ _ _ | .setMapping2 _ _ _ _
  | .setMapping2Word _ _ _ _ _ | .setMappingUint _ _ _ | .setMappingChain _ _ _
  | .setStructMember _ _ _ _ | .setStructMember2 _ _ _ _ _
  | .storageArrayPush _ _ | .storageArrayPop _ | .setStorageArrayElement _ _ _
  | .calldatacopy _ _ _ | .returndataCopy _ _ _ | .revertEmpty | .revertReturndata
  | .internalCall _ _ | .internalCallAssign _ _ _ => false
  | .unsafeBlock _ _ | .unsafeYul _ | .matchAdt _ _ _ => true
  | .ite _ thenBranch elseBranch =>
      stmtListTouchesUnsupportedEffectSurface thenBranch ||
        stmtListTouchesUnsupportedEffectSurface elseBranch
  | .forEach _ _ body | .forEachSetBit _ _ body =>
      stmtListTouchesUnsupportedEffectSurface body

/-- Statement forms intentionally still outside the current generic-induction
core, excluding richer state/call/effect surfaces that now have dedicated
interfaces of their own. -/
def stmtTouchesUnsupportedCoreSurface : Stmt → Bool
  | .panicCode _ => false
  | .panic _ => false
  | .letVar _ value | .assignVar _ value | .setStorage _ value =>
      exprTouchesUnsupportedCoreSurface value
  | .setStorageAddr _ value | .setImmutable _ value =>
      exprTouchesUnsupportedCoreSurface value
  | .setStorageWord _ _ value =>
      exprTouchesUnsupportedCoreSurface value
  | .setMapping _ key value | .setMappingWord _ key _ value
  | .setMappingPackedWord _ key _ _ value | .setMappingUint _ key value
  | .setStructMember _ key _ value =>
      exprTouchesUnsupportedCoreSurface key ||
        exprTouchesUnsupportedCoreSurface value
  | .setMappingChain _ keys value =>
      keys.any exprTouchesUnsupportedCoreSurface ||
        exprTouchesUnsupportedCoreSurface value
  | .setMapping2 _ key1 key2 value | .setMapping2Word _ key1 key2 _ value
  | .setStructMember2 _ key1 key2 _ value =>
      exprTouchesUnsupportedCoreSurface key1 ||
        exprTouchesUnsupportedCoreSurface key2 ||
        exprTouchesUnsupportedCoreSurface value
  | .storageArrayPush _ value =>
      exprTouchesUnsupportedCoreSurface value
  | .setStorageArrayElement _ index value =>
      exprTouchesUnsupportedCoreSurface index ||
        exprTouchesUnsupportedCoreSurface value
  | .mstore offset value | .tstore offset value  =>
      exprTouchesUnsupportedCoreSurface offset ||
        exprTouchesUnsupportedCoreSurface value
  | .require cond _ | .return cond =>
      exprTouchesUnsupportedCoreSurface cond
  | .stop => false
  | .ite cond thenBranch elseBranch =>
      exprTouchesUnsupportedCoreSurface cond ||
        stmtListTouchesUnsupportedCoreSurface thenBranch ||
        stmtListTouchesUnsupportedCoreSurface elseBranch
  | .forEach _ (.literal _) body =>
      stmtListTouchesUnsupportedCoreSurface body
  | .forEach _ _ _ | .forEachSetBit _ _ _ => true
  | .calldatacopy destOffset sourceOffset size
  | .returndataCopy destOffset sourceOffset size =>
      exprTouchesUnsupportedCoreSurface destOffset ||
        exprTouchesUnsupportedCoreSurface sourceOffset ||
        exprTouchesUnsupportedCoreSurface size
  | .storageArrayPop _
  | .requireError _ _ _ | .revertError _ _ | .returnValues _ | .returnArray _
  | .returnBytes _ | .returnStorageWords _ | .returnCodeData _
  | .revertEmpty | .revertReturndata => false
  | .emit _ _ | .internalCall _ _ | .internalCallAssign _ _ _
  | .rawLog _ _ _ | .externalCallBind _ _ _ | .tryExternalCallBind _ _ _ _ | .ecm _ _ => false
  | .unsafeBlock _ _ | .unsafeYul _ | .matchAdt _ _ _ => true

/-- State/layout-rich statement surfaces still outside the current whole-contract
theorem. -/
def stmtTouchesUnsupportedStateSurface : Stmt → Bool
  | .panicCode _ => false
  | .panic _ => false
  | .letVar _ value | .assignVar _ value | .setStorage _ value =>
      exprTouchesUnsupportedStateSurface value
  | .require cond _ | .return cond =>
      exprTouchesUnsupportedStateSurface cond
  | .setStorageAddr _ value | .setImmutable _ value =>
      exprTouchesUnsupportedStateSurface value
  | .setStorageWord _ _ _ | .setMapping _ _ _ | .setMappingWord _ _ _ _ | .setMappingPackedWord _ _ _ _ _
  | .setMapping2 _ _ _ _ | .setMapping2Word _ _ _ _ _ | .setMappingUint _ _ _
  | .setMappingChain _ _ _
  | .setStructMember _ _ _ _ | .setStructMember2 _ _ _ _ _
  | .storageArrayPush _ _ | .storageArrayPop _ | .setStorageArrayElement _ _ _ => true
  | .mstore offset value | .tstore offset value  =>
      exprTouchesUnsupportedStateSurface offset ||
        exprTouchesUnsupportedStateSurface value
  | .calldatacopy destOffset sourceOffset size
  | .returndataCopy destOffset sourceOffset size =>
      exprTouchesUnsupportedStateSurface destOffset ||
        exprTouchesUnsupportedStateSurface sourceOffset ||
        exprTouchesUnsupportedStateSurface size
  | .stop
  | .requireError _ _ _ | .revertError _ _ | .returnValues _ | .returnArray _
  | .returnBytes _ | .returnStorageWords _ | .returnCodeData _
  | .revertEmpty | .revertReturndata => false
  | .internalCall _ args =>
      exprListTouchesUnsupportedStateSurface args
  | .internalCallAssign _ _ args =>
      exprListTouchesUnsupportedStateSurface args
  | .emit _ _
  | .rawLog _ _ _ | .externalCallBind _ _ _ | .tryExternalCallBind _ _ _ _ | .ecm _ _ => false
  | .unsafeBlock _ _ | .unsafeYul _ | .matchAdt _ _ _ => true
  | .ite cond thenBranch elseBranch =>
      exprTouchesUnsupportedStateSurface cond ||
        stmtListTouchesUnsupportedStateSurface thenBranch ||
        stmtListTouchesUnsupportedStateSurface elseBranch
  | .forEach _ (.literal _) [] => false
  | .forEach _ _ _ | .forEachSetBit _ _ _ => true

def exprListTouchesUnsupportedStateSurface : List Expr → Bool
  | [] => false
  | expr :: rest =>
      exprTouchesUnsupportedStateSurface expr ||
        exprListTouchesUnsupportedStateSurface rest

/-- Weaker Tier 2 state-surface gate used by the singleton storage-write bridge:
all existing unsupported stateful forms remain excluded except for the proved
singleton mapping-write heads. -/
def stmtTouchesUnsupportedStateSurfaceExceptMappingWrites : Stmt → Bool
  | .setMapping _ _ _ | .setMappingWord _ _ _ _ | .setMappingPackedWord _ _ _ _ _
  | .setMappingUint _ _ _ | .setStructMember _ _ _ _ | .setMappingChain _ _ _
  | .setMapping2 _ _ _ _ | .setMapping2Word _ _ _ _ _ | .setStructMember2 _ _ _ _ _ =>
      false
  | stmt => stmtTouchesUnsupportedStateSurface stmt

/-- Helper/foreign/runtime-call statement surfaces still outside the current
generic theorem. -/
def stmtTouchesUnsupportedCallSurface : Stmt → Bool
  | .panicCode _ => false
  | .panic _ => false
  | .letVar _ value | .assignVar _ value | .setStorage _ value
  | .setStorageAddr _ value | .setImmutable _ value | .setStorageWord _ _ value | .storageArrayPush _ value =>
      exprTouchesUnsupportedCallSurface value
  | .setMapping _ key value | .setMappingWord _ key _ value
  | .setMappingPackedWord _ key _ _ value | .setMappingUint _ key value
  | .setStructMember _ key _ value =>
      exprTouchesUnsupportedCallSurface key ||
        exprTouchesUnsupportedCallSurface value
  | .setMappingChain _ keys value =>
      keys.any exprTouchesUnsupportedCallSurface ||
        exprTouchesUnsupportedCallSurface value
  | .setMapping2 _ key1 key2 value | .setMapping2Word _ key1 key2 _ value
  | .setStructMember2 _ key1 key2 _ value =>
      exprTouchesUnsupportedCallSurface key1 ||
        exprTouchesUnsupportedCallSurface key2 ||
        exprTouchesUnsupportedCallSurface value
  | .setStorageArrayElement _ index value
  | .mstore index value | .tstore index value =>
      exprTouchesUnsupportedCallSurface index ||
        exprTouchesUnsupportedCallSurface value
  | .require cond _ | .return cond =>
      exprTouchesUnsupportedCallSurface cond
  | .returnCodeData _ => true
  | .internalCall _ _ | .internalCallAssign _ _ _ => true
  | .calldatacopy destOffset sourceOffset size
  | .returndataCopy destOffset sourceOffset size =>
      exprTouchesUnsupportedCallSurface destOffset ||
        exprTouchesUnsupportedCallSurface sourceOffset ||
        exprTouchesUnsupportedCallSurface size
  | .revertEmpty | .revertReturndata => false
  | .externalCallBind _ _ args => args.any exprTouchesUnsupportedCallSurface
  | .tryExternalCallBind _ _ _ args => args.any exprTouchesUnsupportedCallSurface
  | .ecm _ _ => true
  | .stop | .storageArrayPop _
  | .returnValues _ | .returnArray _
  | .returnBytes _ | .returnStorageWords _ | .rawLog _ _ _ => false
  | .requireError cond _ args =>
      exprTouchesUnsupportedCallSurface cond ||
        args.any exprTouchesUnsupportedCallSurface
  | .revertError _ args => args.any exprTouchesUnsupportedCallSurface
  | .emit _ args => args.any exprTouchesUnsupportedCallSurface
  | .unsafeBlock _ _ | .unsafeYul _ | .matchAdt _ _ _ => true
  | .ite cond thenBranch elseBranch =>
      exprTouchesUnsupportedCallSurface cond ||
        stmtListTouchesUnsupportedCallSurface thenBranch ||
        stmtListTouchesUnsupportedCallSurface elseBranch
  | .forEach _ count body | .forEachSetBit _ count body =>
      exprTouchesUnsupportedCallSurface count ||
        stmtListTouchesUnsupportedCallSurface body

def stmtTouchesUnsupportedHelperSurface : Stmt → Bool
  | .panicCode _ => false
  | .panic _ => false
  | .letVar _ value | .assignVar _ value | .setStorage _ value
  | .setStorageAddr _ value | .setImmutable _ value | .setStorageWord _ _ value | .storageArrayPush _ value =>
      exprTouchesUnsupportedHelperSurface value
  | .setMapping _ key value | .setMappingWord _ key _ value
  | .setMappingPackedWord _ key _ _ value | .setMappingUint _ key value
  | .setStructMember _ key _ value =>
      exprTouchesUnsupportedHelperSurface key ||
        exprTouchesUnsupportedHelperSurface value
  | .setMappingChain _ keys value =>
      exprListTouchesUnsupportedHelperSurface keys ||
        exprTouchesUnsupportedHelperSurface value
  | .setMapping2 _ key1 key2 value | .setMapping2Word _ key1 key2 _ value
  | .setStructMember2 _ key1 key2 _ value =>
      exprTouchesUnsupportedHelperSurface key1 ||
        exprTouchesUnsupportedHelperSurface key2 ||
        exprTouchesUnsupportedHelperSurface value
  | .setStorageArrayElement _ index value
  | .mstore index value | .tstore index value  =>
      exprTouchesUnsupportedHelperSurface index ||
        exprTouchesUnsupportedHelperSurface value
  | .require cond _ | .return cond =>
      exprTouchesUnsupportedHelperSurface cond
  | .returnCodeData pointer =>
      exprTouchesUnsupportedHelperSurface pointer
  | .internalCall _ _ | .internalCallAssign _ _ _ => true
  | .calldatacopy destOffset sourceOffset size
  | .returndataCopy destOffset sourceOffset size =>
      exprTouchesUnsupportedHelperSurface destOffset ||
        exprTouchesUnsupportedHelperSurface sourceOffset ||
        exprTouchesUnsupportedHelperSurface size
  | .externalCallBind _ _ args | .tryExternalCallBind _ _ _ args
  | .ecm _ args =>
      exprListTouchesUnsupportedHelperSurface args
  | .stop
  | .revertEmpty | .revertReturndata
  | .storageArrayPop _
  | .returnValues _ | .returnArray _
  | .returnBytes _ | .returnStorageWords _ | .rawLog _ _ _ => false
  | .requireError cond _ args =>
      exprTouchesUnsupportedHelperSurface cond ||
        exprListTouchesUnsupportedHelperSurface args
  | .revertError _ args => exprListTouchesUnsupportedHelperSurface args
  | .emit _ args => exprListTouchesUnsupportedHelperSurface args
  | .unsafeBlock _ _ | .unsafeYul _ | .matchAdt _ _ _ => true
  | .ite cond thenBranch elseBranch =>
      exprTouchesUnsupportedHelperSurface cond ||
        stmtListTouchesUnsupportedHelperSurface thenBranch ||
        stmtListTouchesUnsupportedHelperSurface elseBranch
  | .forEach _ count body | .forEachSetBit _ count body =>
      exprTouchesUnsupportedHelperSurface count ||
        stmtListTouchesUnsupportedHelperSurface body

/-- Narrow helper-effect surface used by the exact helper-aware induction seam:
this isolates heads that genuinely execute internal helpers, leaving residual
non-helper unsupported cases to be tracked separately. -/
def stmtTouchesInternalHelperSurface : Stmt → Bool
  | .panicCode _ => false
  | .panic _ => false
  | .letVar _ value | .assignVar _ value | .setStorage _ value
  | .setStorageAddr _ value | .setImmutable _ value | .setStorageWord _ _ value | .storageArrayPush _ value =>
      exprTouchesInternalHelperSurface value
  | .setMapping _ key value | .setMappingWord _ key _ value
  | .setMappingPackedWord _ key _ _ value | .setMappingUint _ key value
  | .setStructMember _ key _ value =>
      exprTouchesInternalHelperSurface key ||
        exprTouchesInternalHelperSurface value
  | .setMappingChain _ keys value =>
      keys.any exprTouchesInternalHelperSurface ||
        exprTouchesInternalHelperSurface value
  | .setMapping2 _ key1 key2 value | .setMapping2Word _ key1 key2 _ value
  | .setStructMember2 _ key1 key2 _ value =>
      exprTouchesInternalHelperSurface key1 ||
        exprTouchesInternalHelperSurface key2 ||
        exprTouchesInternalHelperSurface value
  | .setStorageArrayElement _ index value
  | .mstore index value | .tstore index value  =>
      exprTouchesInternalHelperSurface index ||
        exprTouchesInternalHelperSurface value
  | .require cond _ | .return cond =>
      exprTouchesInternalHelperSurface cond
  | .returnCodeData pointer =>
      exprTouchesInternalHelperSurface pointer
  | .internalCall _ _ | .internalCallAssign _ _ _ => true
  | .calldatacopy destOffset sourceOffset size
  | .returndataCopy destOffset sourceOffset size =>
      exprTouchesInternalHelperSurface destOffset ||
        exprTouchesInternalHelperSurface sourceOffset ||
        exprTouchesInternalHelperSurface size
  | .stop
  | .revertEmpty | .revertReturndata | .externalCallBind _ _ _ | .tryExternalCallBind _ _ _ _
  | .ecm _ _ | .storageArrayPop _ | .returnValues _ | .returnArray _
  | .returnBytes _ | .returnStorageWords _ | .emit _ _
  | .rawLog _ _ _ => false
  | .requireError cond _ args =>
      exprTouchesInternalHelperSurface cond ||
        args.any exprTouchesInternalHelperSurface
  | .revertError _ args => args.any exprTouchesInternalHelperSurface
  | .unsafeBlock _ _ | .unsafeYul _ | .matchAdt _ _ _ => true
  | .ite cond thenBranch elseBranch =>
      exprTouchesInternalHelperSurface cond ||
        stmtListTouchesInternalHelperSurface thenBranch ||
        stmtListTouchesInternalHelperSurface elseBranch
  | .forEach _ count body | .forEachSetBit _ count body =>
      exprTouchesInternalHelperSurface count ||
        stmtListTouchesInternalHelperSurface body

/-- Direct statement-position internal helper execution. This is the part of the
exact helper seam that should consume the existing statement-level helper
summary lemmas from `SourceSemantics.lean`. -/
def stmtTouchesDirectInternalHelperSurface : Stmt → Bool
  | .internalCall _ _ =>
      true
  | .internalCallAssign _ _ _ =>
      true
  | _ => false

/-- Direct helper statements with no source-level return binding. These match
the `Stmt.internalCall` source-summary shape exactly. -/
def stmtTouchesDirectInternalHelperCallSurface : Stmt → Bool
  | .internalCall _ _ => true
  | _ => false

/-- Direct helper statements that bind helper returns into source locals. These
match the `Stmt.internalCallAssign` source-summary shape exactly. -/
def stmtTouchesDirectInternalHelperAssignSurface : Stmt → Bool
  | .internalCallAssign _ _ _ => true
  | _ => false

/-- Expression-position internal helper execution at the current statement head.
This isolates the cases that should consume the expression-level helper-summary
soundness and world-preservation lemmas directly, rather than bundling them
with direct helper statements or recursive structural transport. -/
def stmtTouchesExprInternalHelperSurface : Stmt → Bool
  | .panicCode _ => false
  | .panic _ => false
  | .letVar _ value | .assignVar _ value | .setStorage _ value
  | .setStorageAddr _ value | .setImmutable _ value | .setStorageWord _ _ value | .storageArrayPush _ value =>
      exprTouchesInternalHelperSurface value
  | .setMapping _ key value | .setMappingWord _ key _ value
  | .setMappingPackedWord _ key _ _ value | .setMappingUint _ key value
  | .setStructMember _ key _ value =>
      exprTouchesInternalHelperSurface key ||
        exprTouchesInternalHelperSurface value
  | .setMappingChain _ keys value =>
      keys.any exprTouchesInternalHelperSurface ||
        exprTouchesInternalHelperSurface value
  | .setMapping2 _ key1 key2 value | .setMapping2Word _ key1 key2 _ value
  | .setStructMember2 _ key1 key2 _ value =>
      exprTouchesInternalHelperSurface key1 ||
        exprTouchesInternalHelperSurface key2 ||
        exprTouchesInternalHelperSurface value
  | .setStorageArrayElement _ index value
  | .mstore index value | .tstore index value  =>
      exprTouchesInternalHelperSurface index ||
        exprTouchesInternalHelperSurface value
  | .require cond _ | .return cond =>
      exprTouchesInternalHelperSurface cond
  | .returnCodeData pointer =>
      exprTouchesInternalHelperSurface pointer
  | .ite cond _ _ =>
      exprTouchesInternalHelperSurface cond
  | .forEach _ count _ | .forEachSetBit _ count _ =>
      exprTouchesInternalHelperSurface count
  | .calldatacopy destOffset sourceOffset size
  | .returndataCopy destOffset sourceOffset size =>
      exprTouchesInternalHelperSurface destOffset ||
        exprTouchesInternalHelperSurface sourceOffset ||
        exprTouchesInternalHelperSurface size
  | .internalCall _ _ | .internalCallAssign _ _ _ | .stop
  | .revertEmpty | .revertReturndata | .externalCallBind _ _ _ | .tryExternalCallBind _ _ _ _ | .ecm _ _
  | .storageArrayPop _ | .returnValues _ | .returnArray _
  | .returnBytes _ | .returnStorageWords _ | .emit _ _
  | .rawLog _ _ _ => false
  | .requireError cond _ args =>
      exprTouchesInternalHelperSurface cond ||
        args.any exprTouchesInternalHelperSurface
  | .revertError _ args => args.any exprTouchesInternalHelperSurface
  | .unsafeBlock _ _ | .unsafeYul _ | .matchAdt _ _ _ => true

/-- Recursive structural internal-helper transport at the current statement
head. This isolates `ite` / `forEach` obligations whose proof burden is mainly
list-level recursion rather than direct helper-summary consumption. -/
def stmtTouchesStructuralInternalHelperSurface : Stmt → Bool
  | .panicCode _ => false
  | .panic _ => false
  | .ite _ thenBranch elseBranch =>
      stmtListTouchesInternalHelperSurface thenBranch ||
        stmtListTouchesInternalHelperSurface elseBranch
  | .forEach _ _ body | .forEachSetBit _ _ body =>
      stmtListTouchesInternalHelperSurface body
  | .letVar _ _ | .assignVar _ _ | .setStorage _ _ | .require _ _
  | .return _ | .returnCodeData _ | .internalCall _ _ | .internalCallAssign _ _ _
  | .stop | .setStorageAddr _ _ | .setImmutable _ _ | .setStorageWord _ _ _ | .mstore _ _ | .tstore _ _
 
  | .calldatacopy _ _ _ | .returndataCopy _ _ _
  | .revertEmpty | .revertReturndata | .externalCallBind _ _ _ | .tryExternalCallBind _ _ _ _ | .ecm _ _
  | .setMapping _ _ _ | .setMappingWord _ _ _ _
  | .setMappingPackedWord _ _ _ _ _ | .setMapping2 _ _ _ _
  | .setMapping2Word _ _ _ _ _ | .setMappingUint _ _ _
  | .setMappingChain _ _ _
  | .setStructMember _ _ _ _ | .setStructMember2 _ _ _ _ _
  | .storageArrayPush _ _ | .storageArrayPop _
  | .setStorageArrayElement _ _ _ | .requireError _ _ _
  | .revertError _ _ | .returnValues _ | .returnArray _
  | .returnBytes _ | .returnStorageWords _ | .emit _ _
  | .rawLog _ _ _ => false
  | .unsafeBlock _ _ | .unsafeYul _ | .matchAdt _ _ _ => true

def stmtTouchesUnsupportedForeignSurface : Stmt → Bool
  | .panicCode _ => false
  | .panic _ => false
  | .letVar _ value | .assignVar _ value | .setStorage _ value
  | .setStorageAddr _ value | .setImmutable _ value | .setStorageWord _ _ value | .storageArrayPush _ value =>
      exprTouchesUnsupportedForeignSurface value
  | .setMapping _ key value | .setMappingWord _ key _ value
  | .setMappingPackedWord _ key _ _ value | .setMappingUint _ key value
  | .setStructMember _ key _ value =>
      exprTouchesUnsupportedForeignSurface key ||
        exprTouchesUnsupportedForeignSurface value
  | .setMappingChain _ keys value =>
      keys.any exprTouchesUnsupportedForeignSurface ||
        exprTouchesUnsupportedForeignSurface value
  | .setMapping2 _ key1 key2 value | .setMapping2Word _ key1 key2 _ value
  | .setStructMember2 _ key1 key2 _ value =>
      exprTouchesUnsupportedForeignSurface key1 ||
        exprTouchesUnsupportedForeignSurface key2 ||
        exprTouchesUnsupportedForeignSurface value
  | .setStorageArrayElement _ index value
  | .mstore index value | .tstore index value  =>
      exprTouchesUnsupportedForeignSurface index ||
        exprTouchesUnsupportedForeignSurface value
  | .require cond _ | .return cond =>
      exprTouchesUnsupportedForeignSurface cond
  | .returnCodeData pointer =>
      exprTouchesUnsupportedForeignSurface pointer
  | .externalCallBind _ _ args => args.any exprTouchesUnsupportedForeignSurface
  | .tryExternalCallBind _ _ _ args => args.any exprTouchesUnsupportedForeignSurface
  | .ecm _ _ => true
  | .calldatacopy destOffset sourceOffset size
  | .returndataCopy destOffset sourceOffset size =>
      exprTouchesUnsupportedForeignSurface destOffset ||
        exprTouchesUnsupportedForeignSurface sourceOffset ||
        exprTouchesUnsupportedForeignSurface size
  | .stop
  | .internalCall _ _ | .internalCallAssign _ _ _
  | .revertEmpty | .revertReturndata
  | .storageArrayPop _
  | .returnValues _ | .returnArray _
  | .returnBytes _ | .returnStorageWords _ | .rawLog _ _ _ => false
  | .requireError cond _ args =>
      exprTouchesUnsupportedForeignSurface cond ||
        args.any exprTouchesUnsupportedForeignSurface
  | .revertError _ args => args.any exprTouchesUnsupportedForeignSurface
  | .emit _ args => args.any exprTouchesUnsupportedForeignSurface
  | .unsafeBlock _ _ | .unsafeYul _ | .matchAdt _ _ _ => true
  | .ite cond thenBranch elseBranch =>
      exprTouchesUnsupportedForeignSurface cond ||
        stmtListTouchesUnsupportedForeignSurface thenBranch ||
        stmtListTouchesUnsupportedForeignSurface elseBranch
  | .forEach _ count body | .forEachSetBit _ count body =>
      exprTouchesUnsupportedForeignSurface count ||
        stmtListTouchesUnsupportedForeignSurface body

def stmtTouchesUnsupportedLowLevelSurface : Stmt → Bool
  | .panicCode _ => false
  | .panic _ => false
  | .letVar _ value | .assignVar _ value | .setStorage _ value
  | .setStorageAddr _ value | .setImmutable _ value | .setStorageWord _ _ value | .storageArrayPush _ value =>
      exprTouchesUnsupportedLowLevelSurface value
  | .setMapping _ key value | .setMappingWord _ key _ value
  | .setMappingPackedWord _ key _ _ value | .setMappingUint _ key value
  | .setStructMember _ key _ value =>
      exprTouchesUnsupportedLowLevelSurface key ||
        exprTouchesUnsupportedLowLevelSurface value
  | .setMappingChain _ keys value =>
      keys.any exprTouchesUnsupportedLowLevelSurface ||
        exprTouchesUnsupportedLowLevelSurface value
  | .setMapping2 _ key1 key2 value | .setMapping2Word _ key1 key2 _ value
  | .setStructMember2 _ key1 key2 _ value =>
      exprTouchesUnsupportedLowLevelSurface key1 ||
        exprTouchesUnsupportedLowLevelSurface key2 ||
        exprTouchesUnsupportedLowLevelSurface value
  | .setStorageArrayElement _ index value
  | .mstore index value | .tstore index value =>
      exprTouchesUnsupportedLowLevelSurface index ||
        exprTouchesUnsupportedLowLevelSurface value
  | .require cond _ | .return cond =>
      exprTouchesUnsupportedLowLevelSurface cond
  | .returnCodeData _ => true
  | .calldatacopy destOffset sourceOffset size
  | .returndataCopy destOffset sourceOffset size =>
      exprTouchesUnsupportedLowLevelSurface destOffset ||
        exprTouchesUnsupportedLowLevelSurface sourceOffset ||
        exprTouchesUnsupportedLowLevelSurface size
  | .revertEmpty | .revertReturndata => false
  | .externalCallBind _ _ args => args.any exprTouchesUnsupportedLowLevelSurface
  | .tryExternalCallBind _ _ _ args => args.any exprTouchesUnsupportedLowLevelSurface
  | .stop
  | .internalCall _ _ | .internalCallAssign _ _ _
  | .ecm _ _ | .storageArrayPop _
  | .returnValues _ | .returnArray _
  | .returnBytes _ | .returnStorageWords _ | .rawLog _ _ _ => false
  | .requireError cond _ args =>
      exprTouchesUnsupportedLowLevelSurface cond ||
        args.any exprTouchesUnsupportedLowLevelSurface
  | .revertError _ args => args.any exprTouchesUnsupportedLowLevelSurface
  | .emit _ args => args.any exprTouchesUnsupportedLowLevelSurface
  | .unsafeBlock _ _ | .unsafeYul _ | .matchAdt _ _ _ => true
  | .ite cond thenBranch elseBranch =>
      exprTouchesUnsupportedLowLevelSurface cond ||
        stmtListTouchesUnsupportedLowLevelSurface thenBranch ||
        stmtListTouchesUnsupportedLowLevelSurface elseBranch
  | .forEach _ count body | .forEachSetBit _ count body =>
      exprTouchesUnsupportedLowLevelSurface count ||
        stmtListTouchesUnsupportedLowLevelSurface body

def stmtTouchesUnsupportedContractSurface (stmt : Stmt) : Bool :=
  match stmt with
  | .letVar _ value | .assignVar _ value | .setStorage _ value =>
      exprTouchesUnsupportedContractSurface value
  | .setStorageAddr _ value =>
      exprTouchesUnsupportedContractSurface value
  | .setImmutable _ _ => true
  | .setStorageWord _ _ value =>
      exprTouchesUnsupportedContractSurface value
  | .require cond _ | .return cond =>
      exprTouchesUnsupportedContractSurface cond
  | .returnCodeData _ => true
  | .mstore offset value | .tstore offset value =>
      exprTouchesUnsupportedContractSurface offset ||
        exprTouchesUnsupportedContractSurface value
  | .calldatacopy destOffset sourceOffset size
  | .returndataCopy destOffset sourceOffset size =>
      exprTouchesUnsupportedContractSurface destOffset ||
        exprTouchesUnsupportedContractSurface sourceOffset ||
        exprTouchesUnsupportedContractSurface size
  | .stop => false
  | .revertEmpty | .revertReturndata => false
  | .ite cond thenBranch elseBranch =>
      exprTouchesUnsupportedContractSurface cond ||
        stmtListTouchesUnsupportedContractSurface thenBranch ||
        stmtListTouchesUnsupportedContractSurface elseBranch
  | .setMapping _ _ _ | .setMappingWord _ _ _ _ | .setMappingPackedWord _ _ _ _ _
  | .setMapping2 _ _ _ _ | .setMapping2Word _ _ _ _ _ | .setMappingUint _ _ _
  | .setMappingChain _ _ _
  | .setStructMember _ _ _ _ | .setStructMember2 _ _ _ _ _
  | .storageArrayPush _ _ | .storageArrayPop _ | .setStorageArrayElement _ _ _
  | .requireError _ _ _ | .revertError _ _ | .returnValues _ | .returnArray _
  | .returnBytes _ | .returnStorageWords _
  | .emit _ _ | .internalCall _ _ | .internalCallAssign _ _ _
  | .rawLog _ _ _ | .externalCallBind _ _ _ | .ecm _ _
  | .tryExternalCallBind _ _ _ _ | .unsafeBlock _ _ | .unsafeYul _ | .matchAdt _ _ _
  | .panicCode _ | .panic _ => true
  | .forEach _ (.literal _) body =>
      stmtListTouchesUnsupportedContractSurface body
  | .forEach _ _ _ | .forEachSetBit _ _ _ => true

def stmtTouchesUnsupportedContractSurfaceWithEvents
    (events : List EventDef) (stmt : Stmt) : Bool :=
  match stmt with
  | .emit eventName args =>
      args.any exprTouchesUnsupportedContractSurface ||
        !eventEmissionProofSupported events eventName args
  | .ite cond thenBranch elseBranch =>
      exprTouchesUnsupportedContractSurface cond ||
        stmtListTouchesUnsupportedContractSurfaceWithEvents events thenBranch ||
        stmtListTouchesUnsupportedContractSurfaceWithEvents events elseBranch
  | _ => stmtTouchesUnsupportedContractSurface stmt

def stmtListTouchesUnsupportedContractSurface : List Stmt → Bool
  | [] => false
  | stmt :: rest =>
      stmtTouchesUnsupportedContractSurface stmt ||
        stmtListTouchesUnsupportedContractSurface rest

def stmtListTouchesUnsupportedContractSurfaceWithEvents
    (events : List EventDef) : List Stmt → Bool
  | [] => false
  | stmt :: rest =>
      stmtTouchesUnsupportedContractSurfaceWithEvents events stmt ||
        stmtListTouchesUnsupportedContractSurfaceWithEvents events rest

/-- Direct event-emission heads admitted by the top-level scalar-event slice.
Recursive event occurrences remain outside this predicate. -/
def stmtTouchesEventSurface : Stmt → Bool
  | .emit _ _ => true
  | _ => false

/-- Weaker contract-surface gate used by the Tier 2 singleton storage-write
bridge: ordinary unsupported contract effects remain excluded, but the proved
singleton mapping-write heads are admitted. -/
def stmtTouchesUnsupportedContractSurfaceExceptMappingWrites (stmt : Stmt) : Bool :=
  match stmt with
  | .setMapping _ _ _ | .setMappingWord _ _ _ _ | .setMappingPackedWord _ _ _ _ _
  | .setMappingUint _ _ _ | .setStructMember _ _ _ _ | .setMappingChain _ _ _
  | .setMapping2 _ _ _ _ | .setMapping2Word _ _ _ _ _ | .setStructMember2 _ _ _ _ _ =>
      false
  | _ => stmtTouchesUnsupportedContractSurface stmt

def stmtListTouchesUnsupportedCoreSurface : List Stmt → Bool
  | [] => false
  | stmt :: rest =>
      stmtTouchesUnsupportedCoreSurface stmt ||
        stmtListTouchesUnsupportedCoreSurface rest

def stmtListTouchesUnsupportedStateSurface : List Stmt → Bool
  | [] => false
  | stmt :: rest =>
      stmtTouchesUnsupportedStateSurface stmt ||
        stmtListTouchesUnsupportedStateSurface rest

def stmtListTouchesUnsupportedStateSurfaceExceptMappingWrites : List Stmt → Bool
  | [] => false
  | stmt :: rest =>
      stmtTouchesUnsupportedStateSurfaceExceptMappingWrites stmt ||
        stmtListTouchesUnsupportedStateSurfaceExceptMappingWrites rest

def stmtListTouchesUnsupportedCallSurface : List Stmt → Bool
  | [] => false
  | stmt :: rest =>
      stmtTouchesUnsupportedCallSurface stmt ||
        stmtListTouchesUnsupportedCallSurface rest

def stmtListTouchesUnsupportedHelperSurface : List Stmt → Bool
  | [] => false
  | stmt :: rest =>
      stmtTouchesUnsupportedHelperSurface stmt ||
        stmtListTouchesUnsupportedHelperSurface rest

/-- List-level narrow helper-effect surface used to target only genuine
internal-helper execution in the exact helper-aware induction seam. -/
def stmtListTouchesInternalHelperSurface : List Stmt → Bool
  | [] => false
  | stmt :: rest =>
      stmtTouchesInternalHelperSurface stmt ||
        stmtListTouchesInternalHelperSurface rest

def stmtListTouchesDirectInternalHelperSurface : List Stmt → Bool
  | [] => false
  | stmt :: rest =>
      stmtTouchesDirectInternalHelperSurface stmt ||
        stmtListTouchesDirectInternalHelperSurface rest

def stmtListTouchesDirectInternalHelperCallSurface : List Stmt → Bool
  | [] => false
  | stmt :: rest =>
      stmtTouchesDirectInternalHelperCallSurface stmt ||
        stmtListTouchesDirectInternalHelperCallSurface rest

def stmtListTouchesDirectInternalHelperAssignSurface : List Stmt → Bool
  | [] => false
  | stmt :: rest =>
      stmtTouchesDirectInternalHelperAssignSurface stmt ||
        stmtListTouchesDirectInternalHelperAssignSurface rest

def stmtListTouchesExprInternalHelperSurface : List Stmt → Bool
  | [] => false
  | stmt :: rest =>
      stmtTouchesExprInternalHelperSurface stmt ||
        stmtListTouchesExprInternalHelperSurface rest

def stmtListTouchesStructuralInternalHelperSurface : List Stmt → Bool
  | [] => false
  | stmt :: rest =>
      stmtTouchesStructuralInternalHelperSurface stmt ||
        stmtListTouchesStructuralInternalHelperSurface rest

def stmtListTouchesUnsupportedForeignSurface : List Stmt → Bool
  | [] => false
  | stmt :: rest =>
      stmtTouchesUnsupportedForeignSurface stmt ||
        stmtListTouchesUnsupportedForeignSurface rest

def stmtListTouchesUnsupportedLowLevelSurface : List Stmt → Bool
  | [] => false
  | stmt :: rest =>
      stmtTouchesUnsupportedLowLevelSurface stmt ||
        stmtListTouchesUnsupportedLowLevelSurface rest

def stmtListTouchesUnsupportedEffectSurface : List Stmt → Bool
  | [] => false
  | stmt :: rest =>
      stmtTouchesUnsupportedEffectSurface stmt ||
        stmtListTouchesUnsupportedEffectSurface rest

/-- List-level weakening of `stmtListTouchesUnsupportedContractSurface` used by
the Tier 2 singleton mapping-write bridge. -/
def stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites : List Stmt → Bool
  | [] => false
  | stmt :: rest =>
      stmtTouchesUnsupportedContractSurfaceExceptMappingWrites stmt ||
        stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites rest
end

mutual
/-- Events-aware refinement of `stmtTouchesUnsupportedEffectSurface`.

`stmtTouchesUnsupportedEffectSurface` rejects every `emit`, so a body carrying
an event emission can never satisfy the four-surface (core/state/call/effect)
decomposition and has to be routed through the separate scalar-event gate
`stmtTouchesUnsupportedContractSurfaceWithEvents` instead. This variant accepts
exactly the emission heads that gate already proves, so the event slice becomes
reachable from the same decomposition every other statement head uses. -/
def stmtTouchesUnsupportedEffectSurfaceWithEvents
    (events : List EventDef) : Stmt → Bool
  | .emit eventName args =>
      args.any exprTouchesUnsupportedContractSurface ||
        !eventEmissionProofSupported events eventName args
  | .ite _ thenBranch elseBranch =>
      stmtListTouchesUnsupportedEffectSurfaceWithEvents events thenBranch ||
        stmtListTouchesUnsupportedEffectSurfaceWithEvents events elseBranch
  | stmt => stmtTouchesUnsupportedEffectSurface stmt

def stmtListTouchesUnsupportedEffectSurfaceWithEvents
    (events : List EventDef) : List Stmt → Bool
  | [] => false
  | stmt :: rest =>
      stmtTouchesUnsupportedEffectSurfaceWithEvents events stmt ||
        stmtListTouchesUnsupportedEffectSurfaceWithEvents events rest
end

private theorem compileStmtWithFork_cancun_eq_compileStmt
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String)
    (adtTypes : List AdtTypeDef) (stmt : Stmt)
    (internalFunctions : List FunctionSpec := []) :
    CompilationModel.compileStmtWithFork fields events errors dynamicSource
      internalRetNames isInternal inScopeNames adtTypes Verity.Core.Intrinsics.HardFork.cancun
      stmt internalFunctions =
    CompilationModel.compileStmt fields events errors dynamicSource
      internalRetNames isInternal inScopeNames adtTypes stmt internalFunctions := rfl

private theorem compileStmtListWithFork_cancun_eq_compileStmtList
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String)
    (adtTypes : List AdtTypeDef) (stmts : List Stmt)
    (internalFunctions : List FunctionSpec := []) :
    CompilationModel.compileStmtListWithFork fields events errors dynamicSource
      internalRetNames isInternal inScopeNames adtTypes Verity.Core.Intrinsics.HardFork.cancun
      stmts internalFunctions =
    CompilationModel.compileStmtList fields events errors dynamicSource
      internalRetNames isInternal inScopeNames adtTypes stmts internalFunctions := rfl

/-- The body of a contract-surface-closed `forEach` head is itself
contract-surface closed: the gate only admits literal bounds with a
closed body. -/
theorem stmtListTouchesUnsupportedContractSurface_of_forEach_surfaceClosed
    {varName : String}
    {count : Expr}
    {body : List Stmt}
    (hsurface :
      stmtTouchesUnsupportedContractSurface (.forEach varName count body) = false) :
    stmtListTouchesUnsupportedContractSurface body = false := by
  cases count
  case literal k => exact hsurface
  all_goals exact Bool.noConfusion hsurface

/-- Statement-level catalog agnosticism of `compileStmt` for statements of size below `n`. -/
private def CompileStmtCatalogAgnosticBelow (n : Nat) (fields : List Field)
    (events : List EventDef) (errors : List ErrorDef) : Prop :=
  ∀ (stmt : Stmt) (scope : List String),
    sizeOf stmt < n →
    stmtTouchesUnsupportedContractSurface stmt = false →
    CompilationModel.compileStmt fields events errors .calldata [] false scope [] stmt [] =
      CompilationModel.compileStmt fields [] [] .calldata [] false scope [] stmt []

/-- List-level catalog agnosticism of `compileStmtList` for lists of size below `n`. -/
private def CompileStmtListCatalogAgnosticBelow (n : Nat) (fields : List Field)
    (events : List EventDef) (errors : List ErrorDef) : Prop :=
  ∀ (stmts : List Stmt) (scope : List String),
    sizeOf stmts < n →
    stmtListTouchesUnsupportedContractSurface stmts = false →
    CompilationModel.compileStmtList fields events errors .calldata [] false scope [] stmts [] =
      CompilationModel.compileStmtList fields [] [] .calldata [] false scope [] stmts []

private theorem compileStmt_eventsErrorsAgnostic_step
    {n : Nat} {fields : List Field} {events : List EventDef} {errors : List ErrorDef}
    (ih : CompileStmtListCatalogAgnosticBelow n fields events errors) :
    CompileStmtCatalogAgnosticBelow (n + 1) fields events errors := by
  intro stmt scope hlt hsurface
  cases stmt with
  | ite cond thenBranch elseBranch =>
      simp only [stmtTouchesUnsupportedContractSurface, Bool.or_eq_false_iff] at hsurface
      simp only [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
        compileStmtListWithFork_cancun_eq_compileStmtList,
        ih thenBranch scope (by simp [Stmt.ite.sizeOf_spec] at hlt; omega) hsurface.1.2,
        ih elseBranch scope (by simp [Stmt.ite.sizeOf_spec] at hlt; omega) hsurface.2]
  | forEach varName count body =>
      simp only [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
        compileStmtListWithFork_cancun_eq_compileStmtList,
        ih body (CompilationModel.forEachBodyScope scope varName count body)
          (by simp [Stmt.forEach.sizeOf_spec] at hlt; omega)
          (stmtListTouchesUnsupportedContractSurface_of_forEach_surfaceClosed hsurface)]
  | letVar | assignVar | setStorage | setStorageAddr | setImmutable | setStorageWord
  | require | «return» | mstore | tstore | calldatacopy | returndataCopy
  | revertEmpty | revertReturndata | stop =>
      simp only [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork]
  | _ => simp [stmtTouchesUnsupportedContractSurface] at hsurface

private theorem compileStmtList_eventsErrorsAgnostic_step
    {n : Nat} {fields : List Field} {events : List EventDef} {errors : List ErrorDef}
    (ihStmt : CompileStmtCatalogAgnosticBelow n fields events errors)
    (ihList : CompileStmtListCatalogAgnosticBelow n fields events errors) :
    CompileStmtListCatalogAgnosticBelow (n + 1) fields events errors := by
  intro stmts scope hlt hsurface
  cases stmts with
  | nil => simp only [CompilationModel.compileStmtList, CompilationModel.compileStmtListWithFork]
  | cons s ss =>
      simp only [stmtListTouchesUnsupportedContractSurface, Bool.or_eq_false_iff] at hsurface
      simp only [CompilationModel.compileStmtList,
        CompilationModel.compileStmtListWithFork, bind, Except.bind]
      rw [compileStmtWithFork_cancun_eq_compileStmt,
        ihStmt s scope (by simp [List.cons.sizeOf_spec] at hlt; omega) hsurface.1,
        compileStmtListWithFork_cancun_eq_compileStmtList,
        ihList ss (collectStmtBindNames s ++ scope)
          (by simp [List.cons.sizeOf_spec] at hlt; omega) hsurface.2]
      simp only [compileStmtWithFork_cancun_eq_compileStmt,
        compileStmtListWithFork_cancun_eq_compileStmtList]

/-- `compileStmt` consults `events` only in the `.emit` arm and `errors` only in
the `.requireError`/`.revertError` arms, all of which the plain contract-surface
gate excludes. Surface-closed statements therefore compile identically under any
event/error catalog, which lets event-aware specs reuse the helper-free generic
step library for their non-emit heads. -/
private theorem compileStmt_eventsErrorsAgnostic_aux
    (n : Nat)
    (fields : List Field)
    (events : List EventDef)
    (errors : List ErrorDef) :
    (∀ (stmt : Stmt) (scope : List String),
      sizeOf stmt < n →
      stmtTouchesUnsupportedContractSurface stmt = false →
      CompilationModel.compileStmt fields events errors .calldata [] false scope [] stmt [] =
        CompilationModel.compileStmt fields [] [] .calldata [] false scope [] stmt []) ∧
    (∀ (stmts : List Stmt) (scope : List String),
      sizeOf stmts < n →
      stmtListTouchesUnsupportedContractSurface stmts = false →
      CompilationModel.compileStmtList fields events errors .calldata [] false scope [] stmts [] =
        CompilationModel.compileStmtList fields [] [] .calldata [] false scope [] stmts []) := by
  induction n with
  | zero =>
      exact ⟨fun _ _ hlt => absurd hlt (Nat.not_lt_zero _),
        fun _ _ hlt => absurd hlt (Nat.not_lt_zero _)⟩
  | succ n ih =>
      exact ⟨compileStmt_eventsErrorsAgnostic_step ih.2,
        compileStmtList_eventsErrorsAgnostic_step ih.1 ih.2⟩

/-- Surface-closed statements compile identically under any event/error
catalog. -/
theorem compileStmt_eventsErrorsAgnostic_of_contractSurfaceClosed
    {fields : List Field}
    {events : List EventDef}
    {errors : List ErrorDef}
    {scope : List String}
    {stmt : Stmt}
    (hsurface : stmtTouchesUnsupportedContractSurface stmt = false) :
    CompilationModel.compileStmt fields events errors .calldata [] false scope [] stmt [] =
      CompilationModel.compileStmt fields [] [] .calldata [] false scope [] stmt [] :=
  (compileStmt_eventsErrorsAgnostic_aux (sizeOf stmt + 1) fields events errors).1
    stmt scope (Nat.lt_succ_of_le (Nat.le_refl _)) hsurface

/-- Surface-closed statement lists compile identically under any event/error
catalog. -/
theorem compileStmtList_eventsErrorsAgnostic_of_contractSurfaceClosed
    {fields : List Field}
    {events : List EventDef}
    {errors : List ErrorDef}
    {scope : List String}
    {stmts : List Stmt}
    (hsurface : stmtListTouchesUnsupportedContractSurface stmts = false) :
    CompilationModel.compileStmtList fields events errors .calldata [] false scope [] stmts [] =
      CompilationModel.compileStmtList fields [] [] .calldata [] false scope [] stmts [] :=
  (compileStmt_eventsErrorsAgnostic_aux (sizeOf stmts + 1) fields events errors).2
    stmts scope (Nat.lt_succ_of_le (Nat.le_refl _)) hsurface

theorem exprListTouchesUnsupportedContractSurface_eq_false_of_emit_contractSurfaceWithEventsClosed
    {events : List EventDef}
    {eventName : String}
    {args : List Expr}
    (hsurface :
      stmtTouchesUnsupportedContractSurfaceWithEvents events (.emit eventName args) = false) :
    args.any exprTouchesUnsupportedContractSurface = false := by
  simpa [stmtTouchesUnsupportedContractSurfaceWithEvents] using
    (Bool.or_eq_false_iff.mp hsurface).1

theorem eventEmissionProofSupported_eq_true_of_emit_contractSurfaceWithEventsClosed
    {events : List EventDef}
    {eventName : String}
    {args : List Expr}
    (hsurface :
      stmtTouchesUnsupportedContractSurfaceWithEvents events (.emit eventName args) = false) :
    eventEmissionProofSupported events eventName args = true := by
  have hsupport :
      (!eventEmissionProofSupported events eventName args) = false := by
    simpa [stmtTouchesUnsupportedContractSurfaceWithEvents] using
      (Bool.or_eq_false_iff.mp hsurface).2
  cases h : eventEmissionProofSupported events eventName args <;> simp [h] at hsupport ⊢

mutual
  /-- Collect direct internal-helper callee names mentioned by an expression. This
  inventory is used to define a compositional helper-summary interface without yet
  changing the current generic theorem's fail-closed helper boundary. -/
  def exprInternalHelperCallNames : Expr → List String
    | .internalCall calleeName args =>
        calleeName :: exprListInternalHelperCallNames args
    | .mapping _ key | .mappingWord _ key _ | .mappingPackedWord _ key _ _
    | .mappingUint _ key | .structMember _ key _ | .arrayElement _ key
    | .memoryArrayElement _ key
    | .arrayElementWord _ key _ _
    | .arrayElementDynamicWord _ key _
    | .arrayElementDynamicDataOffset _ key
    | .arrayElementDynamicMemberLength _ key _
    | .arrayElementDynamicMemberDataOffset _ key _
    | .storageArrayElement _ key | .mload key | .tload key | .calldataload key
    | .extcodesize key | .returndataOptionalBoolAt key =>
        exprInternalHelperCallNames key
    | .paramDynamicMemberElement _ _ innerKey =>
        exprInternalHelperCallNames innerKey
    | .arrayElementDynamicMemberElement _ key _ innerKey =>
        exprInternalHelperCallNames key ++ exprInternalHelperCallNames innerKey
    | .mappingChain _ keys =>
        exprListInternalHelperCallNames keys
    | .mapping2 _ key1 key2 | .mapping2Word _ key1 key2 _
    | .structMember2 _ key1 key2 _ =>
        exprInternalHelperCallNames key1 ++ exprInternalHelperCallNames key2
    | .call gas target value inOffset inSize outOffset outSize =>
        exprInternalHelperCallNames gas ++ exprInternalHelperCallNames target ++
          exprInternalHelperCallNames value ++ exprInternalHelperCallNames inOffset ++
          exprInternalHelperCallNames inSize ++ exprInternalHelperCallNames outOffset ++
          exprInternalHelperCallNames outSize
    | .staticcall gas target inOffset inSize outOffset outSize =>
        exprInternalHelperCallNames gas ++ exprInternalHelperCallNames target ++
          exprInternalHelperCallNames inOffset ++ exprInternalHelperCallNames inSize ++
          exprInternalHelperCallNames outOffset ++ exprInternalHelperCallNames outSize
    | .delegatecall gas target inOffset inSize outOffset outSize =>
        exprInternalHelperCallNames gas ++ exprInternalHelperCallNames target ++
          exprInternalHelperCallNames inOffset ++ exprInternalHelperCallNames inSize ++
          exprInternalHelperCallNames outOffset ++ exprInternalHelperCallNames outSize
    | .keccak256 offset size =>
        exprInternalHelperCallNames offset ++ exprInternalHelperCallNames size
    | .add a b | .sub a b | .mul a b | .div a b | .sdiv a b | .mod a b | .smod a b
    | .bitAnd a b | .bitOr a b | .bitXor a b | .shl a b | .shr a b | .sar a b
    | .byte a b | .signextend a b | .eq a b | .ge a b | .gt a b | .sgt a b | .lt a b
    | .slt a b | .le a b | .logicalAnd a b | .logicalOr a b | .wMulDown a b
    | .wDivUp a b | .min a b | .max a b | .ceilDiv a b =>
        exprInternalHelperCallNames a ++ exprInternalHelperCallNames b
    | .mulDivDown a b c | .mulDivUp a b c
    | .mulDiv512Down a b c | .mulDiv512Up a b c =>
        exprInternalHelperCallNames a ++ exprInternalHelperCallNames b ++
          exprInternalHelperCallNames c
    | .bitNot a | .logicalNot a =>
        exprInternalHelperCallNames a
    | .ite cond thenVal elseVal =>
        exprInternalHelperCallNames cond ++ exprInternalHelperCallNames thenVal ++
          exprInternalHelperCallNames elseVal
    | .forkIfAtLeast _ thenExpr elseExpr =>
        exprInternalHelperCallNames thenExpr ++ exprInternalHelperCallNames elseExpr
    | .externalCall _ args | .intrinsic _ _ _ args =>
        exprListInternalHelperCallNames args
    -- Pure leaves: no internal helper calls. Listed explicitly (rather than
    -- via `| _ => []`) so the equation-lemma deriver does not have to
    -- enumerate the complement of every pattern above. This avoids the
    -- `_mutual.eq_def` 200 000-heartbeat ceiling when new `Expr` constructors
    -- land (verity#1842 captured the same pitfall for the Expr→Except
    -- validators).
    | .literal _ | .param _ | .immutable _ | .constructorArg _
    | .storage _ | .storageAddr _
    | .caller | .contractAddress | .txOrigin | .chainid | .msgValue | .selfBalance
    | .baseFee | .gasPrice | .blockTimestamp | .blockNumber | .blobbasefee
    | .calldatasize | .returndataSize
    | .localVar _ | .arrayLength _ | .memoryArrayLength _ | .storageArrayLength _
    | .paramDynamicHeadWord _ _ | .paramDynamicStaticComposite _ _
    | .paramDynamicMemberLength _ _
    | .paramDynamicMemberDataOffset _ _
    | .dynamicBytesEq _ _
    | .adtConstruct _ _ _ | .adtTag _ _ | .adtField _ _ _ _ _ =>
        []
  termination_by e => sizeOf e
  decreasing_by all_goals simp_wf; all_goals omega

  def exprListInternalHelperCallNames : List Expr → List String
    | [] => []
    | expr :: rest =>
        exprInternalHelperCallNames expr ++ exprListInternalHelperCallNames rest
  termination_by es => sizeOf es
  decreasing_by all_goals simp_wf; all_goals omega
end

mutual
  /-- Collect direct internal-helper callee names that occur specifically in expression
  positions. These calls must preserve the world on success because the current
  helper-aware expression semantics returns only a value. -/
  def stmtExprHelperCallNames : Stmt → List String
    | .panicCode code => exprInternalHelperCallNames code
    | .panic _ => []
    | .letVar _ value | .assignVar _ value | .setStorage _ value | .setStorageAddr _ value
    | .setImmutable _ value
    | .setStorageWord _ _ value
    | .storageArrayPush _ value | .return value | .require value _ =>
        exprInternalHelperCallNames value
    | .returnCodeData pointer =>
        exprInternalHelperCallNames pointer
    | .setStorageArrayElement _ index value =>
        exprInternalHelperCallNames index ++ exprInternalHelperCallNames value
    | .requireError cond _ args =>
        exprInternalHelperCallNames cond ++ exprListInternalHelperCallNames args
    | .revertError _ args | .emit _ args | .returnValues args
    | .externalCallBind _ _ args | .tryExternalCallBind _ _ _ args | .ecm _ args =>
        exprListInternalHelperCallNames args
    | .mstore offset value | .tstore offset value =>
        exprInternalHelperCallNames offset ++ exprInternalHelperCallNames value
    | .calldatacopy destOffset sourceOffset size
    | .returndataCopy destOffset sourceOffset size =>
        exprInternalHelperCallNames destOffset ++ exprInternalHelperCallNames sourceOffset ++
          exprInternalHelperCallNames size
    | .setMapping _ key value | .setMappingWord _ key _ value
    | .setMappingPackedWord _ key _ _ value | .setMappingUint _ key value
    | .setStructMember _ key _ value =>
        exprInternalHelperCallNames key ++ exprInternalHelperCallNames value
    | .setMappingChain _ keys value =>
        exprListInternalHelperCallNames keys ++ exprInternalHelperCallNames value
    | .setMapping2 _ key1 key2 value | .setMapping2Word _ key1 key2 _ value
    | .setStructMember2 _ key1 key2 _ value =>
        exprInternalHelperCallNames key1 ++ exprInternalHelperCallNames key2 ++
          exprInternalHelperCallNames value
    | .ite cond thenBranch elseBranch =>
        exprInternalHelperCallNames cond ++ stmtListExprHelperCallNames thenBranch ++
          stmtListExprHelperCallNames elseBranch
    | .forEach _ count body | .forEachSetBit _ count body =>
        exprInternalHelperCallNames count ++ stmtListExprHelperCallNames body
    | .internalCall _ args | .internalCallAssign _ _ args =>
        exprListInternalHelperCallNames args
    | .rawLog topics dataOffset dataSize =>
        exprListInternalHelperCallNames topics ++ exprInternalHelperCallNames dataOffset ++
          exprInternalHelperCallNames dataSize
    | .storageArrayPop _ | .returnArray _ | .returnBytes _ | .returnStorageWords _
    | .revertEmpty | .revertReturndata | .stop =>
        []
    | .unsafeBlock _ body => stmtListExprHelperCallNames body
    | .unsafeYul _ => []
    | .matchAdt _ _ branches =>
        matchAdtBranchesExprHelperCallNames branches
  termination_by s => sizeOf s
  decreasing_by all_goals simp_wf; all_goals omega

  def matchAdtBranchesExprHelperCallNames : List (String × List String × List Stmt) → List String
    | [] => []
    | (_, _, body) :: rest =>
        stmtListExprHelperCallNames body ++ matchAdtBranchesExprHelperCallNames rest
  termination_by bs => sizeOf bs
  decreasing_by all_goals simp_wf; all_goals omega

  def stmtListExprHelperCallNames : List Stmt → List String
    | [] => []
    | stmt :: rest =>
        stmtExprHelperCallNames stmt ++ stmtListExprHelperCallNames rest
  termination_by stmts => sizeOf stmts
  decreasing_by all_goals simp_wf; all_goals omega
end

mutual
  /-- Collect direct internal-helper callee names mentioned by a statement list. -/
  def stmtInternalHelperCallNames : Stmt → List String
    | .panicCode code => exprInternalHelperCallNames code
    | .panic _ => []
    | .letVar _ value | .assignVar _ value | .setStorage _ value | .setStorageAddr _ value
    | .setImmutable _ value
    | .setStorageWord _ _ value
    | .storageArrayPush _ value | .return value | .require value _ =>
        exprInternalHelperCallNames value
    | .returnCodeData pointer =>
        exprInternalHelperCallNames pointer
    | .setStorageArrayElement _ index value =>
        exprInternalHelperCallNames index ++ exprInternalHelperCallNames value
    | .requireError cond _ args =>
        exprInternalHelperCallNames cond ++ exprListInternalHelperCallNames args
    | .revertError _ args | .emit _ args | .returnValues args
    | .externalCallBind _ _ args | .tryExternalCallBind _ _ _ args | .ecm _ args =>
        exprListInternalHelperCallNames args
    | .mstore offset value | .tstore offset value =>
        exprInternalHelperCallNames offset ++ exprInternalHelperCallNames value
    | .calldatacopy destOffset sourceOffset size
    | .returndataCopy destOffset sourceOffset size =>
        exprInternalHelperCallNames destOffset ++ exprInternalHelperCallNames sourceOffset ++
          exprInternalHelperCallNames size
    | .setMapping _ key value | .setMappingWord _ key _ value
    | .setMappingPackedWord _ key _ _ value | .setMappingUint _ key value
    | .setStructMember _ key _ value =>
        exprInternalHelperCallNames key ++ exprInternalHelperCallNames value
    | .setMappingChain _ keys value =>
        exprListInternalHelperCallNames keys ++ exprInternalHelperCallNames value
    | .setMapping2 _ key1 key2 value | .setMapping2Word _ key1 key2 _ value
    | .setStructMember2 _ key1 key2 _ value =>
        exprInternalHelperCallNames key1 ++ exprInternalHelperCallNames key2 ++
          exprInternalHelperCallNames value
    | .ite cond thenBranch elseBranch =>
        exprInternalHelperCallNames cond ++ stmtListInternalHelperCallNames thenBranch ++
          stmtListInternalHelperCallNames elseBranch
    | .forEach _ count body | .forEachSetBit _ count body =>
        exprInternalHelperCallNames count ++ stmtListInternalHelperCallNames body
    | .internalCall calleeName args =>
        calleeName :: exprListInternalHelperCallNames args
    | .internalCallAssign _ calleeName args =>
        calleeName :: exprListInternalHelperCallNames args
    | .rawLog topics dataOffset dataSize =>
        exprListInternalHelperCallNames topics ++ exprInternalHelperCallNames dataOffset ++
          exprInternalHelperCallNames dataSize
    | .storageArrayPop _ | .returnArray _ | .returnBytes _ | .returnStorageWords _
    | .revertEmpty | .revertReturndata | .stop =>
        []
    | .unsafeBlock _ body => stmtListInternalHelperCallNames body
    | .unsafeYul _ => []
    | .matchAdt _ _ branches =>
        matchAdtBranchesInternalHelperCallNames branches
  termination_by s => sizeOf s
  decreasing_by all_goals simp_wf; all_goals omega

  def matchAdtBranchesInternalHelperCallNames : List (String × List String × List Stmt) → List String
    | [] => []
    | (_, _, body) :: rest =>
        stmtListInternalHelperCallNames body ++ matchAdtBranchesInternalHelperCallNames rest
  termination_by bs => sizeOf bs
  decreasing_by all_goals simp_wf; all_goals omega

  def stmtListInternalHelperCallNames : List Stmt → List String
    | [] => []
    | stmt :: rest =>
        stmtInternalHelperCallNames stmt ++ stmtListInternalHelperCallNames rest
  termination_by stmts => sizeOf stmts
  decreasing_by all_goals simp_wf; all_goals omega
end

private theorem eraseDups_nodup_and_mem_aux [BEq α] [LawfulBEq α]
    (n : Nat) (l : List α) (hlen : l.length ≤ n) :
    (l.eraseDups).Nodup ∧ (∀ a, a ∈ l.eraseDups ↔ a ∈ l) := by
  induction n generalizing l with
  | zero =>
    have : l = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hlen)
    subst this
    exact ⟨List.Pairwise.nil, fun _ => Iff.rfl⟩
  | succ n ih =>
    match l with
    | [] => exact ⟨List.Pairwise.nil, fun _ => Iff.rfl⟩
    | x :: xs =>
      rw [List.eraseDups_cons]
      have hfilt_len : (xs.filter fun b => !b == x).length ≤ n := by
        have := List.length_filter_le (fun b => !b == x) xs
        simp [List.length_cons] at hlen; omega
      have ⟨ihNd, ihMem⟩ := ih _ hfilt_len
      constructor
      · rw [List.nodup_cons]
        constructor
        · intro h
          have hmf := (ihMem x).mp h
          rw [List.mem_filter] at hmf
          have := hmf.2
          simp at this
        · exact ihNd
      · intro a; constructor
        · intro h; rw [List.mem_cons] at h ⊢
          rcases h with rfl | h
          · exact Or.inl rfl
          · exact Or.inr (List.mem_filter.mp ((ihMem a).mp h)).1
        · intro h; rw [List.mem_cons] at h ⊢
          rcases h with rfl | h
          · exact Or.inl rfl
          · by_cases heq : a == x
            · exact Or.inl (beq_iff_eq.mp heq)
            · exact Or.inr ((ihMem a).mpr (List.mem_filter.mpr ⟨h, by simp [heq]⟩))

private theorem List.eraseDups_nodup [BEq α] [LawfulBEq α]
    (l : List α) : (l.eraseDups).Nodup :=
  (eraseDups_nodup_and_mem_aux l.length l (Nat.le_refl _)).1

private theorem List.mem_eraseDups_iff [BEq α] [LawfulBEq α]
    {a : α} {l : List α} : a ∈ l.eraseDups ↔ a ∈ l :=
  (eraseDups_nodup_and_mem_aux l.length l (Nat.le_refl _)).2 a

private theorem List.mem_eraseDups_of_mem [BEq α] [LawfulBEq α]
    {a : α} {l : List α} (h : a ∈ l) : a ∈ l.eraseDups :=
  List.mem_eraseDups_iff.mpr h

private theorem List.mem_of_mem_eraseDups [BEq α] [LawfulBEq α]
    {a : α} {l : List α} (h : a ∈ l.eraseDups) : a ∈ l :=
  List.mem_eraseDups_iff.mp h

/-- Deduplicated direct helper-callee inventory for a function body. -/
def helperCallNames (fn : FunctionSpec) : List String :=
  (stmtListInternalHelperCallNames fn.body).eraseDups

theorem helperCallNames_nodup (fn : FunctionSpec) :
    (helperCallNames fn).Nodup := by
  simpa [helperCallNames] using List.eraseDups_nodup (stmtListInternalHelperCallNames fn.body)

/-- Deduplicated direct helper-callee inventory for expression-position helper uses. -/
def exprHelperCallNames (fn : FunctionSpec) : List String :=
  (stmtListExprHelperCallNames fn.body).eraseDups

theorem exprHelperCallNames_nodup (fn : FunctionSpec) :
    (exprHelperCallNames fn).Nodup := by
  simpa [exprHelperCallNames] using List.eraseDups_nodup (stmtListExprHelperCallNames fn.body)

mutual
private theorem stmtExprHelperCallNames_subset_stmtInternalHelperCallNames_aux
    (stmt : Stmt)
    {calleeName : String}
    (hstmt : calleeName ∈ stmtExprHelperCallNames stmt) :
    calleeName ∈ stmtInternalHelperCallNames stmt := by
  cases stmt with
  | ite cond thenBranch elseBranch =>
      simp only [stmtExprHelperCallNames, stmtInternalHelperCallNames, List.mem_append] at hstmt ⊢
      exact hstmt.imp (Or.imp id
        (stmtListExprHelperCallNames_subset_stmtListInternalHelperCallNames thenBranch))
        (stmtListExprHelperCallNames_subset_stmtListInternalHelperCallNames elseBranch)
  | forEach var count body | forEachSetBit var count body =>
      simp only [stmtExprHelperCallNames, stmtInternalHelperCallNames, List.mem_append] at hstmt ⊢
      exact hstmt.imp id (stmtListExprHelperCallNames_subset_stmtListInternalHelperCallNames body)
  | internalCall _ _ | internalCallAssign _ _ _ =>
      simp [stmtExprHelperCallNames, stmtInternalHelperCallNames, List.mem_cons] at hstmt ⊢
      exact Or.inr hstmt
  | unsafeBlock reason body =>
      simp only [stmtExprHelperCallNames, stmtInternalHelperCallNames] at hstmt ⊢
      exact stmtListExprHelperCallNames_subset_stmtListInternalHelperCallNames body hstmt
  | matchAdt adtName scrutinee branches =>
      simp only [stmtExprHelperCallNames, stmtInternalHelperCallNames] at hstmt ⊢
      exact matchAdtBranchesExprHelperCallNames_subset_internalHelperCallNames branches hstmt
  | _ =>
      all_goals
        simpa [stmtExprHelperCallNames, stmtInternalHelperCallNames, List.mem_append,
          or_left_comm, or_assoc] using hstmt
termination_by sizeOf stmt

private theorem stmtListExprHelperCallNames_subset_stmtListInternalHelperCallNames
    (stmts : List Stmt)
    {calleeName : String}
    (hmem : calleeName ∈ stmtListExprHelperCallNames stmts) :
    calleeName ∈ stmtListInternalHelperCallNames stmts := by
  match stmts with
  | [] =>
      simpa [stmtListExprHelperCallNames, stmtListInternalHelperCallNames] using hmem
  | stmt :: rest =>
      simp only [stmtListExprHelperCallNames, stmtListInternalHelperCallNames,
        List.mem_append] at hmem ⊢
      rcases hmem with hstmt | hrest
      · exact Or.inl (stmtExprHelperCallNames_subset_stmtInternalHelperCallNames_aux stmt hstmt)
      · exact Or.inr (stmtListExprHelperCallNames_subset_stmtListInternalHelperCallNames rest hrest)
termination_by sizeOf stmts

private theorem matchAdtBranchesExprHelperCallNames_subset_internalHelperCallNames
    (branches : List (String × List String × List Stmt))
    {calleeName : String}
    (hmem : calleeName ∈ matchAdtBranchesExprHelperCallNames branches) :
    calleeName ∈ matchAdtBranchesInternalHelperCallNames branches := by
  match branches with
  | [] => simp [matchAdtBranchesExprHelperCallNames] at hmem
  | (vn, vl, body) :: rest =>
    simp only [matchAdtBranchesExprHelperCallNames,
      matchAdtBranchesInternalHelperCallNames, List.mem_append] at hmem ⊢
    rcases hmem with hbody | hrest
    · exact Or.inl (stmtListExprHelperCallNames_subset_stmtListInternalHelperCallNames body hbody)
    · exact Or.inr (matchAdtBranchesExprHelperCallNames_subset_internalHelperCallNames rest hrest)
termination_by sizeOf branches
end

theorem stmtExprHelperCallNames_subset_stmtInternalHelperCallNames
    (stmt : Stmt) :
    ∀ {calleeName : String},
      calleeName ∈ stmtExprHelperCallNames stmt →
        calleeName ∈ stmtInternalHelperCallNames stmt := by
  intro calleeName hmem
  have : calleeName ∈ stmtListExprHelperCallNames [stmt] := by
    simp [stmtListExprHelperCallNames, hmem]
  have := stmtListExprHelperCallNames_subset_stmtListInternalHelperCallNames [stmt] this
  simp [stmtListInternalHelperCallNames] at this
  exact this

theorem exprHelperCallNames_subset_helperCallNames
    {fn : FunctionSpec}
    {calleeName : String}
    (hmem : calleeName ∈ exprHelperCallNames fn) :
    calleeName ∈ helperCallNames fn := by
  have hexpr : calleeName ∈ stmtListExprHelperCallNames fn.body := by
    exact List.mem_of_mem_eraseDups (show calleeName ∈ (stmtListExprHelperCallNames fn.body).eraseDups from hmem)
  have hhelper : calleeName ∈ stmtListInternalHelperCallNames fn.body :=
    stmtListExprHelperCallNames_subset_stmtListInternalHelperCallNames fn.body hexpr
  exact List.mem_eraseDups_of_mem hhelper

example :
    stmtListTouchesUnsupportedHelperSurface
      [Stmt.ite (.literal 1) [Stmt.internalCall "helper" []] []] = true := by
  decide

example :
    stmtListTouchesUnsupportedForeignSurface
      [Stmt.forEach "i" (.literal 1)
        [Stmt.externalCallBind [] "ext" [.externalCall "ext" []]]] = true := by
  decide

example :
    stmtListTouchesUnsupportedEffectSurface
      [Stmt.ite (.literal 1) [Stmt.emit "Evt" []] []] = true := by
  decide

-- Helper/internal-surface smoke tests omitted: mutual recursion prevents
-- kernel-level `decide` reduction; runtime `native_decide` is not permitted
-- in proof modules by CI hygiene policy.

structure SupportedBodyCoreInterface (fn : FunctionSpec) : Prop where
  surfaceClosed : stmtListTouchesUnsupportedCoreSurface fn.body = false

structure SupportedBodyStateInterface (fn : FunctionSpec) : Prop where
  surfaceClosed : stmtListTouchesUnsupportedStateSurface fn.body = false

structure SupportedBodyStateInterfaceExceptMappingWrites (fn : FunctionSpec) : Prop where
  surfaceClosed : stmtListTouchesUnsupportedStateSurfaceExceptMappingWrites fn.body = false

structure SupportedBodyEffectInterface (fn : FunctionSpec) : Prop where
  surfaceClosed : stmtListTouchesUnsupportedEffectSurface fn.body = false

/-- Effect-surface interface for bodies that emit events. `SupportedBodyEffectInterface`
rejects every `emit`, so it is unusable for event-carrying bodies; this variant
accepts exactly the emission heads the scalar-event slice already proves. -/
structure SupportedBodyEffectInterfaceWithEvents
    (spec : CompilationModel) (fn : FunctionSpec) : Prop where
  surfaceClosed :
    stmtListTouchesUnsupportedEffectSurfaceWithEvents spec.events fn.body = false

structure InternalHelperSummaryContract where
  post : Nat → Nat → Verity.ContractState → List Nat → Bool → Option Nat → Verity.ContractState → Prop

def InternalHelperSummaryPreservesWorldOnSuccess
    (summary : InternalHelperSummaryContract) : Prop :=
  ∀ fuel selector initialWorld args success returnValue finalWorld,
    summary.post fuel selector initialWorld args success returnValue finalWorld →
      success = true →
      finalWorld = initialWorld

structure SupportedInternalHelperSummary (spec : CompilationModel) (callee : FunctionSpec) where
  present : callee ∈ spec.functions
  internal : callee.isInternal = true
  nonSpecialEntrypoint : isInteropEntrypointName callee.name = false
  helperRank : Nat
  params : SupportedParamProfile callee.params
  returns : SupportedReturnProfile callee
  core : SupportedBodyCoreInterface callee
  state : SupportedBodyStateInterface callee
  foreign : stmtListTouchesUnsupportedForeignSurface callee.body = false
  lowLevel : stmtListTouchesUnsupportedLowLevelSurface callee.body = false
  effects : SupportedBodyEffectInterface callee
  constructorRawCalldataSurfaceClosed :
    stmtListTouchesUnsupportedConstructorRawCalldataSurface callee.body = false
  contract : InternalHelperSummaryContract
  noLocalObligations : callee.localObligations = []

structure SupportedInternalHelperWitness
    (spec : CompilationModel) (calleeName : String) where
  callee : FunctionSpec
  summary : SupportedInternalHelperSummary spec callee
  nameEq : callee.name = calleeName

/-- Compiled-side witness for a source-defined internal helper inside a runtime
contract's helper table. This is the compositional bridge between the
source-side helper summary inventory and the helper-aware IR interpreter target:
it records exactly which internal-function definition in `runtimeContract`
came from compiling a supported source helper. -/
structure SupportedCompiledInternalHelperWitness
    (spec : CompilationModel)
    (runtimeContract : IRContract)
    (calleeName : String) where
  sourceWitness : SupportedInternalHelperWitness spec calleeName
  compiledStmt : YulStmt
  compileOk :
    compileInternalFunction
        (applySlotAliasRanges spec.fields spec.slotAliasRanges)
        spec.events
        spec.errors
        spec.adtTypes
        sourceWitness.callee =
      Except.ok compiledStmt
  presentInRuntime :
    compiledStmt ∈ runtimeContract.internalFunctions
  uniqueInRuntime :
    ∀ stmt ∈ runtimeContract.internalFunctions,
      ∀ p r b, irInternalFunctionDefOfStmt? stmt =
        some ⟨CompilationModel.internalFunctionYulName calleeName, p, r, b⟩ →
        stmt = compiledStmt

/-- Runtime-contract inventory of source-defined internal helpers.
This keeps future exact helper-step proofs generic: they can require a
compositional mapping from source helper witnesses to compiled helper bodies,
instead of baking ad hoc assumptions about a particular runtime contract's
internal helper table into each theorem. -/
structure SupportedRuntimeHelperTableInterface
    (spec : CompilationModel)
    (runtimeContract : IRContract) where
  compiledOfWitness :
    ∀ calleeName (witness : SupportedInternalHelperWitness spec calleeName),
      SupportedCompiledInternalHelperWitness spec runtimeContract calleeName
  /-- The compiled witness returned for a source witness is compiled from that
  same source witness. Without this law `compiledOfWitness` could return a
  witness carrying an unrelated `sourceWitness`, letting a source summary proof
  be paired with a compiled helper it does not describe. -/
  compiledOfWitness_sourceWitness :
    ∀ calleeName (witness : SupportedInternalHelperWitness spec calleeName),
      (compiledOfWitness calleeName witness).sourceWitness = witness

/-- Positive helper-summary boundary used by both helper-free and helper-rich
bodies. Every syntactically mentioned callee must resolve to a supported
internal function with a decreasing rank, and expression-position helpers must
preserve the world on success. -/
structure SupportedBodyHelperInterface (spec : CompilationModel) (fn : FunctionSpec) where
  helperRank : Nat
  callNamesNodup : (helperCallNames fn).Nodup
  summaryOf :
    ∀ calleeName, calleeName ∈ helperCallNames fn →
      SupportedInternalHelperWitness spec calleeName
  calleeRanksDecrease :
    ∀ calleeName (hmem : calleeName ∈ helperCallNames fn),
      (summaryOf calleeName hmem).summary.helperRank < helperRank
  exprCallsPreserveWorld :
    ∀ calleeName (hmem : calleeName ∈ exprHelperCallNames fn),
      let hcall : calleeName ∈ helperCallNames fn :=
        exprHelperCallNames_subset_helperCallNames hmem
      InternalHelperSummaryPreservesWorldOnSuccess
        ((summaryOf calleeName hcall).summary.contract)

structure SupportedBodyCallInterface (spec : CompilationModel) (fn : FunctionSpec) where
  helpers : SupportedBodyHelperInterface spec fn
  foreign : stmtListTouchesUnsupportedForeignSurface fn.body = false
  lowLevel : stmtListTouchesUnsupportedLowLevelSurface fn.body = false

mutual
  /-- Core-safe helper-positive statement heads. Helper arguments must remain in
  the existing core expression fragment; every non-helper head still passes the
  existing fail-closed core classifier. -/
  def stmtHelperRichCoreSupported : Stmt → Bool
    | .internalCall _ args | .internalCallAssign _ _ args =>
        args.all (fun arg => !exprTouchesUnsupportedCoreSurface arg)
    | .letVar _ (.internalCall _ args) | .assignVar _ (.internalCall _ args) =>
        args.all (fun arg => !exprTouchesUnsupportedCoreSurface arg)
    | .ite cond thenBranch elseBranch =>
        !exprTouchesUnsupportedCoreSurface cond &&
          stmtListHelperRichCoreSupported thenBranch &&
          stmtListHelperRichCoreSupported elseBranch
    | stmt => !stmtTouchesUnsupportedCoreSurface stmt

def stmtListHelperRichCoreSupported : List Stmt → Bool
    | [] => true
    | stmt :: rest =>
        stmtHelperRichCoreSupported stmt && stmtListHelperRichCoreSupported rest
end

mutual
  /-- State-surface gate for helper-rich statements. Expression-position helper
  calls are transparent here: their arguments must satisfy the ordinary state
  classifier even though the helper call node itself is admitted. -/
  def stmtHelperRichStateSupported : Stmt → Bool
    | .letVar _ (.internalCall _ args) | .assignVar _ (.internalCall _ args) =>
        args.all (fun arg => !exprTouchesUnsupportedStateSurface arg)
    | .ite cond thenBranch elseBranch =>
        !exprTouchesUnsupportedStateSurface cond &&
          stmtListHelperRichStateSupported thenBranch &&
          stmtListHelperRichStateSupported elseBranch
    | stmt => !stmtTouchesUnsupportedStateSurface stmt

  def stmtListHelperRichStateSupported : List Stmt → Bool
    | [] => true
    | stmt :: rest =>
        stmtHelperRichStateSupported stmt && stmtListHelperRichStateSupported rest
end

mutual
  /-- Every expression evaluated by an admitted helper-rich statement must use
  only names already in scope. `directMetadata.subexpressions` is the common
  inventory for all statement heads, including ordinary expressions and helper
  arguments; admitted `ite` children are checked recursively. -/
  def stmtHelperRichExprsInScope (scope : List String) (stmt : Stmt) : Prop :=
    (∀ expr ∈ stmt.directMetadata.subexpressions,
      FunctionBody.exprBoundNamesInScope expr scope) ∧
    match stmt with
    | .ite _ thenBranch elseBranch =>
        stmtListHelperRichExprsInScope scope thenBranch ∧
          stmtListHelperRichExprsInScope scope elseBranch
    | _ => True

  def stmtListHelperRichExprsInScope : List String → List Stmt → Prop
    | _, [] => True
    | scope, stmt :: rest =>
        stmtHelperRichExprsInScope scope stmt ∧
          stmtListHelperRichExprsInScope (stmtHelperRichNextScope scope stmt) rest
end

mutual
  /-- Direct assigning helper calls are supported only when the source helper
  has exactly one resolved return and the call binds exactly one target.  This
  matches the successful arm of `execStmtWithHelpers`; in particular, an empty
  or multi-target `letMany` can no longer expose names to a continuation that
  source execution would never reach. -/
  def stmtHelperRichAssignTargetsSupported
      (spec : CompilationModel) : Stmt → Prop
    | .internalCallAssign names calleeName _ =>
        (∃ name, names = [name]) ∧
          ∃ callee ∈ spec.functions, callee.name = calleeName ∧
            ∃ returnTy, functionReturns callee = Except.ok [returnTy]
    | .ite _ thenBranch elseBranch =>
        stmtListHelperRichAssignTargetsSupported spec thenBranch ∧
          stmtListHelperRichAssignTargetsSupported spec elseBranch
    | _ => True

  def stmtListHelperRichAssignTargetsSupported
      (spec : CompilationModel) : List Stmt → Prop
    | [] => True
    | stmt :: rest =>
        stmtHelperRichAssignTargetsSupported spec stmt ∧
          stmtListHelperRichAssignTargetsSupported spec rest
end

/-- Regression: helper arguments nested below a branch remain subject to the
core-expression gate. -/
example :
    stmtListHelperRichCoreSupported
      [.ite (.literal 1) [.internalCall "helper" [.internalCall "nested" []]] []] = false := by
  rfl

/-- Regression: branch-local helper calls cannot consume an unbound name. -/
example :
    ¬ stmtListHelperRichExprsInScope []
      [.ite (.literal 1) [.internalCall "helper" [.param "missing"]] []] := by
  simp [stmtListHelperRichExprsInScope, stmtHelperRichExprsInScope,
    Stmt.directMetadata, FunctionBody.exprBoundNamesInScope,
    FunctionBody.exprBoundNames]

/-- Regression: a valid helper call elsewhere in the body does not allow an
ordinary expression to read an unbound local. -/
example :
    ¬ stmtListHelperRichExprsInScope []
      [.letVar "x" (.localVar "missing"), .internalCall "helper" []] := by
  simp [stmtListHelperRichExprsInScope, stmtHelperRichExprsInScope,
    Stmt.directMetadata, FunctionBody.exprBoundNamesInScope,
    FunctionBody.exprBoundNames, stmtNextScope, collectStmtBindNames]

/-- Regression: a binding introduced inside either `ite` branch is not visible
to the statement following the conditional. -/
example :
    ¬ stmtListHelperRichExprsInScope []
      [.ite (.literal 1) [.letVar "x" (.literal 1)] [],
        .letVar "y" (.localVar "x")] := by
  simp [stmtListHelperRichExprsInScope, stmtHelperRichExprsInScope,
    stmtHelperRichNextScope, Stmt.directMetadata,
    FunctionBody.exprBoundNamesInScope, FunctionBody.exprBoundNames]

/-- Regression: direct helper assignment cannot advertise no targets (and the
same singleton requirement excludes multiple targets). -/
example (spec : CompilationModel) :
    ¬ stmtListHelperRichAssignTargetsSupported spec
      [.internalCallAssign [] "helper" []] := by
  simp [stmtListHelperRichAssignTargetsSupported,
    stmtHelperRichAssignTargetsSupported]

/-- Regression: admitting an expression-position helper call does not hide a
stateful argument from the helper-rich state boundary. -/
example :
    stmtListHelperRichStateSupported
      [.letVar "x" (.internalCall "helper" [.storage "slot"])] = false := by
  rfl

/-- Positive supported fragment for a helper-rich function body. Unlike the
initial `SupportedBodyInterface`, this interface does not pass through
`SupportedStmtList` (whose current constructors imply helper-surface closure).
Instead it explicitly requires a genuine internal-helper call while retaining
the independent syntactic gates and the semantic helper-summary obligations.

This is only a supported-fragment definition; it does not claim the final
whole-contract correctness theorem for helper-rich bodies. -/
structure SupportedHelperRichBodyFragment
    (spec : CompilationModel) (fn : FunctionSpec) where
  hasInternalHelperCall : ∃ calleeName, calleeName ∈ helperCallNames fn
  coreSupported : stmtListHelperRichCoreSupported fn.body = true
  expressionsInScope :
    stmtListHelperRichExprsInScope (fn.params.map (·.name)) fn.body
  assignTargetsSupported :
    stmtListHelperRichAssignTargetsSupported spec fn.body
  stateSupported : stmtListHelperRichStateSupported fn.body = true
  calls : SupportedBodyCallInterface spec fn
  effects : SupportedBodyEffectInterface fn
  constructorRawCalldataSurfaceClosed :
    stmtListTouchesUnsupportedConstructorRawCalldataSurface fn.body = false
  noLocalObligations : fn.localObligations = []

/-- Body-level interface for the initial theorem boundary. This keeps the current
syntactic support inventory local to the body witness instead of baking it
directly into the top-level `SupportedSpec` inventory. Each sub-interface is a
feature-local place to hang future widening work. -/
structure SupportedBodyInterface (spec : CompilationModel) (fn : FunctionSpec) where
  stmtList : SupportedStmtList spec.fields (fn.params.map (·.name)) fn.body
  core : SupportedBodyCoreInterface fn
  state : SupportedBodyStateInterface fn
  calls : SupportedBodyCallInterface spec fn
  effects : SupportedBodyEffectInterface fn
  noLocalObligations : fn.localObligations = []

/-- Body-level support for the scalar-event slice. Event emissions are admitted
only as top-level statement heads; structural statements such as `ite` and
`forEach` must remain fully plain contract-surface closed. -/
structure SupportedBodyInterfaceWithScalarEvents
    (spec : CompilationModel) (fn : FunctionSpec) where
  stmtList : SupportedStmtList spec.fields (fn.params.map (·.name)) fn.body
  core : SupportedBodyCoreInterface fn
  state : SupportedBodyStateInterface fn
  calls : SupportedBodyCallInterface spec fn
  contractSurfaceWithEvents :
    stmtListTouchesUnsupportedContractSurfaceWithEvents spec.events fn.body = false
  topLevelEventHeads :
    ∀ s ∈ fn.body,
      stmtTouchesEventSurface s = true ∨
        stmtTouchesUnsupportedContractSurface s = false
  eventScratchFreshInitial :
    "__evt_ptr" ∉ fn.params.map (·.name) ∧
      "__evt_topic0" ∉ fn.params.map (·.name)
  eventScratchFreshStmts :
    ∀ s ∈ fn.body,
      "__evt_ptr" ∉ collectStmtBindNames s ∧ "__evt_topic0" ∉ collectStmtBindNames s
  emitArgsInScope :
    ∀ s ∈ fn.body, ∀ (eventName : String) (args : List Expr),
      s = Stmt.emit eventName args →
      ∀ arg ∈ args,
        FunctionBody.exprBoundNamesInScope arg (fn.params.map (·.name))
  noLocalObligations : fn.localObligations = []

/-- Tier 2 body-level interface that weakens only the state-surface closure to
admit the currently proved singleton storage-write shapes; all other fail-closed
boundaries remain unchanged. -/
structure SupportedBodyInterfaceExceptMappingWrites
    (spec : CompilationModel) (fn : FunctionSpec) where
  stmtList : SupportedStmtList spec.fields (fn.params.map (·.name)) fn.body
  core : SupportedBodyCoreInterface fn
  state : SupportedBodyStateInterfaceExceptMappingWrites fn
  calls : SupportedBodyCallInterface spec fn
  effects : SupportedBodyEffectInterface fn
  noLocalObligations : fn.localObligations = []

/-- Supported external function for the first whole-contract Layer 2 theorem.
This lifts the raw `SupportedStmtList` witness to the function boundary and
makes the whole-contract scope auditable without proof-internal inspection. -/
structure SupportedFunction (spec : CompilationModel) (fn : FunctionSpec) where
  nonInternal : fn.isInternal = false
  nonSpecialEntrypoint : isInteropEntrypointName fn.name = false
  /-- `nonreentrant(lockField)` guards sit outside the proven fragment: the
      TLOAD/TSTORE prologue injected by `attachNonReentrantGuard` is not yet
      modelled by the source semantics. This makes the documented boundary
      (docs/TRUST_ASSUMPTIONS.md) machine-checked instead of prose-only. -/
  noNonReentrant : fn.nonReentrantLock = none
  /-- Explicit source ABI preludes need their own decoder equivalence proof. -/
  standardAbi : fn.abiDecoding = .standard
  params : SupportedParamProfile fn.params
  returns : SupportedReturnProfile fn
  body : SupportedBodyInterface spec fn

/-- Body support at the helper-aware function boundary.  The legacy arm keeps
all existing helper-free consumers available, while the helper-rich arm admits
the positive fragment directly without manufacturing a `SupportedStmtList`
witness (which would imply that the helper-call inventory is empty). -/
inductive SupportedFunctionBodyWithHelpers
    (spec : CompilationModel) (fn : FunctionSpec) : Type where
  | legacy (body : SupportedBodyInterface spec fn)
  | helperRich (body : SupportedHelperRichBodyFragment spec fn)
  | internalHelper (summary : SupportedInternalHelperSummary spec fn)

/-- Function support interface for helper-aware consumers.  Internal helpers
and selector-dispatched callers share this interface; whether a function is an
external dispatch target remains a property of `selectorDispatchedFunctions`,
not a body-fragment restriction. -/
structure SupportedFunctionWithHelpers
    (spec : CompilationModel) (fn : FunctionSpec) where
  nonSpecialEntrypoint : isInteropEntrypointName fn.name = false
  noNonReentrant : fn.nonReentrantLock = none
  /-- Explicit source ABI preludes need their own decoder equivalence proof. -/
  standardAbi : fn.abiDecoding = .standard
  params : SupportedParamProfile fn.params
  returns : SupportedReturnProfile fn
  body : SupportedFunctionBodyWithHelpers spec fn

/-- Supported external function for the scalar-event Layer 2 slice. -/
structure SupportedFunctionWithScalarEvents
    (spec : CompilationModel) (fn : FunctionSpec) where
  nonInternal : fn.isInternal = false
  nonSpecialEntrypoint : isInteropEntrypointName fn.name = false
  noNonReentrant : fn.nonReentrantLock = none
  /-- Explicit source ABI preludes need their own decoder equivalence proof. -/
  standardAbi : fn.abiDecoding = .standard
  params : SupportedParamProfile fn.params
  returns : SupportedReturnProfile fn
  body : SupportedBodyInterfaceWithScalarEvents spec fn

/-- Tier 2 function-level support witness that weakens only the body state
surface closure to admit the currently proved singleton storage-write shapes. -/
structure SupportedFunctionExceptMappingWrites
    (spec : CompilationModel) (fn : FunctionSpec) where
  nonInternal : fn.isInternal = false
  nonSpecialEntrypoint : isInteropEntrypointName fn.name = false
  noNonReentrant : fn.nonReentrantLock = none
  /-- Explicit source ABI preludes need their own decoder equivalence proof. -/
  standardAbi : fn.abiDecoding = .standard
  params : SupportedParamProfile fn.params
  returns : SupportedReturnProfile fn
  body : SupportedBodyInterfaceExceptMappingWrites spec fn

/-- Constructor bodies reuse the same statement-fragment interface as ordinary
functions once deploy-time arguments have been decoded into local bindings. -/
def constructorAsFunctionSpec (ctor : ConstructorSpec) : FunctionSpec :=
  { name := "__constructor__"
    params := (constructorArgAliasNames ctor.params).map (fun name => { name := name, ty := .uint256 }) ++
      ctor.params
    returnType := none
    returns := []
    isPayable := ctor.isPayable
    isView := false
    isPure := false
    body := ctor.body
    isInternal := false
    localObligations := ctor.localObligations }

/-- Body-level support witness for constructors. This is intentionally local:
it covers the user-written constructor body after argument decoding, not the
initcode wrapper that materializes those locals. -/
structure SupportedConstructor (spec : CompilationModel) (ctor : ConstructorSpec) where
  params : SupportedParamProfile ctor.params
  body : SupportedBodyInterfaceExceptMappingWrites spec (constructorAsFunctionSpec ctor)
  rawCalldataSurfaceClosed :
    stmtListTouchesUnsupportedConstructorRawCalldataSurface ctor.body = false

theorem SupportedConstructor.paramNamesNodup
    {spec : CompilationModel} {ctor : ConstructorSpec}
    (hSupported : SupportedConstructor spec ctor) :
    (ctor.params.map (·.name)).Nodup :=
  hSupported.params.namesNodup

theorem SupportedConstructor.paramsSupported
    {spec : CompilationModel} {ctor : ConstructorSpec}
    (hSupported : SupportedConstructor spec ctor) :
    ∀ param ∈ ctor.params, SupportedExternalScalarParamType param.ty :=
  hSupported.params.supported

theorem SupportedConstructor.stmtList_ctorBody
    {spec : CompilationModel} {ctor : ConstructorSpec}
    (hSupported : SupportedConstructor spec ctor) :
    SupportedStmtList spec.fields (constructorBodyScope ctor.params) ctor.body := by
  change SupportedStmtList spec.fields
    (constructorArgAliasNames ctor.params ++ ctor.params.map (·.name)) ctor.body
  simpa [constructorAsFunctionSpec, constructorArgAliasNames, Function.comp_def] using
    hSupported.body.stmtList

/-- Whole-contract invariants that should remain global preconditions for the
current generic theorem, independent of feature-local proof interfaces. -/
structure SupportedSpecInvariants (spec : CompilationModel) (selectors : List Nat) : Prop where
  normalizedFields :
    applySlotAliasRanges spec.fields spec.slotAliasRanges = spec.fields
  noPackedFields :
    ∀ field ∈ spec.fields, field.packedBits = none
  selectorCount : selectors.length = (selectorDispatchedFunctions spec).length
  selectorsDistinct : firstDuplicateSelector selectors = none
  functionNamesNodup : (spec.functions.map (·.name)).Nodup

/-- Whole-contract surfaces intentionally still outside the initial theorem,
kept separate from global normalization/dispatch invariants so future widening
can replace these by dedicated proof interfaces feature-by-feature. -/
structure SupportedSpecSurface (spec : CompilationModel) : Prop where
  noEvents : spec.events = []
  noErrors : spec.errors = []
  noExternals : spec.externals = []
  noAdtTypes : spec.adtTypes = []
  noCheckedArithmetic : contractUsesCheckedArithmetic spec = false
  noTemplateIntrinsics : templateIntrinsicItems spec = []
  noFallback :
    ∀ fn ∈ spec.functions, fn.name != "fallback"
  noReceive :
    ∀ fn ∈ spec.functions, fn.name != "receive"

/-- Whole-contract scalar-event surface. Events may be declared, but every
declared event must live in the scalar proof-supported fragment: scalar params
and at most three indexed parameters. -/
structure SupportedSpecSurfaceWithScalarEvents (spec : CompilationModel) : Prop where
  eventsSupported :
    ∀ eventDef ∈ spec.events, eventDefScalarProofSupported eventDef = true
  noErrors : spec.errors = []
  noExternals : spec.externals = []
  noAdtTypes : spec.adtTypes = []
  noCheckedArithmetic : contractUsesCheckedArithmetic spec = false
  noTemplateIntrinsics : templateIntrinsicItems spec = []
  noFallback :
    ∀ fn ∈ spec.functions, fn.name != "fallback"
  noReceive :
    ∀ fn ∈ spec.functions, fn.name != "receive"

/-- Whole-contract support witness for the first generic Layer 2 theorem.
The initial scope is deliberately narrow: selector-dispatched external entrypoints only,
no constructor, no fallback/receive, no foreign/linking surface, and every function body
must already live inside the explicit supported statement fragment. -/
structure SupportedSpec (spec : CompilationModel) (selectors : List Nat) where
  invariants : SupportedSpecInvariants spec selectors
  surface : SupportedSpecSurface spec
  constructor :
    ∀ ctor, spec.constructor = some ctor → SupportedConstructor spec ctor
  functions :
    ∀ fn, fn ∈ spec.functions → SupportedFunction spec fn

/-- Whole-contract support inventory for the helper-aware Function/Contract/
Dispatch chain.  It shares the established global invariants and surface gates,
but its function inventory accepts `SupportedHelperRichBodyFragment` through
`SupportedFunctionWithHelpers`. -/
structure SupportedSpecWithHelpers
    (spec : CompilationModel) (selectors : List Nat) where
  invariants : SupportedSpecInvariants spec selectors
  surface : SupportedSpecSurface spec
  constructor :
    ∀ ctor, spec.constructor = some ctor → SupportedConstructor spec ctor
  functions :
    ∀ fn, fn ∈ spec.functions → SupportedFunctionWithHelpers spec fn

/-- Whole-contract support witness for the top-level scalar-event theorem. -/
structure SupportedSpecWithScalarEvents
    (spec : CompilationModel) (selectors : List Nat) where
  invariants : SupportedSpecInvariants spec selectors
  surface : SupportedSpecSurfaceWithScalarEvents spec
  constructor :
    ∀ ctor, spec.constructor = some ctor → SupportedConstructor spec ctor
  functions :
    ∀ fn, fn ∈ spec.functions → SupportedFunctionWithScalarEvents spec fn

/-- Tier 2 whole-contract support witness that weakens only the function-body
state closure to admit the currently proved singleton storage-write shapes. -/
structure SupportedSpecExceptMappingWrites
    (spec : CompilationModel) (selectors : List Nat) where
  invariants : SupportedSpecInvariants spec selectors
  surface : SupportedSpecSurface spec
  constructor :
    ∀ ctor, spec.constructor = some ctor → SupportedConstructor spec ctor
  functions :
    ∀ fn, fn ∈ spec.functions → SupportedFunctionExceptMappingWrites spec fn

private theorem stmtTouchesUnsupportedStateSurfaceExceptMappingWrites_eq_false_of_stateSurface
    {stmt : Stmt}
    (hstate : stmtTouchesUnsupportedStateSurface stmt = false) :
    stmtTouchesUnsupportedStateSurfaceExceptMappingWrites stmt = false := by
  cases stmt <;>
    simp [stmtTouchesUnsupportedStateSurfaceExceptMappingWrites,
      stmtTouchesUnsupportedStateSurface] at hstate ⊢ <;>
    try exact hstate

theorem stmtListTouchesUnsupportedStateSurfaceExceptMappingWrites_eq_false_of_stateSurface
    {stmts : List Stmt}
    (hstate : stmtListTouchesUnsupportedStateSurface stmts = false) :
    stmtListTouchesUnsupportedStateSurfaceExceptMappingWrites stmts = false := by
  induction stmts with
  | nil =>
      simp [stmtListTouchesUnsupportedStateSurfaceExceptMappingWrites]
  | cons stmt rest ih =>
      have hsplit := Bool.or_eq_false_iff.mp hstate
      simp [stmtListTouchesUnsupportedStateSurfaceExceptMappingWrites,
        stmtTouchesUnsupportedStateSurfaceExceptMappingWrites_eq_false_of_stateSurface hsplit.1,
        ih hsplit.2]

def SupportedBodyStateInterface.exceptMappingWrites
    {fn : FunctionSpec}
    (hState : SupportedBodyStateInterface fn) :
    SupportedBodyStateInterfaceExceptMappingWrites fn :=
  { surfaceClosed :=
      stmtListTouchesUnsupportedStateSurfaceExceptMappingWrites_eq_false_of_stateSurface
        hState.surfaceClosed }

def SupportedBodyInterface.exceptMappingWrites
    {spec : CompilationModel} {fn : FunctionSpec}
    (hBody : SupportedBodyInterface spec fn) :
    SupportedBodyInterfaceExceptMappingWrites spec fn :=
  { stmtList := hBody.stmtList
    core := hBody.core
    state := hBody.state.exceptMappingWrites
    calls := hBody.calls
    effects := hBody.effects
    noLocalObligations := hBody.noLocalObligations }

def SupportedFunction.exceptMappingWrites
    {spec : CompilationModel} {fn : FunctionSpec}
    (hSupported : SupportedFunction spec fn) :
    SupportedFunctionExceptMappingWrites spec fn :=
  { nonInternal := hSupported.nonInternal
    nonSpecialEntrypoint := hSupported.nonSpecialEntrypoint
    standardAbi := hSupported.standardAbi
    noNonReentrant := hSupported.noNonReentrant
    params := hSupported.params
    returns := hSupported.returns
    body := hSupported.body.exceptMappingWrites }

def SupportedSpec.exceptMappingWrites
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors) :
    SupportedSpecExceptMappingWrites spec selectors :=
  { invariants := hSupported.invariants
    surface := hSupported.surface
    constructor := hSupported.constructor
    functions := fun fn hmem =>
      (hSupported.functions fn hmem).exceptMappingWrites }

theorem SupportedFunction.paramNamesNodup
    {spec : CompilationModel} {fn : FunctionSpec}
    (hSupported : SupportedFunction spec fn) :
    (fn.params.map (·.name)).Nodup :=
  hSupported.params.namesNodup

theorem SupportedFunction.paramsSupported
    {spec : CompilationModel} {fn : FunctionSpec}
    (hSupported : SupportedFunction spec fn) :
    ∀ param ∈ fn.params, SupportedExternalScalarParamType param.ty :=
  hSupported.params.supported

theorem SupportedFunction.paramCalldataThreshold
    {spec : CompilationModel} {fn : FunctionSpec}
    (hSupported : SupportedFunction spec fn) :
    4 + fn.params.length * 32 < Compiler.Constants.evmModulus :=
  hSupported.params.calldataThreshold

theorem SupportedFunction.returnsSupported
    {spec : CompilationModel} {fn : FunctionSpec}
    (hSupported : SupportedFunction spec fn) :
    ∃ resolvedReturns,
      functionReturns fn = Except.ok resolvedReturns ∧
        SupportedExternalReturnProfile resolvedReturns :=
  hSupported.returns.resolved

theorem SupportedFunctionWithScalarEvents.paramNamesNodup
    {spec : CompilationModel} {fn : FunctionSpec}
    (hSupported : SupportedFunctionWithScalarEvents spec fn) :
    (fn.params.map (·.name)).Nodup :=
  hSupported.params.namesNodup

theorem SupportedFunctionWithScalarEvents.paramsSupported
    {spec : CompilationModel} {fn : FunctionSpec}
    (hSupported : SupportedFunctionWithScalarEvents spec fn) :
    ∀ param ∈ fn.params, SupportedExternalScalarParamType param.ty :=
  hSupported.params.supported

theorem SupportedFunctionWithScalarEvents.paramCalldataThreshold
    {spec : CompilationModel} {fn : FunctionSpec}
    (hSupported : SupportedFunctionWithScalarEvents spec fn) :
    4 + fn.params.length * 32 < Compiler.Constants.evmModulus :=
  hSupported.params.calldataThreshold

theorem SupportedFunctionWithScalarEvents.returnsSupported
    {spec : CompilationModel} {fn : FunctionSpec}
    (hSupported : SupportedFunctionWithScalarEvents spec fn) :
    ∃ resolvedReturns,
      functionReturns fn = Except.ok resolvedReturns ∧
        SupportedExternalReturnProfile resolvedReturns :=
  hSupported.returns.resolved

theorem SupportedFunctionExceptMappingWrites.paramNamesNodup
    {spec : CompilationModel} {fn : FunctionSpec}
    (hSupported : SupportedFunctionExceptMappingWrites spec fn) :
    (fn.params.map (·.name)).Nodup :=
  hSupported.params.namesNodup

theorem SupportedFunctionExceptMappingWrites.paramsSupported
    {spec : CompilationModel} {fn : FunctionSpec}
    (hSupported : SupportedFunctionExceptMappingWrites spec fn) :
    ∀ param ∈ fn.params, SupportedExternalScalarParamType param.ty :=
  hSupported.params.supported

theorem SupportedFunctionExceptMappingWrites.paramCalldataThreshold
    {spec : CompilationModel} {fn : FunctionSpec}
    (hSupported : SupportedFunctionExceptMappingWrites spec fn) :
    4 + fn.params.length * 32 < Compiler.Constants.evmModulus :=
  hSupported.params.calldataThreshold

theorem SupportedFunctionExceptMappingWrites.returnsSupported
    {spec : CompilationModel} {fn : FunctionSpec}
    (hSupported : SupportedFunctionExceptMappingWrites spec fn) :
    ∃ resolvedReturns,
      functionReturns fn = Except.ok resolvedReturns ∧
        SupportedExternalReturnProfile resolvedReturns :=
  hSupported.returns.resolved

def SupportedFunction.helperFuel
    {spec : CompilationModel} {fn : FunctionSpec}
    (hSupported : SupportedFunction spec fn) : Nat :=
  hSupported.body.calls.helpers.helperRank

def SupportedFunctionWithScalarEvents.helperFuel
    {spec : CompilationModel} {fn : FunctionSpec}
    (hSupported : SupportedFunctionWithScalarEvents spec fn) : Nat :=
  hSupported.body.calls.helpers.helperRank

def SupportedFunctionExceptMappingWrites.helperFuel
    {spec : CompilationModel} {fn : FunctionSpec}
    (hSupported : SupportedFunctionExceptMappingWrites spec fn) : Nat :=
  hSupported.body.calls.helpers.helperRank

def SupportedFunctionWithHelpers.helperFuel
    {spec : CompilationModel} {fn : FunctionSpec}
    (hSupported : SupportedFunctionWithHelpers spec fn) : Nat :=
  match hSupported.body with
  | .legacy body => body.calls.helpers.helperRank
  | .helperRich body => body.calls.helpers.helperRank
  | .internalHelper summary => summary.helperRank

def SupportedFunction.withHelpers
    {spec : CompilationModel} {fn : FunctionSpec}
    (hSupported : SupportedFunction spec fn) : SupportedFunctionWithHelpers spec fn :=
  { nonSpecialEntrypoint := hSupported.nonSpecialEntrypoint
    standardAbi := hSupported.standardAbi
    noNonReentrant := hSupported.noNonReentrant
    params := hSupported.params
    returns := hSupported.returns
    body := .legacy hSupported.body }

def SupportedSpec.withHelpers
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors) : SupportedSpecWithHelpers spec selectors :=
  { invariants := hSupported.invariants
    surface := hSupported.surface
    constructor := hSupported.constructor
    functions := fun fn hmem => (hSupported.functions fn hmem).withHelpers }

private theorem exprCompileCore_helperSurfaceClosed
    {expr : Expr}
    (hcore : FunctionBody.ExprCompileCore expr) :
    exprTouchesUnsupportedHelperSurface expr = false := by
  induction hcore with
  | literal | param | constructorArg | localVar | caller | contractAddress | txOrigin | msgValue
    | blockTimestamp | blockNumber | chainid | blobbasefee | calldatasize | returndataSize =>
      simp only [exprTouchesUnsupportedHelperSurface]
  | add _ _ ihL ihR
    | sub _ _ ihL ihR
    | mul _ _ ihL ihR
    | div _ _ ihL ihR
    | mod _ _ ihL ihR
    | eq _ _ ihL ihR
    | lt _ _ ihL ihR
    | gt _ _ ihL ihR
    | ge _ _ ihL ihR
    | le _ _ ihL ihR
    | logicalAnd _ _ ihL ihR
    | logicalOr _ _ ihL ihR
    | bitAnd _ _ ihL ihR
    | bitOr _ _ ihL ihR
    | bitXor _ _ ihL ihR
    | shl _ _ ihL ihR
    | shr _ _ ihL ihR
    | min _ _ ihL ihR
    | max _ _ ihL ihR
    | ceilDiv _ _ ihL ihR | wMulDown _ _ ihL ihR | wDivUp _ _ ihL ihR
    | slt _ _ ihL ihR | sgt _ _ ihL ihR | sdiv _ _ ihL ihR
    | smod _ _ ihL ihR | sar _ _ ihL ihR | byte _ _ ihL ihR | signextend _ _ ihL ihR
    | keccak256 _ _ ihL ihR =>
      simp only [exprTouchesUnsupportedHelperSurface, ihL, ihR, Bool.or_false, Bool.false_or]
  | logicalNot _ ih | bitNot _ ih | tload _ ih | calldataload _ ih | mload _ ih | extcodesize _ ih
  | returndataOptionalBoolAt _ ih =>
      simp only [exprTouchesUnsupportedHelperSurface, ih]
  | ite _ _ _ ihC ihT ihE =>
      simp only [exprTouchesUnsupportedHelperSurface, ihC, ihT, ihE,
        Bool.or_false, Bool.false_or]
  | mulDivDown _ _ _ ihA ihB ihC | mulDivUp _ _ _ ihA ihB ihC =>
      simp only [exprTouchesUnsupportedHelperSurface, ihA, ihB, ihC,
        Bool.or_false, Bool.false_or]
  | builtinExp _ _ ihB ihE =>
      simp only [exprTouchesUnsupportedHelperSurface, beq_self_eq_true, if_true, ihB, ihE,
        Bool.or_false, Bool.false_or]

private theorem exprCompileCore_internalHelperCallNames_nil
    {expr : Expr}
    (hcore : FunctionBody.ExprCompileCore expr) :
    exprInternalHelperCallNames expr = [] := by
  induction hcore with
  | literal | param | constructorArg | localVar | caller | contractAddress | txOrigin | msgValue
    | blockTimestamp | blockNumber | chainid | blobbasefee | calldatasize | returndataSize =>
      simp only [exprInternalHelperCallNames]
  | add _ _ ihL ihR
    | sub _ _ ihL ihR
    | mul _ _ ihL ihR
    | div _ _ ihL ihR
    | mod _ _ ihL ihR
    | eq _ _ ihL ihR
    | lt _ _ ihL ihR
    | gt _ _ ihL ihR
    | ge _ _ ihL ihR
    | le _ _ ihL ihR
    | logicalAnd _ _ ihL ihR
    | logicalOr _ _ ihL ihR
    | bitAnd _ _ ihL ihR
    | bitOr _ _ ihL ihR
    | bitXor _ _ ihL ihR
    | shl _ _ ihL ihR
    | shr _ _ ihL ihR
    | min _ _ ihL ihR
    | max _ _ ihL ihR
    | ceilDiv _ _ ihL ihR | wMulDown _ _ ihL ihR | wDivUp _ _ ihL ihR
    | slt _ _ ihL ihR | sgt _ _ ihL ihR | sdiv _ _ ihL ihR
    | smod _ _ ihL ihR | sar _ _ ihL ihR | byte _ _ ihL ihR | signextend _ _ ihL ihR
    | keccak256 _ _ ihL ihR =>
      simp only [exprInternalHelperCallNames, ihL, ihR, List.nil_append]
  | logicalNot _ ih | bitNot _ ih | tload _ ih | calldataload _ ih | mload _ ih | extcodesize _ ih
  | returndataOptionalBoolAt _ ih =>
      simp only [exprInternalHelperCallNames, ih]
  | ite _ _ _ ihC ihT ihE =>
      simp only [exprInternalHelperCallNames, ihC, ihT, ihE, List.nil_append]
  | mulDivDown _ _ _ ihA ihB ihC | mulDivUp _ _ _ ihA ihB ihC =>
      simp only [exprInternalHelperCallNames, ihA, ihB, ihC, List.nil_append]
  | builtinExp _ _ ihB ihE =>
      simp only [exprInternalHelperCallNames, exprListInternalHelperCallNames, ihB, ihE,
        List.nil_append, List.append_nil]

private theorem exprListCompileCore_helperSurfaceClosed
    {exprs : List Expr}
    (hcore : ∀ expr ∈ exprs, FunctionBody.ExprCompileCore expr) :
    exprListTouchesUnsupportedHelperSurface exprs = false := by
  induction exprs with
  | nil =>
      simp only [exprListTouchesUnsupportedHelperSurface,
        Bool.or_false, Bool.false_or]
  | cons expr rest ih =>
      have hhead : FunctionBody.ExprCompileCore expr := hcore expr (by simp)
      have htail : ∀ e ∈ rest, FunctionBody.ExprCompileCore e := by
        intro e he
        exact hcore e (by simp [he])
      simp only [exprListTouchesUnsupportedHelperSurface,
        exprCompileCore_helperSurfaceClosed hhead,
        ih htail,
        Bool.or_false, Bool.false_or]

private theorem exprListCompileCore_internalHelperCallNames_nil
    {exprs : List Expr}
    (hcore : ∀ expr ∈ exprs, FunctionBody.ExprCompileCore expr) :
    exprListInternalHelperCallNames exprs = [] := by
  induction exprs with
  | nil =>
      simp only [exprListInternalHelperCallNames]
  | cons expr rest ih =>
      have hhead : FunctionBody.ExprCompileCore expr := hcore expr (by simp)
      have htail : ∀ e ∈ rest, FunctionBody.ExprCompileCore e := by
        intro e he
        exact hcore e (by simp [he])
      simp only [exprListInternalHelperCallNames,
        exprCompileCore_internalHelperCallNames_nil hhead,
        ih htail, List.nil_append]

private theorem stmtListCompileCore_helperSurfaceClosed
    {scope : List String}
    {stmts : List Stmt}
    (hcore : FunctionBody.StmtListCompileCore scope stmts) :
    stmtListTouchesUnsupportedHelperSurface stmts = false := by
  induction hcore with
  | nil =>
      simp only [stmtListTouchesUnsupportedHelperSurface,
        Bool.or_false, Bool.false_or]
  | letVar hvalue _ _ ih
    | assignVar hvalue _ _ ih
    | return_ hvalue _ _ ih =>
      simp only [stmtListTouchesUnsupportedHelperSurface,
        stmtTouchesUnsupportedHelperSurface,
        exprCompileCore_helperSurfaceClosed hvalue,
        ih,
        Bool.or_false, Bool.false_or]
  | require_ hcond _ _ ih =>
      simp only [stmtListTouchesUnsupportedHelperSurface,
        stmtTouchesUnsupportedHelperSurface,
        exprCompileCore_helperSurfaceClosed hcond,
        ih,
        Bool.or_false, Bool.false_or]
  | stop _ ih =>
      simp only [stmtListTouchesUnsupportedHelperSurface,
        stmtTouchesUnsupportedHelperSurface,
        ih,
        Bool.or_false, Bool.false_or]
  | mstore hoffset _ hvalue _ _ ih =>
      simp only [stmtListTouchesUnsupportedHelperSurface,
        stmtTouchesUnsupportedHelperSurface,
        exprCompileCore_helperSurfaceClosed hoffset,
        exprCompileCore_helperSurfaceClosed hvalue,
        ih,
        Bool.or_false, Bool.false_or]
  | tstore hoffset _ hvalue _ _ ih =>
      simp only [stmtListTouchesUnsupportedHelperSurface,
        stmtTouchesUnsupportedHelperSurface,
        exprCompileCore_helperSurfaceClosed hoffset,
        exprCompileCore_helperSurfaceClosed hvalue,
        ih,
        Bool.or_false, Bool.false_or]

private theorem stmtListCompileCore_internalHelperCallNames_nil
    {scope : List String}
    {stmts : List Stmt}
    (hcore : FunctionBody.StmtListCompileCore scope stmts) :
    stmtListInternalHelperCallNames stmts = [] := by
  induction hcore with
  | nil =>
      simp only [stmtListInternalHelperCallNames]
  | letVar hvalue _ _ ih
    | assignVar hvalue _ _ ih
    | return_ hvalue _ _ ih =>
      simp only [stmtListInternalHelperCallNames,
        stmtInternalHelperCallNames,
        exprCompileCore_internalHelperCallNames_nil hvalue,
        ih, List.nil_append, List.append_nil]
  | require_ hcond _ _ ih =>
      simp only [stmtListInternalHelperCallNames,
        stmtInternalHelperCallNames,
        exprCompileCore_internalHelperCallNames_nil hcond,
        ih, List.nil_append, List.append_nil]
  | stop _ ih =>
      simp only [stmtListInternalHelperCallNames,
        stmtInternalHelperCallNames,
        ih, List.nil_append, List.append_nil]
  | mstore hoffset _ hvalue _ _ ih =>
      simp only [stmtListInternalHelperCallNames,
        stmtInternalHelperCallNames,
        exprCompileCore_internalHelperCallNames_nil hoffset,
        exprCompileCore_internalHelperCallNames_nil hvalue,
        ih, List.nil_append, List.append_nil]
  | tstore hoffset _ hvalue _ _ ih =>
      simp only [stmtListInternalHelperCallNames,
        stmtInternalHelperCallNames,
        exprCompileCore_internalHelperCallNames_nil hoffset,
        exprCompileCore_internalHelperCallNames_nil hvalue,
        ih, List.nil_append, List.append_nil]


private theorem stmtListTerminalCore_internalHelperCallNames_nil
    {scope : List String}
    {stmts : List Stmt}
    (hterminal : FunctionBody.StmtListTerminalCore scope stmts) :
    stmtListInternalHelperCallNames stmts = [] := by
  induction hterminal with
  | letVar hvalue _ _ ih
    | assignVar hvalue _ _ ih =>
      simp only [stmtListInternalHelperCallNames,
        stmtInternalHelperCallNames,
        exprCompileCore_internalHelperCallNames_nil hvalue,
        ih, List.nil_append, List.append_nil]
  | require_ hcond _ _ ih =>
      simp only [stmtListInternalHelperCallNames,
        stmtInternalHelperCallNames,
        exprCompileCore_internalHelperCallNames_nil hcond,
        ih, List.nil_append, List.append_nil]
  | return_ hvalue _ hrest =>
      simp only [stmtListInternalHelperCallNames,
        stmtInternalHelperCallNames,
        exprCompileCore_internalHelperCallNames_nil hvalue,
        stmtListCompileCore_internalHelperCallNames_nil hrest,
        List.nil_append, List.append_nil]
  | stop hrest =>
      simp only [stmtListInternalHelperCallNames,
        stmtInternalHelperCallNames,
        stmtListCompileCore_internalHelperCallNames_nil hrest,
        List.nil_append, List.append_nil]
  | ite hcond _ hthen helse hrest ihThen ihElse =>
      simp only [stmtListInternalHelperCallNames,
        stmtInternalHelperCallNames,
        exprCompileCore_internalHelperCallNames_nil hcond,
        ihThen, ihElse,
        stmtListCompileCore_internalHelperCallNames_nil hrest,
        List.nil_append, List.append_nil]
  | mstore hoffset _ hvalue _ _ ih =>
      simp only [stmtListInternalHelperCallNames,
        stmtInternalHelperCallNames,
        exprCompileCore_internalHelperCallNames_nil hoffset,
        exprCompileCore_internalHelperCallNames_nil hvalue,
        ih, List.nil_append, List.append_nil]
  | tstore hoffset _ hvalue _ _ ih =>
      simp only [stmtListInternalHelperCallNames,
        stmtInternalHelperCallNames,
        exprCompileCore_internalHelperCallNames_nil hoffset,
        exprCompileCore_internalHelperCallNames_nil hvalue,
        ih, List.nil_append, List.append_nil]


private theorem stmtListTerminalCore_helperSurfaceClosed
    {scope : List String}
    {stmts : List Stmt}
    (hterminal : FunctionBody.StmtListTerminalCore scope stmts) :
    stmtListTouchesUnsupportedHelperSurface stmts = false := by
  induction hterminal with
  | letVar hvalue _ _ ih | assignVar hvalue _ _ ih | require_ hvalue _ _ ih =>
      simp only [stmtListTouchesUnsupportedHelperSurface, stmtTouchesUnsupportedHelperSurface,
        exprCompileCore_helperSurfaceClosed hvalue, ih, Bool.or_false, Bool.false_or]
  | return_ hvalue _ hrest =>
      simp only [stmtListTouchesUnsupportedHelperSurface, stmtTouchesUnsupportedHelperSurface,
        exprCompileCore_helperSurfaceClosed hvalue,
        stmtListCompileCore_helperSurfaceClosed hrest, Bool.or_false, Bool.false_or]
  | stop hrest =>
      simp only [stmtListTouchesUnsupportedHelperSurface, stmtTouchesUnsupportedHelperSurface,
        stmtListCompileCore_helperSurfaceClosed hrest, Bool.or_false, Bool.false_or]
  | ite hcond _ hthen helse hrest ihThen ihElse =>
      simp only [stmtListTouchesUnsupportedHelperSurface, stmtTouchesUnsupportedHelperSurface,
        exprCompileCore_helperSurfaceClosed hcond, ihThen, ihElse,
        stmtListCompileCore_helperSurfaceClosed hrest, Bool.or_false, Bool.false_or]
  | mstore hoffset _ hvalue _ _ ih | tstore hoffset _ hvalue _ _ ih =>
      simp only [stmtListTouchesUnsupportedHelperSurface, stmtTouchesUnsupportedHelperSurface,
        exprCompileCore_helperSurfaceClosed hoffset,
        exprCompileCore_helperSurfaceClosed hvalue, ih, Bool.or_false, Bool.false_or]

/-- Single-statement leaves of `SupportedStmtList`: the constructors whose
conclusion is a one-statement list without a nested statement body. Only the
`ExprCompileCore` facts about the expression operands are retained, which is all
the syntactic closure properties below need. -/
private inductive SupportedLeafStmt : Stmt → Prop
  | setStorage {fieldName : String} {value : Expr} :
      FunctionBody.ExprCompileCore value → SupportedLeafStmt (.setStorage fieldName value)
  | setStorageAddr {fieldName : String} {value : Expr} :
      FunctionBody.ExprCompileCore value → SupportedLeafStmt (.setStorageAddr fieldName value)
  | setImmutable {name : String} {value : Expr} :
      FunctionBody.ExprCompileCore value → SupportedLeafStmt (.setImmutable name value)
  | calldatacopy {destOffset sourceOffset size : Expr} :
      FunctionBody.ExprCompileCore destOffset → FunctionBody.ExprCompileCore sourceOffset →
      FunctionBody.ExprCompileCore size →
      SupportedLeafStmt (.calldatacopy destOffset sourceOffset size)
  | returndataCopyEmpty {destOffset : Expr} :
      FunctionBody.ExprCompileCore destOffset →
      SupportedLeafStmt (.returndataCopy destOffset (.literal 0) (.literal 0))
  | revertEmpty : SupportedLeafStmt .revertEmpty
  | revertReturndata : SupportedLeafStmt .revertReturndata
  | letStorage {tmp fieldName : String} :
      SupportedLeafStmt (.letVar tmp (.storage fieldName))
  | letStorageAddr {tmp fieldName : String} :
      SupportedLeafStmt (.letVar tmp (.storageAddr fieldName))
  | assignStorage {name fieldName : String} :
      SupportedLeafStmt (.assignVar name (.storage fieldName))
  | assignStorageAddr {name fieldName : String} :
      SupportedLeafStmt (.assignVar name (.storageAddr fieldName))
  | emit {eventName : String} {args : List Expr} :
      (∀ arg ∈ args, FunctionBody.ExprCompileCore arg) →
      SupportedLeafStmt (.emit eventName args)
  | ecm {mod : Compiler.ECM.ExternalCallModule} {args : List Expr} :
      (∀ arg ∈ args, FunctionBody.ExprCompileCore arg) → SupportedLeafStmt (.ecm mod args)
  | letMapping {tmp fieldName : String} {key : Expr} :
      FunctionBody.ExprCompileCore key →
      SupportedLeafStmt (.letVar tmp (.mapping fieldName key))
  | letMappingWord {tmp fieldName : String} {key : Expr} {wordOffset : Nat} :
      FunctionBody.ExprCompileCore key →
      SupportedLeafStmt (.letVar tmp (.mappingWord fieldName key wordOffset))
  | letMappingUint {tmp fieldName : String} {key : Expr} :
      FunctionBody.ExprCompileCore key →
      SupportedLeafStmt (.letVar tmp (.mappingUint fieldName key))
  | letMappingPackedWord {tmp fieldName : String} {key : Expr} {wordOffset : Nat}
      {packed : PackedBits} :
      FunctionBody.ExprCompileCore key →
      SupportedLeafStmt (.letVar tmp (.mappingPackedWord fieldName key wordOffset packed))
  | letStructMember {tmp fieldName memberName : String} {key : Expr} :
      FunctionBody.ExprCompileCore key →
      SupportedLeafStmt (.letVar tmp (.structMember fieldName key memberName))
  | letMapping2 {tmp fieldName : String} {key1 key2 : Expr} :
      FunctionBody.ExprCompileCore key1 → FunctionBody.ExprCompileCore key2 →
      SupportedLeafStmt (.letVar tmp (.mapping2 fieldName key1 key2))
  | letMapping2Word {tmp fieldName : String} {key1 key2 : Expr} {wordOffset : Nat} :
      FunctionBody.ExprCompileCore key1 → FunctionBody.ExprCompileCore key2 →
      SupportedLeafStmt (.letVar tmp (.mapping2Word fieldName key1 key2 wordOffset))
  | letStructMember2 {tmp fieldName memberName : String} {key1 key2 : Expr} :
      FunctionBody.ExprCompileCore key1 → FunctionBody.ExprCompileCore key2 →
      SupportedLeafStmt (.letVar tmp (.structMember2 fieldName key1 key2 memberName))
  | setMappingUint {fieldName : String} {key value : Expr} :
      FunctionBody.ExprCompileCore key → FunctionBody.ExprCompileCore value →
      SupportedLeafStmt (.setMappingUint fieldName key value)
  | setMappingChain {fieldName : String} {keys : List Expr} {value : Expr} :
      (∀ key ∈ keys, FunctionBody.ExprCompileCore key) → FunctionBody.ExprCompileCore value →
      SupportedLeafStmt (.setMappingChain fieldName keys value)
  | setMapping {fieldName : String} {key value : Expr} :
      FunctionBody.ExprCompileCore key → FunctionBody.ExprCompileCore value →
      SupportedLeafStmt (.setMapping fieldName key value)
  | setMappingWord {fieldName : String} {key value : Expr} {wordOffset : Nat} :
      FunctionBody.ExprCompileCore key → FunctionBody.ExprCompileCore value →
      SupportedLeafStmt (.setMappingWord fieldName key wordOffset value)
  | setMappingPackedWord {fieldName : String} {key value : Expr} {wordOffset : Nat}
      {packed : PackedBits} :
      FunctionBody.ExprCompileCore key → FunctionBody.ExprCompileCore value →
      SupportedLeafStmt (.setMappingPackedWord fieldName key wordOffset packed value)
  | setStructMember {fieldName memberName : String} {key value : Expr} :
      FunctionBody.ExprCompileCore key → FunctionBody.ExprCompileCore value →
      SupportedLeafStmt (.setStructMember fieldName key memberName value)
  | setMapping2 {fieldName : String} {key1 key2 value : Expr} :
      FunctionBody.ExprCompileCore key1 → FunctionBody.ExprCompileCore key2 →
      FunctionBody.ExprCompileCore value →
      SupportedLeafStmt (.setMapping2 fieldName key1 key2 value)
  | setMapping2Word {fieldName : String} {key1 key2 value : Expr} {wordOffset : Nat} :
      FunctionBody.ExprCompileCore key1 → FunctionBody.ExprCompileCore key2 →
      FunctionBody.ExprCompileCore value →
      SupportedLeafStmt (.setMapping2Word fieldName key1 key2 wordOffset value)
  | setStructMember2 {fieldName memberName : String} {key1 key2 value : Expr} :
      FunctionBody.ExprCompileCore key1 → FunctionBody.ExprCompileCore key2 →
      FunctionBody.ExprCompileCore value →
      SupportedLeafStmt (.setStructMember2 fieldName key1 key2 memberName value)
  | forEachCore {scope : List String} {varName : String} {body : List Stmt} (n : Nat) :
      FunctionBody.StmtListCompileCore (varName :: scope) body →
      SupportedLeafStmt (.forEach varName (.literal n) body)
  | iteCore {scope : List String} {cond : Expr} {thenBranch elseBranch : List Stmt} :
      FunctionBody.ExprCompileCore cond →
      FunctionBody.StmtListCompileCore scope thenBranch →
      FunctionBody.StmtListCompileCore scope elseBranch →
      SupportedLeafStmt (.ite cond thenBranch elseBranch)
  | require {cond : Expr} {message : String} :
      FunctionBody.ExprCompileCore cond → SupportedLeafStmt (.require cond message)

open Verity.Core.Free in
/-- A unified `require` guard-family clause encodes a `require` whose guard is a
compile-core expression over literals. -/
private theorem requireLiteralGuardFamilyClause_toStmt_eq_require
    (clause : RequireLiteralGuardFamilyClause) :
    ∃ cond, clause.toStmt = Stmt.require cond clause.message ∧
      FunctionBody.ExprCompileCore cond := by
  rcases clause with ⟨family, n, m, p, q, message⟩
  cases family with
  | binary op => cases op <;> exact ⟨_, rfl, by repeat constructor⟩
  | andEqLt | orEqLt => exact ⟨_, rfl, by repeat constructor⟩

/-- Generic induction principle for `SupportedStmtList`: an append-closed
statement-list property holds on every supported list once it holds on the
compile-core and terminal-core lists, the single-statement leaves, literal-zero
`forEach` loops, and terminal `ite` heads. -/
private theorem SupportedStmtList.induction_of_leaf
    {P : List Stmt → Prop}
    (hCore : ∀ {scope stmts}, FunctionBody.StmtListCompileCore scope stmts → P stmts)
    (hTerminal : ∀ {scope stmts}, FunctionBody.StmtListTerminalCore scope stmts → P stmts)
    (hLeaf : ∀ {stmt}, SupportedLeafStmt stmt → P [stmt])
    (hForEach : ∀ {varName body}, P body → P [Stmt.forEach varName (.literal 0) body])
    (hIte : ∀ {scope cond thenBranch elseBranch}, FunctionBody.ExprCompileCore cond →
      FunctionBody.StmtListTerminalCore scope thenBranch →
      FunctionBody.StmtListTerminalCore scope elseBranch →
      P [Stmt.ite cond thenBranch elseBranch])
    (hAppend : ∀ {xs ys}, P xs → P ys → P (xs ++ ys))
    {fields : List Field} {scope : List String} {stmts : List Stmt}
    (h : SupportedStmtList fields scope stmts) : P stmts := by
  induction h with
  | compileCore hcore => exact hCore hcore
  | terminalCore hterminal => exact hTerminal hterminal
  | forEachLiteralBounded _ _ ih => exact hForEach ih
  | requireClause clause _ ih =>
      obtain ⟨cond, hstmt, hcond⟩ := requireLiteralGuardFamilyClause_toStmt_eq_require clause
      rw [hstmt]
      exact hAppend (xs := [_]) (hLeaf (.require hcond)) ih
  | iteTerminal hcond _ hthen helse => exact hIte hcond hthen helse
  | append _ _ ihPfx ihSfx => exact hAppend ihPfx ihSfx
  | _ => exact hLeaf (by constructor <;> assumption)

/-- A statement-list Boolean fold `listF` built from `stmtF` with `||` vanishes on
an append when it vanishes on both halves. -/
private theorem boolFold_append_eq_false
    {listF : List Stmt → Bool} {stmtF : Stmt → Bool}
    (hnil : listF [] = false) (hcons : ∀ s ss, listF (s :: ss) = (stmtF s || listF ss))
    {xs ys : List Stmt} (hxs : listF xs = false) (hys : listF ys = false) :
    listF (xs ++ ys) = false := by
  induction xs with
  | nil => simpa using hys
  | cons x xs ih =>
      rw [hcons, Bool.or_eq_false_iff] at hxs
      rw [List.cons_append, hcons, hxs.1, ih hxs.2, Bool.or_false]

/-- Specialization of `SupportedStmtList.induction_of_leaf` to `||`-folds over
statements: such a fold is `false` on every supported list once `stmtF` is
`false` on the leaves, `forEach` heads and terminal `ite` heads. -/
private theorem SupportedStmtList.boolFold_eq_false
    {listF : List Stmt → Bool} {stmtF : Stmt → Bool}
    (hnil : listF [] = false) (hcons : ∀ s ss, listF (s :: ss) = (stmtF s || listF ss))
    (hCore : ∀ {scope stmts}, FunctionBody.StmtListCompileCore scope stmts → listF stmts = false)
    (hTerminal : ∀ {scope stmts},
      FunctionBody.StmtListTerminalCore scope stmts → listF stmts = false)
    (hLeaf : ∀ {stmt}, SupportedLeafStmt stmt → stmtF stmt = false)
    (hForEach : ∀ {varName body},
      listF body = false → stmtF (Stmt.forEach varName (.literal 0) body) = false)
    (hIte : ∀ {scope cond thenBranch elseBranch}, FunctionBody.ExprCompileCore cond →
      FunctionBody.StmtListTerminalCore scope thenBranch →
      FunctionBody.StmtListTerminalCore scope elseBranch →
      stmtF (Stmt.ite cond thenBranch elseBranch) = false)
    {fields : List Field} {scope : List String} {stmts : List Stmt}
    (h : SupportedStmtList fields scope stmts) : listF stmts = false := by
  have hsingle : ∀ {s}, stmtF s = false → listF [s] = false := fun hs => by
    rw [hcons, hs, hnil, Bool.or_false]
  exact SupportedStmtList.induction_of_leaf hCore hTerminal (hsingle <| hLeaf ·)
    (hsingle <| hForEach ·) (fun hc ht he => hsingle (hIte hc ht he))
    (boolFold_append_eq_false hnil hcons) h

private theorem supportedLeafStmt_helperSurfaceClosed
    {stmt : Stmt} (h : SupportedLeafStmt stmt) :
    stmtTouchesUnsupportedHelperSurface stmt = false := by
  cases h with
  | emit hargs | ecm hargs =>
      simpa [stmtTouchesUnsupportedHelperSurface] using
        exprListCompileCore_helperSurfaceClosed hargs
  | setMappingChain hkeys hvalue =>
      simp [stmtTouchesUnsupportedHelperSurface, exprListCompileCore_helperSurfaceClosed hkeys,
        exprCompileCore_helperSurfaceClosed hvalue]
  | forEachCore _ hbody =>
      simp [stmtTouchesUnsupportedHelperSurface, exprTouchesUnsupportedHelperSurface,
        stmtListCompileCore_helperSurfaceClosed hbody]
  | iteCore hcond hthen helse =>
      simp [stmtTouchesUnsupportedHelperSurface, exprCompileCore_helperSurfaceClosed hcond,
        stmtListCompileCore_helperSurfaceClosed hthen, stmtListCompileCore_helperSurfaceClosed helse]
  | _ =>
      simp_all [stmtTouchesUnsupportedHelperSurface, exprTouchesUnsupportedHelperSurface,
        stmtListTouchesUnsupportedHelperSurface, exprCompileCore_helperSurfaceClosed]

open Verity.Core.Free in
theorem SupportedStmtList.helperSurfaceClosed
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hSupported : SupportedStmtList fields scope stmts) :
    stmtListTouchesUnsupportedHelperSurface stmts = false := by
  refine SupportedStmtList.boolFold_eq_false (stmtF := stmtTouchesUnsupportedHelperSurface)
    (by simp [stmtListTouchesUnsupportedHelperSurface])
    (fun _ _ => by simp [stmtListTouchesUnsupportedHelperSurface])
    stmtListCompileCore_helperSurfaceClosed stmtListTerminalCore_helperSurfaceClosed
    supportedLeafStmt_helperSurfaceClosed (fun hbody => ?_) (fun hcond hthen helse => ?_)
    hSupported
  · simpa [stmtTouchesUnsupportedHelperSurface, exprTouchesUnsupportedHelperSurface] using hbody
  · simp only [stmtTouchesUnsupportedHelperSurface, exprCompileCore_helperSurfaceClosed hcond,
      stmtListTerminalCore_helperSurfaceClosed hthen,
      stmtListTerminalCore_helperSurfaceClosed helse, Bool.or_false]

private theorem supportedLeafStmt_internalHelperCallNames_nil
    {stmt : Stmt} (h : SupportedLeafStmt stmt) :
    stmtInternalHelperCallNames stmt = [] := by
  cases h with
  | emit hargs | ecm hargs =>
      simpa [stmtInternalHelperCallNames] using
        exprListCompileCore_internalHelperCallNames_nil hargs
  | setMappingChain hkeys hvalue =>
      simp [stmtInternalHelperCallNames, exprListCompileCore_internalHelperCallNames_nil hkeys,
        exprCompileCore_internalHelperCallNames_nil hvalue]
  | forEachCore _ hbody =>
      simp [stmtInternalHelperCallNames, exprInternalHelperCallNames,
        stmtListCompileCore_internalHelperCallNames_nil hbody]
  | iteCore hcond hthen helse =>
      simp [stmtInternalHelperCallNames, exprCompileCore_internalHelperCallNames_nil hcond,
        stmtListCompileCore_internalHelperCallNames_nil hthen,
        stmtListCompileCore_internalHelperCallNames_nil helse]
  | _ =>
      simp_all [stmtInternalHelperCallNames, exprInternalHelperCallNames,
        stmtListInternalHelperCallNames, exprCompileCore_internalHelperCallNames_nil]

private theorem stmtListInternalHelperCallNames_append
    (xs ys : List Stmt) :
    stmtListInternalHelperCallNames (xs ++ ys) =
      stmtListInternalHelperCallNames xs ++ stmtListInternalHelperCallNames ys := by
  induction xs with
  | nil => simp [stmtListInternalHelperCallNames]
  | cons x xs ih => simp [stmtListInternalHelperCallNames, ih]

open Verity.Core.Free in
theorem SupportedStmtList.internalHelperCallNames_nil
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hSupported : SupportedStmtList fields scope stmts) :
    stmtListInternalHelperCallNames stmts = [] := by
  refine SupportedStmtList.induction_of_leaf (P := (stmtListInternalHelperCallNames · = []))
    stmtListCompileCore_internalHelperCallNames_nil
    stmtListTerminalCore_internalHelperCallNames_nil
    (fun h => by simp [stmtListInternalHelperCallNames,
      supportedLeafStmt_internalHelperCallNames_nil h])
    (fun hbody => ?_) (fun hcond hthen helse => ?_)
    (fun hxs hys => by rw [stmtListInternalHelperCallNames_append, hxs, hys, List.nil_append])
    hSupported
  · simpa [stmtListInternalHelperCallNames, stmtInternalHelperCallNames,
      exprInternalHelperCallNames] using hbody
  · simp only [stmtListInternalHelperCallNames, stmtInternalHelperCallNames,
      exprCompileCore_internalHelperCallNames_nil hcond,
      stmtListTerminalCore_internalHelperCallNames_nil hthen,
      stmtListTerminalCore_internalHelperCallNames_nil helse, List.nil_append, List.append_nil]


theorem SupportedBodyInterface.helperCallNames_nil
    {spec : CompilationModel} {fn : FunctionSpec}
    (hBody : SupportedBodyInterface spec fn) :
    helperCallNames fn = [] := by
  simp [helperCallNames, hBody.stmtList.internalHelperCallNames_nil]

theorem SupportedBodyInterfaceExceptMappingWrites.helperCallNames_nil
    {spec : CompilationModel} {fn : FunctionSpec}
    (hBody : SupportedBodyInterfaceExceptMappingWrites spec fn) :
    helperCallNames fn = [] := by
  simp [helperCallNames, hBody.stmtList.internalHelperCallNames_nil]

mutual
  theorem exprTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed
      {expr : Expr}
      (hsurface : exprTouchesUnsupportedHelperSurface expr = false) :
      exprTouchesInternalHelperSurface expr = false := by
    cases expr with
    | externalCall name args =>
        -- Only the reserved two-operand `exp` builtin lane recurses; every other
        -- `externalCall` shape is still uniformly outside the helper surface.
        rcases args with _ | ⟨base, _ | ⟨exponent, _ | ⟨_, _⟩⟩⟩
        all_goals try simp [exprTouchesInternalHelperSurface]
        by_cases hname : name = builtinExpName
        · subst hname
          simp only [exprTouchesUnsupportedHelperSurface, beq_self_eq_true, if_true,
            Bool.or_eq_false_iff] at hsurface
          simp [exprTouchesInternalHelperSurface,
            exprTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed hsurface.1,
            exprTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed hsurface.2]
        · simp [exprTouchesInternalHelperSurface, hname]
    | _ =>
        simp only [exprTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
        simp_all [exprTouchesInternalHelperSurface,
          exprTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed]

  theorem exprListTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed
      {exprs : List Expr}
      (hsurface : exprListTouchesUnsupportedHelperSurface exprs = false) :
      exprs.any exprTouchesInternalHelperSurface = false := by
    cases exprs with
    | nil =>
        simp
    | cons expr rest =>
        simp only [exprListTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
        simp [exprTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed hsurface.1,
          exprListTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed hsurface.2]
end

-- Statement closure depends on expression closure but not conversely, so it is
-- its own mutual block. Both blocks recurse structurally over the nested
-- `Expr`/`Stmt` inductives: well-founded `termination_by sizeOf` recursion
-- here cost over 200 000 heartbeats in generated termination proofs alone.

mutual
  theorem stmtTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed
      {stmt : Stmt}
      (hsurface : stmtTouchesUnsupportedHelperSurface stmt = false) :
      stmtTouchesInternalHelperSurface stmt = false := by
    cases stmt with
    | ite cond thenBranch elseBranch =>
        simp only [stmtTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
        simp [stmtTouchesInternalHelperSurface,
          exprTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed hsurface.1.1,
          stmtListTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed hsurface.1.2,
          stmtListTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed hsurface.2]
    | forEach _ count body | forEachSetBit _ count body =>
        simp only [stmtTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
        simp [stmtTouchesInternalHelperSurface,
          exprTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed hsurface.1,
          stmtListTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed hsurface.2]
    | _ =>
        simp only [stmtTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
        simp_all [stmtTouchesInternalHelperSurface,
          exprTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed,
          exprListTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed]

  theorem stmtListTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed
      {stmts : List Stmt}
      (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false) :
      stmtListTouchesInternalHelperSurface stmts = false := by
    cases stmts with
    | nil => simp [stmtListTouchesInternalHelperSurface]
    | cons stmt rest =>
        simp only [stmtListTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
        simp [stmtListTouchesInternalHelperSurface,
          stmtTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed hsurface.1,
          stmtListTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed hsurface.2]
end

theorem stmtTouchesInternalHelperSurface_eq_split
    (stmt : Stmt) :
    stmtTouchesInternalHelperSurface stmt =
      (stmtTouchesDirectInternalHelperSurface stmt ||
        stmtTouchesExprInternalHelperSurface stmt ||
        stmtTouchesStructuralInternalHelperSurface stmt) := by
  cases stmt <;>
    simp [stmtTouchesInternalHelperSurface,
      stmtTouchesDirectInternalHelperSurface,
      stmtTouchesExprInternalHelperSurface,
      stmtTouchesStructuralInternalHelperSurface,
      Bool.or_assoc]


theorem stmtTouchesDirectInternalHelperSurface_eq_split
    (stmt : Stmt) :
    stmtTouchesDirectInternalHelperSurface stmt =
      (stmtTouchesDirectInternalHelperCallSurface stmt ||
        stmtTouchesDirectInternalHelperAssignSurface stmt) := by
  cases stmt <;>
    simp [stmtTouchesDirectInternalHelperSurface,
      stmtTouchesDirectInternalHelperCallSurface,
      stmtTouchesDirectInternalHelperAssignSurface]

theorem stmtTouchesDirectInternalHelperSurface_eq_false_of_helperSurfaceClosed
    {stmt : Stmt}
    (hsurface : stmtTouchesUnsupportedHelperSurface stmt = false) :
    stmtTouchesDirectInternalHelperSurface stmt = false := by
  have hinternal := stmtTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed hsurface
  rw [stmtTouchesInternalHelperSurface_eq_split] at hinternal
  cases hdirect : stmtTouchesDirectInternalHelperSurface stmt <;>
    simp [hdirect] at hinternal ⊢

theorem stmtTouchesDirectInternalHelperCallSurface_eq_false_of_helperSurfaceClosed
    {stmt : Stmt}
    (hsurface : stmtTouchesUnsupportedHelperSurface stmt = false) :
    stmtTouchesDirectInternalHelperCallSurface stmt = false := by
  have := stmtTouchesDirectInternalHelperSurface_eq_false_of_helperSurfaceClosed hsurface
  rw [stmtTouchesDirectInternalHelperSurface_eq_split] at this
  exact (Bool.or_eq_false_iff.mp this).1

theorem stmtTouchesDirectInternalHelperAssignSurface_eq_false_of_helperSurfaceClosed
    {stmt : Stmt}
    (hsurface : stmtTouchesUnsupportedHelperSurface stmt = false) :
    stmtTouchesDirectInternalHelperAssignSurface stmt = false := by
  have := stmtTouchesDirectInternalHelperSurface_eq_false_of_helperSurfaceClosed hsurface
  rw [stmtTouchesDirectInternalHelperSurface_eq_split] at this
  exact (Bool.or_eq_false_iff.mp this).2

theorem stmtTouchesExprInternalHelperSurface_eq_false_of_helperSurfaceClosed
    {stmt : Stmt}
    (hsurface : stmtTouchesUnsupportedHelperSurface stmt = false) :
    stmtTouchesExprInternalHelperSurface stmt = false := by
  have hinternal := stmtTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed hsurface
  rw [stmtTouchesInternalHelperSurface_eq_split] at hinternal
  cases hdirect : stmtTouchesDirectInternalHelperSurface stmt <;>
    cases hexpr : stmtTouchesExprInternalHelperSurface stmt <;>
      simp [hdirect, hexpr] at hinternal ⊢

theorem stmtTouchesStructuralInternalHelperSurface_eq_false_of_helperSurfaceClosed
    {stmt : Stmt}
    (hsurface : stmtTouchesUnsupportedHelperSurface stmt = false) :
    stmtTouchesStructuralInternalHelperSurface stmt = false := by
  have hinternal := stmtTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed hsurface
  rw [stmtTouchesInternalHelperSurface_eq_split] at hinternal
  cases hdirect : stmtTouchesDirectInternalHelperSurface stmt <;>
    cases hexpr : stmtTouchesExprInternalHelperSurface stmt <;>
      cases hstruct : stmtTouchesStructuralInternalHelperSurface stmt <;>
        simp [hdirect, hexpr, hstruct] at hinternal ⊢

theorem stmtListTouchesDirectInternalHelperSurface_eq_false_of_helperSurfaceClosed
    {stmts : List Stmt}
    (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false) :
    stmtListTouchesDirectInternalHelperSurface stmts = false := by
  induction stmts with
  | nil => simp [stmtListTouchesDirectInternalHelperSurface]
  | cons stmt rest ih =>
      simp only [stmtListTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
      simp [stmtListTouchesDirectInternalHelperSurface,
        stmtTouchesDirectInternalHelperSurface_eq_false_of_helperSurfaceClosed hsurface.1,
        ih hsurface.2]

theorem stmtListTouchesDirectInternalHelperCallSurface_eq_false_of_helperSurfaceClosed
    {stmts : List Stmt}
    (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false) :
    stmtListTouchesDirectInternalHelperCallSurface stmts = false := by
  induction stmts with
  | nil => simp [stmtListTouchesDirectInternalHelperCallSurface]
  | cons stmt rest ih =>
      simp only [stmtListTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
      simp [stmtListTouchesDirectInternalHelperCallSurface,
        stmtTouchesDirectInternalHelperCallSurface_eq_false_of_helperSurfaceClosed hsurface.1,
        ih hsurface.2]

theorem stmtListTouchesDirectInternalHelperAssignSurface_eq_false_of_helperSurfaceClosed
    {stmts : List Stmt}
    (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false) :
    stmtListTouchesDirectInternalHelperAssignSurface stmts = false := by
  induction stmts with
  | nil => simp [stmtListTouchesDirectInternalHelperAssignSurface]
  | cons stmt rest ih =>
      simp only [stmtListTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
      simp [stmtListTouchesDirectInternalHelperAssignSurface,
        stmtTouchesDirectInternalHelperAssignSurface_eq_false_of_helperSurfaceClosed hsurface.1,
        ih hsurface.2]

theorem stmtListTouchesExprInternalHelperSurface_eq_false_of_helperSurfaceClosed
    {stmts : List Stmt}
    (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false) :
    stmtListTouchesExprInternalHelperSurface stmts = false := by
  induction stmts with
  | nil => simp [stmtListTouchesExprInternalHelperSurface]
  | cons stmt rest ih =>
      simp only [stmtListTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
      simp [stmtListTouchesExprInternalHelperSurface,
        stmtTouchesExprInternalHelperSurface_eq_false_of_helperSurfaceClosed hsurface.1,
        ih hsurface.2]

theorem stmtListTouchesStructuralInternalHelperSurface_eq_false_of_helperSurfaceClosed
    {stmts : List Stmt}
    (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false) :
    stmtListTouchesStructuralInternalHelperSurface stmts = false := by
  induction stmts with
  | nil => simp [stmtListTouchesStructuralInternalHelperSurface]
  | cons stmt rest ih =>
      simp only [stmtListTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
      simp [stmtListTouchesStructuralInternalHelperSurface,
        stmtTouchesStructuralInternalHelperSurface_eq_false_of_helperSurfaceClosed hsurface.1,
        ih hsurface.2]


theorem SupportedStmtList.internalHelperSurfaceClosed
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hSupported : SupportedStmtList fields scope stmts) :
    stmtListTouchesInternalHelperSurface stmts = false := by
  exact stmtListTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed
    hSupported.helperSurfaceClosed

theorem SupportedBodyInterface.helperSurfaceClosed
    {spec : CompilationModel} {fn : FunctionSpec}
    (hBody : SupportedBodyInterface spec fn) :
    stmtListTouchesUnsupportedHelperSurface fn.body = false := by
  exact hBody.stmtList.helperSurfaceClosed

theorem SupportedBodyInterfaceWithScalarEvents.helperSurfaceClosed
    {spec : CompilationModel} {fn : FunctionSpec}
    (hBody : SupportedBodyInterfaceWithScalarEvents spec fn) :
    stmtListTouchesUnsupportedHelperSurface fn.body = false := by
  exact hBody.stmtList.helperSurfaceClosed

theorem SupportedBodyInterfaceExceptMappingWrites.helperSurfaceClosed
    {spec : CompilationModel} {fn : FunctionSpec}
    (hBody : SupportedBodyInterfaceExceptMappingWrites spec fn) :
    stmtListTouchesUnsupportedHelperSurface fn.body = false := by
  exact hBody.stmtList.helperSurfaceClosed

def SupportedBodyHelperInterface.summaryOfCall
    {spec : CompilationModel} {fn : FunctionSpec}
    (hHelpers : SupportedBodyHelperInterface spec fn)
    {calleeName : String}
    (hmem : calleeName ∈ helperCallNames fn) :
    SupportedInternalHelperWitness spec calleeName :=
  hHelpers.summaryOf calleeName hmem

def SupportedBodyHelperInterface.summaryContractOfCall
    {spec : CompilationModel} {fn : FunctionSpec}
    (hHelpers : SupportedBodyHelperInterface spec fn)
    {calleeName : String}
    (hmem : calleeName ∈ helperCallNames fn) :
    InternalHelperSummaryContract :=
  (hHelpers.summaryOfCall hmem).summary.contract

theorem SupportedBodyHelperInterface.calleeRank_lt
    {spec : CompilationModel} {fn : FunctionSpec}
    (hHelpers : SupportedBodyHelperInterface spec fn)
    {calleeName : String}
    (hmem : calleeName ∈ helperCallNames fn) :
    (hHelpers.summaryOfCall hmem).summary.helperRank < hHelpers.helperRank :=
  hHelpers.calleeRanksDecrease calleeName hmem

theorem SupportedBodyHelperInterface.exprSummaryPreservesWorld
    {spec : CompilationModel} {fn : FunctionSpec}
    (hHelpers : SupportedBodyHelperInterface spec fn)
    {calleeName : String}
    (hmem : calleeName ∈ exprHelperCallNames fn) :
    let hcall : calleeName ∈ helperCallNames fn :=
      exprHelperCallNames_subset_helperCallNames hmem
    InternalHelperSummaryPreservesWorldOnSuccess
      (hHelpers.summaryContractOfCall hcall) :=
  hHelpers.exprCallsPreserveWorld calleeName hmem

def SupportedRuntimeHelperTableInterface.compiledOfCall
    {spec : CompilationModel}
    {runtimeContract : IRContract}
    {fn : FunctionSpec}
    (hRuntime : SupportedRuntimeHelperTableInterface spec runtimeContract)
    (hHelpers : SupportedBodyHelperInterface spec fn)
    {calleeName : String}
    (hmem : calleeName ∈ helperCallNames fn) :
    SupportedCompiledInternalHelperWitness spec runtimeContract calleeName :=
  hRuntime.compiledOfWitness calleeName (hHelpers.summaryOfCall hmem)

/-- The compiled helper produced by `compiledOfCall` carries exactly the source
witness inventoried for that call, so a source summary proof about
`hHelpers.summaryOfCall hmem` is a proof about `compiledHelper.sourceWitness`. -/
theorem SupportedRuntimeHelperTableInterface.compiledOfCall_sourceWitness
    {spec : CompilationModel}
    {runtimeContract : IRContract}
    {fn : FunctionSpec}
    (hRuntime : SupportedRuntimeHelperTableInterface spec runtimeContract)
    (hHelpers : SupportedBodyHelperInterface spec fn)
    {calleeName : String}
    (hmem : calleeName ∈ helperCallNames fn) :
    (hRuntime.compiledOfCall hHelpers hmem).sourceWitness = hHelpers.summaryOfCall hmem :=
  hRuntime.compiledOfWitness_sourceWitness calleeName (hHelpers.summaryOfCall hmem)


-- NOTE: An exact decomposition theorem
--   exprTouchesUnsupportedContractSurface expr =
--     (exprTouchesUnsupportedCoreSurface expr ||
--      exprTouchesUnsupportedStateSurface expr ||
--      exprTouchesUnsupportedCallSurface expr)
-- was removed because it is not used by any downstream proof and the
-- implication direction (featureClosed → contractSurface = false) already
-- suffices for the generic-induction bridge.
--
-- The original expression-level counterexample (sdiv returning true in
-- core but recursing in contract) was resolved when signed arithmetic was
-- ungated in the core surface. The statement-level `.ite` mismatch
-- (both core and contract return true directly) does not block the
-- decomposition, but the equality is still fragile under future surface
-- changes and carries no proof value, so it remains intentionally absent.

private theorem exprTouchesUnsupportedCallSurface_eq_featureOr
    (expr : Expr) :
    exprTouchesUnsupportedCallSurface expr =
      (exprTouchesUnsupportedHelperSurface expr ||
        exprTouchesUnsupportedForeignSurface expr ||
        exprTouchesUnsupportedLowLevelSurface expr) := by
  cases expr with
  | externalCall name args =>
      -- All four predicates recurse identically on the reserved `exp` builtin
      -- lane, so the decomposition holds there by associativity/commutativity.
      rcases args with _ | ⟨base, _ | ⟨exponent, _ | ⟨_, _⟩⟩⟩
      all_goals try simp [exprTouchesUnsupportedCallSurface, exprTouchesUnsupportedHelperSurface,
        exprTouchesUnsupportedForeignSurface, exprTouchesUnsupportedLowLevelSurface]
      by_cases hname : name = builtinExpName
      · subst hname
        simp only [exprTouchesUnsupportedCallSurface, exprTouchesUnsupportedHelperSurface,
          exprTouchesUnsupportedForeignSurface, exprTouchesUnsupportedLowLevelSurface,
          beq_self_eq_true, if_true]
        rw [exprTouchesUnsupportedCallSurface_eq_featureOr base,
          exprTouchesUnsupportedCallSurface_eq_featureOr exponent]
        simp [Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]
      · simp [exprTouchesUnsupportedCallSurface, exprTouchesUnsupportedHelperSurface,
          exprTouchesUnsupportedForeignSurface, exprTouchesUnsupportedLowLevelSurface, hname]
  | _ =>
      simp [exprTouchesUnsupportedCallSurface, exprTouchesUnsupportedHelperSurface,
        exprTouchesUnsupportedForeignSurface, exprTouchesUnsupportedLowLevelSurface,
        exprTouchesUnsupportedCallSurface_eq_featureOr,
        Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem exprListTouchesUnsupportedCallSurface_eq_featureOr
    (exprs : List Expr) :
    exprs.any exprTouchesUnsupportedCallSurface =
      (exprs.any exprTouchesUnsupportedForeignSurface ||
        exprListTouchesUnsupportedHelperSurface exprs ||
        exprs.any exprTouchesUnsupportedLowLevelSurface) := by
  induction exprs with
  | nil =>
      simp [exprListTouchesUnsupportedHelperSurface]
  | cons expr rest ih =>
      simp only [List.any_cons, exprListTouchesUnsupportedHelperSurface]
      rw [exprTouchesUnsupportedCallSurface_eq_featureOr, ih]
      simp [Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

mutual
  private theorem stmtTouchesUnsupportedCallSurface_eq_featureOr_aux
      (stmt : Stmt) :
      stmtTouchesUnsupportedCallSurface stmt =
        (stmtTouchesUnsupportedHelperSurface stmt ||
          stmtTouchesUnsupportedForeignSurface stmt ||
          stmtTouchesUnsupportedLowLevelSurface stmt) := by
    cases stmt with
    | ite cond thenBranch elseBranch =>
        simp only [stmtTouchesUnsupportedCallSurface, stmtTouchesUnsupportedHelperSurface,
          stmtTouchesUnsupportedForeignSurface, stmtTouchesUnsupportedLowLevelSurface]
        rw [exprTouchesUnsupportedCallSurface_eq_featureOr,
          stmtListTouchesUnsupportedCallSurface_eq_featureOr_aux thenBranch,
          stmtListTouchesUnsupportedCallSurface_eq_featureOr_aux elseBranch]
        simp [Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]
    | forEach _ count body | forEachSetBit _ count body =>
        simp only [stmtTouchesUnsupportedCallSurface, stmtTouchesUnsupportedHelperSurface,
          stmtTouchesUnsupportedForeignSurface, stmtTouchesUnsupportedLowLevelSurface]
        rw [exprTouchesUnsupportedCallSurface_eq_featureOr,
          stmtListTouchesUnsupportedCallSurface_eq_featureOr_aux body]
        simp [Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]
    | _ =>
        simp [stmtTouchesUnsupportedCallSurface, stmtTouchesUnsupportedHelperSurface,
          stmtTouchesUnsupportedForeignSurface, stmtTouchesUnsupportedLowLevelSurface,
          exprTouchesUnsupportedCallSurface_eq_featureOr,
          exprListTouchesUnsupportedCallSurface_eq_featureOr,
          Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

  private theorem stmtListTouchesUnsupportedCallSurface_eq_featureOr_aux
      (stmts : List Stmt) :
      stmtListTouchesUnsupportedCallSurface stmts =
        (stmtListTouchesUnsupportedHelperSurface stmts ||
          stmtListTouchesUnsupportedForeignSurface stmts ||
          stmtListTouchesUnsupportedLowLevelSurface stmts) := by
    cases stmts with
    | nil =>
        simp [stmtListTouchesUnsupportedCallSurface, stmtListTouchesUnsupportedHelperSurface,
          stmtListTouchesUnsupportedForeignSurface, stmtListTouchesUnsupportedLowLevelSurface]
    | cons stmt rest =>
        simp only [stmtListTouchesUnsupportedCallSurface, stmtListTouchesUnsupportedHelperSurface,
          stmtListTouchesUnsupportedForeignSurface, stmtListTouchesUnsupportedLowLevelSurface,
          List.any_cons]
        rw [stmtTouchesUnsupportedCallSurface_eq_featureOr_aux stmt,
          stmtListTouchesUnsupportedCallSurface_eq_featureOr_aux rest]
        simp [Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]
end

private theorem stmtOrListTouchesUnsupportedCallSurface_eq_featureOr :
    (target : Sum Stmt (List Stmt)) →
      match target with
      | .inl stmt =>
          stmtTouchesUnsupportedCallSurface stmt =
            (stmtTouchesUnsupportedHelperSurface stmt ||
              stmtTouchesUnsupportedForeignSurface stmt ||
              stmtTouchesUnsupportedLowLevelSurface stmt)
      | .inr stmts =>
          stmtListTouchesUnsupportedCallSurface stmts =
            (stmtListTouchesUnsupportedHelperSurface stmts ||
              stmtListTouchesUnsupportedForeignSurface stmts ||
              stmtListTouchesUnsupportedLowLevelSurface stmts)
  | .inl stmt => stmtTouchesUnsupportedCallSurface_eq_featureOr_aux stmt
  | .inr stmts => stmtListTouchesUnsupportedCallSurface_eq_featureOr_aux stmts

theorem stmtListTouchesUnsupportedCallSurface_eq_featureOr
    (stmts : List Stmt) :
    stmtListTouchesUnsupportedCallSurface stmts =
      (stmtListTouchesUnsupportedHelperSurface stmts ||
        stmtListTouchesUnsupportedForeignSurface stmts ||
        stmtListTouchesUnsupportedLowLevelSurface stmts) := by
  simpa using stmtOrListTouchesUnsupportedCallSurface_eq_featureOr (.inr stmts)


private theorem exprTouchesUnsupportedContractSurface_eq_false_of_featureClosed
    (expr : Expr)
    (hcore : exprTouchesUnsupportedCoreSurface expr = false)
    (hstate : exprTouchesUnsupportedStateSurface expr = false)
    (hcalls : exprTouchesUnsupportedCallSurface expr = false) :
    exprTouchesUnsupportedContractSurface expr = false := by
  cases expr with
  | externalCall name args =>
      rcases args with _ | ⟨base, _ | ⟨exponent, _ | ⟨_, _⟩⟩⟩
      all_goals try simp [exprTouchesUnsupportedCoreSurface] at hcore
      by_cases hname : name = builtinExpName
      · subst hname
        simp only [exprTouchesUnsupportedCoreSurface, exprTouchesUnsupportedStateSurface,
          exprTouchesUnsupportedCallSurface, beq_self_eq_true, if_true,
          Bool.or_eq_false_iff] at hcore hstate hcalls
        simp_all [exprTouchesUnsupportedContractSurface,
          exprTouchesUnsupportedContractSurface_eq_false_of_featureClosed]
      · simp [exprTouchesUnsupportedCoreSurface, hname] at hcore
  | _ =>
      simp only [exprTouchesUnsupportedCoreSurface, exprTouchesUnsupportedStateSurface,
        exprTouchesUnsupportedCallSurface, Bool.or_eq_false_iff] at hcore hstate hcalls
      simp_all [exprTouchesUnsupportedContractSurface,
        exprTouchesUnsupportedContractSurface_eq_false_of_featureClosed]

private theorem stmtListFeatureClosed_cons_inv
    (stmt : Stmt)
    (rest : List Stmt)
    (hcore : stmtListTouchesUnsupportedCoreSurface (stmt :: rest) = false)
    (hstate : stmtListTouchesUnsupportedStateSurface (stmt :: rest) = false)
    (hcalls : stmtListTouchesUnsupportedCallSurface (stmt :: rest) = false)
    (heffects : stmtListTouchesUnsupportedEffectSurface (stmt :: rest) = false) :
    stmtTouchesUnsupportedCoreSurface stmt = false ∧
    stmtListTouchesUnsupportedCoreSurface rest = false ∧
    stmtTouchesUnsupportedStateSurface stmt = false ∧
    stmtListTouchesUnsupportedStateSurface rest = false ∧
    stmtTouchesUnsupportedCallSurface stmt = false ∧
    stmtListTouchesUnsupportedCallSurface rest = false ∧
    stmtTouchesUnsupportedEffectSurface stmt = false ∧
    stmtListTouchesUnsupportedEffectSurface rest = false := by
  constructor
  · simpa [stmtListTouchesUnsupportedCoreSurface] using (Bool.or_eq_false_iff.mp hcore).1
  constructor
  · simpa [stmtListTouchesUnsupportedCoreSurface] using (Bool.or_eq_false_iff.mp hcore).2
  constructor
  · simpa [stmtListTouchesUnsupportedStateSurface] using (Bool.or_eq_false_iff.mp hstate).1
  constructor
  · simpa [stmtListTouchesUnsupportedStateSurface] using (Bool.or_eq_false_iff.mp hstate).2
  constructor
  · simpa [stmtListTouchesUnsupportedCallSurface] using (Bool.or_eq_false_iff.mp hcalls).1
  constructor
  · simpa [stmtListTouchesUnsupportedCallSurface] using (Bool.or_eq_false_iff.mp hcalls).2
  constructor
  · simpa [stmtListTouchesUnsupportedEffectSurface] using (Bool.or_eq_false_iff.mp heffects).1
  · simpa [stmtListTouchesUnsupportedEffectSurface] using (Bool.or_eq_false_iff.mp heffects).2

private theorem stmtListFeatureClosedExceptMappingWrites_cons_inv
    (stmt : Stmt)
    (rest : List Stmt)
    (hcore : stmtListTouchesUnsupportedCoreSurface (stmt :: rest) = false)
    (hstate : stmtListTouchesUnsupportedStateSurfaceExceptMappingWrites (stmt :: rest) = false)
    (hcalls : stmtListTouchesUnsupportedCallSurface (stmt :: rest) = false)
    (heffects : stmtListTouchesUnsupportedEffectSurface (stmt :: rest) = false) :
    stmtTouchesUnsupportedCoreSurface stmt = false ∧
    stmtListTouchesUnsupportedCoreSurface rest = false ∧
    stmtTouchesUnsupportedStateSurfaceExceptMappingWrites stmt = false ∧
    stmtListTouchesUnsupportedStateSurfaceExceptMappingWrites rest = false ∧
    stmtTouchesUnsupportedCallSurface stmt = false ∧
    stmtListTouchesUnsupportedCallSurface rest = false ∧
    stmtTouchesUnsupportedEffectSurface stmt = false ∧
    stmtListTouchesUnsupportedEffectSurface rest = false := by
  constructor
  · simpa [stmtListTouchesUnsupportedCoreSurface] using (Bool.or_eq_false_iff.mp hcore).1
  constructor
  · simpa [stmtListTouchesUnsupportedCoreSurface] using (Bool.or_eq_false_iff.mp hcore).2
  constructor
  · simpa [stmtListTouchesUnsupportedStateSurfaceExceptMappingWrites] using
      (Bool.or_eq_false_iff.mp hstate).1
  constructor
  · simpa [stmtListTouchesUnsupportedStateSurfaceExceptMappingWrites] using
      (Bool.or_eq_false_iff.mp hstate).2
  constructor
  · simpa [stmtListTouchesUnsupportedCallSurface] using (Bool.or_eq_false_iff.mp hcalls).1
  constructor
  · simpa [stmtListTouchesUnsupportedCallSurface] using (Bool.or_eq_false_iff.mp hcalls).2
  constructor
  · simpa [stmtListTouchesUnsupportedEffectSurface] using (Bool.or_eq_false_iff.mp heffects).1
  · simpa [stmtListTouchesUnsupportedEffectSurface] using (Bool.or_eq_false_iff.mp heffects).2

mutual
private theorem stmtTouchesUnsupportedContractSurface_eq_false_of_featureClosed
    (stmt : Stmt)
    (hcore : stmtTouchesUnsupportedCoreSurface stmt = false)
    (hstate : stmtTouchesUnsupportedStateSurface stmt = false)
    (hcalls : stmtTouchesUnsupportedCallSurface stmt = false)
    (heffects : stmtTouchesUnsupportedEffectSurface stmt = false) :
    stmtTouchesUnsupportedContractSurface stmt = false := by
  cases stmt with
  | ite cond thenBranch elseBranch =>
      simp only [stmtTouchesUnsupportedCoreSurface, stmtTouchesUnsupportedStateSurface,
        stmtTouchesUnsupportedCallSurface, stmtTouchesUnsupportedEffectSurface,
        Bool.or_eq_false_iff] at hcore hstate hcalls heffects
      simp only [stmtTouchesUnsupportedContractSurface, Bool.or_eq_false_iff]
      exact ⟨⟨exprTouchesUnsupportedContractSurface_eq_false_of_featureClosed cond
          hcore.1.1 hstate.1.1 hcalls.1.1,
        stmtListTouchesUnsupportedContractSurface_eq_false_of_featureClosed
          thenBranch hcore.1.2 hstate.1.2 hcalls.1.2 heffects.1⟩,
        stmtListTouchesUnsupportedContractSurface_eq_false_of_featureClosed
          elseBranch hcore.2 hstate.2 hcalls.2 heffects.2⟩
  | forEach varName count body =>
      cases count <;> cases body <;>
        simp [stmtTouchesUnsupportedStateSurface, stmtTouchesUnsupportedContractSurface,
          stmtListTouchesUnsupportedContractSurface] at hstate ⊢
  | _ =>
      simp only [stmtTouchesUnsupportedCoreSurface, stmtTouchesUnsupportedStateSurface,
        stmtTouchesUnsupportedCallSurface, stmtTouchesUnsupportedEffectSurface,
        Bool.or_eq_false_iff] at hcore hstate hcalls heffects
      simp_all [stmtTouchesUnsupportedContractSurface,
        exprTouchesUnsupportedContractSurface_eq_false_of_featureClosed]
termination_by sizeOf stmt

theorem stmtListTouchesUnsupportedContractSurface_eq_false_of_featureClosed
    (stmts : List Stmt)
    (hcore : stmtListTouchesUnsupportedCoreSurface stmts = false)
    (hstate : stmtListTouchesUnsupportedStateSurface stmts = false)
    (hcalls : stmtListTouchesUnsupportedCallSurface stmts = false)
    (heffects : stmtListTouchesUnsupportedEffectSurface stmts = false) :
    stmtListTouchesUnsupportedContractSurface stmts = false := by
  match stmts with
  | [] => simp [stmtListTouchesUnsupportedContractSurface]
  | stmt :: rest =>
      rcases stmtListFeatureClosed_cons_inv stmt rest hcore hstate hcalls heffects with
        ⟨hcoreStmt, hcoreRest, hstateStmt, hstateRest,
          hcallsStmt, hcallsRest, heffectsStmt, heffectsRest⟩
      have hstmt :
          stmtTouchesUnsupportedContractSurface stmt = false :=
        stmtTouchesUnsupportedContractSurface_eq_false_of_featureClosed stmt
          hcoreStmt hstateStmt hcallsStmt heffectsStmt
      have hrest :
          stmtListTouchesUnsupportedContractSurface rest = false :=
        stmtListTouchesUnsupportedContractSurface_eq_false_of_featureClosed rest
          hcoreRest hstateRest hcallsRest heffectsRest
      simp [stmtListTouchesUnsupportedContractSurface, hstmt, hrest]
termination_by sizeOf stmts
end

mutual
/-- Events-aware counterpart of
`stmtTouchesUnsupportedContractSurface_eq_false_of_featureClosed`: the
core/state/call/effect decomposition still implies the contract-surface gate
once the effect component is taken in its events-aware form. -/
theorem stmtTouchesUnsupportedContractSurfaceWithEvents_eq_false_of_featureClosedWithEvents
    {events : List EventDef}
    (stmt : Stmt)
    (hcore : stmtTouchesUnsupportedCoreSurface stmt = false)
    (hstate : stmtTouchesUnsupportedStateSurface stmt = false)
    (hcalls : stmtTouchesUnsupportedCallSurface stmt = false)
    (heffects : stmtTouchesUnsupportedEffectSurfaceWithEvents events stmt = false) :
    stmtTouchesUnsupportedContractSurfaceWithEvents events stmt = false := by
  cases stmt with
  | emit eventName args =>
      simpa [stmtTouchesUnsupportedContractSurfaceWithEvents,
        stmtTouchesUnsupportedEffectSurfaceWithEvents] using heffects
  | ite cond thenBranch elseBranch =>
      simp only [stmtTouchesUnsupportedCoreSurface, Bool.or_eq_false_iff] at hcore
      simp only [stmtTouchesUnsupportedStateSurface, Bool.or_eq_false_iff] at hstate
      simp only [stmtTouchesUnsupportedCallSurface, Bool.or_eq_false_iff] at hcalls
      simp only [stmtTouchesUnsupportedEffectSurfaceWithEvents,
        Bool.or_eq_false_iff] at heffects
      show (exprTouchesUnsupportedContractSurface cond ||
            stmtListTouchesUnsupportedContractSurfaceWithEvents events thenBranch ||
            stmtListTouchesUnsupportedContractSurfaceWithEvents events elseBranch) = false
      rw [Bool.or_eq_false_iff, Bool.or_eq_false_iff]
      exact ⟨⟨exprTouchesUnsupportedContractSurface_eq_false_of_featureClosed cond
          hcore.1.1 hstate.1.1 hcalls.1.1,
        stmtListTouchesUnsupportedContractSurfaceWithEvents_eq_false_of_featureClosedWithEvents
          thenBranch hcore.1.2 hstate.1.2 hcalls.1.2 heffects.1⟩,
        stmtListTouchesUnsupportedContractSurfaceWithEvents_eq_false_of_featureClosedWithEvents
          elseBranch hcore.2 hstate.2 hcalls.2 heffects.2⟩
  | _ =>
      all_goals
        (simp only [stmtTouchesUnsupportedContractSurfaceWithEvents]
         exact stmtTouchesUnsupportedContractSurface_eq_false_of_featureClosed _
           hcore hstate hcalls
           (by simpa [stmtTouchesUnsupportedEffectSurfaceWithEvents] using heffects))
termination_by sizeOf stmt

theorem stmtListTouchesUnsupportedContractSurfaceWithEvents_eq_false_of_featureClosedWithEvents
    {events : List EventDef}
    (stmts : List Stmt)
    (hcore : stmtListTouchesUnsupportedCoreSurface stmts = false)
    (hstate : stmtListTouchesUnsupportedStateSurface stmts = false)
    (hcalls : stmtListTouchesUnsupportedCallSurface stmts = false)
    (heffects : stmtListTouchesUnsupportedEffectSurfaceWithEvents events stmts = false) :
    stmtListTouchesUnsupportedContractSurfaceWithEvents events stmts = false := by
  match stmts with
  | [] => simp [stmtListTouchesUnsupportedContractSurfaceWithEvents]
  | stmt :: rest =>
      simp only [stmtListTouchesUnsupportedCoreSurface, Bool.or_eq_false_iff] at hcore
      simp only [stmtListTouchesUnsupportedStateSurface, Bool.or_eq_false_iff] at hstate
      simp only [stmtListTouchesUnsupportedCallSurface, Bool.or_eq_false_iff] at hcalls
      simp only [stmtListTouchesUnsupportedEffectSurfaceWithEvents,
        Bool.or_eq_false_iff] at heffects
      have hstmt :
          stmtTouchesUnsupportedContractSurfaceWithEvents events stmt = false :=
        stmtTouchesUnsupportedContractSurfaceWithEvents_eq_false_of_featureClosedWithEvents
          stmt hcore.1 hstate.1 hcalls.1 heffects.1
      have hrest :
          stmtListTouchesUnsupportedContractSurfaceWithEvents events rest = false :=
        stmtListTouchesUnsupportedContractSurfaceWithEvents_eq_false_of_featureClosedWithEvents
          rest hcore.2 hstate.2 hcalls.2 heffects.2
      simp [stmtListTouchesUnsupportedContractSurfaceWithEvents, hstmt, hrest]
termination_by sizeOf stmts
end

mutual
/-- The events-aware effect surface is a genuine weakening: every body the plain
effect surface accepts is still accepted here. -/
theorem stmtTouchesUnsupportedEffectSurfaceWithEvents_eq_false_of_effectSurfaceClosed
    {events : List EventDef}
    (stmt : Stmt)
    (heffects : stmtTouchesUnsupportedEffectSurface stmt = false) :
    stmtTouchesUnsupportedEffectSurfaceWithEvents events stmt = false := by
  cases stmt with
  | emit _ _ => simp [stmtTouchesUnsupportedEffectSurface] at heffects
  | ite _ thenBranch elseBranch =>
      simp only [stmtTouchesUnsupportedEffectSurface, Bool.or_eq_false_iff] at heffects
      simp only [stmtTouchesUnsupportedEffectSurfaceWithEvents, Bool.or_eq_false_iff]
      exact ⟨stmtListTouchesUnsupportedEffectSurfaceWithEvents_eq_false_of_effectSurfaceClosed
          thenBranch heffects.1,
        stmtListTouchesUnsupportedEffectSurfaceWithEvents_eq_false_of_effectSurfaceClosed
          elseBranch heffects.2⟩
  | _ =>
      all_goals
        (simp only [stmtTouchesUnsupportedEffectSurfaceWithEvents]; exact heffects)
termination_by sizeOf stmt

theorem stmtListTouchesUnsupportedEffectSurfaceWithEvents_eq_false_of_effectSurfaceClosed
    {events : List EventDef}
    (stmts : List Stmt)
    (heffects : stmtListTouchesUnsupportedEffectSurface stmts = false) :
    stmtListTouchesUnsupportedEffectSurfaceWithEvents events stmts = false := by
  match stmts with
  | [] => simp [stmtListTouchesUnsupportedEffectSurfaceWithEvents]
  | stmt :: rest =>
      simp only [stmtListTouchesUnsupportedEffectSurface, Bool.or_eq_false_iff] at heffects
      simp [stmtListTouchesUnsupportedEffectSurfaceWithEvents,
        stmtTouchesUnsupportedEffectSurfaceWithEvents_eq_false_of_effectSurfaceClosed
          (events := events) stmt heffects.1,
        stmtListTouchesUnsupportedEffectSurfaceWithEvents_eq_false_of_effectSurfaceClosed
          (events := events) rest heffects.2]
termination_by sizeOf stmts
end

private theorem stmtTouchesUnsupportedContractSurfaceExceptMappingWrites_eq_false_of_featureClosed
    (stmt : Stmt)
    (hcore : stmtTouchesUnsupportedCoreSurface stmt = false)
    (hstate : stmtTouchesUnsupportedStateSurfaceExceptMappingWrites stmt = false)
    (hcalls : stmtTouchesUnsupportedCallSurface stmt = false)
    (heffects : stmtTouchesUnsupportedEffectSurface stmt = false) :
    stmtTouchesUnsupportedContractSurfaceExceptMappingWrites stmt = false := by
  cases stmt with
  | setMapping _ key value | setMappingWord _ key _ value
  | setMappingPackedWord _ key _ _ value | setMappingUint _ key value
  | setStructMember _ key _ value =>
      simp [stmtTouchesUnsupportedContractSurfaceExceptMappingWrites]
  | setMappingChain _ keys value =>
      simp [stmtTouchesUnsupportedContractSurfaceExceptMappingWrites]
  | setMapping2 _ key1 key2 value | setMapping2Word _ key1 key2 _ value
  | setStructMember2 _ key1 key2 _ value =>
      simp [stmtTouchesUnsupportedContractSurfaceExceptMappingWrites]
  | ite cond thenBranch elseBranch =>
      simp only [stmtTouchesUnsupportedContractSurfaceExceptMappingWrites]
      exact stmtTouchesUnsupportedContractSurface_eq_false_of_featureClosed _
        hcore
        (by simpa [stmtTouchesUnsupportedStateSurfaceExceptMappingWrites] using hstate)
        hcalls heffects
  | forEachSetBit _ _ _ => cases hcore
  | _ =>
      simp only [stmtTouchesUnsupportedContractSurfaceExceptMappingWrites]
      exact stmtTouchesUnsupportedContractSurface_eq_false_of_featureClosed _
        hcore
        (by simpa [stmtTouchesUnsupportedStateSurfaceExceptMappingWrites] using hstate)
        hcalls heffects

theorem stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites_eq_false_of_featureClosed
    (stmts : List Stmt)
    (hcore : stmtListTouchesUnsupportedCoreSurface stmts = false)
    (hstate : stmtListTouchesUnsupportedStateSurfaceExceptMappingWrites stmts = false)
    (hcalls : stmtListTouchesUnsupportedCallSurface stmts = false)
    (heffects : stmtListTouchesUnsupportedEffectSurface stmts = false) :
    stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites stmts = false := by
  induction stmts with
  | nil => simp [stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites]
  | cons stmt rest ih =>
      rcases stmtListFeatureClosedExceptMappingWrites_cons_inv stmt rest hcore hstate hcalls heffects with
        ⟨hcoreStmt, hcoreRest, hstateStmt, hstateRest,
          hcallsStmt, hcallsRest, heffectsStmt, heffectsRest⟩
      have hstmt :=
        stmtTouchesUnsupportedContractSurfaceExceptMappingWrites_eq_false_of_featureClosed stmt
          hcoreStmt hstateStmt hcallsStmt heffectsStmt
      have hrest := ih hcoreRest hstateRest hcallsRest heffectsRest
      simp [stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites, hstmt, hrest]


theorem exprTouchesUnsupportedHelperSurface_eq_false_of_contractSurfaceClosed
    {expr : Expr}
    (hsurface : exprTouchesUnsupportedContractSurface expr = false) :
    exprTouchesUnsupportedHelperSurface expr = false := by
  cases expr with
  | externalCall name args =>
      rcases args with _ | ⟨base, _ | ⟨exponent, _ | ⟨_, _⟩⟩⟩
      all_goals try simp [exprTouchesUnsupportedContractSurface] at hsurface
      by_cases hname : name = builtinExpName
      · subst hname
        simp only [exprTouchesUnsupportedContractSurface, beq_self_eq_true, if_true,
          Bool.or_eq_false_iff] at hsurface
        simp_all [exprTouchesUnsupportedHelperSurface,
          exprTouchesUnsupportedHelperSurface_eq_false_of_contractSurfaceClosed]
      · simp [exprTouchesUnsupportedContractSurface, hname] at hsurface
  | _ =>
      simp only [exprTouchesUnsupportedContractSurface, Bool.or_eq_false_iff] at hsurface
      simp_all [exprTouchesUnsupportedHelperSurface,
        exprTouchesUnsupportedHelperSurface_eq_false_of_contractSurfaceClosed]

private theorem exprListTouchesUnsupportedHelperSurface_eq_false_of_contractSurfaceClosed
    {exprs : List Expr}
    (hsurface : exprs.any exprTouchesUnsupportedContractSurface = false) :
    exprListTouchesUnsupportedHelperSurface exprs = false := by
  induction exprs with
  | nil =>
      simp [exprListTouchesUnsupportedHelperSurface]
  | cons expr rest ih =>
      simp only [List.any_cons, Bool.or_eq_false_iff] at hsurface
      simp [exprListTouchesUnsupportedHelperSurface,
        exprTouchesUnsupportedHelperSurface_eq_false_of_contractSurfaceClosed hsurface.1,
        ih hsurface.2]

/-- A contract-surface-closed `forEach` head has a literal bound. -/
private theorem forEach_count_eq_literal_of_contractSurfaceClosed
    {varName : String} {count : Expr} {body : List Stmt}
    (hsurface : stmtTouchesUnsupportedContractSurface (.forEach varName count body) = false) :
    ∃ n, count = .literal n := by
  cases count with
  | literal n => exact ⟨n, rfl⟩
  | _ => simp [stmtTouchesUnsupportedContractSurface] at hsurface

mutual
theorem stmtTouchesUnsupportedHelperSurface_eq_false_of_contractSurfaceClosed
    {stmt : Stmt}
    (hsurface : stmtTouchesUnsupportedContractSurface stmt = false) :
    stmtTouchesUnsupportedHelperSurface stmt = false := by
  cases stmt with
  | ite cond thenBranch elseBranch =>
      simp only [stmtTouchesUnsupportedContractSurface, Bool.or_eq_false_iff] at hsurface
      show (exprTouchesUnsupportedHelperSurface cond ||
            stmtListTouchesUnsupportedHelperSurface thenBranch ||
            stmtListTouchesUnsupportedHelperSurface elseBranch) = false
      rw [Bool.or_eq_false_iff, Bool.or_eq_false_iff]
      exact ⟨⟨exprTouchesUnsupportedHelperSurface_eq_false_of_contractSurfaceClosed hsurface.1.1,
        stmtListTouchesUnsupportedHelperSurface_eq_false_of_contractSurfaceClosed hsurface.1.2⟩,
        stmtListTouchesUnsupportedHelperSurface_eq_false_of_contractSurfaceClosed hsurface.2⟩
  | forEach varName count body =>
      have hbody := stmtListTouchesUnsupportedContractSurface_of_forEach_surfaceClosed hsurface
      obtain ⟨n, rfl⟩ := forEach_count_eq_literal_of_contractSurfaceClosed hsurface
      simp only [stmtTouchesUnsupportedHelperSurface, exprTouchesUnsupportedHelperSurface,
        Bool.false_or]
      exact stmtListTouchesUnsupportedHelperSurface_eq_false_of_contractSurfaceClosed hbody
  | _ =>
      simp only [stmtTouchesUnsupportedContractSurface, Bool.or_eq_false_iff] at hsurface
      simp_all [stmtTouchesUnsupportedHelperSurface,
        exprTouchesUnsupportedHelperSurface_eq_false_of_contractSurfaceClosed]
termination_by sizeOf stmt

theorem stmtListTouchesUnsupportedHelperSurface_eq_false_of_contractSurfaceClosed
    {stmts : List Stmt}
    (hsurface : stmtListTouchesUnsupportedContractSurface stmts = false) :
    stmtListTouchesUnsupportedHelperSurface stmts = false := by
  match stmts with
  | [] => simp [stmtListTouchesUnsupportedHelperSurface]
  | stmt :: rest =>
      simp only [stmtListTouchesUnsupportedContractSurface, Bool.or_eq_false_iff] at hsurface
      simp [stmtListTouchesUnsupportedHelperSurface,
        stmtTouchesUnsupportedHelperSurface_eq_false_of_contractSurfaceClosed hsurface.1,
        stmtListTouchesUnsupportedHelperSurface_eq_false_of_contractSurfaceClosed hsurface.2]
termination_by sizeOf stmts
end

mutual
theorem stmtTouchesUnsupportedHelperSurface_eq_false_of_contractSurfaceWithEventsClosed
    {events : List EventDef}
    {stmt : Stmt}
    (hsurface : stmtTouchesUnsupportedContractSurfaceWithEvents events stmt = false) :
    stmtTouchesUnsupportedHelperSurface stmt = false := by
  cases stmt with
  | emit eventName args =>
      simp only [stmtTouchesUnsupportedContractSurfaceWithEvents,
        Bool.or_eq_false_iff] at hsurface
      simp [stmtTouchesUnsupportedHelperSurface,
        exprListTouchesUnsupportedHelperSurface_eq_false_of_contractSurfaceClosed hsurface.1]
  | ite cond thenBranch elseBranch =>
      simp only [stmtTouchesUnsupportedContractSurfaceWithEvents,
        Bool.or_eq_false_iff] at hsurface
      show (exprTouchesUnsupportedHelperSurface cond ||
            stmtListTouchesUnsupportedHelperSurface thenBranch ||
            stmtListTouchesUnsupportedHelperSurface elseBranch) = false
      rw [Bool.or_eq_false_iff, Bool.or_eq_false_iff]
      exact ⟨⟨exprTouchesUnsupportedHelperSurface_eq_false_of_contractSurfaceClosed hsurface.1.1,
        stmtListTouchesUnsupportedHelperSurface_eq_false_of_contractSurfaceWithEventsClosed
          hsurface.1.2⟩,
        stmtListTouchesUnsupportedHelperSurface_eq_false_of_contractSurfaceWithEventsClosed
          hsurface.2⟩
  | _ =>
      exact stmtTouchesUnsupportedHelperSurface_eq_false_of_contractSurfaceClosed
        (by simpa [stmtTouchesUnsupportedContractSurfaceWithEvents] using hsurface)
termination_by sizeOf stmt

theorem stmtListTouchesUnsupportedHelperSurface_eq_false_of_contractSurfaceWithEventsClosed
    {events : List EventDef}
    {stmts : List Stmt}
    (hsurface : stmtListTouchesUnsupportedContractSurfaceWithEvents events stmts = false) :
    stmtListTouchesUnsupportedHelperSurface stmts = false := by
  match stmts with
  | [] => simp [stmtListTouchesUnsupportedHelperSurface]
  | stmt :: rest =>
      simp only [stmtListTouchesUnsupportedContractSurfaceWithEvents,
        Bool.or_eq_false_iff] at hsurface
      simp [stmtListTouchesUnsupportedHelperSurface,
        stmtTouchesUnsupportedHelperSurface_eq_false_of_contractSurfaceWithEventsClosed
          hsurface.1,
        stmtListTouchesUnsupportedHelperSurface_eq_false_of_contractSurfaceWithEventsClosed
          hsurface.2]
termination_by sizeOf stmts
end

theorem stmtTouchesUnsupportedHelperSurface_eq_false_of_contractSurfaceClosed_exceptMappingWrites
    {fields : List Field}
    {scope : List String}
    {stmt : Stmt}
    (hsupported : SupportedStmtList fields scope [stmt]) :
    stmtTouchesUnsupportedHelperSurface stmt = false := by
  have hlist : stmtListTouchesUnsupportedHelperSurface [stmt] = false := by
    simpa using hsupported.helperSurfaceClosed
  simp [stmtListTouchesUnsupportedHelperSurface] at hlist
  exact hlist

theorem stmtListTouchesUnsupportedHelperSurface_eq_false_of_contractSurfaceClosed_exceptMappingWrites
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hsupported : SupportedStmtList fields scope stmts) :
    stmtListTouchesUnsupportedHelperSurface stmts = false := by
  simpa using hsupported.helperSurfaceClosed


theorem SupportedBodyCallInterface.surfaceClosed
    {spec : CompilationModel} {fn : FunctionSpec}
    (hBody : SupportedBodyInterface spec fn) :
    stmtListTouchesUnsupportedCallSurface fn.body = false := by
  rw [stmtListTouchesUnsupportedCallSurface_eq_featureOr]
  simp [hBody.helperSurfaceClosed, hBody.calls.foreign, hBody.calls.lowLevel]

theorem SupportedBodyCallInterface.surfaceClosed_withScalarEvents
    {spec : CompilationModel} {fn : FunctionSpec}
    (hBody : SupportedBodyInterfaceWithScalarEvents spec fn) :
    stmtListTouchesUnsupportedCallSurface fn.body = false := by
  rw [stmtListTouchesUnsupportedCallSurface_eq_featureOr]
  simp [hBody.helperSurfaceClosed, hBody.calls.foreign, hBody.calls.lowLevel]

/-- Build the scalar-event body interface from the same core/state/call/effect
decomposition every other statement head uses, with the effect component taken
in its events-aware form. Before this, `contractSurfaceWithEvents` had to be
supplied directly because `SupportedBodyEffectInterface` rejects every `emit`. -/
def SupportedBodyInterfaceWithScalarEvents.ofEffectInterfaceWithEvents
    {spec : CompilationModel} {fn : FunctionSpec}
    (stmtList : SupportedStmtList spec.fields (fn.params.map (·.name)) fn.body)
    (core : SupportedBodyCoreInterface fn)
    (state : SupportedBodyStateInterface fn)
    (calls : SupportedBodyCallInterface spec fn)
    (effects : SupportedBodyEffectInterfaceWithEvents spec fn)
    (topLevelEventHeads :
      ∀ s ∈ fn.body,
        stmtTouchesEventSurface s = true ∨
          stmtTouchesUnsupportedContractSurface s = false)
    (eventScratchFreshInitial :
      "__evt_ptr" ∉ fn.params.map (·.name) ∧
        "__evt_topic0" ∉ fn.params.map (·.name))
    (eventScratchFreshStmts :
      ∀ s ∈ fn.body,
        "__evt_ptr" ∉ collectStmtBindNames s ∧ "__evt_topic0" ∉ collectStmtBindNames s)
    (emitArgsInScope :
      ∀ s ∈ fn.body, ∀ (eventName : String) (args : List Expr),
        s = Stmt.emit eventName args →
        ∀ arg ∈ args,
          FunctionBody.exprBoundNamesInScope arg (fn.params.map (·.name)))
    (noLocalObligations : fn.localObligations = []) :
    SupportedBodyInterfaceWithScalarEvents spec fn where
  stmtList := stmtList
  core := core
  state := state
  calls := calls
  contractSurfaceWithEvents :=
    stmtListTouchesUnsupportedContractSurfaceWithEvents_eq_false_of_featureClosedWithEvents
      fn.body core.surfaceClosed state.surfaceClosed
      (by
        rw [stmtListTouchesUnsupportedCallSurface_eq_featureOr]
        simp [stmtList.helperSurfaceClosed, calls.foreign, calls.lowLevel])
      effects.surfaceClosed
  topLevelEventHeads := topLevelEventHeads
  eventScratchFreshInitial := eventScratchFreshInitial
  eventScratchFreshStmts := eventScratchFreshStmts
  emitArgsInScope := emitArgsInScope
  noLocalObligations := noLocalObligations

/-- An emission-free body reaches the scalar-event interface through its plain
effect interface, so the events-aware route strictly extends the existing one. -/
def SupportedBodyEffectInterfaceWithEvents.ofEffectInterface
    {spec : CompilationModel} {fn : FunctionSpec}
    (effects : SupportedBodyEffectInterface fn) :
    SupportedBodyEffectInterfaceWithEvents spec fn where
  surfaceClosed :=
    stmtListTouchesUnsupportedEffectSurfaceWithEvents_eq_false_of_effectSurfaceClosed
      fn.body effects.surfaceClosed

theorem SupportedBodyCallInterface.surfaceClosed_exceptMappingWrites
    {spec : CompilationModel} {fn : FunctionSpec}
    (hBody : SupportedBodyInterfaceExceptMappingWrites spec fn) :
    stmtListTouchesUnsupportedCallSurface fn.body = false := by
  rw [stmtListTouchesUnsupportedCallSurface_eq_featureOr]
  simp [hBody.helperSurfaceClosed, hBody.calls.foreign, hBody.calls.lowLevel]

-- Helper: ExprCompileCore expressions never use arrayElement
private theorem exprCompileCore_usesArrayElement_false
    {expr : Expr}
    (hcore : FunctionBody.ExprCompileCore expr) :
    exprUsesArrayElement expr = false := by
  induction hcore with
  | literal | param | constructorArg | localVar | caller | contractAddress | txOrigin | msgValue
    | blockTimestamp | blockNumber | chainid
    | blobbasefee | calldatasize | returndataSize =>
      simp only [exprUsesArrayElement, Bool.false_or]
  | add _ _ ihL ihR | sub _ _ ihL ihR | mul _ _ ihL ihR
    | div _ _ ihL ihR | mod _ _ ihL ihR | eq _ _ ihL ihR
    | lt _ _ ihL ihR | gt _ _ ihL ihR | ge _ _ ihL ihR
    | le _ _ ihL ihR | logicalAnd _ _ ihL ihR | logicalOr _ _ ihL ihR
    | bitAnd _ _ ihL ihR | bitOr _ _ ihL ihR | bitXor _ _ ihL ihR
    | shl _ _ ihL ihR | shr _ _ ihL ihR
    | min _ _ ihL ihR | max _ _ ihL ihR | ceilDiv _ _ ihL ihR
    | wMulDown _ _ ihL ihR | wDivUp _ _ ihL ihR
    | slt _ _ ihL ihR | sgt _ _ ihL ihR | sdiv _ _ ihL ihR
    | smod _ _ ihL ihR | sar _ _ ihL ihR | byte _ _ ihL ihR | signextend _ _ ihL ihR
    | keccak256 _ _ ihL ihR =>
      simp only [exprUsesArrayElement, ihL, ihR, Bool.false_or]
  | mulDivDown _ _ _ ihA ihB ihC | mulDivUp _ _ _ ihA ihB ihC =>
      simp only [exprUsesArrayElement, ihA, ihB, ihC, Bool.false_or]
  | logicalNot _ ih | bitNot _ ih | tload _ ih | calldataload _ ih | mload _ ih | extcodesize _ ih
  | returndataOptionalBoolAt _ ih =>
      simp only [exprUsesArrayElement, ih, Bool.false_or]
  | ite _ _ _ ihC ihT ihE =>
      simp only [exprUsesArrayElement, ihC, ihT, ihE, Bool.false_or]
  | builtinExp _ _ ihB ihE =>
      simp only [exprUsesArrayElement, exprListUsesArrayElement, ihB, ihE, Bool.false_or,
        Bool.or_false]

-- Helper: ExprCompileCore expressions never use storageArrayElement
private theorem exprCompileCore_usesStorageArrayElement_false
    {expr : Expr}
    (hcore : FunctionBody.ExprCompileCore expr) :
    exprUsesStorageArrayElement expr = false := by
  induction hcore with
  | literal | param | constructorArg | localVar | caller | contractAddress | txOrigin | msgValue
    | blockTimestamp | blockNumber | chainid
    | blobbasefee | calldatasize | returndataSize =>
      simp only [exprUsesStorageArrayElement, Bool.false_or]
  | add _ _ ihL ihR | sub _ _ ihL ihR | mul _ _ ihL ihR
    | div _ _ ihL ihR | mod _ _ ihL ihR | eq _ _ ihL ihR
    | lt _ _ ihL ihR | gt _ _ ihL ihR | ge _ _ ihL ihR
    | le _ _ ihL ihR | logicalAnd _ _ ihL ihR | logicalOr _ _ ihL ihR
    | bitAnd _ _ ihL ihR | bitOr _ _ ihL ihR | bitXor _ _ ihL ihR
    | shl _ _ ihL ihR | shr _ _ ihL ihR
    | min _ _ ihL ihR | max _ _ ihL ihR | ceilDiv _ _ ihL ihR
    | wMulDown _ _ ihL ihR | wDivUp _ _ ihL ihR
    | slt _ _ ihL ihR | sgt _ _ ihL ihR | sdiv _ _ ihL ihR
    | smod _ _ ihL ihR | sar _ _ ihL ihR | byte _ _ ihL ihR | signextend _ _ ihL ihR
    | keccak256 _ _ ihL ihR =>
      simp only [exprUsesStorageArrayElement, ihL, ihR, Bool.false_or]
  | mulDivDown _ _ _ ihA ihB ihC | mulDivUp _ _ _ ihA ihB ihC =>
      simp only [exprUsesStorageArrayElement, ihA, ihB, ihC, Bool.false_or]
  | logicalNot _ ih | bitNot _ ih | tload _ ih | calldataload _ ih | mload _ ih | extcodesize _ ih
  | returndataOptionalBoolAt _ ih =>
      simp only [exprUsesStorageArrayElement, ih, Bool.false_or]
  | ite _ _ _ ihC ihT ihE =>
      simp only [exprUsesStorageArrayElement, ihC, ihT, ihE, Bool.false_or]
  | builtinExp _ _ ihB ihE =>
      simp only [exprUsesStorageArrayElement, exprListUsesStorageArrayElement, ihB, ihE,
        Bool.false_or, Bool.or_false]

-- Helper: ExprCompileCore expressions never use dynamicBytesEq
private theorem exprCompileCore_usesDynamicBytesEq_false
    {expr : Expr}
    (hcore : FunctionBody.ExprCompileCore expr) :
    exprUsesDynamicBytesEq expr = false := by
  induction hcore with
  | literal | param | constructorArg | localVar | caller | contractAddress | txOrigin | msgValue
    | blockTimestamp | blockNumber | chainid
    | blobbasefee | calldatasize | returndataSize =>
      simp only [exprUsesDynamicBytesEq, Bool.false_or]
  | add _ _ ihL ihR | sub _ _ ihL ihR | mul _ _ ihL ihR
    | div _ _ ihL ihR | mod _ _ ihL ihR | eq _ _ ihL ihR
    | lt _ _ ihL ihR | gt _ _ ihL ihR | ge _ _ ihL ihR
    | le _ _ ihL ihR | logicalAnd _ _ ihL ihR | logicalOr _ _ ihL ihR
    | bitAnd _ _ ihL ihR | bitOr _ _ ihL ihR | bitXor _ _ ihL ihR
    | shl _ _ ihL ihR | shr _ _ ihL ihR
    | min _ _ ihL ihR | max _ _ ihL ihR | ceilDiv _ _ ihL ihR
    | wMulDown _ _ ihL ihR | wDivUp _ _ ihL ihR
    | slt _ _ ihL ihR | sgt _ _ ihL ihR | sdiv _ _ ihL ihR
    | smod _ _ ihL ihR | sar _ _ ihL ihR | byte _ _ ihL ihR | signextend _ _ ihL ihR
    | keccak256 _ _ ihL ihR =>
      simp only [exprUsesDynamicBytesEq, ihL, ihR, Bool.false_or]
  | mulDivDown _ _ _ ihA ihB ihC | mulDivUp _ _ _ ihA ihB ihC =>
      simp only [exprUsesDynamicBytesEq, ihA, ihB, ihC, Bool.false_or]
  | logicalNot _ ih | bitNot _ ih | tload _ ih | calldataload _ ih | mload _ ih | extcodesize _ ih
  | returndataOptionalBoolAt _ ih =>
      simp only [exprUsesDynamicBytesEq, ih, Bool.false_or]
  | ite _ _ _ ihC ihT ihE =>
      simp only [exprUsesDynamicBytesEq, ihC, ihT, ihE, Bool.false_or]
  | builtinExp _ _ ihB ihE =>
      simp only [exprUsesDynamicBytesEq, exprListUsesDynamicBytesEq, ihB, ihE, Bool.false_or,
        Bool.or_false]

-- Helper: ExprCompileCore lists never use arrayElement
private theorem exprListCompileCore_usesArrayElement_false
    {exprs : List Expr}
    (hcore : ∀ expr ∈ exprs, FunctionBody.ExprCompileCore expr) :
    exprListUsesArrayElement exprs = false := by
  induction exprs with
  | nil => simp only [exprListUsesArrayElement, Bool.false_or]
  | cons e rest ih =>
      simp only [exprListUsesArrayElement,
        exprCompileCore_usesArrayElement_false (hcore e (List.mem_cons_self ..)),
        ih (fun e he => hcore e (List.mem_cons_of_mem _ he)), Bool.false_or]

-- Helper: ExprCompileCore lists never use storageArrayElement
private theorem exprListCompileCore_usesStorageArrayElement_false
    {exprs : List Expr}
    (hcore : ∀ expr ∈ exprs, FunctionBody.ExprCompileCore expr) :
    exprListUsesStorageArrayElement exprs = false := by
  induction exprs with
  | nil => simp only [exprListUsesStorageArrayElement, Bool.false_or]
  | cons e rest ih =>
      simp only [exprListUsesStorageArrayElement,
        exprCompileCore_usesStorageArrayElement_false (hcore e (List.mem_cons_self ..)),
        ih (fun e he => hcore e (List.mem_cons_of_mem _ he)), Bool.false_or]

-- Helper: ExprCompileCore lists never use dynamicBytesEq
private theorem exprListCompileCore_usesDynamicBytesEq_false
    {exprs : List Expr}
    (hcore : ∀ expr ∈ exprs, FunctionBody.ExprCompileCore expr) :
    exprListUsesDynamicBytesEq exprs = false := by
  induction exprs with
  | nil => simp only [exprListUsesDynamicBytesEq, Bool.false_or]
  | cons e rest ih =>
      simp only [exprListUsesDynamicBytesEq,
        exprCompileCore_usesDynamicBytesEq_false (hcore e (List.mem_cons_self ..)),
        ih (fun e he => hcore e (List.mem_cons_of_mem _ he)), Bool.false_or]

-- Helper: StmtListCompileCore never uses arrayElement
private theorem stmtListCompileCore_usesArrayElement_false
    {scope : List String} {stmts : List Stmt}
    (hcore : FunctionBody.StmtListCompileCore scope stmts) :
    stmtListUsesArrayElement stmts = false := by
  induction hcore with
  | nil => simp only [stmtListUsesArrayElement, Bool.false_or]
  | letVar hvalue _ _ ih =>
      simp only [stmtListUsesArrayElement, stmtUsesArrayElement,
        exprCompileCore_usesArrayElement_false hvalue, Bool.false_or]; assumption
  | assignVar hvalue _ _ ih =>
      simp only [stmtListUsesArrayElement, stmtUsesArrayElement,
        exprCompileCore_usesArrayElement_false hvalue, Bool.false_or]; assumption
  | require_ hcond _ _ ih =>
      simp only [stmtListUsesArrayElement, stmtUsesArrayElement,
        exprCompileCore_usesArrayElement_false hcond, Bool.false_or]; assumption
  | return_ hvalue _ _ ih =>
      simp only [stmtListUsesArrayElement, stmtUsesArrayElement,
        exprCompileCore_usesArrayElement_false hvalue, Bool.false_or]; assumption
  | stop _ ih =>
      simp only [stmtListUsesArrayElement, stmtUsesArrayElement, Bool.false_or]; assumption
  | mstore hoffset _ hvalue _ _ ih =>
      simp only [stmtListUsesArrayElement, stmtUsesArrayElement,
        exprCompileCore_usesArrayElement_false hoffset,
        exprCompileCore_usesArrayElement_false hvalue, Bool.false_or]; assumption
  | tstore hoffset _ hvalue _ _ ih =>
      simp only [stmtListUsesArrayElement, stmtUsesArrayElement,
        exprCompileCore_usesArrayElement_false hoffset,
        exprCompileCore_usesArrayElement_false hvalue, Bool.false_or]; assumption

-- Helper: StmtListTerminalCore never uses arrayElement
private theorem stmtListTerminalCore_usesArrayElement_false
    {scope : List String} {stmts : List Stmt}
    (hcore : FunctionBody.StmtListTerminalCore scope stmts) :
    stmtListUsesArrayElement stmts = false := by
  induction hcore with
  | letVar hvalue _ _ ih =>
      simp only [stmtListUsesArrayElement, stmtUsesArrayElement,
        exprCompileCore_usesArrayElement_false hvalue, Bool.false_or]; assumption
  | assignVar hvalue _ _ ih =>
      simp only [stmtListUsesArrayElement, stmtUsesArrayElement,
        exprCompileCore_usesArrayElement_false hvalue, Bool.false_or]; assumption
  | require_ hcond _ _ ih =>
      simp only [stmtListUsesArrayElement, stmtUsesArrayElement,
        exprCompileCore_usesArrayElement_false hcond, Bool.false_or]; assumption
  | return_ hvalue _ ih =>
      simp only [stmtListUsesArrayElement, stmtUsesArrayElement,
        exprCompileCore_usesArrayElement_false hvalue,
        stmtListCompileCore_usesArrayElement_false ih, Bool.false_or]
  | stop ih =>
      simp only [stmtListUsesArrayElement, stmtUsesArrayElement,
        stmtListCompileCore_usesArrayElement_false ih, Bool.false_or]
  | ite hcond _ _ _ hCompile ih_then ih_else =>
      simp only [stmtListUsesArrayElement, stmtUsesArrayElement,
        exprCompileCore_usesArrayElement_false hcond, ih_then, ih_else,
        stmtListCompileCore_usesArrayElement_false hCompile, Bool.false_or]
  | mstore hoffset _ hvalue _ _ ih =>
      simp only [stmtListUsesArrayElement, stmtUsesArrayElement,
        exprCompileCore_usesArrayElement_false hoffset,
        exprCompileCore_usesArrayElement_false hvalue, Bool.false_or]; assumption
  | tstore hoffset _ hvalue _ _ ih =>
      simp only [stmtListUsesArrayElement, stmtUsesArrayElement,
        exprCompileCore_usesArrayElement_false hoffset,
        exprCompileCore_usesArrayElement_false hvalue, Bool.false_or]; assumption

-- Helper: StmtListCompileCore never uses storageArrayElement
private theorem stmtListCompileCore_usesStorageArrayElement_false
    {scope : List String} {stmts : List Stmt}
    (hcore : FunctionBody.StmtListCompileCore scope stmts) :
    stmtListUsesStorageArrayElement stmts = false := by
  induction hcore with
  | nil => simp only [stmtListUsesStorageArrayElement, Bool.false_or]
  | letVar hvalue _ _ ih =>
      simp only [stmtListUsesStorageArrayElement, stmtUsesStorageArrayElement,
        exprCompileCore_usesStorageArrayElement_false hvalue, Bool.false_or]; assumption
  | assignVar hvalue _ _ ih =>
      simp only [stmtListUsesStorageArrayElement, stmtUsesStorageArrayElement,
        exprCompileCore_usesStorageArrayElement_false hvalue, Bool.false_or]; assumption
  | require_ hcond _ _ ih =>
      simp only [stmtListUsesStorageArrayElement, stmtUsesStorageArrayElement,
        exprCompileCore_usesStorageArrayElement_false hcond, Bool.false_or]; assumption
  | return_ hvalue _ _ ih =>
      simp only [stmtListUsesStorageArrayElement, stmtUsesStorageArrayElement,
        exprCompileCore_usesStorageArrayElement_false hvalue, Bool.false_or]; assumption
  | stop _ ih =>
      simp only [stmtListUsesStorageArrayElement, stmtUsesStorageArrayElement, Bool.false_or]; assumption
  | mstore hoffset _ hvalue _ _ ih =>
      simp only [stmtListUsesStorageArrayElement, stmtUsesStorageArrayElement,
        exprCompileCore_usesStorageArrayElement_false hoffset,
        exprCompileCore_usesStorageArrayElement_false hvalue, Bool.false_or]; assumption
  | tstore hoffset _ hvalue _ _ ih =>
      simp only [stmtListUsesStorageArrayElement, stmtUsesStorageArrayElement,
        exprCompileCore_usesStorageArrayElement_false hoffset,
        exprCompileCore_usesStorageArrayElement_false hvalue, Bool.false_or]; assumption

-- Helper: StmtListTerminalCore never uses storageArrayElement
private theorem stmtListTerminalCore_usesStorageArrayElement_false
    {scope : List String} {stmts : List Stmt}
    (hcore : FunctionBody.StmtListTerminalCore scope stmts) :
    stmtListUsesStorageArrayElement stmts = false := by
  induction hcore with
  | letVar hvalue _ _ ih =>
      simp only [stmtListUsesStorageArrayElement, stmtUsesStorageArrayElement,
        exprCompileCore_usesStorageArrayElement_false hvalue, Bool.false_or]; assumption
  | assignVar hvalue _ _ ih =>
      simp only [stmtListUsesStorageArrayElement, stmtUsesStorageArrayElement,
        exprCompileCore_usesStorageArrayElement_false hvalue, Bool.false_or]; assumption
  | require_ hcond _ _ ih =>
      simp only [stmtListUsesStorageArrayElement, stmtUsesStorageArrayElement,
        exprCompileCore_usesStorageArrayElement_false hcond, Bool.false_or]; assumption
  | return_ hvalue _ ih =>
      simp only [stmtListUsesStorageArrayElement, stmtUsesStorageArrayElement,
        exprCompileCore_usesStorageArrayElement_false hvalue,
        stmtListCompileCore_usesStorageArrayElement_false ih, Bool.false_or]
  | stop ih =>
      simp only [stmtListUsesStorageArrayElement, stmtUsesStorageArrayElement,
        stmtListCompileCore_usesStorageArrayElement_false ih, Bool.false_or]
  | ite hcond _ _ _ hCompile ih_then ih_else =>
      simp only [stmtListUsesStorageArrayElement, stmtUsesStorageArrayElement,
        exprCompileCore_usesStorageArrayElement_false hcond, ih_then, ih_else,
        stmtListCompileCore_usesStorageArrayElement_false hCompile, Bool.false_or]
  | mstore hoffset _ hvalue _ _ ih =>
      simp only [stmtListUsesStorageArrayElement, stmtUsesStorageArrayElement,
        exprCompileCore_usesStorageArrayElement_false hoffset,
        exprCompileCore_usesStorageArrayElement_false hvalue, Bool.false_or]; assumption
  | tstore hoffset _ hvalue _ _ ih =>
      simp only [stmtListUsesStorageArrayElement, stmtUsesStorageArrayElement,
        exprCompileCore_usesStorageArrayElement_false hoffset,
        exprCompileCore_usesStorageArrayElement_false hvalue, Bool.false_or]; assumption

-- Helper: StmtListCompileCore never uses dynamicBytesEq
private theorem stmtListCompileCore_usesDynamicBytesEq_false
    {scope : List String} {stmts : List Stmt}
    (hcore : FunctionBody.StmtListCompileCore scope stmts) :
    stmtListUsesDynamicBytesEq stmts = false := by
  induction hcore with
  | nil => simp only [stmtListUsesDynamicBytesEq, Bool.false_or]
  | letVar hvalue _ _ ih =>
      simp only [stmtListUsesDynamicBytesEq, stmtUsesDynamicBytesEq,
        exprCompileCore_usesDynamicBytesEq_false hvalue, Bool.false_or]; assumption
  | assignVar hvalue _ _ ih =>
      simp only [stmtListUsesDynamicBytesEq, stmtUsesDynamicBytesEq,
        exprCompileCore_usesDynamicBytesEq_false hvalue, Bool.false_or]; assumption
  | require_ hcond _ _ ih =>
      simp only [stmtListUsesDynamicBytesEq, stmtUsesDynamicBytesEq,
        exprCompileCore_usesDynamicBytesEq_false hcond, Bool.false_or]; assumption
  | return_ hvalue _ _ ih =>
      simp only [stmtListUsesDynamicBytesEq, stmtUsesDynamicBytesEq,
        exprCompileCore_usesDynamicBytesEq_false hvalue, Bool.false_or]; assumption
  | stop _ ih =>
      simp only [stmtListUsesDynamicBytesEq, stmtUsesDynamicBytesEq, Bool.false_or]; assumption
  | mstore hoffset _ hvalue _ _ ih =>
      simp only [stmtListUsesDynamicBytesEq, stmtUsesDynamicBytesEq,
        exprCompileCore_usesDynamicBytesEq_false hoffset,
        exprCompileCore_usesDynamicBytesEq_false hvalue, Bool.false_or]; assumption
  | tstore hoffset _ hvalue _ _ ih =>
      simp only [stmtListUsesDynamicBytesEq, stmtUsesDynamicBytesEq,
        exprCompileCore_usesDynamicBytesEq_false hoffset,
        exprCompileCore_usesDynamicBytesEq_false hvalue, Bool.false_or]; assumption

-- Helper: StmtListTerminalCore never uses dynamicBytesEq
private theorem stmtListTerminalCore_usesDynamicBytesEq_false
    {scope : List String} {stmts : List Stmt}
    (hcore : FunctionBody.StmtListTerminalCore scope stmts) :
    stmtListUsesDynamicBytesEq stmts = false := by
  induction hcore with
  | letVar hvalue _ _ ih =>
      simp only [stmtListUsesDynamicBytesEq, stmtUsesDynamicBytesEq,
        exprCompileCore_usesDynamicBytesEq_false hvalue, Bool.false_or]; assumption
  | assignVar hvalue _ _ ih =>
      simp only [stmtListUsesDynamicBytesEq, stmtUsesDynamicBytesEq,
        exprCompileCore_usesDynamicBytesEq_false hvalue, Bool.false_or]; assumption
  | require_ hcond _ _ ih =>
      simp only [stmtListUsesDynamicBytesEq, stmtUsesDynamicBytesEq,
        exprCompileCore_usesDynamicBytesEq_false hcond, Bool.false_or]; assumption
  | return_ hvalue _ ih =>
      simp only [stmtListUsesDynamicBytesEq, stmtUsesDynamicBytesEq,
        exprCompileCore_usesDynamicBytesEq_false hvalue,
        stmtListCompileCore_usesDynamicBytesEq_false ih, Bool.false_or]
  | stop ih =>
      simp only [stmtListUsesDynamicBytesEq, stmtUsesDynamicBytesEq,
        stmtListCompileCore_usesDynamicBytesEq_false ih, Bool.false_or]
  | ite hcond _ _ _ hCompile ih_then ih_else =>
      simp only [stmtListUsesDynamicBytesEq, stmtUsesDynamicBytesEq,
        exprCompileCore_usesDynamicBytesEq_false hcond, ih_then, ih_else,
        stmtListCompileCore_usesDynamicBytesEq_false hCompile, Bool.false_or]
  | mstore hoffset _ hvalue _ _ ih =>
      simp only [stmtListUsesDynamicBytesEq, stmtUsesDynamicBytesEq,
        exprCompileCore_usesDynamicBytesEq_false hoffset,
        exprCompileCore_usesDynamicBytesEq_false hvalue, Bool.false_or]; assumption
  | tstore hoffset _ hvalue _ _ ih =>
      simp only [stmtListUsesDynamicBytesEq, stmtUsesDynamicBytesEq,
        exprCompileCore_usesDynamicBytesEq_false hoffset,
        exprCompileCore_usesDynamicBytesEq_false hvalue, Bool.false_or]; assumption

-- SupportedStmtList never uses arrayElement
private theorem supportedLeafStmt_usesArrayElement_false
    {stmt : Stmt} (h : SupportedLeafStmt stmt) :
    stmtUsesArrayElement stmt = false := by
  cases h with
  | emit hargs | ecm hargs =>
      simpa [stmtUsesArrayElement] using
        exprListCompileCore_usesArrayElement_false hargs
  | setMappingChain hkeys hvalue =>
      simp [stmtUsesArrayElement, exprListCompileCore_usesArrayElement_false hkeys,
        exprCompileCore_usesArrayElement_false hvalue]
  | forEachCore _ hbody =>
      simp [stmtUsesArrayElement, exprUsesArrayElement,
        stmtListCompileCore_usesArrayElement_false hbody]
  | iteCore hcond hthen helse =>
      simp [stmtUsesArrayElement, exprCompileCore_usesArrayElement_false hcond,
        stmtListCompileCore_usesArrayElement_false hthen,
        stmtListCompileCore_usesArrayElement_false helse]
  | _ =>
      simp_all [stmtUsesArrayElement, exprUsesArrayElement,
        stmtListUsesArrayElement, exprCompileCore_usesArrayElement_false]

open Verity.Core.Free in
private theorem supportedStmtList_usesArrayElement_false
    {fields : List Field} {scope : List String} {stmts : List Stmt}
    (h : SupportedStmtList fields scope stmts) :
    stmtListUsesArrayElement stmts = false := by
  refine SupportedStmtList.boolFold_eq_false (stmtF := stmtUsesArrayElement)
    (by simp [stmtListUsesArrayElement])
    (fun _ _ => by simp [stmtListUsesArrayElement])
    stmtListCompileCore_usesArrayElement_false
    stmtListTerminalCore_usesArrayElement_false
    supportedLeafStmt_usesArrayElement_false
    (fun hbody => ?_) (fun hcond hthen helse => ?_) h
  · simpa [stmtUsesArrayElement, exprUsesArrayElement] using hbody
  · simp only [stmtUsesArrayElement, exprCompileCore_usesArrayElement_false hcond,
      stmtListTerminalCore_usesArrayElement_false hthen,
      stmtListTerminalCore_usesArrayElement_false helse, Bool.false_or]

-- SupportedStmtList never uses storageArrayElement
private theorem supportedLeafStmt_usesStorageArrayElement_false
    {stmt : Stmt} (h : SupportedLeafStmt stmt) :
    stmtUsesStorageArrayElement stmt = false := by
  cases h with
  | emit hargs | ecm hargs =>
      simpa [stmtUsesStorageArrayElement] using
        exprListCompileCore_usesStorageArrayElement_false hargs
  | setMappingChain hkeys hvalue =>
      simp [stmtUsesStorageArrayElement, exprListCompileCore_usesStorageArrayElement_false hkeys,
        exprCompileCore_usesStorageArrayElement_false hvalue]
  | forEachCore _ hbody =>
      simp [stmtUsesStorageArrayElement, exprUsesStorageArrayElement,
        stmtListCompileCore_usesStorageArrayElement_false hbody]
  | iteCore hcond hthen helse =>
      simp [stmtUsesStorageArrayElement, exprCompileCore_usesStorageArrayElement_false hcond,
        stmtListCompileCore_usesStorageArrayElement_false hthen,
        stmtListCompileCore_usesStorageArrayElement_false helse]
  | _ =>
      simp_all [stmtUsesStorageArrayElement, exprUsesStorageArrayElement,
        stmtListUsesStorageArrayElement, exprCompileCore_usesStorageArrayElement_false]

open Verity.Core.Free in
private theorem supportedStmtList_usesStorageArrayElement_false
    {fields : List Field} {scope : List String} {stmts : List Stmt}
    (h : SupportedStmtList fields scope stmts) :
    stmtListUsesStorageArrayElement stmts = false := by
  refine SupportedStmtList.boolFold_eq_false (stmtF := stmtUsesStorageArrayElement)
    (by simp [stmtListUsesStorageArrayElement])
    (fun _ _ => by simp [stmtListUsesStorageArrayElement])
    stmtListCompileCore_usesStorageArrayElement_false
    stmtListTerminalCore_usesStorageArrayElement_false
    supportedLeafStmt_usesStorageArrayElement_false
    (fun hbody => ?_) (fun hcond hthen helse => ?_) h
  · simpa [stmtUsesStorageArrayElement, exprUsesStorageArrayElement] using hbody
  · simp only [stmtUsesStorageArrayElement, exprCompileCore_usesStorageArrayElement_false hcond,
      stmtListTerminalCore_usesStorageArrayElement_false hthen,
      stmtListTerminalCore_usesStorageArrayElement_false helse, Bool.false_or]

-- SupportedStmtList never uses dynamicBytesEq
private theorem supportedLeafStmt_usesDynamicBytesEq_false
    {stmt : Stmt} (h : SupportedLeafStmt stmt) :
    stmtUsesDynamicBytesEq stmt = false := by
  cases h with
  | emit hargs | ecm hargs =>
      simpa [stmtUsesDynamicBytesEq] using
        exprListCompileCore_usesDynamicBytesEq_false hargs
  | setMappingChain hkeys hvalue =>
      simp [stmtUsesDynamicBytesEq, exprListCompileCore_usesDynamicBytesEq_false hkeys,
        exprCompileCore_usesDynamicBytesEq_false hvalue]
  | forEachCore _ hbody =>
      simp [stmtUsesDynamicBytesEq, exprUsesDynamicBytesEq,
        stmtListCompileCore_usesDynamicBytesEq_false hbody]
  | iteCore hcond hthen helse =>
      simp [stmtUsesDynamicBytesEq, exprCompileCore_usesDynamicBytesEq_false hcond,
        stmtListCompileCore_usesDynamicBytesEq_false hthen,
        stmtListCompileCore_usesDynamicBytesEq_false helse]
  | _ =>
      simp_all [stmtUsesDynamicBytesEq, exprUsesDynamicBytesEq,
        stmtListUsesDynamicBytesEq, exprCompileCore_usesDynamicBytesEq_false]

open Verity.Core.Free in
private theorem supportedStmtList_usesDynamicBytesEq_false
    {fields : List Field} {scope : List String} {stmts : List Stmt}
    (h : SupportedStmtList fields scope stmts) :
    stmtListUsesDynamicBytesEq stmts = false := by
  refine SupportedStmtList.boolFold_eq_false (stmtF := stmtUsesDynamicBytesEq)
    (by simp [stmtListUsesDynamicBytesEq])
    (fun _ _ => by simp [stmtListUsesDynamicBytesEq])
    stmtListCompileCore_usesDynamicBytesEq_false
    stmtListTerminalCore_usesDynamicBytesEq_false
    supportedLeafStmt_usesDynamicBytesEq_false
    (fun hbody => ?_) (fun hcond hthen helse => ?_) h
  · simpa [stmtUsesDynamicBytesEq, exprUsesDynamicBytesEq] using hbody
  · simp only [stmtUsesDynamicBytesEq, exprCompileCore_usesDynamicBytesEq_false hcond,
      stmtListTerminalCore_usesDynamicBytesEq_false hthen,
      stmtListTerminalCore_usesDynamicBytesEq_false helse, Bool.false_or]

-- Bridge: stmtListUsesArrayElement is equivalent to List.any
private theorem stmtListUsesArrayElement_eq_any (stmts : List Stmt) :
    stmtListUsesArrayElement stmts = stmts.any stmtUsesArrayElement := by
  induction stmts with
  | nil => simp [stmtListUsesArrayElement, List.any]
  | cons s ss ih => simp [stmtListUsesArrayElement, List.any_cons, ih]

private theorem stmtListUsesStorageArrayElement_eq_any (stmts : List Stmt) :
    stmtListUsesStorageArrayElement stmts = stmts.any stmtUsesStorageArrayElement := by
  induction stmts with
  | nil => simp [stmtListUsesStorageArrayElement, List.any]
  | cons s ss ih => simp [stmtListUsesStorageArrayElement, List.any_cons, ih]

private theorem stmtListUsesDynamicBytesEq_eq_any (stmts : List Stmt) :
    stmtListUsesDynamicBytesEq stmts = stmts.any stmtUsesDynamicBytesEq := by
  induction stmts with
  | nil => simp [stmtListUsesDynamicBytesEq, List.any]
  | cons s ss ih => simp [stmtListUsesDynamicBytesEq, List.any_cons, ih]

private theorem listAny_eq_false_of_mem_eq_false
    {α : Type} (f : α → Bool) :
    ∀ (xs : List α), (∀ x ∈ xs, f x = false) → xs.any f = false
  | [], _ => rfl
  | x :: xs, hmem => by
      have hx : f x = false := hmem x (by simp)
      have hxs : ∀ y ∈ xs, f y = false := by
        intro y hy
        exact hmem y (by simp [hy])
      simp [List.any_cons, hx, listAny_eq_false_of_mem_eq_false f xs hxs]

-- Helper: ExprCompileCore expressions never use mulDiv512 (verity#1761)
private theorem exprCompileCore_usesMulDiv512_false
    {expr : Expr}
    (hcore : FunctionBody.ExprCompileCore expr) :
    exprUsesMulDiv512 expr = false := by
  induction hcore with
  | literal | param | constructorArg | localVar | caller | contractAddress | txOrigin | msgValue
    | blockTimestamp | blockNumber | chainid
    | blobbasefee | calldatasize | returndataSize =>
      simp only [exprUsesMulDiv512, Bool.false_or]
  | add _ _ ihL ihR | sub _ _ ihL ihR | mul _ _ ihL ihR
    | div _ _ ihL ihR | mod _ _ ihL ihR | eq _ _ ihL ihR
    | lt _ _ ihL ihR | gt _ _ ihL ihR | ge _ _ ihL ihR
    | le _ _ ihL ihR | logicalAnd _ _ ihL ihR | logicalOr _ _ ihL ihR
    | bitAnd _ _ ihL ihR | bitOr _ _ ihL ihR | bitXor _ _ ihL ihR
    | shl _ _ ihL ihR | shr _ _ ihL ihR
    | min _ _ ihL ihR | max _ _ ihL ihR | ceilDiv _ _ ihL ihR
    | wMulDown _ _ ihL ihR | wDivUp _ _ ihL ihR
    | slt _ _ ihL ihR | sgt _ _ ihL ihR | sdiv _ _ ihL ihR
    | smod _ _ ihL ihR | sar _ _ ihL ihR | byte _ _ ihL ihR | signextend _ _ ihL ihR
    | keccak256 _ _ ihL ihR =>
      simp only [exprUsesMulDiv512, ihL, ihR, Bool.false_or]
  | mulDivDown _ _ _ ihA ihB ihC | mulDivUp _ _ _ ihA ihB ihC =>
      simp only [exprUsesMulDiv512, ihA, ihB, ihC, Bool.false_or]
  | logicalNot _ ih | bitNot _ ih | tload _ ih | calldataload _ ih | mload _ ih | extcodesize _ ih
  | returndataOptionalBoolAt _ ih =>
      simp only [exprUsesMulDiv512, ih, Bool.false_or]
  | ite _ _ _ ihC ihT ihE =>
      simp only [exprUsesMulDiv512, ihC, ihT, ihE, Bool.false_or]
  | builtinExp _ _ ihB ihE =>
      simp only [exprUsesMulDiv512, exprListUsesMulDiv512, ihB, ihE, Bool.false_or,
        Bool.or_false]

-- Helper: ExprCompileCore expressions never use paramDynamicHeadWord (verity#1832)
private theorem exprCompileCore_usesParamDynamicHeadWord_false
    {expr : Expr}
    (hcore : FunctionBody.ExprCompileCore expr) :
    exprUsesParamDynamicHeadWord expr = false := by
  induction hcore with
  | literal | param | constructorArg | localVar | caller | contractAddress | txOrigin | msgValue
    | blockTimestamp | blockNumber | chainid
    | blobbasefee | calldatasize | returndataSize =>
      simp only [exprUsesParamDynamicHeadWord, Bool.false_or]
  | add _ _ ihL ihR | sub _ _ ihL ihR | mul _ _ ihL ihR
    | div _ _ ihL ihR | mod _ _ ihL ihR | eq _ _ ihL ihR
    | lt _ _ ihL ihR | gt _ _ ihL ihR | ge _ _ ihL ihR
    | le _ _ ihL ihR | logicalAnd _ _ ihL ihR | logicalOr _ _ ihL ihR
    | bitAnd _ _ ihL ihR | bitOr _ _ ihL ihR | bitXor _ _ ihL ihR
    | shl _ _ ihL ihR | shr _ _ ihL ihR
    | min _ _ ihL ihR | max _ _ ihL ihR | ceilDiv _ _ ihL ihR
    | wMulDown _ _ ihL ihR | wDivUp _ _ ihL ihR
    | slt _ _ ihL ihR | sgt _ _ ihL ihR | sdiv _ _ ihL ihR
    | smod _ _ ihL ihR | sar _ _ ihL ihR | byte _ _ ihL ihR | signextend _ _ ihL ihR
    | keccak256 _ _ ihL ihR =>
      simp only [exprUsesParamDynamicHeadWord, ihL, ihR, Bool.false_or]
  | mulDivDown _ _ _ ihA ihB ihC | mulDivUp _ _ _ ihA ihB ihC =>
      simp only [exprUsesParamDynamicHeadWord, ihA, ihB, ihC, Bool.false_or]
  | logicalNot _ ih | bitNot _ ih | tload _ ih | calldataload _ ih | mload _ ih | extcodesize _ ih
  | returndataOptionalBoolAt _ ih =>
      simp only [exprUsesParamDynamicHeadWord, ih, Bool.false_or]
  | ite _ _ _ ihC ihT ihE =>
      simp only [exprUsesParamDynamicHeadWord, ihC, ihT, ihE, Bool.false_or]
  | builtinExp _ _ ihB ihE =>
      simp only [exprUsesParamDynamicHeadWord, exprListUsesParamDynamicHeadWord, ihB, ihE,
        Bool.false_or, Bool.or_false]

-- Helper: ExprCompileCore lists never use mulDiv512
private theorem exprListCompileCore_usesMulDiv512_false
    {exprs : List Expr}
    (hcore : ∀ expr ∈ exprs, FunctionBody.ExprCompileCore expr) :
    exprListUsesMulDiv512 exprs = false := by
  induction exprs with
  | nil => simp only [exprListUsesMulDiv512, Bool.false_or]
  | cons e rest ih =>
      simp only [exprListUsesMulDiv512,
        exprCompileCore_usesMulDiv512_false (hcore e (List.mem_cons_self ..)),
        ih (fun e he => hcore e (List.mem_cons_of_mem _ he)), Bool.false_or]

-- Helper: ExprCompileCore lists never use paramDynamicHeadWord
private theorem exprListCompileCore_usesParamDynamicHeadWord_false
    {exprs : List Expr}
    (hcore : ∀ expr ∈ exprs, FunctionBody.ExprCompileCore expr) :
    exprListUsesParamDynamicHeadWord exprs = false := by
  induction exprs with
  | nil => simp only [exprListUsesParamDynamicHeadWord, Bool.false_or]
  | cons e rest ih =>
      simp only [exprListUsesParamDynamicHeadWord,
        exprCompileCore_usesParamDynamicHeadWord_false (hcore e (List.mem_cons_self ..)),
        ih (fun e he => hcore e (List.mem_cons_of_mem _ he)), Bool.false_or]

-- Helper: StmtListCompileCore never uses mulDiv512
private theorem stmtListCompileCore_usesMulDiv512_false
    {scope : List String} {stmts : List Stmt}
    (hcore : FunctionBody.StmtListCompileCore scope stmts) :
    stmtListUsesMulDiv512 stmts = false := by
  induction hcore with
  | nil => simp only [stmtListUsesMulDiv512, Bool.false_or]
  | letVar hvalue _ _ ih =>
      simp only [stmtListUsesMulDiv512, stmtUsesMulDiv512,
        exprCompileCore_usesMulDiv512_false hvalue, Bool.false_or]; assumption
  | assignVar hvalue _ _ ih =>
      simp only [stmtListUsesMulDiv512, stmtUsesMulDiv512,
        exprCompileCore_usesMulDiv512_false hvalue, Bool.false_or]; assumption
  | require_ hcond _ _ ih =>
      simp only [stmtListUsesMulDiv512, stmtUsesMulDiv512,
        exprCompileCore_usesMulDiv512_false hcond, Bool.false_or]; assumption
  | return_ hvalue _ _ ih =>
      simp only [stmtListUsesMulDiv512, stmtUsesMulDiv512,
        exprCompileCore_usesMulDiv512_false hvalue, Bool.false_or]; assumption
  | stop _ ih =>
      simp only [stmtListUsesMulDiv512, stmtUsesMulDiv512, Bool.false_or]; assumption
  | mstore hoffset _ hvalue _ _ ih =>
      simp only [stmtListUsesMulDiv512, stmtUsesMulDiv512,
        exprCompileCore_usesMulDiv512_false hoffset,
        exprCompileCore_usesMulDiv512_false hvalue, Bool.false_or]; assumption
  | tstore hoffset _ hvalue _ _ ih =>
      simp only [stmtListUsesMulDiv512, stmtUsesMulDiv512,
        exprCompileCore_usesMulDiv512_false hoffset,
        exprCompileCore_usesMulDiv512_false hvalue, Bool.false_or]; assumption

-- Helper: StmtListCompileCore never uses paramDynamicHeadWord
private theorem stmtListCompileCore_usesParamDynamicHeadWord_false
    {scope : List String} {stmts : List Stmt}
    (hcore : FunctionBody.StmtListCompileCore scope stmts) :
    stmtListUsesParamDynamicHeadWord stmts = false := by
  induction hcore with
  | nil => simp only [stmtListUsesParamDynamicHeadWord, Bool.false_or]
  | letVar hvalue _ _ ih =>
      simp only [stmtListUsesParamDynamicHeadWord, stmtUsesParamDynamicHeadWord,
        exprCompileCore_usesParamDynamicHeadWord_false hvalue, Bool.false_or]; assumption
  | assignVar hvalue _ _ ih =>
      simp only [stmtListUsesParamDynamicHeadWord, stmtUsesParamDynamicHeadWord,
        exprCompileCore_usesParamDynamicHeadWord_false hvalue, Bool.false_or]; assumption
  | require_ hcond _ _ ih =>
      simp only [stmtListUsesParamDynamicHeadWord, stmtUsesParamDynamicHeadWord,
        exprCompileCore_usesParamDynamicHeadWord_false hcond, Bool.false_or]; assumption
  | return_ hvalue _ _ ih =>
      simp only [stmtListUsesParamDynamicHeadWord, stmtUsesParamDynamicHeadWord,
        exprCompileCore_usesParamDynamicHeadWord_false hvalue, Bool.false_or]; assumption
  | stop _ ih =>
      simp only [stmtListUsesParamDynamicHeadWord, stmtUsesParamDynamicHeadWord, Bool.false_or]; assumption
  | mstore hoffset _ hvalue _ _ ih =>
      simp only [stmtListUsesParamDynamicHeadWord, stmtUsesParamDynamicHeadWord,
        exprCompileCore_usesParamDynamicHeadWord_false hoffset,
        exprCompileCore_usesParamDynamicHeadWord_false hvalue, Bool.false_or]; assumption
  | tstore hoffset _ hvalue _ _ ih =>
      simp only [stmtListUsesParamDynamicHeadWord, stmtUsesParamDynamicHeadWord,
        exprCompileCore_usesParamDynamicHeadWord_false hoffset,
        exprCompileCore_usesParamDynamicHeadWord_false hvalue, Bool.false_or]; assumption

-- Helper: StmtListTerminalCore never uses mulDiv512
private theorem stmtListTerminalCore_usesMulDiv512_false
    {scope : List String} {stmts : List Stmt}
    (hcore : FunctionBody.StmtListTerminalCore scope stmts) :
    stmtListUsesMulDiv512 stmts = false := by
  induction hcore with
  | letVar hvalue _ _ ih =>
      simp only [stmtListUsesMulDiv512, stmtUsesMulDiv512,
        exprCompileCore_usesMulDiv512_false hvalue, Bool.false_or]; assumption
  | assignVar hvalue _ _ ih =>
      simp only [stmtListUsesMulDiv512, stmtUsesMulDiv512,
        exprCompileCore_usesMulDiv512_false hvalue, Bool.false_or]; assumption
  | require_ hcond _ _ ih =>
      simp only [stmtListUsesMulDiv512, stmtUsesMulDiv512,
        exprCompileCore_usesMulDiv512_false hcond, Bool.false_or]; assumption
  | return_ hvalue _ ih =>
      simp only [stmtListUsesMulDiv512, stmtUsesMulDiv512,
        exprCompileCore_usesMulDiv512_false hvalue,
        stmtListCompileCore_usesMulDiv512_false ih, Bool.false_or]
  | stop ih =>
      simp only [stmtListUsesMulDiv512, stmtUsesMulDiv512,
        stmtListCompileCore_usesMulDiv512_false ih, Bool.false_or]
  | ite hcond _ _ _ hCompile ih_then ih_else =>
      simp only [stmtListUsesMulDiv512, stmtUsesMulDiv512,
        exprCompileCore_usesMulDiv512_false hcond, ih_then, ih_else,
        stmtListCompileCore_usesMulDiv512_false hCompile, Bool.false_or]
  | mstore hoffset _ hvalue _ _ ih =>
      simp only [stmtListUsesMulDiv512, stmtUsesMulDiv512,
        exprCompileCore_usesMulDiv512_false hoffset,
        exprCompileCore_usesMulDiv512_false hvalue, Bool.false_or]; assumption
  | tstore hoffset _ hvalue _ _ ih =>
      simp only [stmtListUsesMulDiv512, stmtUsesMulDiv512,
        exprCompileCore_usesMulDiv512_false hoffset,
        exprCompileCore_usesMulDiv512_false hvalue, Bool.false_or]; assumption

-- Helper: StmtListTerminalCore never uses paramDynamicHeadWord
private theorem stmtListTerminalCore_usesParamDynamicHeadWord_false
    {scope : List String} {stmts : List Stmt}
    (hcore : FunctionBody.StmtListTerminalCore scope stmts) :
    stmtListUsesParamDynamicHeadWord stmts = false := by
  induction hcore with
  | letVar hvalue _ _ ih =>
      simp only [stmtListUsesParamDynamicHeadWord, stmtUsesParamDynamicHeadWord,
        exprCompileCore_usesParamDynamicHeadWord_false hvalue, Bool.false_or]; assumption
  | assignVar hvalue _ _ ih =>
      simp only [stmtListUsesParamDynamicHeadWord, stmtUsesParamDynamicHeadWord,
        exprCompileCore_usesParamDynamicHeadWord_false hvalue, Bool.false_or]; assumption
  | require_ hcond _ _ ih =>
      simp only [stmtListUsesParamDynamicHeadWord, stmtUsesParamDynamicHeadWord,
        exprCompileCore_usesParamDynamicHeadWord_false hcond, Bool.false_or]; assumption
  | return_ hvalue _ ih =>
      simp only [stmtListUsesParamDynamicHeadWord, stmtUsesParamDynamicHeadWord,
        exprCompileCore_usesParamDynamicHeadWord_false hvalue,
        stmtListCompileCore_usesParamDynamicHeadWord_false ih, Bool.false_or]
  | stop ih =>
      simp only [stmtListUsesParamDynamicHeadWord, stmtUsesParamDynamicHeadWord,
        stmtListCompileCore_usesParamDynamicHeadWord_false ih, Bool.false_or]
  | ite hcond _ _ _ hCompile ih_then ih_else =>
      simp only [stmtListUsesParamDynamicHeadWord, stmtUsesParamDynamicHeadWord,
        exprCompileCore_usesParamDynamicHeadWord_false hcond, ih_then, ih_else,
        stmtListCompileCore_usesParamDynamicHeadWord_false hCompile, Bool.false_or]
  | mstore hoffset _ hvalue _ _ ih =>
      simp only [stmtListUsesParamDynamicHeadWord, stmtUsesParamDynamicHeadWord,
        exprCompileCore_usesParamDynamicHeadWord_false hoffset,
        exprCompileCore_usesParamDynamicHeadWord_false hvalue, Bool.false_or]; assumption
  | tstore hoffset _ hvalue _ _ ih =>
      simp only [stmtListUsesParamDynamicHeadWord, stmtUsesParamDynamicHeadWord,
        exprCompileCore_usesParamDynamicHeadWord_false hoffset,
        exprCompileCore_usesParamDynamicHeadWord_false hvalue, Bool.false_or]; assumption

-- SupportedStmtList never uses mulDiv512
private theorem supportedLeafStmt_usesMulDiv512_false
    {stmt : Stmt} (h : SupportedLeafStmt stmt) :
    stmtUsesMulDiv512 stmt = false := by
  cases h with
  | emit hargs | ecm hargs =>
      simpa [stmtUsesMulDiv512] using
        exprListCompileCore_usesMulDiv512_false hargs
  | setMappingChain hkeys hvalue =>
      simp [stmtUsesMulDiv512, exprListCompileCore_usesMulDiv512_false hkeys,
        exprCompileCore_usesMulDiv512_false hvalue]
  | forEachCore _ hbody =>
      simp [stmtUsesMulDiv512, exprUsesMulDiv512,
        stmtListCompileCore_usesMulDiv512_false hbody]
  | iteCore hcond hthen helse =>
      simp [stmtUsesMulDiv512, exprCompileCore_usesMulDiv512_false hcond,
        stmtListCompileCore_usesMulDiv512_false hthen,
        stmtListCompileCore_usesMulDiv512_false helse]
  | _ =>
      simp_all [stmtUsesMulDiv512, exprUsesMulDiv512,
        stmtListUsesMulDiv512, exprCompileCore_usesMulDiv512_false]

open Verity.Core.Free in
private theorem supportedStmtList_usesMulDiv512_false
    {fields : List Field} {scope : List String} {stmts : List Stmt}
    (h : SupportedStmtList fields scope stmts) :
    stmtListUsesMulDiv512 stmts = false := by
  refine SupportedStmtList.boolFold_eq_false (stmtF := stmtUsesMulDiv512)
    (by simp [stmtListUsesMulDiv512])
    (fun _ _ => by simp [stmtListUsesMulDiv512])
    stmtListCompileCore_usesMulDiv512_false
    stmtListTerminalCore_usesMulDiv512_false
    supportedLeafStmt_usesMulDiv512_false
    (fun hbody => ?_) (fun hcond hthen helse => ?_) h
  · simpa [stmtUsesMulDiv512, exprUsesMulDiv512] using hbody
  · simp only [stmtUsesMulDiv512, exprCompileCore_usesMulDiv512_false hcond,
      stmtListTerminalCore_usesMulDiv512_false hthen,
      stmtListTerminalCore_usesMulDiv512_false helse, Bool.false_or]

-- SupportedStmtList never uses paramDynamicHeadWord
private theorem supportedLeafStmt_usesParamDynamicHeadWord_false
    {stmt : Stmt} (h : SupportedLeafStmt stmt) :
    stmtUsesParamDynamicHeadWord stmt = false := by
  cases h with
  | emit hargs | ecm hargs =>
      simpa [stmtUsesParamDynamicHeadWord] using
        exprListCompileCore_usesParamDynamicHeadWord_false hargs
  | setMappingChain hkeys hvalue =>
      simp [stmtUsesParamDynamicHeadWord, exprListCompileCore_usesParamDynamicHeadWord_false hkeys,
        exprCompileCore_usesParamDynamicHeadWord_false hvalue]
  | forEachCore _ hbody =>
      simp [stmtUsesParamDynamicHeadWord, exprUsesParamDynamicHeadWord,
        stmtListCompileCore_usesParamDynamicHeadWord_false hbody]
  | iteCore hcond hthen helse =>
      simp [stmtUsesParamDynamicHeadWord, exprCompileCore_usesParamDynamicHeadWord_false hcond,
        stmtListCompileCore_usesParamDynamicHeadWord_false hthen,
        stmtListCompileCore_usesParamDynamicHeadWord_false helse]
  | _ =>
      simp_all [stmtUsesParamDynamicHeadWord, exprUsesParamDynamicHeadWord,
        stmtListUsesParamDynamicHeadWord, exprCompileCore_usesParamDynamicHeadWord_false]

open Verity.Core.Free in
private theorem supportedStmtList_usesParamDynamicHeadWord_false
    {fields : List Field} {scope : List String} {stmts : List Stmt}
    (h : SupportedStmtList fields scope stmts) :
    stmtListUsesParamDynamicHeadWord stmts = false := by
  refine SupportedStmtList.boolFold_eq_false (stmtF := stmtUsesParamDynamicHeadWord)
    (by simp [stmtListUsesParamDynamicHeadWord])
    (fun _ _ => by simp [stmtListUsesParamDynamicHeadWord])
    stmtListCompileCore_usesParamDynamicHeadWord_false
    stmtListTerminalCore_usesParamDynamicHeadWord_false
    supportedLeafStmt_usesParamDynamicHeadWord_false
    (fun hbody => ?_) (fun hcond hthen helse => ?_) h
  · simpa [stmtUsesParamDynamicHeadWord, exprUsesParamDynamicHeadWord] using hbody
  · simp only [stmtUsesParamDynamicHeadWord, exprCompileCore_usesParamDynamicHeadWord_false hcond,
      stmtListTerminalCore_usesParamDynamicHeadWord_false hthen,
      stmtListTerminalCore_usesParamDynamicHeadWord_false helse, Bool.false_or]

private theorem stmtListUsesMulDiv512_eq_any (stmts : List Stmt) :
    stmtListUsesMulDiv512 stmts = stmts.any stmtUsesMulDiv512 := by
  induction stmts with
  | nil => simp [stmtListUsesMulDiv512, List.any]
  | cons s ss ih => simp [stmtListUsesMulDiv512, List.any_cons, ih]

private theorem stmtListUsesParamDynamicHeadWord_eq_any (stmts : List Stmt) :
    stmtListUsesParamDynamicHeadWord stmts = stmts.any stmtUsesParamDynamicHeadWord := by
  induction stmts with
  | nil => simp [stmtListUsesParamDynamicHeadWord, List.any]
  | cons s ss ih => simp [stmtListUsesParamDynamicHeadWord, List.any_cons, ih]

theorem SupportedSpec.contractUsesMulDiv512_eq_false
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors) :
    contractUsesMulDiv512 spec = false := by
  have hfunctions : ∀ fn ∈ spec.functions, fn.body.any stmtUsesMulDiv512 = false := by
    intro fn hmem
    have := supportedStmtList_usesMulDiv512_false
      (hSupported.functions fn hmem).body.stmtList
    rw [stmtListUsesMulDiv512_eq_any] at this
    simpa using this
  have hfunctionsAny :
      spec.functions.any (fun fn => fn.body.any stmtUsesMulDiv512) = false :=
    listAny_eq_false_of_mem_eq_false
      (fun fn => fn.body.any stmtUsesMulDiv512) spec.functions hfunctions
  cases hctor : spec.constructor with
  | none =>
      simp [contractUsesMulDiv512, hctor, hfunctionsAny]
  | some ctor =>
      have hctorMulDiv :
          ctor.body.any stmtUsesMulDiv512 = false := by
        have := supportedStmtList_usesMulDiv512_false
          (hSupported.constructor ctor hctor).stmtList_ctorBody
        rw [stmtListUsesMulDiv512_eq_any] at this
        simpa using this
      simp [contractUsesMulDiv512, hctor, hctorMulDiv, hfunctionsAny]

theorem SupportedSpec.contractUsesParamDynamicHeadWord_eq_false
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors) :
    contractUsesParamDynamicHeadWord spec = false := by
  have hfunctions :
      ∀ fn ∈ spec.functions, fn.body.any stmtUsesParamDynamicHeadWord = false := by
    intro fn hmem
    have := supportedStmtList_usesParamDynamicHeadWord_false
      (hSupported.functions fn hmem).body.stmtList
    rw [stmtListUsesParamDynamicHeadWord_eq_any] at this
    simpa using this
  have hfunctionsAny :
      spec.functions.any (fun fn => fn.body.any stmtUsesParamDynamicHeadWord) = false :=
    listAny_eq_false_of_mem_eq_false
      (fun fn => fn.body.any stmtUsesParamDynamicHeadWord) spec.functions hfunctions
  cases hctor : spec.constructor with
  | none =>
      simp [contractUsesParamDynamicHeadWord, hctor, hfunctionsAny]
  | some ctor =>
      have hctorParam :
          ctor.body.any stmtUsesParamDynamicHeadWord = false := by
        have := supportedStmtList_usesParamDynamicHeadWord_false
          (hSupported.constructor ctor hctor).stmtList_ctorBody
        rw [stmtListUsesParamDynamicHeadWord_eq_any] at this
        simpa using this
      simp [contractUsesParamDynamicHeadWord, hctor, hctorParam, hfunctionsAny]

theorem SupportedSpecExceptMappingWrites.contractUsesMulDiv512_eq_false
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors) :
    contractUsesMulDiv512 spec = false := by
  have hfunctions : ∀ fn ∈ spec.functions, fn.body.any stmtUsesMulDiv512 = false := by
    intro fn hmem
    have := supportedStmtList_usesMulDiv512_false
      (hSupported.functions fn hmem).body.stmtList
    rw [stmtListUsesMulDiv512_eq_any] at this
    simpa using this
  have hfunctionsAny :
      spec.functions.any (fun fn => fn.body.any stmtUsesMulDiv512) = false :=
    listAny_eq_false_of_mem_eq_false
      (fun fn => fn.body.any stmtUsesMulDiv512) spec.functions hfunctions
  cases hctor : spec.constructor with
  | none =>
      simp [contractUsesMulDiv512, hctor, hfunctionsAny]
  | some ctor =>
      have hctorMulDiv :
          ctor.body.any stmtUsesMulDiv512 = false := by
        have := supportedStmtList_usesMulDiv512_false
          (hSupported.constructor ctor hctor).stmtList_ctorBody
        rw [stmtListUsesMulDiv512_eq_any] at this
        simpa using this
      simp [contractUsesMulDiv512, hctor, hctorMulDiv, hfunctionsAny]

theorem SupportedSpecExceptMappingWrites.contractUsesParamDynamicHeadWord_eq_false
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors) :
    contractUsesParamDynamicHeadWord spec = false := by
  have hfunctions :
      ∀ fn ∈ spec.functions, fn.body.any stmtUsesParamDynamicHeadWord = false := by
    intro fn hmem
    have := supportedStmtList_usesParamDynamicHeadWord_false
      (hSupported.functions fn hmem).body.stmtList
    rw [stmtListUsesParamDynamicHeadWord_eq_any] at this
    simpa using this
  have hfunctionsAny :
      spec.functions.any (fun fn => fn.body.any stmtUsesParamDynamicHeadWord) = false :=
    listAny_eq_false_of_mem_eq_false
      (fun fn => fn.body.any stmtUsesParamDynamicHeadWord) spec.functions hfunctions
  cases hctor : spec.constructor with
  | none =>
      simp [contractUsesParamDynamicHeadWord, hctor, hfunctionsAny]
  | some ctor =>
      have hctorParam :
          ctor.body.any stmtUsesParamDynamicHeadWord = false := by
        have := supportedStmtList_usesParamDynamicHeadWord_false
          (hSupported.constructor ctor hctor).stmtList_ctorBody
        rw [stmtListUsesParamDynamicHeadWord_eq_any] at this
        simpa using this
      simp [contractUsesParamDynamicHeadWord, hctor, hctorParam, hfunctionsAny]

theorem SupportedSpec.noInternalFunctions
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors) :
    ∀ fn ∈ spec.functions, fn.isInternal = false := by
  intro fn hmem
  exact (hSupported.functions fn hmem).nonInternal

theorem SupportedSpecExceptMappingWrites.noInternalFunctions
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors) :
    ∀ fn ∈ spec.functions, fn.isInternal = false := by
  intro fn hmem
  exact (hSupported.functions fn hmem).nonInternal

theorem SupportedSpecWithScalarEvents.noInternalFunctions
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecWithScalarEvents spec selectors) :
    ∀ fn ∈ spec.functions, fn.isInternal = false := by
  intro fn hmem
  exact (hSupported.functions fn hmem).nonInternal

theorem SupportedSpec.contractUsesArrayElement_eq_false
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors) :
    contractUsesArrayElement spec = false := by
  have hfunctions : ∀ fn ∈ spec.functions, functionUsesArrayElement fn = false := by
    intro fn hmem
    simp only [functionUsesArrayElement]
    rw [← stmtListUsesArrayElement_eq_any]
    exact supportedStmtList_usesArrayElement_false (hSupported.functions fn hmem).body.stmtList
  have hfunctionsAny : spec.functions.any functionUsesArrayElement = false :=
    listAny_eq_false_of_mem_eq_false functionUsesArrayElement spec.functions hfunctions
  cases hctor : spec.constructor with
  | none =>
      simp [contractUsesArrayElement, hctor, constructorUsesArrayElement, hfunctionsAny]
  | some ctor =>
      have hctorArray :
          ctor.body.any stmtUsesArrayElement = false := by
        rw [← stmtListUsesArrayElement_eq_any]
        exact supportedStmtList_usesArrayElement_false
          (hSupported.constructor ctor hctor).stmtList_ctorBody
      simp [contractUsesArrayElement, hctor, constructorUsesArrayElement, hctorArray,
        hfunctionsAny]

theorem SupportedSpecExceptMappingWrites.contractUsesArrayElement_eq_false
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors) :
    contractUsesArrayElement spec = false := by
  have hfunctions : ∀ fn ∈ spec.functions, functionUsesArrayElement fn = false := by
    intro fn hmem
    simp only [functionUsesArrayElement]
    rw [← stmtListUsesArrayElement_eq_any]
    exact supportedStmtList_usesArrayElement_false (hSupported.functions fn hmem).body.stmtList
  have hfunctionsAny : spec.functions.any functionUsesArrayElement = false :=
    listAny_eq_false_of_mem_eq_false functionUsesArrayElement spec.functions hfunctions
  cases hctor : spec.constructor with
  | none =>
      simp [contractUsesArrayElement, hctor, constructorUsesArrayElement, hfunctionsAny]
  | some ctor =>
      have hctorArray :
          ctor.body.any stmtUsesArrayElement = false := by
        rw [← stmtListUsesArrayElement_eq_any]
        exact supportedStmtList_usesArrayElement_false
          (hSupported.constructor ctor hctor).stmtList_ctorBody
      simp [contractUsesArrayElement, hctor, constructorUsesArrayElement, hctorArray,
        hfunctionsAny]

theorem SupportedSpec.contractUsesStorageArrayElement_eq_false
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors) :
    contractUsesStorageArrayElement spec = false := by
  have hfunctions : ∀ fn ∈ spec.functions, functionUsesStorageArrayElement fn = false := by
    intro fn hmem
    simp only [functionUsesStorageArrayElement]
    rw [← stmtListUsesStorageArrayElement_eq_any]
    exact supportedStmtList_usesStorageArrayElement_false
      (hSupported.functions fn hmem).body.stmtList
  have hfunctionsAny : spec.functions.any functionUsesStorageArrayElement = false :=
    listAny_eq_false_of_mem_eq_false functionUsesStorageArrayElement spec.functions hfunctions
  cases hctor : spec.constructor with
  | none =>
      simp [contractUsesStorageArrayElement, hctor, constructorUsesStorageArrayElement,
        hfunctionsAny]
  | some ctor =>
      have hctorArray :
          ctor.body.any stmtUsesStorageArrayElement = false := by
        rw [← stmtListUsesStorageArrayElement_eq_any]
        exact supportedStmtList_usesStorageArrayElement_false
          (hSupported.constructor ctor hctor).stmtList_ctorBody
      simp [contractUsesStorageArrayElement, hctor, constructorUsesStorageArrayElement,
        hctorArray, hfunctionsAny]

theorem SupportedSpecExceptMappingWrites.contractUsesStorageArrayElement_eq_false
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors) :
    contractUsesStorageArrayElement spec = false := by
  have hfunctions : ∀ fn ∈ spec.functions, functionUsesStorageArrayElement fn = false := by
    intro fn hmem
    simp only [functionUsesStorageArrayElement]
    rw [← stmtListUsesStorageArrayElement_eq_any]
    exact supportedStmtList_usesStorageArrayElement_false
      (hSupported.functions fn hmem).body.stmtList
  have hfunctionsAny : spec.functions.any functionUsesStorageArrayElement = false :=
    listAny_eq_false_of_mem_eq_false functionUsesStorageArrayElement spec.functions hfunctions
  cases hctor : spec.constructor with
  | none =>
      simp [contractUsesStorageArrayElement, hctor, constructorUsesStorageArrayElement,
        hfunctionsAny]
  | some ctor =>
      have hctorArray :
          ctor.body.any stmtUsesStorageArrayElement = false := by
        rw [← stmtListUsesStorageArrayElement_eq_any]
        exact supportedStmtList_usesStorageArrayElement_false
          (hSupported.constructor ctor hctor).stmtList_ctorBody
      simp [contractUsesStorageArrayElement, hctor, constructorUsesStorageArrayElement,
        hctorArray, hfunctionsAny]

theorem SupportedSpec.contractUsesDynamicBytesEq_eq_false
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors) :
    contractUsesDynamicBytesEq spec = false := by
  have hfunctions : ∀ fn ∈ spec.functions, fn.body.any stmtUsesDynamicBytesEq = false := by
    intro fn hmem
    have := supportedStmtList_usesDynamicBytesEq_false
      (hSupported.functions fn hmem).body.stmtList
    rw [stmtListUsesDynamicBytesEq_eq_any] at this
    simpa using this
  have hfunctionsAny :
      spec.functions.any (fun fn => fn.body.any stmtUsesDynamicBytesEq) = false :=
    listAny_eq_false_of_mem_eq_false
      (fun fn => fn.body.any stmtUsesDynamicBytesEq) spec.functions hfunctions
  cases hctor : spec.constructor with
  | none =>
      simp [contractUsesDynamicBytesEq, hctor, hfunctionsAny]
  | some ctor =>
      have hctorDynamic :
          ctor.body.any stmtUsesDynamicBytesEq = false := by
        have := supportedStmtList_usesDynamicBytesEq_false
          (hSupported.constructor ctor hctor).stmtList_ctorBody
        rw [stmtListUsesDynamicBytesEq_eq_any] at this
        simpa using this
      simp [contractUsesDynamicBytesEq, hctor, hctorDynamic, hfunctionsAny]

theorem SupportedSpecExceptMappingWrites.contractUsesDynamicBytesEq_eq_false
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors) :
    contractUsesDynamicBytesEq spec = false := by
  have hfunctions : ∀ fn ∈ spec.functions, fn.body.any stmtUsesDynamicBytesEq = false := by
    intro fn hmem
    have := supportedStmtList_usesDynamicBytesEq_false
      (hSupported.functions fn hmem).body.stmtList
    rw [stmtListUsesDynamicBytesEq_eq_any] at this
    simpa using this
  have hfunctionsAny :
      spec.functions.any (fun fn => fn.body.any stmtUsesDynamicBytesEq) = false :=
    listAny_eq_false_of_mem_eq_false
      (fun fn => fn.body.any stmtUsesDynamicBytesEq) spec.functions hfunctions
  cases hctor : spec.constructor with
  | none =>
      simp [contractUsesDynamicBytesEq, hctor, hfunctionsAny]
  | some ctor =>
      have hctorDynamic :
          ctor.body.any stmtUsesDynamicBytesEq = false := by
        have := supportedStmtList_usesDynamicBytesEq_false
          (hSupported.constructor ctor hctor).stmtList_ctorBody
        rw [stmtListUsesDynamicBytesEq_eq_any] at this
        simpa using this
      simp [contractUsesDynamicBytesEq, hctor, hctorDynamic, hfunctionsAny]


theorem SupportedSpec.normalizedFields
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors) :
    applySlotAliasRanges spec.fields spec.slotAliasRanges = spec.fields :=
  hSupported.invariants.normalizedFields

theorem SupportedSpecExceptMappingWrites.normalizedFields
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors) :
    applySlotAliasRanges spec.fields spec.slotAliasRanges = spec.fields :=
  hSupported.invariants.normalizedFields

theorem SupportedSpecWithScalarEvents.normalizedFields
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecWithScalarEvents spec selectors) :
    applySlotAliasRanges spec.fields spec.slotAliasRanges = spec.fields :=
  hSupported.invariants.normalizedFields

theorem SupportedSpec.noPackedFields
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors) :
    ∀ field ∈ spec.fields, field.packedBits = none :=
  hSupported.invariants.noPackedFields

theorem SupportedSpecExceptMappingWrites.noPackedFields
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors) :
    ∀ field ∈ spec.fields, field.packedBits = none :=
  hSupported.invariants.noPackedFields

theorem SupportedSpecWithScalarEvents.noPackedFields
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecWithScalarEvents spec selectors) :
    ∀ field ∈ spec.fields, field.packedBits = none :=
  hSupported.invariants.noPackedFields

theorem SupportedSpec.selectorCount
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors) :
    selectors.length = (selectorDispatchedFunctions spec).length :=
  hSupported.invariants.selectorCount

theorem SupportedSpecExceptMappingWrites.selectorCount
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors) :
    selectors.length = (selectorDispatchedFunctions spec).length :=
  hSupported.invariants.selectorCount

theorem SupportedSpec.selectorsDistinct
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors) :
    firstDuplicateSelector selectors = none :=
  hSupported.invariants.selectorsDistinct

theorem SupportedSpecExceptMappingWrites.selectorsDistinct
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors) :
    firstDuplicateSelector selectors = none :=
  hSupported.invariants.selectorsDistinct

theorem SupportedSpec.functionNamesNodup
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors) :
    (spec.functions.map (·.name)).Nodup :=
  hSupported.invariants.functionNamesNodup

theorem SupportedSpecExceptMappingWrites.functionNamesNodup
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors) :
    (spec.functions.map (·.name)).Nodup :=
  hSupported.invariants.functionNamesNodup

theorem SupportedSpec.noEvents
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors) :
    spec.events = [] :=
  hSupported.surface.noEvents

theorem SupportedSpecExceptMappingWrites.noEvents
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors) :
    spec.events = [] :=
  hSupported.surface.noEvents

theorem SupportedSpec.noErrors
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors) :
    spec.errors = [] :=
  hSupported.surface.noErrors

theorem SupportedSpecExceptMappingWrites.noErrors
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors) :
    spec.errors = [] :=
  hSupported.surface.noErrors

theorem SupportedSpecWithScalarEvents.noErrors
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecWithScalarEvents spec selectors) :
    spec.errors = [] :=
  hSupported.surface.noErrors

theorem SupportedSpec.noExternals
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors) :
    spec.externals = [] :=
  hSupported.surface.noExternals

theorem SupportedSpecExceptMappingWrites.noExternals
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors) :
    spec.externals = [] :=
  hSupported.surface.noExternals

theorem SupportedSpecWithScalarEvents.noExternals
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecWithScalarEvents spec selectors) :
    spec.externals = [] :=
  hSupported.surface.noExternals

theorem SupportedSpec.noAdtTypes
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors) :
    spec.adtTypes = [] :=
  hSupported.surface.noAdtTypes

theorem SupportedSpec.noCheckedArithmetic
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors) :
    contractUsesCheckedArithmetic spec = false :=
  hSupported.surface.noCheckedArithmetic

theorem SupportedSpecExceptMappingWrites.noAdtTypes
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors) :
    spec.adtTypes = [] :=
  hSupported.surface.noAdtTypes

theorem SupportedSpecExceptMappingWrites.noCheckedArithmetic
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors) :
    contractUsesCheckedArithmetic spec = false :=
  hSupported.surface.noCheckedArithmetic

theorem SupportedSpecWithScalarEvents.noAdtTypes
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecWithScalarEvents spec selectors) :
    spec.adtTypes = [] :=
  hSupported.surface.noAdtTypes

theorem SupportedSpecWithScalarEvents.noCheckedArithmetic
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecWithScalarEvents spec selectors) :
    contractUsesCheckedArithmetic spec = false :=
  hSupported.surface.noCheckedArithmetic

theorem SupportedSpec.noFallback
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors) :
    ∀ fn ∈ spec.functions, fn.name != "fallback" :=
  hSupported.surface.noFallback

theorem SupportedSpecExceptMappingWrites.noFallback
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors) :
    ∀ fn ∈ spec.functions, fn.name != "fallback" :=
  hSupported.surface.noFallback

theorem SupportedSpec.noReceive
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors) :
    ∀ fn ∈ spec.functions, fn.name != "receive" :=
  hSupported.surface.noReceive

theorem SupportedSpecExceptMappingWrites.noReceive
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors) :
    ∀ fn ∈ spec.functions, fn.name != "receive" :=
  hSupported.surface.noReceive

def SupportedSpec.supportedFunctionOfSelectorDispatched
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors)
    {fn : FunctionSpec}
    (hfn : fn ∈ selectorDispatchedFunctions spec) :
    SupportedFunction spec fn :=
  hSupported.functions fn ((List.mem_filter.mp hfn).1)

def SupportedSpecWithHelpers.supportedFunctionOfSelectorDispatched
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecWithHelpers spec selectors)
    {fn : FunctionSpec}
    (hfn : fn ∈ selectorDispatchedFunctions spec) :
    SupportedFunctionWithHelpers spec fn :=
  hSupported.functions fn ((List.mem_filter.mp hfn).1)

def SupportedSpecExceptMappingWrites.supportedFunctionOfSelectorDispatched
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors)
    {fn : FunctionSpec}
    (hfn : fn ∈ selectorDispatchedFunctions spec) :
    SupportedFunctionExceptMappingWrites spec fn :=
  hSupported.functions fn ((List.mem_filter.mp hfn).1)

def SupportedSpecWithScalarEvents.supportedFunctionOfSelectorDispatched
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecWithScalarEvents spec selectors)
    {fn : FunctionSpec}
    (hfn : fn ∈ selectorDispatchedFunctions spec) :
    SupportedFunctionWithScalarEvents spec fn :=
  hSupported.functions fn ((List.mem_filter.mp hfn).1)

noncomputable def SupportedSpec.helperFuelOfFunction
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors)
    (fn : FunctionSpec) : Nat :=
  open Classical in
  if hfn : fn ∈ selectorDispatchedFunctions spec then
    (hSupported.supportedFunctionOfSelectorDispatched hfn).helperFuel
  else
    0

noncomputable def SupportedSpecWithHelpers.helperFuelOfFunction
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecWithHelpers spec selectors)
    (fn : FunctionSpec) : Nat :=
  open Classical in
  if hfn : fn ∈ selectorDispatchedFunctions spec then
    (hSupported.supportedFunctionOfSelectorDispatched hfn).helperFuel
  else
    0

noncomputable def SupportedSpecExceptMappingWrites.helperFuelOfFunction
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors)
    (fn : FunctionSpec) : Nat :=
  open Classical in
  if hfn : fn ∈ selectorDispatchedFunctions spec then
    (hSupported.supportedFunctionOfSelectorDispatched hfn).helperFuel
  else
    0

noncomputable def SupportedSpecWithScalarEvents.helperFuelOfFunction
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecWithScalarEvents spec selectors)
    (fn : FunctionSpec) : Nat :=
  open Classical in
  if hfn : fn ∈ selectorDispatchedFunctions spec then
    (hSupported.supportedFunctionOfSelectorDispatched hfn).helperFuel
  else
    0


noncomputable def SupportedSpec.helperFuel
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors) : Nat :=
  (selectorDispatchedFunctions spec).foldl
    (fun fuel fn => max fuel (hSupported.helperFuelOfFunction fn))
    0

noncomputable def SupportedSpecWithHelpers.helperFuel
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecWithHelpers spec selectors) : Nat :=
  (selectorDispatchedFunctions spec).foldl
    (fun fuel fn => max fuel (hSupported.helperFuelOfFunction fn))
    0

noncomputable def SupportedSpecExceptMappingWrites.helperFuel
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors) : Nat :=
  (selectorDispatchedFunctions spec).foldl
    (fun fuel fn => max fuel (hSupported.helperFuelOfFunction fn))
    0

noncomputable def SupportedSpecWithScalarEvents.helperFuel
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecWithScalarEvents spec selectors) : Nat :=
  (selectorDispatchedFunctions spec).foldl
    (fun fuel fn => max fuel (hSupported.helperFuelOfFunction fn))
    0

theorem SupportedSpec.selectorFunctionParamsSupported
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors)
    {fn : FunctionSpec}
    (hfn : fn ∈ selectorDispatchedFunctions spec) :
    ∀ param ∈ fn.params, SupportedExternalScalarParamType param.ty :=
  (hSupported.supportedFunctionOfSelectorDispatched hfn).params.supported

theorem SupportedSpecWithHelpers.selectorFunctionParamsSupported
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecWithHelpers spec selectors)
    {fn : FunctionSpec}
    (hfn : fn ∈ selectorDispatchedFunctions spec) :
    ∀ param ∈ fn.params, SupportedExternalScalarParamType param.ty :=
  (hSupported.supportedFunctionOfSelectorDispatched hfn).params.supported

theorem SupportedSpec.selectorFunctionParamCalldataThreshold
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors)
    {fn : FunctionSpec}
    (hfn : fn ∈ selectorDispatchedFunctions spec) :
    4 + fn.params.length * 32 < Compiler.Constants.evmModulus :=
  (hSupported.supportedFunctionOfSelectorDispatched hfn).params.calldataThreshold

theorem SupportedSpecExceptMappingWrites.selectorFunctionParamsSupported
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors)
    {fn : FunctionSpec}
    (hfn : fn ∈ selectorDispatchedFunctions spec) :
    ∀ param ∈ fn.params, SupportedExternalScalarParamType param.ty :=
  (hSupported.supportedFunctionOfSelectorDispatched hfn).params.supported

theorem SupportedSpecExceptMappingWrites.selectorFunctionParamCalldataThreshold
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors)
    {fn : FunctionSpec}
    (hfn : fn ∈ selectorDispatchedFunctions spec) :
    4 + fn.params.length * 32 < Compiler.Constants.evmModulus :=
  (hSupported.supportedFunctionOfSelectorDispatched hfn).params.calldataThreshold

theorem SupportedSpecWithScalarEvents.selectorFunctionParamsSupported
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecWithScalarEvents spec selectors)
    {fn : FunctionSpec}
    (hfn : fn ∈ selectorDispatchedFunctions spec) :
    ∀ param ∈ fn.params, SupportedExternalScalarParamType param.ty :=
  (hSupported.supportedFunctionOfSelectorDispatched hfn).params.supported

theorem SupportedSpecWithScalarEvents.selectorFunctionParamCalldataThreshold
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecWithScalarEvents spec selectors)
    {fn : FunctionSpec}
    (hfn : fn ∈ selectorDispatchedFunctions spec) :
    4 + fn.params.length * 32 < Compiler.Constants.evmModulus :=
  (hSupported.supportedFunctionOfSelectorDispatched hfn).params.calldataThreshold

theorem SupportedSpec.selectorFunctionParamNamesNodup
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors)
    {fn : FunctionSpec}
    (hfn : fn ∈ selectorDispatchedFunctions spec) :
    (fn.params.map (·.name)).Nodup :=
  (hSupported.supportedFunctionOfSelectorDispatched hfn).params.namesNodup

theorem SupportedSpecExceptMappingWrites.selectorFunctionParamNamesNodup
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors)
    {fn : FunctionSpec}
    (hfn : fn ∈ selectorDispatchedFunctions spec) :
    (fn.params.map (·.name)).Nodup :=
  (hSupported.supportedFunctionOfSelectorDispatched hfn).params.namesNodup

theorem SupportedSpecWithScalarEvents.selectorFunctionParamNamesNodup
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecWithScalarEvents spec selectors)
    {fn : FunctionSpec}
    (hfn : fn ∈ selectorDispatchedFunctions spec) :
    (fn.params.map (·.name)).Nodup :=
  (hSupported.supportedFunctionOfSelectorDispatched hfn).params.namesNodup

theorem SupportedSpec.selectorFunctionReturnsSupported
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors)
    {fn : FunctionSpec}
    (hfn : fn ∈ selectorDispatchedFunctions spec) :
    ∃ resolvedReturns,
      functionReturns fn = Except.ok resolvedReturns ∧
        SupportedExternalReturnProfile resolvedReturns :=
  (hSupported.supportedFunctionOfSelectorDispatched hfn).returns.resolved

theorem SupportedSpecExceptMappingWrites.selectorFunctionReturnsSupported
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors)
    {fn : FunctionSpec}
    (hfn : fn ∈ selectorDispatchedFunctions spec) :
    ∃ resolvedReturns,
      functionReturns fn = Except.ok resolvedReturns ∧
        SupportedExternalReturnProfile resolvedReturns :=
  (hSupported.supportedFunctionOfSelectorDispatched hfn).returns.resolved

theorem SupportedSpecWithScalarEvents.selectorFunctionReturnsSupported
    {spec : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecWithScalarEvents spec selectors)
    {fn : FunctionSpec}
    (hfn : fn ∈ selectorDispatchedFunctions spec) :
    ∃ resolvedReturns,
      functionReturns fn = Except.ok resolvedReturns ∧
        SupportedExternalReturnProfile resolvedReturns :=
  (hSupported.supportedFunctionOfSelectorDispatched hfn).returns.resolved


def counterSupportedSpecModel : CompilationModel :=
  { name := "Counter"
    fields := []
    constructor := none
    functions :=
      [ { name := "getCount"
          params := []
          returnType := some .uint256
          body := [Stmt.return (Expr.literal 42)] } ] }

private theorem counter_noPackedFields :
    ∀ field ∈ counterSupportedSpecModel.fields, field.packedBits = none := by
  intro field hfield
  simp [counterSupportedSpecModel] at hfield

private theorem counter_noFallback :
    ∀ fn ∈ counterSupportedSpecModel.functions, fn.name != "fallback" := by
  intro fn hfn
  simp [counterSupportedSpecModel] at hfn
  (rcases hfn with rfl; decide)

private theorem counter_noReceive :
    ∀ fn ∈ counterSupportedSpecModel.functions, fn.name != "receive" := by
  intro fn hfn
  simp [counterSupportedSpecModel] at hfn
  (rcases hfn with rfl; decide)

private def counter_supported_function :
    ∀ fn, fn ∈ counterSupportedSpecModel.functions →
      SupportedFunction counterSupportedSpecModel fn := by
  intro fn hfn
  simp [counterSupportedSpecModel] at hfn
  rcases hfn with rfl
  exact
    { nonInternal := rfl
      nonSpecialEntrypoint := rfl
      standardAbi := rfl
      noNonReentrant := rfl
      params :=
        { namesNodup := by decide
          supported := by intro param hparam; cases hparam
          calldataThreshold := by decide }
      returns := { resolved := ⟨[.uint256], rfl, trivial⟩ }
      body :=
        { stmtList := .terminalCore (.return_ (.literal 42) (by simp [FunctionBody.exprBoundNamesInScope, FunctionBody.exprBoundNames]) .nil)
          core := { surfaceClosed := by decide }
          state := { surfaceClosed := by decide }
          calls :=
            { helpers :=
                { helperRank := 0
                  callNamesNodup := helperCallNames_nodup _
                  summaryOf := by
                    intro calleeName hmem
                    simp [helperCallNames, stmtListInternalHelperCallNames, stmtInternalHelperCallNames, exprInternalHelperCallNames] at hmem
                  calleeRanksDecrease := by
                    intro calleeName hmem
                    simp [helperCallNames, stmtListInternalHelperCallNames, stmtInternalHelperCallNames, exprInternalHelperCallNames] at hmem
                  exprCallsPreserveWorld := by
                    intro calleeName hmem
                    simp [exprHelperCallNames, stmtListExprHelperCallNames, stmtExprHelperCallNames, exprInternalHelperCallNames] at hmem }
              foreign := by decide
              lowLevel := by decide }
          effects := { surfaceClosed := by decide }
          noLocalObligations := rfl } }

def counter_supported_spec : SupportedSpec counterSupportedSpecModel
    [0xa87d942c] :=
  { invariants :=
      { normalizedFields := rfl
        noPackedFields := counter_noPackedFields
        selectorCount := by decide
        selectorsDistinct := by decide
        functionNamesNodup := by decide }
    surface :=
      { noEvents := rfl
        noErrors := rfl
        noExternals := rfl
        noAdtTypes := rfl
        noCheckedArithmetic := by
          simp [contractUsesCheckedArithmetic, counterSupportedSpecModel,
            stmtListMayUseCheckedArithmetic, stmtMayUseCheckedArithmetic]
        noTemplateIntrinsics := by
          rw [templateIntrinsicItems, counterSupportedSpecModel]
          simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
          unfold collectTemplateIntrinsicsFromStmts
          simp only [List.flatMap_cons, List.flatMap_nil]
          rw [collectTemplateIntrinsicsFromStmt.eq_def]
          simp only [Stmt.directMetadata, Stmt.childLists, List.attach_nil,
            List.flatMap_nil, List.append_nil]
          simp only [List.flatMap_cons, List.flatMap_nil]
          rw [collectTemplateIntrinsicsFromExpr.eq_def]
          rfl
        noFallback := counter_noFallback
        noReceive := counter_noReceive }
    constructor := by
      intro ctor hctor
      simp [counterSupportedSpecModel] at hctor
    functions := counter_supported_function }


def simpleStorageSupportedSpecModel : CompilationModel :=
  { name := "SimpleStorage"
    fields := []
    constructor := none
    functions :=
      [ { name := "retrieve"
          params := []
          returnType := some .uint256
          body := [Stmt.return (Expr.literal 11)] } ] }

private theorem simpleStorage_noPackedFields :
    ∀ field ∈ simpleStorageSupportedSpecModel.fields, field.packedBits = none := by
  intro field hfield
  simp [simpleStorageSupportedSpecModel] at hfield

private theorem simpleStorage_noFallback :
    ∀ fn ∈ simpleStorageSupportedSpecModel.functions, fn.name != "fallback" := by
  intro fn hfn
  simp [simpleStorageSupportedSpecModel] at hfn
  (rcases hfn with rfl; decide)

private theorem simpleStorage_noReceive :
    ∀ fn ∈ simpleStorageSupportedSpecModel.functions, fn.name != "receive" := by
  intro fn hfn
  simp [simpleStorageSupportedSpecModel] at hfn
  (rcases hfn with rfl; decide)

private def simpleStorage_supported_function :
    ∀ fn, fn ∈ simpleStorageSupportedSpecModel.functions →
      SupportedFunction simpleStorageSupportedSpecModel fn := by
  intro fn hfn
  simp [simpleStorageSupportedSpecModel] at hfn
  rcases hfn with rfl
  exact
    { nonInternal := rfl
      nonSpecialEntrypoint := rfl
      standardAbi := rfl
      noNonReentrant := rfl
      params :=
        { namesNodup := by decide
          supported := by intro param hparam; cases hparam
          calldataThreshold := by decide }
      returns := { resolved := ⟨[.uint256], rfl, trivial⟩ }
      body :=
        { stmtList := .terminalCore (.return_ (.literal 11) (by simp [FunctionBody.exprBoundNamesInScope, FunctionBody.exprBoundNames]) .nil)
          core := { surfaceClosed := by decide }
          state := { surfaceClosed := by decide }
          calls :=
            { helpers :=
                { helperRank := 0
                  callNamesNodup := helperCallNames_nodup _
                  summaryOf := by
                    intro calleeName hmem
                    simp [helperCallNames, stmtListInternalHelperCallNames, stmtInternalHelperCallNames, exprInternalHelperCallNames] at hmem
                  calleeRanksDecrease := by
                    intro calleeName hmem
                    simp [helperCallNames, stmtListInternalHelperCallNames, stmtInternalHelperCallNames, exprInternalHelperCallNames] at hmem
                  exprCallsPreserveWorld := by
                    intro calleeName hmem
                    simp [exprHelperCallNames, stmtListExprHelperCallNames, stmtExprHelperCallNames, exprInternalHelperCallNames] at hmem }
              foreign := by decide
              lowLevel := by decide }
          effects := { surfaceClosed := by decide }
          noLocalObligations := rfl } }

def simpleStorage_supported_spec : SupportedSpec simpleStorageSupportedSpecModel
    [0x2e64cec1] :=
  { invariants :=
      { normalizedFields := rfl
        noPackedFields := simpleStorage_noPackedFields
        selectorCount := by decide
        selectorsDistinct := by decide
        functionNamesNodup := by decide }
    surface :=
      { noEvents := rfl
        noErrors := rfl
        noExternals := rfl
        noAdtTypes := rfl
        noCheckedArithmetic := by
          simp [contractUsesCheckedArithmetic, simpleStorageSupportedSpecModel,
            stmtListMayUseCheckedArithmetic, stmtMayUseCheckedArithmetic]
        noTemplateIntrinsics := by
          rw [templateIntrinsicItems, simpleStorageSupportedSpecModel]
          simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
          unfold collectTemplateIntrinsicsFromStmts
          simp only [List.flatMap_cons, List.flatMap_nil]
          rw [collectTemplateIntrinsicsFromStmt.eq_def]
          simp only [Stmt.directMetadata, Stmt.childLists, List.attach_nil,
            List.flatMap_nil, List.append_nil]
          simp only [List.flatMap_cons, List.flatMap_nil]
          rw [collectTemplateIntrinsicsFromExpr.eq_def]
          rfl
        noFallback := simpleStorage_noFallback
        noReceive := simpleStorage_noReceive }
    constructor := by
      intro ctor hctor
      simp [simpleStorageSupportedSpecModel] at hctor
    functions := simpleStorage_supported_function }


end Compiler.Proofs.IRGeneration

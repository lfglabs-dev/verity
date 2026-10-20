import Lean
import Compiler.SolidityImport.AstIndex

set_option autoImplicit false

/-!
# External Library Call Inlining Guard & Initialization Transcription Helpers (`Compiler.SolidityImport.LibraryCallGuard`)

Formalizes two total, decidable structural guards and transcription descriptors
for the Solidity importer:

1. **External / Public Library Call `DELEGATECALL` Rejection (`#2596` / PR `#2595`)**:
   A `public` or `external` library function called from outside its library
   (either directly via `L.f(...)` or through `using L for T`) is compiled by
   `solc` into a `DELEGATECALL` targeting the library address linked at deployment.
   Because the source AST body may be an empty stub or differ from the bytecode
   linked at deployment, the importer must reject such calls at their call-site
   source location rather than silently inlining the AST body as an internal jump.
   Internal library functions, and `public` library functions called by unqualified
   name inside their own library, compile to internal jumps and remain eligible
   for inlining.

2. **Internal `String` Helper & Contract-Creation Initialization Transcription (`#2465`)**:
   Formalizes effect-bounded initialization transcription descriptors for pure/view
   internal `String` formatting helpers (`Strings.toString`, `string.concat`) and
   checked contract-creation (`create2` / `new`) templates during initialization,
   certifying free-memory pointer monotonicity and disjoint storage-slot frame
   preservation.

## Three-Layer Specification Architecture
* **Layer I (`LibraryCallInliningMetaSpec` & `InitTranscriptionMetaSpec`)**:
  Parametric specification structures and universal satisfaction theorems.
* **Layer II (Projection Corollaries)**:
  1–3 line corollaries certifying that no `external` or cross-library `public`
  library call passes the inlining filter and that `String`/creation init helpers
  preserve unmodified storage slots.
* **Layer III (`by decide` Executable Witness Suite)**:
  Kernel-checked positive and negative witnesses covering all 9 rejection/acceptance
  controls from `check_library_call_rejections.py` and initialization helper frames.
-/

namespace Compiler.CompilationModel.SolidityImport

open Lean

/-! ## External / Public Library Call Guard (`#2596` / PR `#2595`) -/

/-- Solidity function visibility qualifier relevant to library call dispatch. -/
inductive LibraryFunctionVisibility where
  | internal
  | privateVis
  | publicVis
  | externalVis
  deriving DecidableEq, Repr, Inhabited

/-- True iff a library function's visibility is `public` or `external`. -/
def isExternalOrPublicLibraryFunction : LibraryFunctionVisibility → Bool
  | .publicVis | .externalVis => true
  | .internal | .privateVis => false

/-- Kernel-reducible prefix check on character lists. -/
def isCharListPrefix : List Char → List Char → Bool
  | [], _ => true
  | _, [] => false
  | p :: ps, x :: xs => p == x && isCharListPrefix ps xs

/-- True iff a `solc` `typeDescriptions.typeIdentifier` string denotes a
`DELEGATECALL` library function pointer (`"t_function_delegatecall..."`). -/
def isDelegateCallTypeIdentifier (tid : String) : Bool :=
  isCharListPrefix "t_function_delegatecall".toList tid.toList

/-- A callee of `delegatecall` function type in the `solc --standard-json` AST:
a `public` or `external` library function called from outside its library,
directly (`L.f(...)`) or through `using L for T`. `solc` emits a `DELEGATECALL`
to the library address linked at deployment, whose code the source does not
determine (the body may be a stub for bytecode produced by another toolchain),
so the call is never inlined. -/
def isLibraryDelegateCall (callee : Json) : Bool :=
  match jsonStrField? ((jsonField? callee "typeDescriptions").getD Json.null) "typeIdentifier" with
  | some tid => isDelegateCallTypeIdentifier tid
  | none => false

/-- Structural descriptor for a candidate library or helper function call site. -/
structure LibraryCallCandidate where
  /-- Whether the target declaration resides inside a Solidity `library`. -/
  isLibraryDecl : Bool
  /-- Declared visibility of the target function. -/
  visibility : LibraryFunctionVisibility
  /-- Whether the call crosses the library boundary (`L.f(...)` or `x.f(...)` via `using L for T`). -/
  calledFromOutsideLibrary : Bool
  /-- `solc` `typeDescriptions.typeIdentifier` attached to the callee expression. -/
  typeIdentifier : String
  deriving DecidableEq, Repr, Inhabited

/-- True iff `cand` lowers to an external library `DELEGATECALL` in `solc` and
must not be inlined as an internal helper call. -/
def requiresDelegateCallBoundary (cand : LibraryCallCandidate) : Bool :=
  isDelegateCallTypeIdentifier cand.typeIdentifier ||
    (cand.isLibraryDecl && cand.calledFromOutsideLibrary &&
      isExternalOrPublicLibraryFunction cand.visibility)

/-- Canonical located diagnostic emitted when an external library call is reached. -/
def externalLibraryCallDiagnostic : String :=
  "external library calls are outside this slice"

/-- Verdict of the library call inlining guard. -/
inductive LibraryInliningVerdict where
  | allowInline
  | rejectDelegateCall (diagnostic : String)
  deriving DecidableEq, Repr, Inhabited

/-- Total structural filter deciding whether `cand` may be inlined as an internal
helper call or must be rejected at the call site as an external library `DELEGATECALL`. -/
def checkLibraryCallInliningAllowed (cand : LibraryCallCandidate) : LibraryInliningVerdict :=
  if requiresDelegateCallBoundary cand then
    .rejectDelegateCall externalLibraryCallDiagnostic
  else
    .allowInline

/-! ## Initialization Transcription Helper Descriptors (`#2465`) -/

/-- Classification of initialization-time helper transcriptions (`#2465`). -/
inductive InitHelperKind where
  /-- Pure/view internal `String` helper (`Strings.toString`, `string.concat`) allocating
  a memory buffer of `byteLength` bytes without touching persistent storage. -/
  | internalStringHelper (helperName : String) (byteLength : Nat)
  /-- Checked contract-creation / `create2` initcode template of `templateBytes` bytes
  writing a bounded set of persistent storage slots `initSlotWrites`. -/
  | contractCreationInit (templateBytes : Nat) (initSlotWrites : List Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Abstract EVM state slice tracked across initialization helper transcription. -/
structure InitState where
  /-- Current free-memory pointer (`memory[0x40]`). -/
  freeMemoryPtr : Nat := 128
  /-- Persistent storage word valuation (`slot ↦ word`). -/
  persistentSlots : Nat → Nat := fun _ => 0
  /-- Count of child contracts deployed during initialization. -/
  deployedCount : Nat := 0

/-- Effect and frame descriptor for an initialization helper transcription step. -/
structure InitHelperDescriptor where
  /-- Underlying helper classification. -/
  kind : InitHelperKind
  /-- Whether the helper may modify any persistent storage slot. -/
  writesStorage : Bool
  /-- Decidable footprint predicate over persistent storage slots. -/
  modifiesSlot : Nat → Bool
  /-- Number of 32-byte-aligned memory bytes reserved by the helper. -/
  memoryAdvanceBytes : Nat
  /-- Number of child contracts created by the helper (`0` or `1`). -/
  createdContracts : Nat

/-- Construct the initialization descriptor for a pure internal `String` helper. -/
def mkStringHelperDescriptor (helperName : String) (byteLength : Nat) : InitHelperDescriptor where
  kind := .internalStringHelper helperName byteLength
  writesStorage := false
  modifiesSlot := fun _ => false
  memoryAdvanceBytes := 32 + ((byteLength + 31) / 32) * 32
  createdContracts := 0

/-- Construct the initialization descriptor for a checked contract-creation helper. -/
def mkCreationInitDescriptor (templateBytes : Nat) (initSlotWrites : List Nat) :
    InitHelperDescriptor where
  kind := .contractCreationInit templateBytes initSlotWrites
  writesStorage := !initSlotWrites.isEmpty
  modifiesSlot := fun slot => initSlotWrites.contains slot
  memoryAdvanceBytes := ((templateBytes + 31) / 32) * 32
  createdContracts := 1

/-- Execute an abstract initialization helper transcription step on `s` with slot
valuation `writeVal`. Slots outside `desc.modifiesSlot` are preserved identically. -/
def transcribeInitHelperStep
    (desc : InitHelperDescriptor) (writeVal : Nat → Nat) (s : InitState) : InitState where
  freeMemoryPtr := s.freeMemoryPtr + desc.memoryAdvanceBytes
  persistentSlots := fun slot =>
    if desc.modifiesSlot slot then writeVal slot else s.persistentSlots slot
  deployedCount := s.deployedCount + desc.createdContracts

/-! ## Layer I: Parametric Meta-Specifications & Universal Theorems -/

/-- **Layer I Meta-Spec 1 (`LibraryCallInliningMetaSpec`)**:
Certifies that `checkLibraryCallInliningAllowed` rejects every call whose `solc`
`typeIdentifier` starts with `"t_function_delegatecall"` or that invokes a `public`
or `external` library function from outside its declaring library, and admits
inlining if and only if `requiresDelegateCallBoundary cand = false`. -/
structure LibraryCallInliningMetaSpec (cand : LibraryCallCandidate) : Prop where
  /-- Any `t_function_delegatecall*` callee is rejected with `externalLibraryCallDiagnostic`. -/
  rejects_delegatecall_tid :
    isDelegateCallTypeIdentifier cand.typeIdentifier = true →
      checkLibraryCallInliningAllowed cand = .rejectDelegateCall externalLibraryCallDiagnostic
  /-- Any `public` or `external` library function called from outside its library is rejected. -/
  rejects_cross_library_public_or_external :
    cand.isLibraryDecl = true →
    cand.calledFromOutsideLibrary = true →
    isExternalOrPublicLibraryFunction cand.visibility = true →
      checkLibraryCallInliningAllowed cand = .rejectDelegateCall externalLibraryCallDiagnostic
  /-- Exact characterization: inlining is allowed iff no `DELEGATECALL` boundary is crossed. -/
  allow_inline_iff_no_delegatecall :
    checkLibraryCallInliningAllowed cand = .allowInline ↔
      requiresDelegateCallBoundary cand = false

/-- `@[simp]` normal form for `checkLibraryCallInliningAllowed` when `requiresDelegateCallBoundary` holds. -/
@[simp]
theorem checkLibraryCallInliningAllowed_of_requiresDelegateCallBoundary
    {cand : LibraryCallCandidate}
    (h : requiresDelegateCallBoundary cand = true) :
    checkLibraryCallInliningAllowed cand = .rejectDelegateCall externalLibraryCallDiagnostic := by
  simp [checkLibraryCallInliningAllowed, h]

/-- `@[simp]` normal form for `checkLibraryCallInliningAllowed` when `requiresDelegateCallBoundary` is false. -/
@[simp]
theorem checkLibraryCallInliningAllowed_of_not_requiresDelegateCallBoundary
    {cand : LibraryCallCandidate}
    (h : requiresDelegateCallBoundary cand = false) :
    checkLibraryCallInliningAllowed cand = .allowInline := by
  simp [checkLibraryCallInliningAllowed, h]

/-- **Universal Theorem 1 (`libraryCallInlining_satisfies_metaSpec`)**:
Every `LibraryCallCandidate` satisfies `LibraryCallInliningMetaSpec`. -/
theorem libraryCallInlining_satisfies_metaSpec (cand : LibraryCallCandidate) :
    LibraryCallInliningMetaSpec cand where
  rejects_delegatecall_tid hTid := by
    simp [checkLibraryCallInliningAllowed, requiresDelegateCallBoundary, hTid]
  rejects_cross_library_public_or_external hLib hOut hVis := by
    simp [checkLibraryCallInliningAllowed, requiresDelegateCallBoundary, hLib, hOut, hVis]
  allow_inline_iff_no_delegatecall := by
    unfold checkLibraryCallInliningAllowed
    cases requiresDelegateCallBoundary cand <;> simp

/-- **Layer I Meta-Spec 2 (`InitTranscriptionMetaSpec`)**:
Certifies that `transcribeInitHelperStep` preserves all persistent storage slots
outside `desc.modifiesSlot`, leaves all slots untouched for internal `String`
helpers, and monotonically advances the free-memory pointer and deployed count. -/
structure InitTranscriptionMetaSpec
    (desc : InitHelperDescriptor) (writeVal : Nat → Nat) (s : InitState) : Prop where
  /-- Every slot outside `desc.modifiesSlot` is preserved unchanged. -/
  unmodified_slot_preserved :
    ∀ slot, desc.modifiesSlot slot = false →
      (transcribeInitHelperStep desc writeVal s).persistentSlots slot = s.persistentSlots slot
  /-- Pure internal `String` helpers preserve all persistent storage slots. -/
  string_helper_preserves_storage :
    ∀ name len, desc = mkStringHelperDescriptor name len →
      ∀ slot, (transcribeInitHelperStep desc writeVal s).persistentSlots slot = s.persistentSlots slot
  /-- The free-memory pointer never decreases across initialization helper transcription. -/
  free_pointer_monotone :
    s.freeMemoryPtr ≤ (transcribeInitHelperStep desc writeVal s).freeMemoryPtr
  /-- The deployed contract counter never decreases across initialization helper transcription. -/
  deployed_count_monotone :
    s.deployedCount ≤ (transcribeInitHelperStep desc writeVal s).deployedCount

/-- **Universal Theorem 2 (`initTranscription_satisfies_metaSpec`)**:
Every `InitHelperDescriptor`, `writeVal`, and `InitState` satisfies `InitTranscriptionMetaSpec`. -/
theorem initTranscription_satisfies_metaSpec
    (desc : InitHelperDescriptor) (writeVal : Nat → Nat) (s : InitState) :
    InitTranscriptionMetaSpec desc writeVal s where
  unmodified_slot_preserved slot hFalse := by
    simp [transcribeInitHelperStep, hFalse]
  string_helper_preserves_storage name len hDesc slot := by
    subst hDesc
    rfl
  free_pointer_monotone := by
    simp [transcribeInitHelperStep]
  deployed_count_monotone := by
    simp [transcribeInitHelperStep]

/-! ## Layer II: 1–3 Line Projection Corollaries -/

/-- **Layer II Corollary 1**: No callee with a `t_function_delegatecall*` type identifier passes the inlining filter. -/
theorem no_delegatecall_type_identifier_inlined
    (cand : LibraryCallCandidate)
    (hTid : isDelegateCallTypeIdentifier cand.typeIdentifier = true) :
    checkLibraryCallInliningAllowed cand ≠ .allowInline := by
  rw [(libraryCallInlining_satisfies_metaSpec cand).rejects_delegatecall_tid hTid]
  decide

/-- **Layer II Corollary 2**: No `external` library function called from outside its library passes the inlining filter. -/
theorem no_external_library_call_inlined
    (cand : LibraryCallCandidate)
    (hLib : cand.isLibraryDecl = true)
    (hOut : cand.calledFromOutsideLibrary = true)
    (hVis : cand.visibility = .externalVis) :
    checkLibraryCallInliningAllowed cand = .rejectDelegateCall externalLibraryCallDiagnostic :=
  (libraryCallInlining_satisfies_metaSpec cand).rejects_cross_library_public_or_external
    hLib hOut (by simp [isExternalOrPublicLibraryFunction, hVis])

/-- **Layer II Corollary 3**: No `public` library function called from outside its library passes the inlining filter. -/
theorem no_public_outside_library_call_inlined
    (cand : LibraryCallCandidate)
    (hLib : cand.isLibraryDecl = true)
    (hOut : cand.calledFromOutsideLibrary = true)
    (hVis : cand.visibility = .publicVis) :
    checkLibraryCallInliningAllowed cand = .rejectDelegateCall externalLibraryCallDiagnostic :=
  (libraryCallInlining_satisfies_metaSpec cand).rejects_cross_library_public_or_external
    hLib hOut (by simp [isExternalOrPublicLibraryFunction, hVis])

/-- **Layer II Corollary 4**: An `internal` library function with an internal type identifier is admitted for inlining. -/
theorem internal_library_call_inlined
    (cand : LibraryCallCandidate)
    (hTid : isDelegateCallTypeIdentifier cand.typeIdentifier = false)
    (hVis : cand.visibility = .internal) :
    checkLibraryCallInliningAllowed cand = .allowInline := by
  apply (libraryCallInlining_satisfies_metaSpec cand).allow_inline_iff_no_delegatecall.mpr
  simp [requiresDelegateCallBoundary, isExternalOrPublicLibraryFunction, hTid, hVis]

/-- **Layer II Corollary 5**: A `public` library function called by unqualified name inside its own library is admitted for inlining. -/
theorem public_same_library_call_inlined
    (cand : LibraryCallCandidate)
    (hTid : isDelegateCallTypeIdentifier cand.typeIdentifier = false)
    (hInside : cand.calledFromOutsideLibrary = false) :
    checkLibraryCallInliningAllowed cand = .allowInline := by
  apply (libraryCallInlining_satisfies_metaSpec cand).allow_inline_iff_no_delegatecall.mpr
  simp [requiresDelegateCallBoundary, hTid, hInside]

/-- **Layer II Corollary 6**: Internal `String` initialization helpers preserve every persistent storage slot. -/
theorem string_init_helper_preserves_all_slots
    (name : String) (byteLength : Nat) (writeVal : Nat → Nat) (s : InitState) (slot : Nat) :
    (transcribeInitHelperStep (mkStringHelperDescriptor name byteLength) writeVal s).persistentSlots slot =
      s.persistentSlots slot :=
  (initTranscription_satisfies_metaSpec (mkStringHelperDescriptor name byteLength) writeVal s).string_helper_preserves_storage
    name byteLength rfl slot

/-- **Layer II Corollary 7**: Contract-creation initialization helpers preserve every slot outside `initSlotWrites`. -/
theorem creation_init_helper_preserves_disjoint_slot
    (templateBytes : Nat) (initSlotWrites : List Nat) (writeVal : Nat → Nat)
    (s : InitState) (slot : Nat)
    (hDisjoint : initSlotWrites.contains slot = false) :
    (transcribeInitHelperStep (mkCreationInitDescriptor templateBytes initSlotWrites) writeVal s).persistentSlots slot =
      s.persistentSlots slot :=
  (initTranscription_satisfies_metaSpec (mkCreationInitDescriptor templateBytes initSlotWrites) writeVal s).unmodified_slot_preserved
    slot hDisjoint

/-! ## Layer III: Kernel-Checked Executable Witness Suite (`by decide`) -/

/-- Witness 1 (`public-stub` / `public-body`): `H.h(a, b)` calling a `public` library function from contract `C` is rejected. -/
theorem witness_reject_public_library_member_call :
    checkLibraryCallInliningAllowed
      { isLibraryDecl := true
        visibility := .publicVis
        calledFromOutsideLibrary := true
        typeIdentifier := "t_function_delegatecall_pure$_t_bytes32_$_t_bytes32_$returns$_t_bytes32_$" } =
      .rejectDelegateCall externalLibraryCallDiagnostic := by decide

/-- Witness 2 (`external-stub`): `H.h(a, b)` calling an `external` library function from contract `C` is rejected. -/
theorem witness_reject_external_library_member_call :
    checkLibraryCallInliningAllowed
      { isLibraryDecl := true
        visibility := .externalVis
        calledFromOutsideLibrary := true
        typeIdentifier := "t_function_delegatecall_pure$_t_bytes32_$_t_bytes32_$returns$_t_bytes32_$" } =
      .rejectDelegateCall externalLibraryCallDiagnostic := by decide

/-- Witness 3 (`using-for`): `a.h(b)` via `using H for bytes32` on a `public` library function is rejected. -/
theorem witness_reject_using_for_public_library_call :
    checkLibraryCallInliningAllowed
      { isLibraryDecl := true
        visibility := .publicVis
        calledFromOutsideLibrary := true
        typeIdentifier := "t_function_attached_to$_t_bytes32_$delegatecall_pure" } =
      .rejectDelegateCall externalLibraryCallDiagnostic := by decide

/-- Witness 4 (`internal-member`): `H.h(a, b)` calling an `internal` library function is admitted for inlining. -/
theorem witness_allow_internal_library_member_call :
    checkLibraryCallInliningAllowed
      { isLibraryDecl := true
        visibility := .internal
        calledFromOutsideLibrary := true
        typeIdentifier := "t_function_internal_pure$_t_bytes32_$_t_bytes32_$returns$_t_bytes32_$" } =
      .allowInline := by decide

/-- Witness 5 (`public-by-name-inside-library`): `h(a, b)` called by name inside `library H` is admitted for inlining. -/
theorem witness_allow_public_inside_own_library_call :
    checkLibraryCallInliningAllowed
      { isLibraryDecl := true
        visibility := .publicVis
        calledFromOutsideLibrary := false
        typeIdentifier := "t_function_internal_pure$_t_bytes32_$_t_bytes32_$returns$_t_bytes32_$" } =
      .allowInline := by decide

/-- Witness 6 (`#2465` String init helper): `Strings.toString` reserves 64 bytes (32 length + 32 data) and writes 0 storage slots. -/
theorem witness_string_helper_descriptor_layout :
    let d := mkStringHelperDescriptor "Strings.toString" 20
    d.writesStorage = false ∧ d.memoryAdvanceBytes = 64 ∧ d.createdContracts = 0 := by decide

/-- Witness 7 (`#2465` Contract-creation init helper): 85-byte initcode template reserves 96 aligned bytes and tracks slot 0 vs slot 5. -/
theorem witness_creation_init_descriptor_layout :
    let d := mkCreationInitDescriptor 85 [0, 1]
    d.writesStorage = true ∧ d.memoryAdvanceBytes = 96 ∧
      d.modifiesSlot 0 = true ∧ d.modifiesSlot 5 = false ∧ d.createdContracts = 1 := by decide

end Compiler.CompilationModel.SolidityImport

/-!
Report of a Solidity function slice lowered to `CompilationModel`.

A slice is not a whole-contract invariant. `opaqueMembers` are layout records
copied from solc and deliberately not given an executable encoding.
-/
namespace Compiler.CompilationModel.SolidityImport

/-- One function whose body was translated. Library helpers are included even
when the executable model inlines them. -/
structure ImportedFunction where
  contract : String
  name : String
  declId : Nat
  paramTypes : List String
  deriving Repr, BEq

/-- A memory-struct parameter replaced by the static members the slice reads.
`headWord` is the member's index in the Solidity memory/ABI head, derived from
the struct declaration order. This is not an ABI decoder. -/
structure ParamProjection where
  /-- The imported function whose parameter is projected. -/
  function : String
  parameter : String
  member : String
  structName : String
  headWord : Nat
  modelParam : String
  ignoredMembers : List String
  deriving Repr, BEq

/-- A struct member present in solc's storage layout that this slice does not encode. -/
structure OpaqueMember where
  field : String
  name : String
  solcType : String
  wordOffset : Nat
  byteOffset : Nat
  deriving Repr, BEq

/-- What is known about a Verity compiler-correctness proof for one imported
function. There is no `covered` case: the importer has no decision procedure
for `SupportedSpec` and builds no witness, so it never claims coverage. -/
inductive CompilerProofStatus where
  /-- No compiler-correctness theorem is instantiated for this function. -/
  | unavailable (reason : String)
  deriving Repr, BEq

def CompilerProofStatus.toText : CompilerProofStatus → String
  | .unavailable reason => s!"unavailable ({reason})"

/-- Why `compilerProof` is `unavailable` for every imported function. -/
def noCompilerProofReason : String :=
  "the importer builds no SupportedSpec witness; compiled code is only tested by A/B/C"

/-- Static status of one root. A root is listed only if it was importable.
`compilable` is not recorded here: it depends on the compiler, not the import,
and `Differential` reports it next to these fields. -/
structure FunctionStatus where
  function : String
  /-- `stmtListCovered` holds on the lowered body. The kernel-checked form of
  this fact, for all roots together, is the theorem `x.covered`. -/
  denoteCovered : Bool
  compilerProof : CompilerProofStatus
  deriving Repr, BEq

/-- Provenance and closure report. `sourceDigest` covers sources, solc settings,
the compiler release identity, and the importer sources. -/
structure ImportReport where
  importerVersion : String
  solcLongVersion : String
  solcSha256 : String
  settingsJson : String
  sourceDigest : String
  contract : String
  /-- The imported functions, in `solidity_import` order. -/
  roots : List String
  /-- One status per root, in `roots` order. -/
  functions : List FunctionStatus
  includedFunctions : List ImportedFunction
  excludedFunctions : List ImportedFunction
  projections : List ParamProjection
  storageFields : List String
  /-- Solidity names of each storage field's mapping keys (`""` when unnamed). -/
  storageKeys : List (String × List String) := []
  opaqueMembers : List OpaqueMember
  /-- The statement denotation exposes the exact panic bytes. Legacy scalar
  projections still erase failure bytes; the differential runner retains them. -/
  observesPanicPayload : Bool := false
  deriving Repr, BEq

/-- Stable, reviewable inventory of the translated closure and explicit exclusions. -/
def ImportReport.toText (r : ImportReport) : String := Id.run do
  let mut lines := [s!"importer {r.importerVersion}", s!"solc {r.solcLongVersion}",
    s!"solcSha256 {r.solcSha256}", s!"digest {r.sourceDigest}",
    s!"contract {r.contract}"] ++ r.roots.map (s!"root {·}") ++ [s!"settings {r.settingsJson}"]
  for st in r.functions do
    lines := lines ++ [s!"status {st.function} importable denoteCovered {st.denoteCovered} compilerProof {st.compilerProof.toText}"]
  for fn in r.includedFunctions do
    lines := lines ++ [s!"include {fn.contract}.{fn.name} decl {fn.declId} params {fn.paramTypes}"]
  for fn in r.excludedFunctions do
    lines := lines ++ [s!"exclude {fn.contract}.{fn.name} decl {fn.declId} params {fn.paramTypes}"]
  for p in r.projections do
    lines := lines ++ [s!"projection {p.function} {p.parameter}.{p.member} head {p.headWord} as {p.modelParam} ignored {p.ignoredMembers}"]
  for name in r.storageFields do
    let keys := (r.storageKeys.find? (·.1 == name)).map (·.2) |>.getD []
    lines := lines ++ [s!"storage {name} keys {keys}"]
  for m in r.opaqueMembers do
    lines := lines ++ [s!"opaque {m.field}.{m.name} {m.solcType} word {m.wordOffset} byte {m.byteOffset}"]
  return String.intercalate "\n" lines ++ "\n"

end Compiler.CompilationModel.SolidityImport

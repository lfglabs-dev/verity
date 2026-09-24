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

/-- Provenance and closure report. `sourceDigest` covers sources, solc settings,
the compiler release identity, and the importer sources. -/
structure ImportReport where
  importerVersion : String
  solcLongVersion : String
  solcSha256 : String
  settingsJson : String
  sourceDigest : String
  contract : String
  rootFunction : String
  includedFunctions : List ImportedFunction
  excludedFunctions : List ImportedFunction
  projections : List ParamProjection
  storageFields : List String
  opaqueMembers : List OpaqueMember
  /-- Proof denotation records success versus revert. `Stmt.panic` keeps its
  `PanicCode` on the statement, and `execStmt` does not return that payload. -/
  observesPanicPayload : Bool := false
  deriving Repr, BEq

/-- Stable, reviewable inventory of the translated closure and explicit exclusions. -/
def ImportReport.toText (r : ImportReport) : String := Id.run do
  let mut lines := [s!"importer {r.importerVersion}", s!"solc {r.solcLongVersion}",
    s!"solcSha256 {r.solcSha256}", s!"digest {r.sourceDigest}",
    s!"contract {r.contract}", s!"root {r.rootFunction}", s!"settings {r.settingsJson}"]
  for fn in r.includedFunctions do
    lines := lines ++ [s!"include {fn.contract}.{fn.name} decl {fn.declId} params {fn.paramTypes}"]
  for fn in r.excludedFunctions do
    lines := lines ++ [s!"exclude {fn.contract}.{fn.name} decl {fn.declId} params {fn.paramTypes}"]
  for p in r.projections do
    lines := lines ++ [s!"projection {p.parameter}.{p.member} head {p.headWord} as {p.modelParam} ignored {p.ignoredMembers}"]
  for name in r.storageFields do
    lines := lines ++ [s!"storage {name}"]
  for m in r.opaqueMembers do
    lines := lines ++ [s!"opaque {m.field}.{m.name} {m.solcType} word {m.wordOffset} byte {m.byteOffset}"]
  return String.intercalate "\n" lines ++ "\n"

end Compiler.CompilationModel.SolidityImport

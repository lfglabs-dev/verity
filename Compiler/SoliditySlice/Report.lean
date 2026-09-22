/-!
Report of a Solidity function slice lowered to `CompilationModel`.

A slice is not a whole-contract invariant. `opaqueMembers` are layout records
copied from solc and deliberately not given an executable encoding.
-/
namespace Compiler.CompilationModel.SoliditySlice

/-- One function whose body was translated. Library helpers are included even
when the executable model inlines them. -/
structure SliceFunction where
  contract : String
  name : String
  declId : Nat
  paramTypes : List String
  deriving Repr, BEq

/-- A memory-struct parameter replaced by the static members the slice reads.
`headWord` is the member's index in the Solidity memory/ABI head, derived from
the struct declaration order. This is not an ABI decoder. -/
structure SliceProjection where
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
structure SliceReport where
  importerVersion : String
  solcLongVersion : String
  solcSha256 : String
  settingsJson : String
  sourceDigest : String
  contract : String
  rootFunction : String
  includedFunctions : List SliceFunction
  excludedFunctions : List SliceFunction
  projections : List SliceProjection
  storageFields : List String
  opaqueMembers : List OpaqueMember
  /-- Proof denotation records success versus revert. `Stmt.panic` keeps its
  `PanicCode` on the statement, and `execStmt` does not return that payload. -/
  observesPanicPayload : Bool := false
  deriving Repr, BEq

end Compiler.CompilationModel.SoliditySlice

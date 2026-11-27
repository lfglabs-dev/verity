import Compiler.SolidityImport.Import

/-!
Struct parameters with user-defined field types (`StructFieldTypeSurvey.sol`), surveyed with
`collectUnsupported`. Direct `enum` fields (`configure`), user-defined value type fields (`price`),
and contract-typed fields (`hold`) import. An array of enums (`route`) is reported with the
element's actual type rather than as an unresolved struct declaration.
-/
namespace SolidityImportSmoke.StructFieldTypeSurveyChecks
open Compiler.CompilationModel.SolidityImport

solidity_profile survey where
  evmVersion := "osaka"
  viaIR := true
  optimizerRuns := some 466
  bytecodeHash := "none"
  collectUnsupported := true

/--
warning: collectUnsupported: 1 of 5 roots unsupported; no model, theorem or accessor is emitted, and an unsupported root proves nothing
status route unsupported constructs 1 denoteCovered false compilerProof unavailable (the importer builds no SupportedSpec witness; compiled code is only tested by A/B/C)
  StructFieldTypeSurvey.sol:11:38 UserDefinedTypeName: ABI schema: unsupported struct field type enum Version (closure StructFieldTypeSurvey.route)
-/
#guard_msgs in
solidity_import collected from "Contracts/SolidityImportSmoke" entry "StructFieldTypeSurvey.sol"
  using survey
  contract StructFieldTypeSurvey
  function configure(ConfigStruct)
  function price(PricedStruct)
  function hold(AssetStruct)
  function route(PathStruct)
  function plain(uint256)

/-! Without the survey flag, the roots with direct enum, value-type, and contract-typed fields import. -/
solidity_import imported from "Contracts/SolidityImportSmoke" entry "StructFieldTypeSurvey.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract StructFieldTypeSurvey
  function configure(ConfigStruct)
  function price(PricedStruct)
  function hold(AssetStruct)
  function plain(uint256)

#guard imported.model.functions.map (·.name) == ["configure", "price", "hold", "plain"]

end SolidityImportSmoke.StructFieldTypeSurveyChecks

import Lake
open Lake DSL

package «verity» where
  version := v!"1.0.0"

require evmyul from git
  "https://github.com/lfglabs-dev/EVMYulLean.git"@"a132798069be50e8b03f88d6a96f2618c128ae7f"

@[default_target]
lean_lib «Verity» where
  globs := #[
    .one `Verity,
    .andSubmodules `Verity.Core,
    .submodules `Verity.EVM,
    .andSubmodules `Verity.Macro,
    .submodules `Verity.Stdlib,
    .andSubmodules `Verity.Specs.Common,
    .one `Verity.Specs.ObsAlgebra,
    .one `Verity.Specs.AdversaryAndHelpers,
    .one `Verity.Specs.Composition,
    .submodules `Verity.Proofs.Stdlib,
    .one `Verity.Proofs.LoopSimulation,
    .one `Verity.Proofs.LoopSimulationResultAware,
    .one `Verity.Proofs.CheckedExternalCallConsumer,
    .one `Verity.Proofs.Model.GeneratedEntrypointRegistry
  ]

@[default_target]
lean_lib «Contracts» where
  globs := #[
    .one `Contracts,
    .one `Contracts.Common,
    .one `Contracts.Specs,
    .one `Contracts.Interpreter,
    .submodules `Contracts.Examples,
    .andSubmodules `Contracts.Smoke,
    .andSubmodules `Contracts.Counter,
    .andSubmodules `Contracts.SimpleStorage,
    .andSubmodules `Contracts.Owned,
    .andSubmodules `Contracts.Ownable,
    .andSubmodules `Contracts.OwnedCounter,
    .andSubmodules `Contracts.OwnedCounterComposed,
    .andSubmodules `Contracts.SafeCounter,
    .andSubmodules `Contracts.Ledger,
    .one `Contracts.Vault, .one `Contracts.Vault.Vault,
    .one `Contracts.Vault.Spec, .one `Contracts.Vault.Invariants,
    .one `Contracts.Vault.SpecProofs, .one `Contracts.Vault.Proofs.Basic,
    .one `Contracts.Vault.Proofs.Correctness, .one `Contracts.Vault.Proofs.Conservation,
    .one `Contracts.Vault.Proofs.Native,
    .andSubmodules `Contracts.ERC20,
    .andSubmodules `Contracts.ERC721,
    .andSubmodules `Contracts.SimpleToken,
    .andSubmodules `Contracts.CryptoHash,
    .andSubmodules `Contracts.ReentrancyExample,
    .andSubmodules `Contracts.ReentrancyRelyGuarantee,
    .one `Contracts.BytesEqSmoke,
    .one `Contracts.LocalObligationMacroSmoke.SpecProofs,
    .one `Contracts.StringEqSmoke,
    .one `Contracts.StringErrorSmokeContract,
    .one `Contracts.StringEventSmoke
  ]

/-- Solidity read by `solidity_import`: editing it rebuilds the import. -/
input_dir solidityImportSmokeSources where
  path := "Contracts/SolidityImportSmoke"
  filter := .extension "sol"
  text := true

@[default_target]
lean_lib «SolidityImportSmoke» where
  globs := #[.one `Contracts.SolidityImportSmoke.AccountStorageBridgeChecks,
    .one `Contracts.SolidityImportSmoke.Create2ParentGasChecks,
    .one `Contracts.SolidityImportSmoke.Create2OpcodeChecks,
    .one `Contracts.SolidityImportSmoke.Smoke,
    .one `Contracts.SolidityImportSmoke.AbiCanonicalityModel,
    .one `Contracts.SolidityImportSmoke.StaticAbiChecks,
    .one `Contracts.SolidityImportSmoke.StructValidationOrderModel,
    .one `Contracts.SolidityImportSmoke.EntryPointInvariantChecks,
    .one `Contracts.SolidityImportSmoke.SymbolicExecutionChecks,
    .one `Contracts.SolidityImportSmoke.SolidityAbiPrimitiveChecks,
    .one `Contracts.SolidityImportSmoke.AbiLoweringChecks,
    .one `Contracts.SolidityImportSmoke.PhysicalMemoryFrameChecks,
    .one `Contracts.SolidityImportSmoke.AbiCoverageChecks,
    .one `Contracts.SolidityImportSmoke.ExplicitAbiChecks,
    .one `Contracts.SolidityImportSmoke.SelectorIdentityChecks,
    .one `Contracts.SolidityImportSmoke.ScalarArrayAbiModel,
    .one `Contracts.SolidityImportSmoke.NestedDynamicStructAbiModel,
    .one `Contracts.SolidityImportSmoke.MultipleDynamicAbiModel,
    .one `Contracts.SolidityImportSmoke.Transactions,
    .one `Contracts.SolidityImportSmoke.SequenceModel,
    .one `Contracts.SolidityImportSmoke.EventSequenceModel,
    .one `Contracts.SolidityImportSmoke.AbiEventCompositionModel,
    .one `Contracts.SolidityImportSmoke.ReferenceArgumentsModel,
    .one `Contracts.SolidityImportSmoke.AbiHashingModel,
    .one `Contracts.SolidityImportSmoke.YulNumericSequenceModel,
    .one `Contracts.SolidityImportSmoke.Solc0810SequenceModel,
    .one `Contracts.SolidityImportSmoke.InheritanceSequenceModel,
    .one `Contracts.SolidityImportSmoke.VoidHelperGuardSequenceModel,
    .one `Contracts.SolidityImportSmoke.ModifierUncheckedCompoundSequenceModel,
    .one `Contracts.SolidityImportSmoke.TupleHelperSequenceModel,
    .one `Contracts.SolidityImportSmoke.UncheckedSequenceModel,
    .one `Contracts.SolidityImportSmoke.TupleSequenceModel,
    .one `Contracts.SolidityImportSmoke.Int256ContractTypeSequenceModel,
    .one `Contracts.SolidityImportSmoke.FnPtrStructDeleteModifierSequenceModel,
    .one `Contracts.SolidityImportSmoke.EmptyArrayReturnBytesCalldataSequenceModel,
    .one `Contracts.SolidityImportSmoke.OverloadConstErrorCondTupleTloadSequenceModel,
    .one `Contracts.SolidityImportSmoke.StructFixedArrayAndFixedReturnSequenceModel,
    .one `Contracts.SolidityImportSmoke.MsgDataAndEnumSequenceModel,
    .one `Contracts.SolidityImportSmoke.ExpAndBitwiseShiftSequenceModel,
    .one `Contracts.SolidityImportSmoke.WhileClzAndStructLocSequenceModel,
    .one `Contracts.SolidityImportSmoke.YulBuiltinsAndEncodeSelectorSequenceModel,
    .one `Contracts.SolidityImportSmoke.ArrayStringParamsAndContextSequenceModel,
    .one `Contracts.SolidityImportSmoke.BytesMemoryAndAbiEncodeCallSequenceModel,
    .one `Contracts.SolidityImportSmoke.DynamicBytesAndStringReturnSequenceModel,
    .one `Contracts.SolidityImportSmoke.BytesAndStringStorageSequenceModel,
    .one `Contracts.SolidityImportSmoke.StorageSlotShortStringsTimeSequenceModel,
    .one `Contracts.SolidityImportSmoke.EnumerableSetMapSequenceModel,
    .one `Contracts.SolidityImportSmoke.CheckpointsAndStructArraysSequenceModel,
    .one `Contracts.SolidityImportSmoke.WadExpAndThreeKeyMappingSequenceModel,
    .one `Contracts.SolidityImportSmoke.StructHashAndDomainSeparatorSequenceModel,
    .one `Contracts.SolidityImportSmoke.AbiDecodeAndVerifierSequenceModel,
    .one `Contracts.SolidityImportSmoke.VotesCheckpointsArraysBitMapsSequenceModel,
    .one `Contracts.SolidityImportSmoke.PublicGettersAndBuiltinsSequenceModel,
    .one `Contracts.SolidityImportSmoke.EcrecoverAuthorizerArraysMapSequenceModel,
    .one `Contracts.SolidityImportSmoke.StructParamsAndBalancesSequenceModel,
    .one `Contracts.SolidityImportSmoke.PackedStructMappingAndTernaryTupleSequenceModel,
    .one `Contracts.SolidityImportSmoke.TimelockAndBytes4CastSequenceModel,
    .one `Contracts.SolidityImportSmoke.StringBytesMappingsUriStorageStringsSequenceModel,
    .one `Contracts.SolidityImportSmoke.StringsHexArraysBitmapsSequenceModel,
    .one `Contracts.SolidityImportSmoke.EcdsaMerkleCheckpointsStorageSlotSequenceModel,
    .one `Contracts.SolidityImportSmoke.Create2ClonesMsgDataDequeSequenceModel,
    .one `Contracts.SolidityImportSmoke.GovernorSliceProposerDelaySequenceModel,
    .one `Contracts.SolidityImportSmoke.AccessManagerTargetRoleSequenceModel,
    .one `Contracts.SolidityImportSmoke.UniswapV4TypesAndTransientSequenceModel,
    .one `Compiler.SolidityImport.AbiByteLanes,
    .one `Compiler.SolidityImport.AbiMemory,
    .one `Contracts.SolidityImportSmoke.EnvironmentSequenceModel,
    .one `Contracts.SolidityImportSmoke.StorageSequenceModel,
    .one `Contracts.SolidityImportSmoke.MappingSequenceModel,
    .one `Contracts.SolidityImportSmoke.ShortCircuitSequenceModel,
    .one `Contracts.SolidityImportSmoke.IfElseSequenceModel,
    .one `Contracts.SolidityImportSmoke.NumericLiteralSequenceModel,
    .one `Contracts.SolidityImportSmoke.ConstantArraySequenceModel,
    .one `Contracts.SolidityImportSmoke.ModuloSequenceModel,
    .one `Contracts.SolidityImportSmoke.ImportedEventSequenceModel,
    .one `Contracts.SolidityImportSmoke.NarrowEventSequenceModel,
    .one `Contracts.SolidityImportSmoke.MappingDirtySequenceModel,
    .one `Contracts.SolidityImportSmoke.StorageVoidSequenceModel,
    .one `Contracts.SolidityImportSmoke.StorageBytesSequenceModel,
    .one `Contracts.SolidityImportSmoke.StorageTraceChecks,
    .one `Contracts.SolidityImportSmoke.LoopInvariantChecks,
    .one `Contracts.SolidityImportSmoke.EventRejections,
    .one `Contracts.SolidityImportSmoke.ErrorPayloads,
    .one `Contracts.SolidityImportSmoke.ErrorSequenceModel,
    .one `Contracts.SolidityImportSmoke.Require,
    .one `Contracts.SolidityImportSmoke.RequireCustom,
    .one `Contracts.SolidityImportSmoke.ArrayForAbiModel,
    .one `Contracts.SolidityImportSmoke.BytesObjectMemoryDriver,
    .one `Contracts.SolidityImportSmoke.Create2BytecodeAndStructEmitSequenceModel,
    .one `Contracts.SolidityImportSmoke.Create2OpcodeDriver,
    .one `Contracts.SolidityImportSmoke.Create2ParentGasDriver,
    .one `Contracts.SolidityImportSmoke.DefaultLocalSequenceModel,
    .one `Contracts.SolidityImportSmoke.DeploymentWorldChecks,
    .one `Contracts.SolidityImportSmoke.DeploymentWorldDriver,
    .one `Contracts.SolidityImportSmoke.DiscardedHelperSequenceModel,
    .one `Contracts.SolidityImportSmoke.ERC2981HoldersArraysMsgHashSequenceModel,
    .one `Contracts.SolidityImportSmoke.EmptyRevertSequenceModel,
    .one `Contracts.SolidityImportSmoke.EncodedByteLocalSequenceModel,
    .one `Contracts.SolidityImportSmoke.ExtCodeCopyStructDecodeSequenceModel,
    .one `Contracts.SolidityImportSmoke.ExternalCodeAndLowLevelCallSequenceModel,
    .one `Contracts.SolidityImportSmoke.FixedArrayWriteOrderSequenceModel,
    .one `Contracts.SolidityImportSmoke.HelperEffectSequenceModel,
    .one `Contracts.SolidityImportSmoke.HelperLoopSequenceModel,
    .one `Contracts.SolidityImportSmoke.InitCodeExecutionChecks,
    .one `Contracts.SolidityImportSmoke.InitCodeExecutionDriver,
    .one `Contracts.SolidityImportSmoke.InterfaceStaticCallSequenceModel,
    .one `Contracts.SolidityImportSmoke.InterfaceWordStaticCallSequenceModel,
    .one `Contracts.SolidityImportSmoke.InvariantForSequenceModel,
    .one `Contracts.SolidityImportSmoke.LocalWriteSequenceModel,
    .one `Contracts.SolidityImportSmoke.MappingFixedArraySequenceModel,
    .one `Contracts.SolidityImportSmoke.MerkleAndNoncesSequenceModel,
    .one `Contracts.SolidityImportSmoke.MultiProofMappingKeysVerifiersSequenceModel,
    .one `Contracts.SolidityImportSmoke.NamedHelperReturnSequenceModel,
    .one `Contracts.SolidityImportSmoke.PackedMemberWriteSequenceModel,
    .one `Contracts.SolidityImportSmoke.StorageStructParamsDequeShortStringsSequenceModel,
    .one `Contracts.SolidityImportSmoke.StructMappingAndBytes4InterfaceSequenceModel,
    .one `Contracts.SolidityImportSmoke.UdvtParamAssignStructHashSequenceModel,
    .one `Contracts.SolidityImportSmoke.YulBlockMulmodTstoreSequenceModel]
  needs := #[solidityImportSmokeSources]

@[default_target]
lean_lib «Compiler» where
  globs := #[.andSubmodules `Compiler]

-- Negative/positive control fixtures for `UnionAxiomsControls.lean`, kept under
-- a dot-prefixed directory (`scripts/.assurance_fixtures`) so Turbo-Lean's
-- project-wide `WalkDir` source hygiene scan skips intentional negative-control
-- `axiom` / `sorry` / `native_decide` tokens while Lake still builds and checks them.
lean_lib «AssuranceFixtures» where
  srcDir := "scripts/.assurance_fixtures"
  roots := #[
    `UnionAxiomsFixture.Good,
    `UnionAxiomsFixture.Bad,
    `UnionAxiomsFixture.Dep,
    `UnionAxiomsFixture.ViaDep,
    `UnionAxiomsFixture.NativeAndAttrs
  ]

-- From-scratch axiom walker (`scripts/AxiomAudit.lean`), its negative/positive
-- controls (`scripts/UnionAxiomsControls.lean`), and the whole-library union
-- check (`scripts/VerityUnionAxioms.lean`).
@[default_target]
lean_lib «Assurance» where
  srcDir := "scripts"
  roots := #[
    `AxiomAudit,
    `UnionAxiomsControls
  ]

lean_lib «VerityUnionAxioms» where
  srcDir := "scripts"
  roots := #[`VerityUnionAxioms]

-- Axiom dependency audit: imports `AxiomAudit`, `UnionAxiomsControls`,
-- `VerityUnionAxioms`, plus the minimal verified-module roots covering all
-- verified modules, so `lake build PrintAxioms` builds the walker, controls,
-- whole-population `VerityUnionAxioms`, and verified closure, and
-- `lake env lean PrintAxioms.lean` checks the whole-library union and emits
-- exact per-theorem axiom sets.
lean_lib «PrintAxioms» where
  globs := #[.one `PrintAxioms]

lean_exe «verity-compiler» where
  root := `Compiler.Main
  -- interpreter eval of ecm/interface specs forces init/std decls (e.g. `UInt64.ofNatLT`). (#1951)
  supportInterpreter := true

lean_exe «difftest-interpreter» where
  root := `Contracts.Interpreter

lean_exe «random-gen» where
  root := `Compiler.RandomGen

lean_exe «gas-report» where
  root := `Compiler.Gas.Report
  -- Static gas reporting evaluates compiled terms that may depend on init/std
  -- interpreter support through typed-interface ECMs.
  supportInterpreter := true

lean_exe «compiler-main-test» where
  root := `Compiler.MainTestRunner
  -- Mirrors `verity-compiler`: CLI regression tests evaluate typed-interface ECMs
  -- through the Lean interpreter.
  supportInterpreter := true

-- Emits the canonical storage-layout audit artifact (#1897). Lives at the
-- package root because it imports both Compiler and Contracts, which the
-- Compiler -> Contracts boundary forbids inside `Compiler/`.
lean_lib «StorageLayoutReport» where
  globs := #[.one `StorageLayoutReport]

lean_exe «verity-storage-layout-report» where
  root := `StorageLayoutReport
  supportInterpreter := true

import Lake
open Lake DSL

package «verity» where
  version := v!"1.0.0"

require evmyul from git
  "https://github.com/lfglabs-dev/EVMYulLean.git"@"4cf4c5d0f286e8efc3d9e972ce3616bfe83a0624"

@[default_target]
lean_lib «Verity» where
  globs := #[
    .one `Verity,
    .andSubmodules `Verity.Core,
    .submodules `Verity.EVM,
    .andSubmodules `Verity.Macro,
    .submodules `Verity.Stdlib,
    .andSubmodules `Verity.Specs.Common,
    .one `Verity.Specs.Composition,
    .submodules `Verity.Proofs.Stdlib,
    .one `Verity.Proofs.LoopSimulation,
    .one `Verity.Proofs.LoopSimulationResultAware
  ]

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
    .andSubmodules `Contracts.ReentrancyRelyGuarantee
  ]

/-- Solidity read by `solidity_import`: editing it rebuilds the import. -/
input_dir solidityImportSmokeSources where
  path := "Contracts/SolidityImportSmoke"
  filter := .extension "sol"
  text := true

lean_lib «SolidityImportSmoke» where
  globs := #[.one `Contracts.SolidityImportSmoke.Smoke,
    .one `Contracts.SolidityImportSmoke.ImportedCreationPrefixFrames,
    .one `Contracts.SolidityImportSmoke.ImportedCreationPrefixRelation,
    .one `Contracts.SolidityImportSmoke.ImportedCreationBoundaryRelation,
    .one `Contracts.SolidityImportSmoke.ImportedCreationCopySlices,
    .one `Contracts.SolidityImportSmoke.ImportedCreationPackingFrames,
    .one `Contracts.SolidityImportSmoke.ImportedCreationAllocator,
    .one `Contracts.SolidityImportSmoke.ImportedCreationAllocatedPacking,
    .one `Contracts.SolidityImportSmoke.ImportedCreationOriginalSnapshots,
    .one `Contracts.SolidityImportSmoke.ImportedCreationHeaderAllocation,
    .one `Contracts.SolidityImportSmoke.ImportedCreationHeaderPreparation,
    .one `Contracts.SolidityImportSmoke.ImportedCreationPackedCode,
    .one `Contracts.SolidityImportSmoke.ImportedCreationLength,
    .one `Contracts.SolidityImportSmoke.ImportedCreationArrayAllocation,
    .one `Contracts.SolidityImportSmoke.ImportedCreationArrayElement,
    .one `Contracts.SolidityImportSmoke.ImportedCreationArrayLoop,
    .one `Contracts.SolidityImportSmoke.ImportedCreationArrayHeader,
    .one `Contracts.SolidityImportSmoke.ImportedCreationHeadAllocation,
    .one `Contracts.SolidityImportSmoke.ImportedCreationHeadFields,
    .one `Contracts.SolidityImportSmoke.ImportedCreationArrayDescriptors,
    .one `Contracts.SolidityImportSmoke.ImportedCreationFieldFrames,
    .one `Contracts.SolidityImportSmoke.ImportedCreationPrelude,
    .one `Contracts.SolidityImportSmoke.ImportedCreationAbiLayout,
    .one `Contracts.SolidityImportSmoke.ImportedCreationEncodedPacking,
    .one `Contracts.SolidityImportSmoke.ImportedCreationDecoderAllocation,
    .one `Contracts.SolidityImportSmoke.ImportedCreationDecoderHead,
    .one `Contracts.SolidityImportSmoke.ImportedCreationDecoderFields,
    .one `Contracts.SolidityImportSmoke.ImportedCreationDecoderArrayHead,
    .one `Contracts.SolidityImportSmoke.ImportedCreationDecoderArrayBounds,
    .one `Contracts.SolidityImportSmoke.ImportedCreationDecoderElementFields,
    .one `Contracts.SolidityImportSmoke.ImportedCreationDecoderElementPrelude,
    .one `Contracts.SolidityImportSmoke.ImportedCreationDecoderArrayLoop,
    .one `Contracts.SolidityImportSmoke.ImportedCreationDecodedArray,
    .one `Contracts.SolidityImportSmoke.ImportedCreationDecodedMarket,
    .one `Contracts.SolidityImportSmoke.ImportedCreationDecodedPrefix,
    .one `Contracts.SolidityImportSmoke.ImportedCreationEncoderEntry,
    .one `Contracts.SolidityImportSmoke.ImportedCreationOriginalExecution,
    .one `Contracts.SolidityImportSmoke.ImportedCreationOriginalBytes,
    .one `Contracts.SolidityImportSmoke.ImportedCreationCanonicalBytes,
    .one `Contracts.SolidityImportSmoke.EffectfulReturndataChecks,
    .one `Contracts.SolidityImportSmoke.CanonicalReturndataChecks,
    .one `Contracts.SolidityImportSmoke.SourcePublicExceptionChecks,
    .one `Contracts.SolidityImportSmoke.DenotePublicExceptionChecks,
    .one `Contracts.SolidityImportSmoke.NativeCreationWorldChecks,
    .one `Contracts.SolidityImportSmoke.NativePairedCallerChecks,
    .one `Contracts.SolidityImportSmoke.NativePairedCreationChecks,
    .one `Contracts.SolidityImportSmoke.NativeInitcodeFrameChecks,
    .one `Contracts.SolidityImportSmoke.SourcePublicContextChecks,
    .one `Contracts.SolidityImportSmoke.SourceInternalExceptionChecks,
    .one `Contracts.SolidityImportSmoke.SourceHelperContextChecks,
    .one `Contracts.SolidityImportSmoke.SourceHelperExternalChecks,
    .one `Contracts.SolidityImportSmoke.HelperBodyContextChecks,
    .one `Contracts.SolidityImportSmoke.CanonicalIRReturndataChecks,
    .one `Contracts.SolidityImportSmoke.GenericReturndataChecks,
    .one `Contracts.SolidityImportSmoke.RequirePayloadValidationChecks,
    .one `Contracts.SolidityImportSmoke.DispatcherRevertChecks,
    .one `Contracts.SolidityImportSmoke.CustomErrorConditionalCompilationChecks,
    .one `Contracts.SolidityImportSmoke.CustomErrorConditionalFunctionChecks,
    .one `Contracts.SolidityImportSmoke.CustomErrorConditionalContractChecks,
    .one `Contracts.SolidityImportSmoke.CustomErrorCompilationOriginChecks,
    .one `Contracts.SolidityImportSmoke.CustomErrorDispatchCompilationChecks,
    .one `Contracts.SolidityImportSmoke.CustomErrorContractCompilationChecks,
    .one `Contracts.SolidityImportSmoke.CustomErrorLoadedFunctionChecks,
    .one `Contracts.SolidityImportSmoke.CustomErrorFunctionFuelChecks,
    .one `Contracts.SolidityImportSmoke.CustomErrorScalarFunctionChecks,
    .one `Contracts.SolidityImportSmoke.CustomErrorScalarContractChecks,
    .one `Contracts.SolidityImportSmoke.CustomErrorFunctionResultChecks,
    .one `Contracts.SolidityImportSmoke.CustomErrorFunctionEntryChecks,
    .one `Contracts.SolidityImportSmoke.CustomErrorPrefixFrameChecks,
    .one `Contracts.SolidityImportSmoke.CustomErrorListCompilationChecks,
    .one `Contracts.SolidityImportSmoke.CustomErrorContinuationChecks,
    .one `Contracts.SolidityImportSmoke.IRMemoryCoherenceChecks,
    .one `Contracts.SolidityImportSmoke.ScalarRequireErrorChecks,

    .one `Contracts.SolidityImportSmoke.AbiCanonicalityModel,
    .one `Contracts.SolidityImportSmoke.StaticAbiChecks,
    .one `Contracts.SolidityImportSmoke.StructValidationOrderModel,
    .one `Contracts.SolidityImportSmoke.EntryPointInvariantChecks,
    .one `Contracts.SolidityImportSmoke.SymbolicExecutionChecks,
    .one `Contracts.SolidityImportSmoke.SolidityAbiPrimitiveChecks,
    .one `Contracts.SolidityImportSmoke.AbiLoweringChecks,
    .one `Contracts.SolidityImportSmoke.AbiCoverageChecks,
    .one `Contracts.SolidityImportSmoke.ExplicitAbiChecks,
    .one `Contracts.SolidityImportSmoke.SelectorIdentityChecks,
    .one `Contracts.SolidityImportSmoke.ScalarArrayAbiModel,
    .one `Contracts.SolidityImportSmoke.MarketAbiModel,
    .one `Contracts.SolidityImportSmoke.MultipleDynamicAbiModel,
    .one `Contracts.SolidityImportSmoke.Transactions,
    .one `Contracts.SolidityImportSmoke.AccountInputChecks,
    .one `Contracts.SolidityImportSmoke.CallRefusal,
    .one `Contracts.SolidityImportSmoke.IRCreationChecks,
    .one `Contracts.SolidityImportSmoke.TypedAccessChecks,
    .one `Contracts.SolidityImportSmoke.SourceHelperRefusal,
    .one `Contracts.SolidityImportSmoke.PublicRevertChecks,
    .one `Contracts.SolidityImportSmoke.IRRevertChecks,
    .one `Contracts.SolidityImportSmoke.SourceExpressionOutcomeChecks,
    .one `Contracts.SolidityImportSmoke.SourceExpressionEvaluationChecks,
    .one `Contracts.SolidityImportSmoke.SourceStatementEvaluationChecks,
    .one `Contracts.SolidityImportSmoke.NativeCreationBoundaryChecks,
    .one `Contracts.SolidityImportSmoke.NativePreparedCreationChecks,
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
    .one `Contracts.SolidityImportSmoke.TickLibAndThreeKeyMappingSequenceModel,
    .one `Contracts.SolidityImportSmoke.OfferHashAndDomainSeparatorSequenceModel,
    .one `Contracts.SolidityImportSmoke.AbiDecodeAndRatifierSequenceModel,
    .one `Contracts.SolidityImportSmoke.VotesCheckpointsArraysBitMapsSequenceModel,
    .one `Contracts.SolidityImportSmoke.PublicGettersAndBuiltinsSequenceModel,
    .one `Contracts.SolidityImportSmoke.EcrecoverAuthorizerArraysMapSequenceModel,
    .one `Contracts.SolidityImportSmoke.MarketParamsBalancesSequenceModel,
    .one `Contracts.SolidityImportSmoke.MidnightPositionAndFeeSequenceModel,
    .one `Contracts.SolidityImportSmoke.TimelockAndBytes4CastSequenceModel,
    .one `Contracts.SolidityImportSmoke.StringBytesMappingsUriStorageStringsSequenceModel,
    .one `Contracts.SolidityImportSmoke.StringsHexArraysBitmapsSequenceModel,
    .one `Contracts.SolidityImportSmoke.EcdsaMerkleCheckpointsStorageSlotSequenceModel,
    .one `Contracts.SolidityImportSmoke.Create2ClonesMsgDataDequeSequenceModel,
    .one `Contracts.SolidityImportSmoke.GovernorSliceProposerDelaySequenceModel,
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
    .one `Contracts.SolidityImportSmoke.RequireCustom]
  needs := #[solidityImportSmokeSources]

lean_lib «Compiler» where
  globs := #[.andSubmodules `Compiler]

-- Axiom dependency audit: imports all proof modules so `lake build PrintAxioms`
-- compiles them, then `lake env lean PrintAxioms.lean` can run #print axioms.
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

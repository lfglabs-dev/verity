import Lake
open Lake DSL

package «verity» where
  version := v!"1.0.0"

-- Pinned at the merge of the Yul revert-data fixes and their tests (lfglabs-dev/EVMYulLean#13-#15).
require evmyul from git
  "https://github.com/lfglabs-dev/EVMYulLean.git"@"efca6fc7c85b4fc37612c477b43ee601a5c4099d"

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
    .andSubmodules `Contracts.ProofKit,
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

/-- The importer's own sources, all hashed into `sourceDigest`: editing one
that `Import` does not import still rebuilds the imports and their digests. -/
input_dir solidityImporterSources where
  path := "Compiler/SolidityImport"
  filter := .extension "lean"
  text := true

-- Every module in Contracts/SolidityImportSmoke/: a new smoke model needs no
-- lakefile edit, so PRs adding different models do not conflict here.
@[default_target]
lean_lib «SolidityImportSmoke» where
  globs := #[.submodules `Contracts.SolidityImportSmoke,
    .one `Compiler.SolidityImport.AbiByteLanes,
    .one `Compiler.SolidityImport.AbiMemory]
  needs := #[solidityImportSmokeSources, solidityImporterSources]

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

-- Executables that scripts, the Makefile and CI run directly from `.lake/build/bin/` are
-- default targets, so a bare `lake build` relinks them. A stale binary run against
-- rebuilt `.olean`s (e.g. after a `ContractState` field was added) loads an environment
-- whose layout no longer matches its compiled code and segfaults
-- (`scripts/check_lake_default_coverage.py` enforces this).
@[default_target]
lean_exe «verity-compiler» where
  root := `Compiler.Main
  -- interpreter eval of ecm/interface specs forces init/std decls (e.g. `UInt64.ofNatLT`). (#1951)
  supportInterpreter := true

@[default_target]
lean_exe «difftest-interpreter» where
  root := `Contracts.Interpreter

lean_exe «random-gen» where
  root := `Compiler.RandomGen

@[default_target]
lean_exe «gas-report» where
  root := `Compiler.Gas.Report
  -- Static gas reporting evaluates compiled terms that may depend on init/std
  -- interpreter support through typed-interface ECMs.
  supportInterpreter := true

@[default_target]
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

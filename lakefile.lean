import Lake
open Lake DSL

package «verity» where
  version := v!"1.0.0"

-- Pinned at the merge of the out-of-bounds RETURNDATACOPY halt fix (lfglabs-dev/EVMYulLean#12).
require evmyul from git
  "https://github.com/lfglabs-dev/EVMYulLean.git"@"eb0b6ddfab7daacbc3963f8fbb765853fee6ccb0"

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

-- Every module in Contracts/SolidityImportSmoke/: a new smoke model needs no
-- lakefile edit, so PRs adding different models do not conflict here.
@[default_target]
lean_lib «SolidityImportSmoke» where
  globs := #[.submodules `Contracts.SolidityImportSmoke,
    .one `Compiler.SolidityImport.AbiByteLanes,
    .one `Compiler.SolidityImport.AbiMemory]
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

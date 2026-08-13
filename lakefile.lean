import Lake
open Lake DSL

package «verity» where
  version := v!"1.0.0"

require evmyul from git
  "https://github.com/lfglabs-dev/EVMYulLean.git"@"f7e4ee0dc8f8d5265ce822a937ab5be771f182e9"

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
    .andSubmodules `Contracts.Vault,
    .andSubmodules `Contracts.ERC20,
    .andSubmodules `Contracts.ERC721,
    .andSubmodules `Contracts.SimpleToken,
    .andSubmodules `Contracts.CryptoHash,
    .andSubmodules `Contracts.ReentrancyExample,
    .andSubmodules `Contracts.ReentrancyRelyGuarantee
  ]

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

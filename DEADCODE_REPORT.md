# Dead-Code Audit Report

**Date:** 2026-06-10  
**Branch:** worker/deadcode-audit  
**Method:** Static import-reachability (BFS from all build roots; no dynamic imports in Lean)

---

## 1. Build Roots

### lean_lib Verity (globs)
| Glob kind | Module prefix |
|-----------|--------------|
| `.one` | `Verity` |
| `.andSubmodules` | `Verity.Core` |
| `.submodules` | `Verity.EVM` |
| `.andSubmodules` | `Verity.Macro` |
| `.submodules` | `Verity.Stdlib` |
| `.andSubmodules` | `Verity.Specs.Common` |
| `.submodules` | `Verity.Proofs.Stdlib` |

### lean_lib Contracts (globs)
| Glob kind | Module prefix |
|-----------|--------------|
| `.one` | `Contracts` |
| `.one` | `Contracts.Common` |
| `.one` | `Contracts.Specs` |
| `.one` | `Contracts.Interpreter` |
| `.one` | `Contracts.Smoke` |
| `.andSubmodules` | `Contracts.Legacy` |
| `.andSubmodules` | `Contracts.Counter` |
| `.andSubmodules` | `Contracts.SimpleStorage` |
| `.andSubmodules` | `Contracts.Owned` |
| `.andSubmodules` | `Contracts.OwnedCounter` |
| `.andSubmodules` | `Contracts.SafeCounter` |
| `.andSubmodules` | `Contracts.Ledger` |
| `.andSubmodules` | `Contracts.Vault` |
| `.andSubmodules` | `Contracts.ERC20` |
| `.andSubmodules` | `Contracts.ERC721` |
| `.andSubmodules` | `Contracts.SimpleToken` |
| `.andSubmodules` | `Contracts.CryptoHash` |
| `.andSubmodules` | `Contracts.ReentrancyExample` |

### lean_lib Compiler (globs)
| Glob kind | Module prefix |
|-----------|--------------|
| `.andSubmodules` | `Compiler` (all files under Compiler/) |

### lean_lib PrintAxioms (globs)
| Glob kind | Module prefix |
|-----------|--------------|
| `.one` | `PrintAxioms` |

### lean_exe roots (explicit entry points)
- `Compiler.Main` (verity-compiler)
- `Compiler.MainPatched` (verity-compiler-patched)
- `Contracts.Interpreter` (difftest-interpreter)
- `Compiler.RandomGen` (random-gen)
- `Compiler.Gas.Report` (gas-report)
- `Compiler.MainTestRunner` (compiler-main-test)

**Total build roots:** 301 glob-matched modules + 6 exe entry points  
**Total reachable (transitive):** 317 modules out of 335

---

## 2. Confirmed Orphans — DELETED

All 17 files below had **zero reachable importers**. Verified with oracle:
`for m in $(git diff --cached --name-only --diff-filter=D | sed 's#/#.#g; s#.lean$##'); do grep -rl "import $m" --include=*.lean . | grep -v .lake; done`
(produced no output).

| File | Module | Why unreachable |
|------|--------|----------------|
| `Contracts/BytesEqSmoke.lean` | `Contracts.BytesEqSmoke` | Not in any lib glob; never imported by reachable module |
| `Contracts/LocalObligationMacroSmoke/SpecProofs.lean` | `Contracts.LocalObligationMacroSmoke.SpecProofs` | Not imported by parent `Contracts.LocalObligationMacroSmoke.lean`; no other importers |
| `Contracts/Smoke/ArrayElementDynamicMemberElementSmoke.lean` | `Contracts.Smoke.ArrayElementDynamicMemberElementSmoke` | Lakefile uses `.one \`Contracts.Smoke` (not `.andSubmodules`); file is never imported |
| `Contracts/Smoke/ArrayElementDynamicMemberLengthSmoke.lean` | `Contracts.Smoke.ArrayElementDynamicMemberLengthSmoke` | Same: Smoke submodule not in any glob, never imported |
| `Contracts/Smoke/FixedArrayStructSmoke.lean` | `Contracts.Smoke.FixedArrayStructSmoke` | Same |
| `Contracts/Smoke/LowLevelTryCatchSmoke.lean` | `Contracts.Smoke.LowLevelTryCatchSmoke` | Same |
| `Contracts/Smoke/MathlibReservedBinderEscape.lean` | `Contracts.Smoke.MathlibReservedBinderEscape` | Same |
| `Contracts/Smoke/PackedHashECMSmoke.lean` | `Contracts.Smoke.PackedHashECMSmoke` | Same |
| `Contracts/Smoke/SelfBalanceSmoke.lean` | `Contracts.Smoke.SelfBalanceSmoke` | Same |
| `Contracts/Smoke/UnlinkPoolShapeCheckSmoke.lean` | `Contracts.Smoke.UnlinkPoolShapeCheckSmoke` | Same |
| `Contracts/SpecAliases.lean` | `Contracts.SpecAliases` | Only importer is `Contracts.TypedIRTests` which is itself an orphan |
| `Contracts/StringEqSmoke.lean` | `Contracts.StringEqSmoke` | Not in any lib glob; never imported |
| `Contracts/StringErrorSmokeContract.lean` | `Contracts.StringErrorSmokeContract` | Not in any lib glob; never imported |
| `Contracts/StringEventSmoke.lean` | `Contracts.StringEventSmoke` | Not in any lib glob; never imported |
| `Contracts/TypedIRTests.lean` | `Contracts.TypedIRTests` | Not in any lib glob; never imported by reachable module |
| `Verity/Compiler/FromSolidity.lean` | `Verity.Compiler.FromSolidity` | `Verity.Compiler` is not in any Verity lib glob (`Verity.Core`, `Verity.Macro`, etc.); never imported |
| `Verity/Trace.lean` | `Verity.Trace` | Not matched by `.one \`Verity` or any submodule glob; `Verity.Trace` is not a direct submodule of a covered prefix; never imported |

**Total lines removed:** 4,122

---

## 3. Suspected-but-KEPT Files

### Compiler.MainPatched (`Compiler/MainPatched.lean`)
- **Status: REACHABLE — build target, NOT deleted**
- Reason: Explicit `lean_exe «verity-compiler-patched» where root := \`Compiler.MainPatched` in lakefile.lean
- Also covered by `.andSubmodules \`Compiler` glob

### Contracts.Legacy.SpecAliases (`Contracts/Legacy/SpecAliases.lean`)
- **Status: REACHABLE — NOT deleted**
- Reason: `.andSubmodules \`Contracts.Legacy` covers it; also imported by `Contracts.Specs` which is a build root

### Compiler.Proofs.IRGeneration.GenericInduction.LegacyCompatibility
(`Compiler/Proofs/IRGeneration/GenericInduction/LegacyCompatibility.lean`)
- **Status: REACHABLE — NOT deleted**
- Reason: Under `Compiler/` which is fully covered by `.andSubmodules \`Compiler`
- Importers: `PrintAxioms`, `Compiler.Proofs.IRGeneration.GenericInduction.InterfaceAssembly`

### Verity.EVM.Frame (`Verity/EVM/Frame.lean`)
- **Status: REACHABLE — NOT deleted**
- Reason: `.submodules \`Verity.EVM` matches direct submodules of `Verity.EVM`, and `Frame` is a direct submodule
- No explicit importers in the repo, but it is a direct build target via the glob

### All other Compiler/Proofs/IRGeneration/* files
- **Status: ALL REACHABLE** via `.andSubmodules \`Compiler` glob

---

## 4. Notes on Contracts.Smoke Submodules

The lakefile uses `.one \`Contracts.Smoke` (not `.andSubmodules`). This means only
`Contracts/Smoke.lean` itself is a build root. `Contracts/Smoke.lean` imports only
`Contracts.Smoke.InternalInterfaceSmoke` — the remaining 8 submodules in `Contracts/Smoke/`
are never imported and have been deleted.

`Contracts/Smoke/InternalInterfaceSmoke.lean` is KEPT (imported by `Contracts/Smoke.lean`).

# Solidity import compiler matrix

This is how `scripts/solidity_import_coverage.py` chooses and reports a solc
release for each corpus target. It only affects measurement: it adds no
lowering, and it never changes what the importer accepts.

## Pinned releases

The importer pins seven solc releases (`solcReleases` in
`Compiler/SolidityImport/Import.lean`). `Profile.solc` defaults to
`0.8.34+commit.80d5c536`:

| Release | Linux sha256 | macOS sha256 |
| --- | --- | --- |
| `0.8.38+commit.1835d247` | `65c3180a…8f3243` | `b18ac1d1…e0a2a9` |
| `0.8.35+commit.47b9dedd` | `fa8ac9a3…a617f4` | `6e432580…b19159` |
| `0.8.34+commit.80d5c536` | `d40adc6f…726b39` | `0a282929…fa7746` |
| `0.8.28+commit.7893614a` | `9a0fb7e0…636f25` | `81515b0e…76d9ea` |
| `0.8.26+commit.8a97fa7a` | `d5f23436…f149ef` | `0ff016ae…c30ab9` |
| `0.8.10+commit.fc410830` | `c7effacf…dd06d89` | `a79fff23…dd2a4cc` |
| `0.7.6+commit.7338295f` | `bd69ea85…58a6bb` | `a6a8f9f9…5bd1ab` |

`0.8.35` accepts the importer's `amsterdam` EVM target and passes solc its
`@future` spelling; `0.8.34` and older keep `osaka` as the newest named target.
`0.8.38` accepts `homestead` through `osaka`: it names `amsterdam` (and
`@future`) only behind solc's `settings.experimental` flag, which the importer
does not set for a named target, so the pin rejects `amsterdam` on `0.8.38`.

`IMPORTER_SOLC` and `IMPORTER_DEFAULT_SOLC` in the script mirror these values.
`scripts/test_solidity_import_coverage.py` fails if they drift from the Lean
sources or from the checksums in `scripts/solidity_import_corpus/manifest.json`.

## Selection

A target compiles with exactly one importer release:

1. its manifest `profile.solc`, when a profile is present; otherwise
2. the importer default, `0.8.34+commit.80d5c536`.

The script never infers a release from the source pragma. It never falls back
to a different release, and it never rewrites pragmas. If a profile names a
release outside the pinned set, that is a measurement error, so the contract is
reported as incomplete. That includes a short version such as `0.8.34`, a
mistyped commit, or a legacy release. The script stages the selected release's
verified binary (not the inventory compiler) at
`.lake/solidity-import/solc-<version>`.

## Matrix

For every target, each pinned importer release compiles the entry file and
produces AST output only (`matrix-<version>.json` in the target's artifact
directory). Each row is one of:

- `accepted`: no errors.
- `version_rejected`: solc reported `Source file requires different compiler
  version`. The row records each reported `file:line:column` (byte offsets, as
  the importer counts them) and the full `pragma solidity …;` text there.
- `rejected`: other compiler errors. The first message is kept.

Infrastructure failures make the contract's measurement incomplete. These
include a missing or checksum-mismatched compiler, non-JSON output, or a
version error that has no location or does not point at a `pragma solidity`
directive. Such a contract is never reported as rejected.

A version-rejected entry stops solc before it reads imports. A matrix row
therefore lists only the errors solc actually reported, not every pragma in the
import closure. `accepted` does cover the whole closure, because solc checks
every imported source.

## Version-blocked targets

If the selected release's row is `version_rejected`, solc rejects the source
before the importer selects a root function. One real importer probe (function
0) then serves as the witness for every function in the contract. The witness
is accepted only if:

- the importer rejected the source with a version error,
- the error banner names the selected release
  (`current compiler is <release>.`), so a stale staged binary cannot pass, and
- the reported location is a `pragma solidity` directive in the pinned
  checkout.

The importer submits the whole import closure inline, so its first error may be
an imported file rather than the entry. Every function is then rejected with the
witness's exact location and this reason:

```
source pragma `<pragma>` rejected by importer solc <release> (<selected by>);
pinned importer releases accepting the source: <releases or none>
```

If any check fails, the witness disagrees with the matrix and every function in
the contract is unknown. Unknown functions stay in the denominator, and the
report is incomplete.

If the selected release's row is not `version_rejected`, every function is
probed as before. If a probe still reports a version rejection, the matrix did
not reproduce it, so the function is recorded as unknown.

## Report

`coverage.json` records `importer_solc_releases`, plus a per-contract
`compiler` object with the inventory solc, the selected importer release, how it
was selected, and the matrix rows. `coverage.md` adds a compiler-selection
table. The CI step stays advisory (`continue-on-error`), and the artifact is
always uploaded.

## Current corpus (main `3a549dddd`)

| Target | Inventory solc | Importer solc (selected by) | Pinned releases accepting source | First version blocker |
| --- | --- | --- | --- | --- |
| midnight:Midnight | 0.8.34 | 0.8.34 (default) | 0.8.34 | none |
| uniswap-v2:UniswapV2Pair | 0.5.16 | 0.8.34 (default) | none | `contracts/UniswapV2ERC20.sol:1:1` `pragma solidity =0.5.16;` |
| uniswap-v2:UniswapV2Factory | 0.5.16 | 0.8.34 (default) | none | `contracts/UniswapV2ERC20.sol:1:1` `pragma solidity =0.5.16;` |
| uniswap-v2:UniswapV2ERC20 | 0.5.16 | 0.8.34 (default) | none | `contracts/UniswapV2ERC20.sol:1:1` `pragma solidity =0.5.16;` |
| uniswap-v3:UniswapV3Pool | 0.7.6 | 0.8.34 (default) | none | `contracts/NoDelegateCall.sol:2:1` `pragma solidity =0.7.6;` |
| uniswap-v3:UniswapV3Factory | 0.7.6 | 0.8.34 (default) | none | `contracts/NoDelegateCall.sol:2:1` `pragma solidity =0.7.6;` |
| pareto (3 targets) | 0.8.10 | 0.8.10 (profile) | 0.8.10 | none |
| openzeppelin:ERC20, ERC4626 | 0.8.34 | 0.8.34 (default) | 0.8.34 | none |

All 53 Uniswap functions have the same actual blocker: no importer-pinned
release satisfies their exact `=0.5.16` or `=0.7.6` pragmas, and choosing a
different pinned release with a manifest profile would not help. Unblocking
them would mean pinning a legacy solc in the importer itself (for example AST
schema support for 0.5/0.7 in `Import.lean`). That is outside this instrument.

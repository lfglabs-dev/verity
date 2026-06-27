# Verity Architecture

This page is the contributor map for Verity. It explains where a source feature
enters the system, which proof layer owns it, which trust report should mention
it, and which tests should fail if it regresses.

For the public user-facing version, see `docs-site/content/architecture.mdx`.

## End-to-end Pipeline

```
verity_contract source
  -> macro elaboration
  -> CompilationModel
  -> IR
  -> Yul
  -> solc bytecode
```

| Stage | Main files | Owns | Proof / trust status |
|---|---|---|---|
| Source syntax and executable semantics | `Verity/Core.lean`, `Verity/Macro/*` | Contract author surface, storage declarations, source helpers, executable Lean definitions | Layer 1 bridge to `CompilationModel` for the macro-lowered image |
| CompilationModel | `Compiler/CompilationModel/*`, `Compiler/ECM.lean` | Declarative storage, params, statements, events, externals, ECMs, validation, trust-surface collection | Layer 2 source of truth; full model is wider than the proved fragment |
| IR generation and proofs | `Compiler/Proofs/IRGeneration/*` | Supported-fragment witnesses, helper-aware source semantics, IR lowering correctness | Generic Layer 2 theorem for `SupportedSpec` |
| Yul generation and native bridge | `Compiler/Codegen.lean`, `Compiler/Yul/*`, `Compiler/Proofs/YulGeneration/*` | Dispatcher, ABI loads, runtime helpers, Yul AST, EVMYulLean bridge | Layer 3 theorem surface plus explicit bridge hypotheses |
| Bytecode | `solc --strict-assembly` | Final deployment artifact | Trusted boundary |

## Feature Ownership

When adding a source-level feature, update the earliest layer that can express it
precisely. Avoid patching generated Yul when the feature has a stable source or
`CompilationModel` shape.

The machine-readable ownership registry is
[`artifacts/feature_ownership.json`](../artifacts/feature_ownership.json). It
records whether major surfaces are source-supported, compiler-supported,
proof-modeled, trust-reported, or deprecated, and should be updated when a
compatibility shim is added or a proof boundary changes.

| Feature kind | Preferred owner | Examples | Notes |
|---|---|---|---|
| Ordinary source syntax | `Verity/Macro/*` | `internal` source helpers, storage declarations, ABI-shaped parameters | Must lower to ordinary `CompilationModel` fields/functions/statements. |
| Storage layout metadata | `Verity/Macro/Translate.lean` plus `Compiler/CompilationModel/*` | `MappingStruct`, `MappingStruct2`, fixed arrays inside struct members | Keep layout reviewable as named members and word offsets. |
| Reusable low-level mechanics | `Compiler/Modules/*` ECMs | ERC-20 wrappers, callbacks, CREATE2, SSTORE2, precompiles | Must expose assumptions through `axioms` and trust reports. |
| New primitive mechanic | `Compiler/CompilationModel/Types.lean` and `TrustSurface.lean` | `create2`, `extcodecopy`, `codecopy` | Add deny-flag classification when the mechanic is outside the proof model. |
| Proof-complete widening | `Compiler/Proofs/*` and boundary catalogs | New supported statement forms, helper-summary consumption | Do not claim full verification until the relevant theorem consumes the feature. |

## Current Solidity-facing Surfaces

These are easy to miss because they cross source syntax, layout, ECMs, and trust
reporting:

- Source-level `internal` functions compile as internal helper specs, are omitted
  from selector dispatch and ABI output, and must not be used for `receive` or
  `fallback` entrypoints.
- Source-level `interfaces` are syntax over the existing external-call module
  path. Interface-typed parameters erase to `Address`; typed dot calls lower to
  `Calls.withReturnModule` and stay visible in trust reports as ECM calls.
- `MappingStruct` and `MappingStruct2` support fixed-array members by expanding
  them into stable member names such as `roots[1]` and `proof[1][1]`. The
  expanded names are the storage-access names used by `structMember` and
  `setStructMember`.
- Dynamic calldata structs and arrays are represented through the existing ABI
  head/element machinery. Do not add one-off Yul rewrites when a typed
  parameter-load path already exists.
- Callback helpers live in `Compiler.Modules.Callbacks` and own the ABI frame
  for selector plus static arguments plus dynamic bytes. Protocol behavior of
  the callback target remains an assumption.
- CREATE2 and SSTORE2-style code-as-data live in
  `Compiler.Modules.Create2SSTORE2`. They lower the mechanics directly and
  surface `create2_initcode_layout`, `create2_address_derivation`, and
  `sstore2_pointer_code_layout` as assumptions.

## Trust-surface Rule

If a feature uses a mechanic that the proof interpreters do not fully model, the
compiler must make that visible.

1. Add a typed `CompilationModel` or ECM representation.
2. Classify the mechanic in `Compiler/CompilationModel/TrustSurface.lean`.
3. Add or update `--deny-*` behavior if users need a fail-closed gate.
4. Add a trust-report test in `Compiler/CompilationModelFeatureTest.lean`.
5. Document the assumption in `docs/EXTERNAL_CALL_MODULES.md`,
   `docs/VERIFICATION_STATUS.md`, `docs-site/content/capabilities.mdx`, or the
   narrower page for that surface.

## Checklist for New Solidity-facing Features

- Source syntax or API documented under `docs-site/content/edsl/` (the relevant
  EDSL reference page) or the relevant guide.
- `CompilationModel` representation is typed and validated; no ad hoc string
  patching of generated Yul.
- Mutability, selector/ABI visibility, result binding, and local scoping are
  tested.
- Storage layout changes have smoke tests for resolved names and word offsets.
- Low-level mechanics are collected by `TrustSurface.lean` and covered by
  `--trust-report`.
- ECMs list every protocol assumption in `axioms`.
- `Compiler/CompilationModelFeatureTest.lean` covers lowering and reports.
- `Contracts/Smoke.lean` or a focused contract test covers the source surface.
- Generated Foundry/property fixtures are updated when the macro property
  surface changes.
- Public docs and repo docs name both the supported behavior and the remaining
  proof/trust boundary.

## Fast Regression Commands

Use focused checks before the full suite:

```bash
lake build Verity.Macro.Translate
lake build Contracts.Smoke Compiler.CompilationModelFeatureTest
python3 scripts/check_macro_property_test_generation.py
python3 scripts/check_trust_surface_registry.py
```

Then run the full gate:

```bash
make check
```

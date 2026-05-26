# Verity Intrinsics

`verity_intrinsic` is the extension point for consumer-owned opcode bindings.
It lets a downstream package use an EVM primitive before Verity or EVMYulLean
models it as a first-class builtin.

The motivating example is EIP-7939 `CLZ`. Tamago can declare `clz` in its own
tree, compile calls to `verbatim_1i_1o(hex"1e", x)`, and keep the CLZ trust
assumption local to Tamago. Verity stays opcode-agnostic and does not add a
project-level axiom for every new opcode.

## When to Use This

Use an intrinsic when all of the following are true:

- The target behavior is a single EVM primitive or named Yul builtin.
- The opcode is not yet modeled as a proven Verity/EVMYulLean builtin.
- The consumer can state the source-level Lean semantics that proofs should use.
- The consumer is willing to own the trust obligation until the opcode is
  modeled upstream.

Do not use an intrinsic for multi-step libraries, contract calls, precompile
protocols, or code whose behavior should be audited as ordinary linked Yul.
Those belong in External Call Modules, linked libraries, or first-class compiler
support.

## Declaration

```lean
verity_intrinsic clz (x : Uint256) : Uint256 where
  pure;
  yul := verbatim 1 1 (hex "1e");
  min_fork := fusaka;
  semantics :=
    fun x =>
      Verity.Core.Uint256.ofNat
        (if x.toNat = 0 then 256 else 255 - Nat.log2 x.toNat);
  obligation [clz_matches_eip7939 :=
    assumed "EIP-7939 CLZ opcode; chain must be Fusaka+"]
```

Lean proofs can use the generated wrapper `clz x`. Verity contract bodies use
the explicit intrinsic form so the compiler sees the lowering descriptor:

```lean
let leadingZeros :=
  intrinsic_fusaka "clz" (Verity.Core.Intrinsics.YulLowering.verbatim 1 1 "1e") [x]
```

The three-argument contract form can infer `min_fork` only when the
`verity_intrinsic` declaration is in the same elaboration session. Cross-module
uses should use the explicit fork form shown above:
`intrinsic_cancun`, `intrinsic_prague`, `intrinsic_fusaka`, or
`intrinsic_osaka` (alias for Fusaka).

The declaration has five responsibilities:

- `pure` states that the intrinsic has no storage, environment, or external-call
  effects.
- `yul := verbatim N M (hex "...")` states the compiler lowering. The generated
  Yul call is `verbatim_Ni_Mo(hex"...", args...)`.
- `min_fork := ...` records the minimum chain fork where the emitted opcode is
  valid. Verity enforces this fail-closed: builds targeting an older fork error
  unless the caller explicitly passes `--allow-future-fork-intrinsics`.
- `semantics := ...` is the Lean function used by source-level and consumer
  proofs.
- `obligation [...]` names the consumer-owned trust boundary. While the
  obligation is `assumed`, the consumer must document it in its own `AXIOMS.md`.

## Trust Model

Intrinsics deliberately keep Verity's project-level axiom count at zero. The
trust boundary is generated in the consumer namespace from the declaration's
obligation clause and should appear in the consumer repository's axiom/trust
documentation.

For an assumed intrinsic, reviewers should check:

- the emitted opcode bytes or builtin name match the intended EVM primitive;
- the `semantics` function matches the EIP or target-chain behavior, including
  edge cases such as `clz(0)`;
- the `min_fork` is correct for the deployment target;
- the obligation text names the EIP, fork assumption, and any temporary nature
  of the trust boundary.

This is a consumer trust boundary, not a Verity proof-system axiom. Verity's
own `AXIOMS.md` remains the registry of project-level axioms and should stay at
zero unless Verity itself introduces an axiom.

## Fork Targeting

The pinned EVMYulLean fork used by Verity declares
`EvmYul.TargetSchedule := "Cancun"` and models Cancun-era opcodes such as
`BLOBHASH`, `BLOBBASEFEE`, `TLOAD`, `TSTORE`, `MCOPY`, and `PUSH0`. For that
reason, Verity's intrinsic fork enum starts at `cancun`.

Supported intrinsic fork labels are:

- `cancun`
- `prague`
- `fusaka`
- `osaka` as an accepted alias for the Fusaka execution-layer fork name

The compiler default is `--target-fork cancun`. Use `--target-fork prague` or
`--target-fork fusaka` for newer deployments. Parity packs set the target from
their `evmVersion` when possible. If a build intentionally emits newer-fork
intrinsics while using an older target, it must pass
`--allow-future-fork-intrinsics`; otherwise compilation fails before Yul is
written.

## Audit Surface

Consumer builds that use intrinsics should archive the normal compiler
artifacts, the selected `--target-fork`, and the `verity_intrinsic`
declarations they rely on. A future machine-readable trust-report entry should
include:

- intrinsic name;
- emission mode (`verbatim_Ni_Mo` or named builtin);
- opcode bytes or builtin name;
- minimum fork;
- obligation name and status;
- declaration source location.

Until trust-report integration is complete, reviewers should grep the consumer
tree for `verity_intrinsic` and audit each declaration manually.

## Current Implementation Scope

This branch implements the generic intrinsic path needed by consumers such as
Tamago:

- syntax for `verity_intrinsic`;
- a Lean wrapper using the declared consumer semantics;
- `CompilationModel.Expr.intrinsic`;
- Yul lowering from the declaration's `yul := ...` clause;
- validation plumbing so intrinsic arguments participate in purity and usage
  checks.
- fail-closed `min_fork` enforcement through `YulEmitOptions.targetFork`, the
  `--target-fork` CLI flag, and the explicit
  `--allow-future-fork-intrinsics` override.
- proof plumbing for the Verity-owned part of the feature:
  `Compiler.Proofs.IRGeneration.IntrinsicProofs` proves the fork-order facts,
  intrinsic argument scope accounting, generic verbatim/builtin lowering shape, and
  fail-closed arity rejection.
- fail-closed proof-fragment coverage: `SupportedSpec` and helper-aware source
  semantics classify intrinsics as unsupported/unmodeled until opcode semantics
  are available.
- usage-analysis plumbing recurses through intrinsic arguments so helper
  requirements are not missed by code generation.

Machine-readable intrinsic trust-report rows are still future hardening; the
build-time fork gate is enforced now.

These proofs intentionally stop before opcode semantics. Until EVMYulLean
models CLZ, the statement "opcode `0x1e` computes the declared Lean semantics"
remains the consumer-owned obligation documented next to the
`verity_intrinsic` declaration.

## Upgrade Path

When EVMYulLean models the opcode, the consumer should replace the `assumed`
obligation with a proved bridge to the upstream semantics. Call sites and Yul
emission do not need to change.

For CLZ, the intended path is:

1. Tamago declares `clz` as an assumed intrinsic and documents
   `clz_matches_eip7939`.
2. Verity emits `verbatim_1i_1o(hex"1e", x)` for Tamago builds targeting
   Fusaka-or-later chains.
3. EVMYulLean adds first-class CLZ semantics.
4. Tamago flips the obligation from assumed to proved, removing the consumer
   trust assumption without changing source call sites.

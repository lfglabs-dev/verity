# Verity Intrinsics

`verity_intrinsic` lets consumers register opcode-level primitives (e.g. CLZ / EIP-7939) without modifying Verity.

## Declaration Shape (prototype)

```lean
verity_intrinsic clz (x : Uint256) : Uint256 where pure; yul := verbatim 1 1 (hex "1e"); min_fork := fusaka; semantics := (fun x => x); obligation [clz_matches_eip7939 := assumed "EIP-7939 CLZ opcode; chain must be Fusaka+"]
```

Use site: `let c := clz x`.

## Yul Emission (minimal implementation)

For a `verbatim N M (hex "XX")` clause the compiler emits:

```
verbatim_Ni_Mo(hex"XX", arg0, ...)
```

See `Compiler/CompilationModel/ExpressionCompile.lean` (intrinsic case) and the CLZ example in `Contracts/Smoke.lean`.

## Trust Model

- One consumer-namespaced obligation marker per intrinsic.
- `--trust-report` integration is still planned.
- `min_fork` hard-error enforcement is still planned.
- Verity AXIOMS.md stays at 0 project axioms.

See `TRUST_ASSUMPTIONS.md` § "Trusted Intrinsics" and `AXIOMS.md`.

## Upgrade Path

When EVMYulLean models the opcode, the consumer obligation can be changed from `assumed` to `proved` with no change to call sites.

## Adding an Intrinsic (for contributors)

1. Add the declaration in your consumer tree (no Verity change needed after this mechanism lands).
2. Document the obligation in your AXIOMS.md.
3. (Optional) later: upstream opcode to EVMYulLean + flip status.

See plan.md and the reference byte opcode PR (#1912).

# Low-Level Yul Surface

Verity keeps two low-level escape routes separate:

- First-class typed primitives, such as `Stmt.mstore` and
  `Stmt.calldatacopy`, are kept when they have stable Verity semantics, trust
  reporting, and proof value.
- One-off statements that only expose a single Yul instruction should be helper
  constructors returning `UnsafeYulFragment`, used through `Stmt.unsafeYul`.

Raw Yul is the explicit escape hatch. An `UnsafeYulFragment` carries the EVMYul
AST payload, low-level mechanics, local obligations, scope effects, and
termination metadata at the same boundary. This keeps ad-hoc assembly visible
in trust reports without making every Yul instruction look like a modeled
Verity statement.

When lowered, each fragment is surrounded by comment-only provenance markers.
The checked-arithmetic peephole treats that marked region as opaque, so raw Yul
cannot be mistaken for compiler-generated checked arithmetic or have repeated
operand evaluation changed by the rewrite.

For example, raw memory reverts now use the fragment helper:

```lean
Stmt.unsafeYul
  (UnsafeYulFragment.rawRevert
    (Compiler.Yul.YulExpr.ident "offset")
    (Compiler.Yul.YulExpr.ident "size")
    { name := "raw_revert_memory_slice_refinement"
      obligation := "Caller-provided raw revert memory slice must refine the intended failure payload."
      proofStatus := .assumed })
```

Raw memory reverts should use `UnsafeYulFragment.rawRevert`. Typed primitives such as
`mstore`, `calldatacopy`, and similar common operations should remain
first-class only when Verity commits to their semantics and they are useful in
proofs or audits.

## Yul Temporary Slot Reuse and Scratch-Memory Spilling (`--max-stack-locals`)

To keep large unrolled functions (such as 8-tier `quoteTier` functions with 48+
`let` bindings) within the EVM's 16-slot `DUP`/`SWAP` reach under both
`solc --strict-assembly` and `solc --strict-assembly --optimize`, the compiler
applies `Compiler.Yul.TempReuse.reuseAndSpillTempsObject` (`Compiler/Yul/TempReuse.lean`):

- **Fast-path identity (`countLetBindings stmts ≤ maxStackLocals`, default `12`)**:
  Blocks with at most `maxStackLocals` `let` bindings are returned definitionally
  unchanged (`reuseBlockTemps_eq_self_of_le` in
  `Compiler/Proofs/YulGeneration/TempReuseSoundness.lean`), preserving existing
  artifacts and Layer 2/3 proofs verbatim.
- **Short-lived dead-slot reuse (`letSpanInStmts v rest ≤ 2`)**:
  Intra-tier temporaries whose last use is within 2 subsequent `let` bindings
  reuse dead stack variables via `YulStmt.assign` (`t := rhs`) instead of
  allocating new `let` slots (`reuseDeadLetStep_eval_eq`).
- **Cross-tier scratch-memory spilling (`letSpanInStmts v rest > 2`)**:
  Longer-lived accumulators (whose SSA splitting and expression inlining under
  `solc --strict-assembly --optimize` would otherwise trigger
  `StackTooDeepError`) spill to reusable 32-byte scratch memory slots starting
  at `0x1000` (`4096`) via `mstore(slot, rhs)` / `mload(slot)`
  (`spillLetStep_eval_eq`), whenever the block does not touch linear memory at
  or above `0x1000`.
- **CLI control**: Pass `--max-stack-locals <n>` (default: `12`) to adjust the
  per-block `let`-binding threshold before temporary reuse and spilling kick in.

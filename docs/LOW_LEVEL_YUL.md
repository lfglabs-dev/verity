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

The spill pass is a **trusted, tested-only** component (see
[TRUST_ASSUMPTIONS.md](TRUST_ASSUMPTIONS.md#12-yul-stack-spill-pass-tempreuse)): no theorem
states that its output means the same as its input. It exists to keep blocks with many
`let` bindings within the EVM's 16-slot `DUP`/`SWAP` reach under `solc --strict-assembly`.
Both compile paths, the CLI (`verity-compiler`, every Verity contract) and the Solidity import
model drivers (`Compiler.emitYulSpilled`), apply the same entry point,
`Compiler.Yul.TempReuse.reuseAndSpillTempsStaticObject` (`Compiler/Yul/TempReuse.lean`), to the
deploy and runtime code sections separately:

- **Static memory gate (per code section)**: a section is rewritten only if every memory access
  in it, functions included, has a literal address and a literal length ending at or below
  `0x1000` (`4096`); it does not use `msize`; and every call is a memory-free builtin or a
  function defined in the same section (`sectionMemoryStaticBelow`). An unknown builtin, a
  computed address or length (free-pointer allocations, ABI encodings written from address 0
  with a runtime size, `calldatacopy` of a dynamic argument), and a call to a linked library
  function all fail the gate. A section that fails the gate is emitted **unchanged** (no dead
  variable reuse either); if it is too deep for the stack, `solc` rejects it with `StackTooDeep` instead of the compiler
  emitting spill words that runtime-sized memory traffic could overwrite. The free-memory
  pointer is never moved. Gas is not preserved: a spilling section expands memory to just
  above its highest spill word (about 4.1 KB) and adds `mstore`/`mload`s, so `gas()` values and
  out-of-gas margins differ from the unspilled code.
- **Fast path**: inside a gated section, a block with at most `maxStackLocals` `let` bindings
  (default `12`) is returned unchanged. (`reuseBlockTemps_eq_self_of_le` in
  `Compiler/Proofs/YulGeneration/TempReuseSoundness.lean` states this for the single-block
  function `reuseBlockTemps`, which no compile path calls; it is not a theorem about the
  pass.)
- **Short-lived dead-slot reuse**: a `let` whose value is used within the next 2 `let`
  bindings may reuse a dead stack variable of the same block via `t := rhs`.
- **Scratch-memory spilling**: other `let`s past the stack budget spill to 32-byte words from
  `0x1000` via `mstore(slot, rhs)` / `mload(slot)`. A block's new words start above every word
  its (already rewritten) nested blocks use, so a nested block never overwrites a live word of
  an enclosing block; sibling blocks may share words.
- **Never spilled**: function bodies (and blocks inside them), because a word would be shared by
  a caller and its callee or by recursive frames; and `for` initialisers, whose variables stay
  live in the condition, body and post block. They only reuse dead stack variables, and a
  `for` initialiser never reuses its own variables, which are live after the initialiser.
- **Not proven**: slot selection, liveness (`findDeadStackVar`, `findFreeSpillSlot`), the
  nested-block rule, function and loop handling, and the gate itself are covered by
  `Compiler/MainTest.lean` cases, the Foundry tests `test/SpillReturnArraySmoke.t.sol` and
  `test/SpillFreeMemorySmoke.t.sol`, and differential tests only.
  `reuseDeadLetStep_eval_eq` and `spillLetStep_eval_eq` are single-step lemmas over a toy
  word-keyed state; the `computedSpillBase` theorems in `Compiler/Codegen/Profile.lean` are
  about a spill base that no compile path uses.
- **CLI control**: Pass `--max-stack-locals <n>` (default: `12`) to adjust the
  per-block `let`-binding threshold before temporary reuse and spilling kick in.

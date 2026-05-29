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

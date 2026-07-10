# Panic Surface #1999 Spec

## Existing State

The `feat-1999-panic-surface` branch already contains a partial Solidity panic
surface for checked `uint256` arithmetic:

- `Verity.Stdlib.Math` exposes `addPanic`, `subPanic`, `mulPanic`, and
  `divPanic` as source-level bind helpers.
- `Verity.Macro.Translate.Expr` lowers those helpers to the same IR shape as
  `requireSomeUint (safeXxx a b) "<fixed Panic message>"`.
- `Compiler.CodegenCommon` recognizes the generated guard-plus-operation Yul
  pattern and replaces it with checked arithmetic helper calls.
- `Compiler.CompilationModel.DynamicData` defines `solidityPanicPayload` and
  emits Solidity's `Panic(uint256)` ABI payload:
  selector `0x4e487b71`, ABI word `code`, and `revert(0, 36)`.
- `Compiler.CompilationModelFeatureTest` checks that arithmetic smoke contracts
  compile to the checked helpers and to the observable panic payload bytes for
  codes `0x11` and `0x12`.

## Missing Pieces

1. General source/IR primitive: there is no first-class `panic(code)` source
   form or IR statement/expression. Today the surface is limited to arithmetic
   shorthands that encode panic intent through fixed revert-message strings.

2. Typed code set: the panic codes are plain `Nat` literals at the Yul helper
   layer. A small enum or validated wrapper would make supported codes explicit
   and avoid accidental non-Solidity panic payloads.

3. Revert-payload observability in the model: executable semantics still expose
   string reverts for these helpers. The Yul backend payload is tested by string
   containment, but there is no shared IR/model value that records
   `Panic(uint256)` payload bytes for proof reuse.

## Proposed Next Slice

Add a narrow IR-level panic representation before broadening the source macro:

```lean
inductive PanicCode where
  | arithmeticOverflow
  | divisionByZero

def PanicCode.toNat : PanicCode -> Nat
  | .arithmeticOverflow => 0x11
  | .divisionByZero => 0x12
```

Then add either `Stmt.panic PanicCode` or a small typed revert-payload node and
lower existing arithmetic helpers through it. Keep the current string-message
compatibility tests while adding one proof/test that `PanicCode.divisionByZero`
lowers to selector `0x4e487b71`, code word `18`, and length `36`.

This preserves the landed arithmetic parity while giving #1999 a reusable
surface for Morpho-Midnight parity cases that need explicit `panic(code)`.

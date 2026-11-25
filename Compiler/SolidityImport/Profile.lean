/-!
Compiler settings for a Solidity import.

A profile is an ordinary value, so it can be named, reused and `#print`ed:

```lean
def build : Profile :=
  { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
```

The settings are passed to solc and are part of the import digest. They should
match the settings the audited bytecode is built with.

`collectUnsupported` is not a solc setting and is not part of the digest: it
only changes how the importer reports failures (see `docs/SOLIDITY_IMPORT.md`,
"Collecting every unsupported construct"). An import without failures yields
the same model and report with the flag on or off.
-/
namespace Compiler.CompilationModel.SolidityImport

structure Profile where
  /-- Exact solc release. The importer accepts only its pinned releases
      (0.7.6, 0.8.10, 0.8.26, 0.8.28, 0.8.34, 0.8.35 and 0.8.38 with their exact
      commit suffixes). The legacy release admits only its documented scalar subset.
      Solc 0.8.35 adds the `amsterdam` target, lowered to its `@future` fork;
      0.8.38 accepts targets up to `osaka`. -/
  solc : String := "0.8.34+commit.80d5c536"
  evmVersion : String
  viaIR : Bool
  /-- Optimizer runs; `none` disables the optimizer. -/
  optimizerRuns : Option Nat
  /-- solc `metadata.bytecodeHash`, e.g. `"none"` or `"ipfs"`. -/
  bytecodeHash : String
  /-- Survey mode: record every unsupported construct a root reaches instead of
      failing at the first one. A root with a recorded construct is reported
      `unsupported` and the import then emits no model and no theorems. -/
  collectUnsupported : Bool := false
  deriving Repr, BEq, Inhabited

end Compiler.CompilationModel.SolidityImport

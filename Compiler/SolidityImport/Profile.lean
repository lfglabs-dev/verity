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

`linkedLibrariesMatchSource` is not a solc setting either, but it changes the
model, so it is part of the digest when set (see `docs/SOLIDITY_IMPORT.md`,
"Linked library calls").
-/
namespace Compiler.CompilationModel.SolidityImport

structure Profile where
  /-- Exact solc release. The importer accepts only its pinned releases
      (0.7.6, 0.8.10, 0.8.26, 0.8.28, 0.8.34 and 0.8.35 with their exact commit
      suffixes). The legacy release admits only its documented scalar subset.
      Solc 0.8.35 adds the `amsterdam` target, lowered to its `@future` fork. -/
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
  /-- Trust assumption, off by default: every library a `DELEGATECALL` reaches is linked to
      an account whose code behaves as solc's compilation of that library in this same
      solc input. With it, a direct `L.f(...)` call of a `public` or `external` library
      function with value-type or `storage` arguments and value-type results inlines
      `f`'s body (the call frame is the caller's: same storage, `msg.sender`,
      `msg.value` and `address(this)`; the library's revert data is forwarded), and each
      root records the calls it relies on. Without it such calls are rejected. -/
  linkedLibrariesMatchSource : Bool := false
  deriving Repr, BEq, Inhabited

end Compiler.CompilationModel.SolidityImport

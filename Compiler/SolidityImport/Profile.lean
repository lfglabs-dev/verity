/-!
Compiler settings for a Solidity import.

A profile is an ordinary value, so it can be named, reused and `#print`ed:

```lean
def build : Profile :=
  { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
```

The settings are passed to solc and are part of the import digest. They should
match the settings the audited bytecode is built with.
-/
namespace Compiler.CompilationModel.SolidityImport

structure Profile where
  /-- Exact solc release. The importer accepts only its pinned release. -/
  solc : String := "0.8.34+commit.80d5c536"
  evmVersion : String
  viaIR : Bool
  /-- Optimizer runs; `none` disables the optimizer. -/
  optimizerRuns : Option Nat
  /-- solc `metadata.bytecodeHash`, e.g. `"none"` or `"ipfs"`. -/
  bytecodeHash : String
  deriving Repr, BEq, Inhabited

end Compiler.CompilationModel.SolidityImport

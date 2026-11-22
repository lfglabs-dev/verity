import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential

/-!
An internal library function over a storage mapping is modeled by its own body, whatever the
library and function are called (`MappingLibraryNameIndependence.sol`,
`MappingLibraryAssemblyFlip.sol`).

In a contract with more than one state variable, a three-argument `flipTick` of a library named
`TickBitmap` used to be replaced by a fixed bitmap update: sign-extend both arguments, revert
empty unless `tick` is a multiple of `tickSpacing`, then XOR bit `(tick / tickSpacing) mod 256` of
word `(tick / tickSpacing) >> 8`, whatever the body did. `viaTickName` below, whose `flipTick`
ORs bit `tick mod 256` of word `tick >> 8`, then imported silently as that update. The same body
in another library (`viaOtherName`) imported as written. Both now take the ordinary helper
lowering and agree with solc.
-/
namespace SolidityImportSmoke.MappingLibraryNameIndependenceChecks
open Compiler.CompilationModel Denote Verity.Core

solidity_profile mappingLibraryName where
  evmVersion := "osaka"
  viaIR := true
  optimizerRuns := some 466
  bytecodeHash := "none"

solidity_import named from "Contracts/SolidityImportSmoke" entry "MappingLibraryNameIndependence.sol"
  using mappingLibraryName
  contract MappingLibraryNameIndependence
  function viaTickName(int24, int24)
  function viaOtherName(int24, int24)

/-- An `int24` argument as its ABI word. -/
private def int24Word (v : Int) : Nat := (v % 2 ^ 256).toNat

/-- Status and returned words of `name(tick, spacing)` in the imported model, from empty storage. -/
private def observe (name : String) (tick spacing : Int) : Option (Bool × List Nat) := do
  let fn ← named.model.functions.find? (·.name == name)
  let r := denoteFunction SolidityImport.Differential.oracle named.model fn
    {sender := 0, functionSelector := 0, args := [int24Word tick, int24Word spacing]}
    Verity.defaultState
  return (r.success, if r.success then
    (if r.returnWords.isEmpty then r.returnValue.toList else r.returnWords) else [])

-- Status and returned word observed from solc 0.8.26 (cancun) and 0.8.34 (osaka) via-IR, which
-- agree, each from a fresh deployment. Revert data is not compared here.
#guard observe "viaTickName" 10 5 == some (true, [2 ^ 10])
#guard observe "viaTickName" (-1) 1 == some (true, [2 ^ 255])
#guard observe "viaTickName" 300 60 == some (true, [2 ^ 44])
#guard observe "viaTickName" 10 0 == some (false, [])
#guard observe "viaTickName" (-300) 60 == some (true, [2 ^ 212])
#guard observe "viaTickName" 7 5 == some (true, [2 ^ 7])
#guard observe "viaOtherName" 10 5 == some (true, [2 ^ 10])
#guard observe "viaOtherName" (-1) 1 == some (true, [2 ^ 255])
#guard observe "viaOtherName" 300 60 == some (true, [2 ^ 44])
#guard observe "viaOtherName" 10 0 == some (false, [])
#guard observe "viaOtherName" (-300) 60 == some (true, [2 ^ 212])
#guard observe "viaOtherName" 7 5 == some (true, [2 ^ 7])

-- A `TickBitmap.flipTick` written in inline assembly (the structure of Uniswap v4's) is lowered
-- through its body: a located rejection where it reads the free-memory pointer to build its
-- custom-error revert payload, which the ordinary Yul lowering admits only to restore the pointer
-- or place a bubbled revert.
/--
error: MappingLibraryAssemblyFlip.sol:13:28: YulFunctionCall: [solidity-import:unsupported] Yul reads of the free-memory pointer may only restore it or place a bubbled revert
closure: MappingLibraryAssemblyFlip.flip -> TickBitmap.flipTick
mload(0x40)
-/
#guard_msgs in
solidity_import assemblyFlip from "Contracts/SolidityImportSmoke" entry "MappingLibraryAssemblyFlip.sol"
  using mappingLibraryName
  contract MappingLibraryAssemblyFlip
  function flip(int24, int24)

end SolidityImportSmoke.MappingLibraryNameIndependenceChecks

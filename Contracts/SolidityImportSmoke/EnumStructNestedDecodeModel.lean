import Compiler.SolidityImport.Import
import Compiler.SolidityImport.SequenceRunner
import Compiler.SolidityImport.Differential
import Compiler.CompilationModel
import Compiler.Codegen
import Compiler.Yul.PrettyPrint

namespace SolidityImportSmoke.EnumStructNestedDecodeModel
open Compiler.CompilationModel

solidity_import imported from "Contracts/SolidityImportSmoke" entry "EnumStructNestedDecode.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract EnumStructNestedDecode
  function writePacked(uint64,uint8,uint64,bool)
  function writeLevelParam(Level)
  function readLevelCast()
  function isHigh()
  function readUnusedLevel()
  function copyPackedToMemory()
  function pushAndReadArray(uint64,uint8,uint64,bool)
  function decodeOuter(bytes)
  function decodeOuterTuple(bytes)
  function decodeInterfaceConfig(bytes)
  function processInterfaceOrder(IRegistry.Order)
  function sumInterfaceItems(«IRegistry.Item[]»)

def model : CompilationModel := imported.model
def oracle : Denote.DenoteOracle := SolidityImport.Differential.oracle

end SolidityImportSmoke.EnumStructNestedDecodeModel

def main (args : List String) : IO UInt32 := do
  match args with
  | ["compile", selectorsFile, output] =>
      let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile selectorsFile))
      let selectors ← IO.ofExcept do
        (← parsed.getArr?).toList.mapM fun j => j.getNat?
      let compiled ← IO.ofExcept (Compiler.CompilationModel.compile
        SolidityImportSmoke.EnumStructNestedDecodeModel.model selectors .osaka)
      IO.FS.writeFile output (Compiler.Yul.render (Compiler.emitYulSpilled compiled))
      return 0
  | _ =>
      Compiler.CompilationModel.SolidityImport.SequenceRunner.run
        SolidityImportSmoke.EnumStructNestedDecodeModel.model
        SolidityImportSmoke.EnumStructNestedDecodeModel.oracle args

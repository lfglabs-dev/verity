import Compiler.SolidityImport.Import
import Compiler.SolidityImport.SequenceRunner
import Compiler.SolidityImport.Differential
import Compiler.CompilationModel
import Compiler.Codegen
import Compiler.Yul.PrettyPrint

namespace SolidityImportSmoke.StructStringMemberParamSequenceModel
open Compiler.CompilationModel
solidity_import imported from "Contracts/SolidityImportSmoke" entry "StructStringMemberParamSequence.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract SequenceFixture
  function change(uint256)
  function fail()
  function read()
  function scalarsBesideString(LabeledStruct)
  function labelLength(LabeledStruct)
  function labelHash(LabeledStruct)
  function labelLengthCalldata(LabeledStruct)
  function labelHashCalldata(LabeledStruct)
  function taggedDigest(Tagged)
  function storeLabel(LabeledStruct)
  function readLabel()
  function storeLabelCalldata(LabeledStruct)
  function nestedName(Outer)
  function nestedNameCalldata(Outer)
def model : CompilationModel := imported.model

/-- The ABI parameter types of the imported roots named `fn`. -/
def paramTypesOf (fn : String) : Option (List ParamType) :=
  (model.functions.find? (·.name == fn)).map (·.params.map (·.ty))

/-- A `string` struct member keeps the `string` ABI type (`AbiSchema.memberType`
of `bytesField _ true`); the selectors and ABI of the model depend on it. -/
example : paramTypesOf "scalarsBesideString" = some [.tuple [.uintN 16, .bool, .string]] := by rfl

/-- The `bytes`-typed reading of the same member is not the imported ABI. -/
example : paramTypesOf "scalarsBesideString" ≠ some [.tuple [.uintN 16, .bool, .bytes]] := by
  intro h
  cases h

/-- A `string` beside a `bytes` member: each keeps its own ABI type. -/
example : paramTypesOf "taggedDigest" = some [.tuple [.string, .uint256, .bytes]] := by rfl

/-- A `string` inside a nested dynamic struct. -/
example : paramTypesOf "nestedName" =
    some [.tuple [.uint256, .tuple [.string, .uint256, .bytes]]] := by rfl

-- Mapping slots use the actual Keccak oracle shared with differential execution.
def oracle : Denote.DenoteOracle := SolidityImport.Differential.oracle
end SolidityImportSmoke.StructStringMemberParamSequenceModel

def main (args : List String) : IO UInt32 := do
  match args with
  | ["compile", selectorsFile, output] =>
      let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile selectorsFile))
      let selectors ← IO.ofExcept do
        (← parsed.getArr?).toList.mapM fun j => j.getNat?
      let compiled ← IO.ofExcept (Compiler.CompilationModel.compile
        SolidityImportSmoke.StructStringMemberParamSequenceModel.model selectors .osaka)
      IO.FS.writeFile output (Compiler.Yul.render (Compiler.emitYul compiled))
      return 0
  | _ =>
      Compiler.CompilationModel.SolidityImport.SequenceRunner.run
        SolidityImportSmoke.StructStringMemberParamSequenceModel.model SolidityImportSmoke.StructStringMemberParamSequenceModel.oracle args

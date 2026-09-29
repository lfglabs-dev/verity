import Compiler.SolidityImport.Differential

namespace SolidityImportSmoke.ErrorPayloads
open Compiler.CompilationModel Compiler.CompilationModel.Denote

private def errors : List ErrorDef := [
  { name := "Unauthorized", params := [] },
  { name := "BadValue", params := [.uint256, .address, .bool] },
  { name := "AReallyLongErrorNameThatCrossesAWordBoundary", params := [.uint256] }]

def runChecks : IO Unit := do
  let oracle := SolidityImport.Differential.oracle
  let emptyExpected : List UInt8 := [0x08, 0xc3, 0x79, 0xa0] ++ wordBytes 32 ++ wordBytes 0
  unless errorStringBytes "" == emptyExpected do throw (IO.userError "empty Error(string) differs")
  let unicodeExpected : List UInt8 := [0x08, 0xc3, 0x79, 0xa0] ++ wordBytes 32 ++ wordBytes 2 ++
    [0xc3, 0xa9] ++ List.replicate 30 0
  unless errorStringBytes "é" == unicodeExpected do throw (IO.userError "UTF-8 Error(string) differs")
  -- Selectors independently computed with Ethereum Keccak, including a signature
  -- spanning multiple words; actual solc/EVM differential coverage is separate.
  unless customErrorBytes oracle errors "Unauthorized" [] == some [0x82, 0xb4, 0x29, 0x00] do
    throw (IO.userError "zero-argument custom error differs")
  let expected : List UInt8 := [0x6a, 0x5e, 0xeb, 0xe1] ++ wordBytes 7 ++ wordBytes 9 ++ wordBytes 1
  unless customErrorBytes oracle errors "BadValue" [7, 9, 1] == some expected do
    throw (IO.userError "static custom error differs")
  unless customErrorBytes oracle errors "AReallyLongErrorNameThatCrossesAWordBoundary" [7] ==
      some ([0x0d, 0xf8, 0x7d, 0xad] ++ wordBytes 7) do
    throw (IO.userError "multi-word error signature differs")
  for (name, declarations, values) in [
      ("Missing", errors, []), ("Unauthorized", errors, [1]),
      ("BadValue", errors, [7, 9, 2]),
      ("Unauthorized", errors ++ [{ name := "Unauthorized", params := [] }], []),
      ("Narrow", [{ name := "Narrow", params := [.uintN 8] }], [256]),
      ("InvalidWidth", [{ name := "InvalidWidth", params := [.uintN 17] }], [0]),
      ("Dynamic", [{ name := "Dynamic", params := [.bytes] }], [0])] do
    unless (customErrorBytes oracle declarations name values).isNone do
      throw (IO.userError s!"unsupported custom error accepted: {name}")
  let state : DenoteState := { world := Verity.defaultState, bindings := [], errors }
  match execStmt oracle [] state (.require (.literal 0) "é") with
  | .revertWithData bytes =>
      unless bytes == unicodeExpected do throw (IO.userError "require lost its message bytes")
  | _ => throw (IO.userError "require did not preserve rich revert")
  match execStmt oracle [] state (.requireError (.literal 0) "BadValue"
      [.literal 7, .literal 9, .literal 1]) with
  | .revertWithData bytes =>
      unless bytes == expected do throw (IO.userError "requireError lost its argument bytes")
  | _ => throw (IO.userError "requireError did not preserve rich revert")
  match execStmt oracle [] state (.revertError "BadValue"
      [.literal 7, .literal 9, .literal 1]) with
  | .revertWithData bytes =>
      unless bytes == expected do throw (IO.userError "revertError lost its argument bytes")
  | _ => throw (IO.userError "revertError did not preserve rich revert")
  IO.println "Exact message/custom-error payload and fail-closed scalar checks passed"
end SolidityImportSmoke.ErrorPayloads

def main : IO Unit := SolidityImportSmoke.ErrorPayloads.runChecks

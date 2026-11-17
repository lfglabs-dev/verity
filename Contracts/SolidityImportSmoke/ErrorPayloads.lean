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
  -- `bytesN` parameters hash as `bytesN` and encode as left-aligned words.
  let selectorWord := 0xdeadbeef * 2 ^ 224
  unless customErrorBytes oracle [{ name := "LockedSelector", params := [.bytesN 4] }]
      "LockedSelector" [selectorWord] == some ([0xc2, 0xf3, 0xb4, 0x73] ++ wordBytes selectorWord) do
    throw (IO.userError "bytes4 custom error differs")
  let tagWord := 0x7f * 2 ^ 248
  let prefixWord := 0x0102030405060708090a0b0c * 2 ^ 160
  unless customErrorBytes oracle
      [{ name := "Tagged", params := [.bytesN 1, .uint256, .bytesN 12] }] "Tagged"
      [tagWord, 5, prefixWord] ==
      some ([0x0a, 0x99, 0xab, 0x28] ++ wordBytes tagWord ++ wordBytes 5 ++ wordBytes prefixWord) do
    throw (IO.userError "bytes1/bytes12 custom error differs")
  let oddWord := 0x0102030405060708 * 2 ^ 192
  let nearlyWord := (2 ^ 248 - 1) * 2 ^ 8
  unless customErrorBytes oracle [{ name := "Odd", params := [.bytesN 8, .bytesN 31] }] "Odd"
      [oddWord, nearlyWord] ==
      some ([0xc4, 0x41, 0xd6, 0xb3] ++ wordBytes oddWord ++ wordBytes nearlyWord) do
    throw (IO.userError "bytes8/bytes31 custom error differs")
  for (name, declarations, values) in [
      ("LockedSelector", [{ name := "LockedSelector", params := [.bytesN 4] }], [selectorWord + 1]),
      ("Wide", [{ name := "Wide", params := [.bytesN 31] }], [2 ^ 256]),
      ("Odd", [{ name := "Odd", params := [.bytesN 31] }], [1]),
      ("Zero", [{ name := "Zero", params := [.bytesN 0] }], [0]),
      ("Full", [{ name := "Full", params := [.bytesN 32] }], [0]),
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
  -- The closed memory revert transport reverts with exactly the bytes in
  -- memory, including a length that is not a whole number of words.
  let world := Verity.defaultState.copyPhysicalMemory (rawPhysicalByte unicodeExpected) 96 0
    unicodeExpected.length
  match execStmt oracle [] { state with world } (.ecm Compiler.ECM.SolidityRevertMemory.module
      [.literal 96, .literal unicodeExpected.length]) with
  | .revertWithData bytes =>
      unless bytes == unicodeExpected do throw (IO.userError "memory revert lost its bytes")
  | _ => throw (IO.userError "memory revert did not revert with data")
  match execStmt oracle [] { state with world } (.ecm Compiler.ECM.SolidityRevertMemory.module
      [.literal 99, .literal 5]) with
  | .revertWithData bytes =>
      unless bytes == (unicodeExpected.drop 3).take 5 do
        throw (IO.userError "unaligned memory revert lost its bytes")
  | _ => throw (IO.userError "unaligned memory revert did not revert with data")
  IO.println "Exact message/custom-error payload and fail-closed scalar checks passed"
end SolidityImportSmoke.ErrorPayloads

def main : IO Unit := SolidityImportSmoke.ErrorPayloads.runChecks

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
  -- Signed parameters hash as `intN` and encode the sign-extended word unchanged.
  -- Selectors and words agree with solc 0.8.34 revert data for the same errors.
  let downcast : List ErrorDef := [{ name := "IntDowncastOverflow", params := [.uint8, .int256] }]
  unless customErrorBytes oracle downcast "IntDowncastOverflow" [104, 2 ^ 256 - 3] ==
      some ([0xa2, 0x24, 0xbd, 0x28] ++ wordBytes 104 ++ wordBytes (2 ^ 256 - 3)) do
    throw (IO.userError "int256 custom error differs")
  let narrow : List ErrorDef := [{ name := "Narrow", params := [.intN 8, .intN 104, .intN 24] }]
  unless customErrorBytes oracle narrow "Narrow" [2 ^ 256 - 128, 2 ^ 103 - 1, 2 ^ 256 - 2 ^ 23] ==
      some ([0xee, 0xc5, 0xd7, 0x60] ++ wordBytes (2 ^ 256 - 128) ++ wordBytes (2 ^ 103 - 1) ++
        wordBytes (2 ^ 256 - 2 ^ 23)) do
    throw (IO.userError "int8/int104/int24 custom error differs")
  unless customErrorBytes oracle narrow "Narrow" [127, 2 ^ 256 - 2 ^ 103, 2 ^ 23 - 1] ==
      some ([0xee, 0xc5, 0xd7, 0x60] ++ wordBytes 127 ++ wordBytes (2 ^ 256 - 2 ^ 103) ++
        wordBytes (2 ^ 23 - 1)) do
    throw (IO.userError "signed custom error range ends differ")
  unless customErrorBytes oracle [{ name := "Bounds", params := [.int256, .intN 64] }] "Bounds"
      [2 ^ 255, 2 ^ 256 - 1] ==
      some ([0x20, 0x6f, 0x55, 0x13] ++ wordBytes (2 ^ 255) ++ wordBytes (2 ^ 256 - 1)) do
    throw (IO.userError "int256/int64 custom error differs")
  unless customErrorBytes oracle [{ name := "Wide", params := [.intN 248] }] "Wide"
      [2 ^ 256 - 2 ^ 247] == some ([0xb3, 0x50, 0x79, 0xb4] ++ wordBytes (2 ^ 256 - 2 ^ 247)) do
    throw (IO.userError "int248 custom error differs")
  -- A noncanonical argument word is encoded as the compiled code encodes it
  -- (`customErrorArgWord`: masked, sign-extended or collapsed to 0/1), so it gives the
  -- bytes of the canonical word the bytecode stores.
  for (name, declarations, dirty, canonical) in [
      ("Narrow", narrow, [128, 0, 0], [2 ^ 256 - 128, 0, 0]),
      ("Narrow", narrow, [0x1ff, 0, 0], [2 ^ 256 - 1, 0, 0]),
      ("Narrow", narrow, [2 ^ 256 - 129, 0, 0], [127, 0, 0]),
      ("Narrow", narrow, [0, 2 ^ 103, 0], [0, 2 ^ 256 - 2 ^ 103, 0]),
      ("Narrow", narrow, [0, 0, 2 ^ 255], [0, 0, 0]),
      ("Narrow", narrow, [2 ^ 256, 0, 0], [0, 0, 0]),
      ("IntDowncastOverflow", downcast, [104, 2 ^ 256], [104, 0]),
      ("Wide", [{ name := "Wide", params := [.intN 248] }], [2 ^ 247], [2 ^ 256 - 2 ^ 247]),
      ("LockedSelector", [{ name := "LockedSelector", params := [.bytesN 4] }],
        [selectorWord + 1], [selectorWord]),
      ("Wide", [{ name := "Wide", params := [.bytesN 31] }], [2 ^ 256], [0]),
      ("Odd", [{ name := "Odd", params := [.bytesN 31] }], [1], [0]),
      ("BadValue", errors, [7, 9, 2], [7, 9, 1]),
      ("Narrow", [{ name := "Narrow", params := [.uintN 8] }], [256], [0])] do
    match customErrorBytes oracle declarations name dirty with
    | some bytes =>
        unless bytes.length == 4 + 32 * canonical.length &&
            bytes.drop 4 == canonical.flatMap wordBytes do
          throw (IO.userError s!"noncanonical custom-error argument not normalised: {name}")
    | none => throw (IO.userError s!"noncanonical custom-error argument rejected: {name}")
  -- Unsupported types, widths, arities and ambiguous names stay rejected.
  for (name, declarations, values) in [
      ("ZeroInt", [{ name := "ZeroInt", params := [.intN 0] }], [0]),
      ("OddInt", [{ name := "OddInt", params := [.intN 12] }], [0]),
      ("HugeInt", [{ name := "HugeInt", params := [.intN 264] }], [0]),
      ("Zero", [{ name := "Zero", params := [.bytesN 0] }], [0]),
      ("Full", [{ name := "Full", params := [.bytesN 32] }], [0]),
      ("Missing", errors, []), ("Unauthorized", errors, [1]),
      ("Unauthorized", errors ++ [{ name := "Unauthorized", params := [] }], []),
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
  IO.println "Exact message/custom-error payload, normalised-argument and unsupported-type checks passed"
end SolidityImportSmoke.ErrorPayloads

def main : IO Unit := SolidityImportSmoke.ErrorPayloads.runChecks

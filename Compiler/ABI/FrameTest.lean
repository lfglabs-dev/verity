import Compiler.ABI.Frame

namespace Compiler.ABI.FrameTest

open Compiler.ABI.Frame
open Compiler.CompilationModel
open Compiler.Yul

private def assert (label : String) (ok : Bool) : IO Unit := do
  if !ok then
    throw (IO.userError s!"frame test failed: {label}")
  IO.println s!"ok: {label}"

private def takeFields : List FrameField :=
  [ { name := "offer", ty := .tuple [.address, .uint256, .tuple [.bytes32, .uint256]], source := .calldata }
  , { name := "units", ty := .uint256, source := .calldata }
  , { name := "ratifierData", ty := .bytes, source := .calldata, tailBytes := 96 } ]

private def sourceFields : List FrameField :=
  [ { name := "c", ty := .uint256, source := .calldata }
  , { name := "m", ty := .bytes, source := .memory, tailBytes := 64 }
  , { name := "x", ty := .bytes32, source := .code }
  , { name := "s", ty := .uint256, source := .storage } ]

private def inlineFields : List FrameField :=
  [ { name := "pair", ty := .tuple [.uint256, .bytes32], source := .calldata }
  , { name := "amount", ty := .uint256, source := .calldata } ]

private def dynamicStorageFields : List FrameField :=
  [ { name := "blob", ty := .bytes, source := .storage, tailBytes := 64 } ]

private def calldataLoadName? : YulExpr → Option String
  | .call "calldataload" [.ident name] => some name
  | .call "calldataload" [.call "add" [.ident name, _]] => some name
  | _ => none

private def hasExtcodecopy : List YulStmt → Bool :=
  fun stmts => stmts.any fun
    | .expr (.call "extcodecopy" _) => true
    | _ => false

private def hasDynamicCalldataTailCopy : List YulStmt → Bool :=
  fun stmts => stmts.any fun
    | .expr (.call "mstore" [
        _,
        .call "calldataload" [
          .call "add" [
            .call "add" [.ident "ratifierData", .call "calldataload" [.ident "ratifierData"]],
            .lit 0
          ]
        ]
      ]) => true
    | _ => false

#eval! do
  let takeLayout := layout takeFields
  assert "nested struct supported" (supportsNestedStructs takeLayout)
  assert "dynamic bytes/arrays force pointer mode" (takeLayout.mode == FramePassMode.pointer)
  assert "Take frame passes pointer pair" ((loweredArgs "take" takeLayout).length == 2)
  assert "Take spills early to memory" ((spillPayloadToMemory "take" takeLayout).length > 2)
  assert "dynamic tail contributes to pointer payload size" (frameSizeBytes takeLayout == 288)
  assert "dynamic tail contributes to allocated words" (frameAllocBytes takeLayout == 288)
  let srcLayout := layout sourceFields
  assert "calldata/memory/code/storage sources supported" (layoutSourcesSupported srcLayout)
  assert "dynamic storage tails are not lowered as sequential slots"
    (!layoutSourcesSupported (layout dynamicStorageFields))
  assert "dynamic source frame is pointer mode" (srcLayout.mode == FramePassMode.pointer)
  assert "code source spills through extcodecopy" (hasExtcodecopy (spillPayloadToMemory "src" srcLayout))
  assert "dynamic calldata tail follows ABI offset"
    (hasDynamicCalldataTailCopy (spillPayloadToMemory "take" takeLayout))
  let inlineNames := (inlineArgs (layout inlineFields)).filterMap calldataLoadName?
  assert "inline source words are indexed per field"
    (inlineNames == ["pair", "pair", "amount"])

end Compiler.ABI.FrameTest

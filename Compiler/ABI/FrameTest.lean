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
  , { name := "ratifierData", ty := .bytes, source := .calldata } ]

private def sourceFields : List FrameField :=
  [ { name := "c", ty := .uint256, source := .calldata }
  , { name := "m", ty := .bytes, source := .memory }
  , { name := "x", ty := .bytes32, source := .code }
  , { name := "s", ty := .uint256, source := .storage } ]

private def inlineFields : List FrameField :=
  [ { name := "pair", ty := .tuple [.uint256, .bytes32], source := .calldata }
  , { name := "amount", ty := .uint256, source := .calldata } ]

private def calldataLoadName? : YulExpr → Option String
  | .call "calldataload" [.ident name] => some name
  | _ => none

#eval! do
  let takeLayout := layout takeFields
  assert "nested struct supported" (supportsNestedStructs takeLayout)
  assert "dynamic bytes/arrays force pointer mode" (takeLayout.mode == FramePassMode.pointer)
  assert "Take frame passes pointer pair" ((loweredArgs "take" takeLayout).length == 2)
  assert "Take spills early to memory" ((spillPayloadToMemory "take" takeLayout).length > 2)
  let srcLayout := layout sourceFields
  assert "calldata/memory/code/storage sources supported" (layoutSourcesSupported srcLayout)
  assert "dynamic source frame is pointer mode" (srcLayout.mode == FramePassMode.pointer)
  let inlineNames := (inlineArgs (layout inlineFields)).filterMap calldataLoadName?
  assert "inline source words are indexed per field"
    (inlineNames == ["__abi_frame_src_pair_0", "__abi_frame_src_pair_1", "__abi_frame_src_amount_0"])

end Compiler.ABI.FrameTest

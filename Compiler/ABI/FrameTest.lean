import Compiler.ABI.Frame

namespace Compiler.ABI.FrameTest

open Compiler.ABI.Frame
open Compiler.CompilationModel

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

#eval! do
  let takeLayout := layout takeFields
  assert "nested struct supported" (supportsNestedStructs takeLayout)
  assert "dynamic bytes/arrays force pointer mode" (takeLayout.mode == FramePassMode.pointer)
  assert "Take frame passes pointer pair" ((loweredArgs "take" takeLayout).length == 2)
  assert "Take spills early to memory" ((spillPayloadToMemory "take" takeLayout).length > 2)
  let srcLayout := layout sourceFields
  assert "calldata/memory/code/storage sources supported" (layoutSourcesSupported srcLayout)
  assert "dynamic source frame is pointer mode" (srcLayout.mode == FramePassMode.pointer)

end Compiler.ABI.FrameTest

import Verity.Core.Model.DenoteByteExternalCalls

open Compiler.CompilationModel

private def state : DenoteByteExternalCalls.State :=
  { frame := { world := { Verity.defaultState with thisAddress := 17 }, bindings := [] } }

private def request := DenoteByteExternalCalls.staticRequest state 23
  ⟨0xa035b1fe, by decide⟩ [1, 255] 100000

example : request.caller = 17 := rfl
example : request.target = 23 := rfl
example : request.kind = ByteExternalCall.Kind.staticcall := rfl
example : request.value = 0 := rfl
example : request.gas = 100000 := rfl
example : request.calldata.length = 68 := by decide
example : request.calldata.take 4 = [0xa0, 0x35, 0xb1, 0xfe] := by decide
example : (request.calldata.drop 4).take 32 = List.replicate 31 0 ++ [1] := by decide
example : request.calldata.drop 36 = List.replicate 31 0 ++ [255] := by decide

private def responseModel := DenoteByteExternalCalls.staticAdversary fun req world =>
  if req.target == 23 && req.caller == world.thisAddress.val &&
      req.calldata == request.calldata && req.value == 0 then
    (true, List.replicate 31 0 ++ [42], [.contractSlot 23 0])
  else (false, [0xff], [.contractSlot req.target 0])

private def executed := DenoteByteExternalCalls.executeStaticUint256 responseModel state 23
  ⟨0xa035b1fe, by decide⟩ [1, 255] 100000

example : executed.2 = [.contractSlot 23 0] := by decide
example : (match executed.1 with
    | .return value _ => value
    | _ => 0) = 42 := by decide

-- Changing the actual target changes the adversary response, not just a
-- metadata record. The failed call retains its byte payload and foreign trace.
private def wrongTarget := DenoteByteExternalCalls.executeStaticUint256 responseModel state 24
  ⟨0xa035b1fe, by decide⟩ [1, 255] 100000

example : wrongTarget.2 = [.contractSlot 24 0] := by decide
example : (match wrongTarget.1 with
    | .revertWithData data => data
    | _ => []) = [0xff] := by decide

#print axioms DenoteByteExternalCalls.staticRequest_value
#print axioms DenoteByteExternalCalls.staticRequest_caller

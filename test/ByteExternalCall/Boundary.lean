import Verity.Core.Model.ByteExternalCall

open Compiler.CompilationModel.ByteExternalCall

private abbrev World := Nat × List Nat
private abbrev Access := Nat × Nat

-- A one-byte zero revert is different from the empty return buffer.
example : (Response.revert [0] [(17, 0)] : Response World Access).returndata ≠
    (Response.revert [] [(17, 0)] : Response World Access).returndata := by decide

-- Non-word lengths and leading/trailing zero bytes survive the boundary.
example : (Response.revert [0, 255, 0] [(17, 0)] : Response World Access).returndata =
    [0, 255, 0] := rfl

example : (Response.success (9, [4]) [0, 255, 0] [(17, 0)] : Response World Access).returndata =
    [0, 255, 0] := rfl

example : (Response.revert [0, 255, 0] [(17, 0)] : Response World Access).commit (8, [3]) =
    (8, [3]) := rfl

example : (Response.exceptional [(17, 0)] : Response World Access).returndata = [] := rfl

example : (Response.exceptional [(17, 0)] : Response World Access).accesses = [(17, 0)] := rfl

-- An invalid state-changing static success must fail the validity obligation;
-- silently dropping the mutation would misclassify this as a successful call.
example : ¬ (Response.success (9, [4]) [] [] : Response World Access).valid
    { kind := .staticcall, caller := 1, target := 17, value := 0, calldata := [], gas := 100 }
    (8, [3]) := by unfold Response.valid; decide

example : (Response.success (9, [4]) [] [] : Response World Access).valid
    { kind := .call, caller := 1, target := 17, value := 0, calldata := [], gas := 100 }
    (8, [3]) := by unfold Response.valid; decide

private def observation : Observation World Access :=
  { success := true, world := (9, [3, 4]), returndata := [0, 255], touched := [(1, 0), (17, 0)] }

example : (rollbackOuter (8, [3]) observation [0, 255, 0]).world = (8, [3]) := rfl
example : (rollbackOuter (8, [3]) observation [0, 255, 0]).returndata = [0, 255, 0] := rfl
example : (rollbackOuter (8, [3]) observation [0, 255, 0]).touched = [(1, 0), (17, 0)] := rfl

#print axioms Response.valid_static_preserves_world
#print axioms execute_static_world
#print axioms rollbackOuter_world
#print axioms rollbackOuter_accesses
#print axioms rollbackOuter_bytes

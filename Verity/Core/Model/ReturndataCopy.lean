import Verity.Core.Model.ExecutionContext
import Verity.Core.Model.PhysicalCopy

/-! Shared whole-word returndata primitive. A failed bounds check is an
exceptional opcode exit only when the actual frame context is available.
Successful copy gas/memory admission still belongs to the native executor. -/
namespace Verity.Core.Model.ReturndataCopy

inductive Outcome where
  | continued (world : Verity.ContractState)
  | exceptional (context : ExecutionContext)
  | interpretationError (message : String)

def run (world : Verity.ContractState) (context : Option ExecutionContext)
    (destination source size : Nat) : Outcome :=
  let destination := destination % Verity.Core.Uint256.modulus
  let source := source % Verity.Core.Uint256.modulus
  let size := size % Verity.Core.Uint256.modulus
  if source + size ≤ 32 * world.returndata.length then
    .continued (world.copyPhysicalReturndata destination source size)
  else
    match context with
    | none => .interpretationError "returndata copy exceptional exit requires actual opcode context"
    | some actual => .exceptional { actual with opcode := { actual.opcode with gas := 0 } }

theorem run_in_bounds (world : Verity.ContractState) (context : Option ExecutionContext)
    (destination source size : Nat)
    (inside : source % Verity.Core.Uint256.modulus + size % Verity.Core.Uint256.modulus ≤
      32 * world.returndata.length) :
    run world context destination source size = .continued
      (world.copyPhysicalReturndata (destination % Verity.Core.Uint256.modulus)
        (source % Verity.Core.Uint256.modulus) (size % Verity.Core.Uint256.modulus)) := by
  simp only [run, inside, if_true]

theorem run_exceptional (world : Verity.ContractState) (actual : ExecutionContext)
    (destination source size : Nat)
    (outside : 32 * world.returndata.length <
      source % Verity.Core.Uint256.modulus + size % Verity.Core.Uint256.modulus) :
    run world (some actual) destination source size =
      .exceptional { actual with opcode := { actual.opcode with gas := 0 } } := by
  simp only [run, Nat.not_le.mpr outside, if_false]

theorem run_missing_context (world : Verity.ContractState) (destination source size : Nat)
    (outside : 32 * world.returndata.length <
      source % Verity.Core.Uint256.modulus + size % Verity.Core.Uint256.modulus) :
    run world none destination source size =
      .interpretationError "returndata copy exceptional exit requires actual opcode context" := by
  simp only [run, Nat.not_le.mpr outside, if_false]

end Verity.Core.Model.ReturndataCopy

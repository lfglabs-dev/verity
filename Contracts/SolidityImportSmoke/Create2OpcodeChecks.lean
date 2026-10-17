import Verity.Core.Model.Create2Opcode

namespace SolidityImportSmoke.Create2OpcodeChecks
open Verity.Core Compiler.CompilationModel Compiler.CompilationModel.DenoteMemory
open Compiler.CompilationModel.Create2Opcode

theorem dirty_inactive_memory_stays_zero :
    (expand { bytes := fun _ => ⟨255, by decide⟩, size := 32 } 4).readByte 64 = zeroByte := by
  apply expand_new_zero
  decide

theorem active_memory_is_preserved :
    (expand { bytes := fun _ => ⟨171, by decide⟩, size := 32 } 4).readByte 31 = ⟨171, by decide⟩ := by
  rw [expand_before _ _ _ (by decide) (by decide)]
  rfl

theorem parent_out_of_gas :
    (execute (fun _ => 0) Verity.defaultState Memory.empty
      { creator := 0, gas := 31999 } 0 0 0).map (fun result => (result.control, result.gasLeft)) =
      .ok (.outOfGas, 0) := by rfl

theorem zero_length_max_offset_and_depth_refund :
    (execute (fun _ => 0) Verity.defaultState Memory.empty
      { creator := 0, gas := 40000, depth := 1024 } 0 (Uint256.ofNat (2^256 - 1)) 0).map
      (fun result => (result.control, result.gasLeft, result.memory.size, result.childGas, result.childGasLeft)) =
      .ok (.creation (.zero .depth), 8000, 0, 7875, 7875) := by rfl

theorem nonaligned_memory_is_instrument_error :
    (execute (fun _ => 0) Verity.defaultState { bytes := fun _ => zeroByte, size := 1 }
      { creator := 0, gas := 40000 } 0 0 0).map (fun result => result.gasLeft) =
      .error "CREATE2 opcode memory size is not word aligned" := by rfl

end SolidityImportSmoke.Create2OpcodeChecks

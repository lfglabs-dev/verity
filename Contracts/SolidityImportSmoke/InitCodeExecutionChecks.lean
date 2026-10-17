import Verity.Core.Model.InitCodeExecution

namespace SolidityImportSmoke.InitCodeExecutionChecks
open Compiler.CompilationModel.InitCodeExecution
open Compiler.CompilationModel.DenoteMemory

theorem unsupported_opcode_rejected :
    run 1 [⟨0xfe, by decide⟩] {} = .failed (.unsupportedOpcode 0xfe) := rfl

theorem subtract_underflow_rejected :
    run 1 [⟨0x03, by decide⟩] {} = .failed .stackUnderflow := rfl

theorem copy_underflow_rejected :
    run 1 [⟨0x39, by decide⟩] {} = .failed .stackUnderflow := rfl

theorem return_underflow_rejected :
    run 1 [⟨0xf3, by decide⟩] {} = .failed .stackUnderflow := rfl

theorem duplicate_underflow_rejected :
    run 1 [⟨0x80, by decide⟩] {} = .failed .stackUnderflow := rfl

theorem fuel_exhaustion_rejected :
    run 1 [⟨0x5f, by decide⟩] {} = .failed .outOfFuel := rfl

theorem truncated_push_zero_extends :
    run 2 [⟨0x60, by decide⟩] {} = .returned [] := rfl

theorem empty_code_stops : run 1 [] {} = .returned [] := rfl

theorem zero_copy_preserves_memory (memory : Memory) (code : List Byte) (dest source : Nat) :
    codeCopy memory code dest source 0 = memory := codeCopy_zero memory code dest source

end SolidityImportSmoke.InitCodeExecutionChecks

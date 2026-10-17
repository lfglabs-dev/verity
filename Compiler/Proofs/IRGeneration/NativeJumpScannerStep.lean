import Compiler.Proofs.IRGeneration.NativeJumpScannerFrame

namespace Compiler.Proofs.IRGeneration.NativeJumpScannerStep
open EvmYul

theorem step (code : ByteArray) (fuel pc : Nat) (found : Array UInt256) (op : Operation .EVM)
    (inside : pc < code.size) (parsed : EVM.parseInstr code[pc] = some op) :
    EVM.D_J_aux code (fuel + 1) pc found =
      EVM.D_J_aux code fuel (pc + 1 + EVM.argOnNBytesOfInstr op)
        (if op = .JUMPDEST then found.push (UInt256.ofNat pc) else found) := by
  rw [EVM.D_J_aux, dif_pos inside, parsed]

end Compiler.Proofs.IRGeneration.NativeJumpScannerStep

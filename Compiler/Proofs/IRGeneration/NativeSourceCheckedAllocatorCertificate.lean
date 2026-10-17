import Compiler.Proofs.IRGeneration.NativeSourceCheckedAllocatorBounds

namespace Compiler.Proofs.IRGeneration.NativeSourceCheckedAllocatorCertificate
open EvmYul EVM EVM.Proof

theorem execute (fuel : Nat) (pre : EVM.State) (base size : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 910)
    (stack : pre.stack = base :: size :: UInt256.ofNat 292 :: tail)
    (bound : base.toNat + (NativeSourceCheckedAllocatorFullDecision.amount size).toNat ≤ 2^64-1)
    (gas : 76 + NativeSourceCheckedAllocatorSuccess.expansion pre base size tail ≤ pre.gasAvailable.toNat)
    (depth : tail.length ≤ 1019) :
    EVM.X (fuel + 23) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      EVM.X (fuel + 1) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0))
        (NativeSourceCheckedAllocatorSuccess.returned pre base size tail) := by
  exact NativeSourceCheckedAllocatorSuccess.execute fuel pre base size tail code pc stack
    (NativeSourceCheckedAllocatorBounds.accepted base size bound) gas depth

theorem pointer_value (base size : UInt256)
    (bound : base.toNat + (NativeSourceCheckedAllocatorFullDecision.amount size).toNat ≤ 2^64-1) :
    (base + NativeSourceCheckedAllocatorFullDecision.amount size).toNat =
      base.toNat + (NativeSourceCheckedAllocatorFullDecision.amount size).toNat := by
  apply NativeSourceCheckedAllocatorBounds.addition
  have : 2^64-1 < UInt256.size := by decide
  omega

end Compiler.Proofs.IRGeneration.NativeSourceCheckedAllocatorCertificate

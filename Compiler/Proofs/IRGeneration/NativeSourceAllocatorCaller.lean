import Compiler.Proofs.IRGeneration.NativeSourceAllocatorGuardZero

namespace Compiler.Proofs.IRGeneration.NativeSourceAllocatorCaller
open EvmYul EVM.Proof NativeSourcePreludeDecoded NativeSourceAllocatorOverflowEntry

def returned (cost : Nat) (pre : EVM.State) (size target base : UInt256) (tail : Stack UInt256) :=
  NativeSourceAllocatorSuccess.returned cost
    (NativeSourceAllocatorJump.entered cost pre size target base tail) base size target (base :: tail)

theorem finish (fuel cost : Nat) (pre : EVM.State) (size target base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code)
    (guard : NativeSourceAllocatorDecision.flag base size = ⟨0⟩) :
    run fuel cost 22 (NativeSourceAllocatorJump.entered cost pre size target base tail) =
      .ok (returned cost pre size target base tail) := by
  exact NativeSourceAllocatorSuccess.execute fuel cost
    (NativeSourceAllocatorJump.entered cost pre size target base tail) base size target (base :: tail)
    code (NativeSourceAllocatorJump.entry_pc cost pre size target base tail)
    (NativeSourceAllocatorJump.entry_stack cost pre size target base tail) guard

theorem execute (fuel cost : Nat) (pre : EVM.State) (size target base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 676)
    (stack : pre.stack = size :: target :: base :: tail)
    (guard : NativeSourceAllocatorDecision.flag base size = ⟨0⟩) :
    run fuel cost 25 pre = .ok (returned cost pre size target base tail) := by
  exact NativeSourceSizedPacking.compose fuel cost 3 22 pre _ _
    (NativeSourceAllocatorJump.execute fuel cost pre size target base tail code pc stack)
    (finish fuel cost pre size target base tail code guard)

theorem target (cost : Nat) (pre : EVM.State) (size address base : UInt256) (tail : Stack UInt256) :
    (returned cost pre size address base tail).pc = address := by
  rfl

theorem stack (cost : Nat) (pre : EVM.State) (size address base : UInt256) (tail : Stack UInt256) :
    (returned cost pre size address base tail).stack = base :: tail := by
  rfl

end Compiler.Proofs.IRGeneration.NativeSourceAllocatorCaller

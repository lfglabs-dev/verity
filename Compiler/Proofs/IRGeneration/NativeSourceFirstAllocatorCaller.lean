import Compiler.Proofs.IRGeneration.NativeSourceFirstAllocatorJump
import Compiler.Proofs.IRGeneration.NativeSourceAllocatorSuccess

namespace Compiler.Proofs.IRGeneration.NativeSourceFirstAllocatorCaller
open EvmYul EVM.Proof NativeSourcePreludeDecoded

def returned (cost : Nat) (pre : EVM.State) (size target a b c d base : UInt256) (tail : Stack UInt256) :=
  NativeSourceAllocatorSuccess.returned cost
    (NativeSourceFirstAllocatorJump.entered cost pre size target a b c d base tail)
    base size target (a :: b :: c :: d :: base :: tail)

theorem finish (fuel cost : Nat) (pre : EVM.State) (size target a b c d base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code)
    (guard : NativeSourceAllocatorDecision.flag base size = ⟨0⟩) :
    run fuel cost 22 (NativeSourceFirstAllocatorJump.entered cost pre size target a b c d base tail) =
      .ok (returned cost pre size target a b c d base tail) := by
  exact NativeSourceAllocatorSuccess.execute fuel cost
    (NativeSourceFirstAllocatorJump.entered cost pre size target a b c d base tail)
    base size target (a :: b :: c :: d :: base :: tail) code
    (NativeSourceFirstAllocatorJump.entry_pc cost pre size target a b c d base tail)
    (NativeSourceFirstAllocatorJump.entry_stack cost pre size target a b c d base tail) guard

theorem execute (fuel cost : Nat) (pre : EVM.State) (size target a b c d base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 627)
    (stack : pre.stack = size :: target :: a :: b :: c :: d :: base :: tail)
    (guard : NativeSourceAllocatorDecision.flag base size = ⟨0⟩) :
    run fuel cost 25 pre = .ok (returned cost pre size target a b c d base tail) := by
  exact NativeSourceSizedPacking.compose fuel cost 3 22 pre _ _
    (NativeSourceFirstAllocatorJump.execute fuel cost pre size target a b c d base tail code pc stack)
    (finish fuel cost pre size target a b c d base tail code guard)

theorem target (cost : Nat) (pre : EVM.State) (size address a b c d base : UInt256) (tail : Stack UInt256) :
    (returned cost pre size address a b c d base tail).pc = address := by rfl

theorem stack (cost : Nat) (pre : EVM.State) (size address a b c d base : UInt256) (tail : Stack UInt256) :
    (returned cost pre size address a b c d base tail).stack = a :: b :: c :: d :: base :: tail := by rfl

end Compiler.Proofs.IRGeneration.NativeSourceFirstAllocatorCaller

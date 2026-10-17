import Compiler.Proofs.IRGeneration.NativeSourceFieldsAllocation
import Compiler.Proofs.IRGeneration.NativeSourcePreCreate

namespace Compiler.Proofs.IRGeneration.NativeSourceContextPreCreate
open EvmYul EVM.Proof NativeSourcePreludeDecoded

def ready (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k l : UInt256) (tail : Stack UInt256) :=
  NativeSourcePreCreate.ready cost (NativeSourceFieldsAllocation.returned cost pre a b c d e f g h i j k (l :: tail)) h (UInt256.ofNat 32) i (UInt256.ofNat 681) j k (UInt256.ofNat 0) l tail

theorem finish (fuel : Nat) (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k l : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code)
    (guard : NativeSourceAllocatorDecision.flag (NativeSourceDecodedPackingStart.free cost (NativeSourceFieldsAllocation.returned cost pre a b c d e f g h i j k (l :: tail)))
      (NativeSourceOriginalAllocation.size cost (NativeSourceFieldsAllocation.returned cost pre a b c d e f g h i j k (l :: tail)) h (UInt256.ofNat 32) i (UInt256.ofNat 681) j k (UInt256.ofNat 0) l tail) = ⟨0⟩) :
    run fuel cost 71 (NativeSourceFieldsAllocation.returned cost pre a b c d e f g h i j k (l :: tail)) = .ok (ready cost pre a b c d e f g h i j k l tail) := by
  exact NativeSourcePreCreate.execute cost (NativeSourceFieldsAllocation.returned cost pre a b c d e f g h i j k (l :: tail)) h (UInt256.ofNat 32) i (UInt256.ofNat 681) j k (UInt256.ofNat 0) l tail fuel code
    (NativeSourceFieldsAllocation.target cost pre a b c d e f g h i j k (l :: tail)) (NativeSourceFieldsAllocation.stack cost pre a b c d e f g h i j k (l :: tail)) rfl guard

theorem execute (fuel : Nat) (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k l : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 573)
    (stack : pre.stack = a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: l :: tail)
    (firstGuard : NativeSourceAllocatorDecision.flag j (b - c) = ⟨0⟩)
    (secondGuard : NativeSourceAllocatorDecision.flag (NativeSourceDecodedPackingStart.free cost (NativeSourceFieldsAllocation.returned cost pre a b c d e f g h i j k (l :: tail)))
      (NativeSourceOriginalAllocation.size cost (NativeSourceFieldsAllocation.returned cost pre a b c d e f g h i j k (l :: tail)) h (UInt256.ofNat 32) i (UInt256.ofNat 681) j k (UInt256.ofNat 0) l tail) = ⟨0⟩) :
    run fuel cost 138 pre = .ok (ready cost pre a b c d e f g h i j k l tail) := by
  exact NativeSourceSizedPacking.compose fuel cost 67 71 pre _ _
    (NativeSourceFieldsAllocation.execute fuel cost pre a b c d e f g h i j k (l :: tail) code pc stack firstGuard)
    (finish fuel cost pre a b c d e f g h i j k l tail code secondGuard)

theorem operands (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k l : UInt256) (tail : Stack UInt256) :
    Stack.pop4 (ready cost pre a b c d e f g h i j k l tail).stack =
      some (l :: tail, UInt256.ofNat 0, (NativeSourceDecodedPackingStart.free cost (NativeSourceFieldsAllocation.returned cost pre a b c d e f g h i j k (l :: tail))) + UInt256.ofNat 32,
        (NativeSourceCreateOperands.s1 cost (NativeSourceOriginalAllocation.returned cost (NativeSourceFieldsAllocation.returned cost pre a b c d e f g h i j k (l :: tail)) h (UInt256.ofNat 32) i (UInt256.ofNat 681) j k (UInt256.ofNat 0) l tail)).toMachineState.lookupMemory (NativeSourceDecodedPackingStart.free cost (NativeSourceFieldsAllocation.returned cost pre a b c d e f g h i j k (l :: tail))), UInt256.ofNat 0) := by
  exact NativeSourcePreCreate.operands cost (NativeSourceFieldsAllocation.returned cost pre a b c d e f g h i j k (l :: tail)) h (UInt256.ofNat 32) i (UInt256.ofNat 681) j k (UInt256.ofNat 0) l tail

end Compiler.Proofs.IRGeneration.NativeSourceContextPreCreate

import Compiler.Proofs.IRGeneration.NativeSourceCreateOperands

namespace Compiler.Proofs.IRGeneration.NativeSourcePreCreate
open EvmYul EVM.Proof NativeSourcePreludeDecoded

def ready (cost : Nat) (pre : EVM.State) (a b c d e f g h : UInt256) (tail : Stack UInt256) := NativeSourceCreateOperands.s4 cost (NativeSourceOriginalAllocation.returned cost pre a b c d e f g h tail) (NativeSourceDecodedPackingStart.free cost pre) ((NativeSourceDecodedPackingStart.free cost pre) + b) g h tail

theorem finish (cost : Nat) (pre : EVM.State) (a b c d e f g h : UInt256) (tail : Stack UInt256) (fuel : Nat)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (returnPC : d = UInt256.ofNat 681) :
    run fuel cost 4 (NativeSourceOriginalAllocation.returned cost pre a b c d e f g h tail) = .ok (ready cost pre a b c d e f g h tail) := by
  have atPC : (NativeSourceOriginalAllocation.returned cost pre a b c d e f g h tail).pc = UInt256.ofNat 681 :=
    (NativeSourceOriginalAllocation.target cost pre a b c d e f g h tail).trans returnPC
  exact NativeSourceCreateOperands.execute fuel cost (NativeSourceOriginalAllocation.returned cost pre a b c d e f g h tail) (NativeSourceDecodedPackingStart.free cost pre) ((NativeSourceDecodedPackingStart.free cost pre) + b) g h tail code atPC (NativeSourceOriginalAllocation.stack cost pre a b c d e f g h tail)

theorem execute (cost : Nat) (pre : EVM.State) (a b c d e f g h : UInt256) (tail : Stack UInt256) (fuel : Nat)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 632)
    (stack : pre.stack = a :: b :: c :: d :: e :: f :: g :: h :: tail)
    (returnPC : d = UInt256.ofNat 681)
    (guard : NativeSourceAllocatorDecision.flag (NativeSourceDecodedPackingStart.free cost pre) (NativeSourceOriginalAllocation.size cost pre a b c d e f g h tail) = ⟨0⟩) :
    run fuel cost 71 pre = .ok (ready cost pre a b c d e f g h tail) := by
  exact NativeSourceSizedPacking.compose fuel cost 67 4 pre _ _
    (NativeSourceOriginalAllocation.execute cost pre a b c d e f g h tail fuel code pc stack guard)
    (finish cost pre a b c d e f g h tail fuel code returnPC)

theorem operands (cost : Nat) (pre : EVM.State) (a b c d e f g h : UInt256) (tail : Stack UInt256) :
    (ready cost pre a b c d e f g h tail).stack.pop4 = some (h :: tail, g, (NativeSourceDecodedPackingStart.free cost pre) + b,
      (NativeSourceCreateOperands.s1 cost (NativeSourceOriginalAllocation.returned cost pre a b c d e f g h tail)).toMachineState.lookupMemory (NativeSourceDecodedPackingStart.free cost pre), g) := by
  exact NativeSourceCreateOperands.operands cost (NativeSourceOriginalAllocation.returned cost pre a b c d e f g h tail) (NativeSourceDecodedPackingStart.free cost pre) ((NativeSourceDecodedPackingStart.free cost pre) + b) g h tail

end Compiler.Proofs.IRGeneration.NativeSourcePreCreate

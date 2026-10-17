import Compiler.Proofs.IRGeneration.NativeSourceCheckedAllocatorFullDecision

namespace Compiler.Proofs.IRGeneration.NativeSourceCheckedAllocatorSuccess
open EvmYul EVM EVM.Proof NativeSourceCheckedAllocatorFullDecision

def entry (pre : EVM.State) (base size : UInt256) (tail : Stack UInt256) :=
  decided pre base size (UInt256.ofNat 292 :: tail)

def expansion (pre : EVM.State) (base size : UInt256) (tail : Stack UInt256) :=
  NativeSourceCheckedAllocatorExit.expansion (entry pre base size tail)

def returned (pre : EVM.State) (base size : UInt256) (tail : Stack UInt256) :=
  NativeSourceCheckedAllocatorExit.returned (entry pre base size tail) (base + amount size) tail

theorem accepted_pc (pre : EVM.State) (base size : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 910) (accept : (condition base size != ⟨0⟩) = false) :
    (entry pre base size tail).pc = UInt256.ofNat 940 := by
  have dest := destinations pre base size (UInt256.ofNat 292 :: tail) pc
  rw [accept] at dest
  exact dest

theorem execute (fuel : Nat) (pre : EVM.State) (base size : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 910)
    (stack : pre.stack = base :: size :: UInt256.ofNat 292 :: tail)
    (accept : (condition base size != ⟨0⟩) = false)
    (gas : 76 + expansion pre base size tail ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1019) :
    EVM.X (fuel + 23) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      EVM.X (fuel + 1) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) (returned pre base size tail) := by
  have charged := gas_exact pre base size (UInt256.ofNat 292 :: tail) (by omega)
  change (entry pre base size tail).gasAvailable.toNat = pre.gasAvailable.toNat - 62 at charged
  rw [NativeSourceCheckedAllocatorFullDecision.execute (fuel + 3) pre base size (UInt256.ofNat 292 :: tail)
    code pc stack (by omega) (by simp only [List.length_cons]; omega)]
  exact NativeSourceCheckedAllocatorExit.execute fuel (entry pre base size tail) (base + amount size) tail
    code (accepted_pc pre base size tail pc accept) (frame pre base size (UInt256.ofNat 292 :: tail)).1
    (by change 14 + expansion pre base size tail ≤ _; omega) (by omega)

theorem gas_exact (pre : EVM.State) (base size : UInt256) (tail : Stack UInt256)
    (gas : 76 + expansion pre base size tail ≤ pre.gasAvailable.toNat) :
    (returned pre base size tail).gasAvailable.toNat = pre.gasAvailable.toNat - expansion pre base size tail - 76 := by
  have charged := NativeSourceCheckedAllocatorFullDecision.gas_exact pre base size (UInt256.ofNat 292 :: tail) (by omega)
  change (entry pre base size tail).gasAvailable.toNat = pre.gasAvailable.toNat - 62 at charged
  have final := NativeSourceCheckedAllocatorExit.gas_exact (entry pre base size tail) (base + amount size) tail
    (by change 14 + expansion pre base size tail ≤ _; omega)
  change (returned pre base size tail).gasAvailable.toNat = (entry pre base size tail).gasAvailable.toNat - expansion pre base size tail - 14 at final
  omega

end Compiler.Proofs.IRGeneration.NativeSourceCheckedAllocatorSuccess

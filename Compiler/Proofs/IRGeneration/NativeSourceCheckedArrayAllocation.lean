import Compiler.Proofs.IRGeneration.NativeSourceCheckedAllocatorCertificate

namespace Compiler.Proofs.IRGeneration.NativeSourceCheckedArrayAllocation
open EvmYul EVM EVM.Proof

def base (pre : EVM.State) := NativeSourceArrayReadEntry.pointer pre

def size (n : UInt256) := (n <<< UInt256.ofNat 5) + UInt256.ofNat 32

def rest (pre : EVM.State) (n x array : UInt256) (tail : Stack UInt256) :=
  array :: n :: x :: base pre :: tail

def called (pre : EVM.State) (n x array : UInt256) (tail : Stack UInt256) :=
  NativeSourceArrayReadEntry.called pre n x array tail

def storeExpansion (pre : EVM.State) (n x array : UInt256) (tail : Stack UInt256) :=
  NativeSourceCheckedAllocatorSuccess.expansion (called pre n x array tail) (base pre) (size n)
    (rest pre n x array tail)

def returned (pre : EVM.State) (n x array : UInt256) (tail : Stack UInt256) :=
  NativeSourceCheckedAllocatorSuccess.returned (called pre n x array tail) (base pre) (size n)
    (rest pre n x array tail)

theorem call_frame (pre : EVM.State) (n x array : UInt256) (tail : Stack UInt256) :
    (called pre n x array tail).pc = UInt256.ofNat 910 ∧
    (called pre n x array tail).stack = base pre :: size n :: UInt256.ofNat 292 :: rest pre n x array tail ∧
    (called pre n x array tail).memory = pre.memory ∧ (called pre n x array tail).toState = pre.toState := by
  exact NativeSourceArrayCallJump.frame (NativeSourceArrayReadEntry.prepared pre n x array tail)
    array n x (base pre) tail

theorem execute (fuel : Nat) (pre : EVM.State) (n x array : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 273)
    (stack : pre.stack = n :: x :: array :: tail)
    (bound : (base pre).toNat + (NativeSourceCheckedAllocatorFullDecision.amount (size n)).toNat ≤ 2^64-1)
    (gas : 117 + NativeSourceArrayReadEntry.expansion pre + storeExpansion pre n x array tail ≤ pre.gasAvailable.toNat)
    (depth : tail.length ≤ 1015) :
    EVM.X (fuel + 35) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      EVM.X (fuel + 1) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) (returned pre n x array tail) := by
  have charged := NativeSourceArrayReadEntry.call_gas pre n x array tail (by omega)
  change (called pre n x array tail).gasAvailable.toNat = pre.gasAvailable.toNat - 41 - NativeSourceArrayReadEntry.expansion pre at charged
  have shape := call_frame pre n x array tail
  rw [NativeSourceArrayReadEntry.call_execute (fuel + 22) pre n x array tail code pc stack (by omega) (by omega)]
  exact NativeSourceCheckedAllocatorCertificate.execute fuel (called pre n x array tail) (base pre) (size n)
    (rest pre n x array tail) code shape.1 shape.2.1 bound
    (by change 76 + storeExpansion pre n x array tail ≤ _; omega)
    (by simp only [rest, List.length_cons]; omega)

theorem gas_exact (pre : EVM.State) (n x array : UInt256) (tail : Stack UInt256)
    (gas : 117 + NativeSourceArrayReadEntry.expansion pre + storeExpansion pre n x array tail ≤ pre.gasAvailable.toNat) :
    (returned pre n x array tail).gasAvailable.toNat =
      pre.gasAvailable.toNat - NativeSourceArrayReadEntry.expansion pre - storeExpansion pre n x array tail - 117 := by
  have charged := NativeSourceArrayReadEntry.call_gas pre n x array tail (by omega)
  change (called pre n x array tail).gasAvailable.toNat = pre.gasAvailable.toNat - 41 - NativeSourceArrayReadEntry.expansion pre at charged
  have final := NativeSourceCheckedAllocatorSuccess.gas_exact (called pre n x array tail)
    (base pre) (size n) (rest pre n x array tail)
    (by change 76 + storeExpansion pre n x array tail ≤ _; omega)
  change (returned pre n x array tail).gasAvailable.toNat =
    (called pre n x array tail).gasAvailable.toNat - storeExpansion pre n x array tail - 76 at final
  omega

end Compiler.Proofs.IRGeneration.NativeSourceCheckedArrayAllocation

import Compiler.Proofs.IRGeneration.NativeSourceArrayLengthStorePrefix

namespace Compiler.Proofs.IRGeneration.NativeSourceArrayAllocatedLength
open EvmYul EVM EVM.Proof

def allocated (pre : EVM.State) (n x array : UInt256) (tail : Stack UInt256) :=
  NativeSourceCheckedArrayAllocation.returned pre n x array tail

def lengthExpansion (pre : EVM.State) (n x array : UInt256) (tail : Stack UInt256) :=
  NativeSourceArrayLengthStorePrefix.expansion (allocated pre n x array tail) array n x
    (NativeSourceCheckedArrayAllocation.base pre) tail

def expansion (pre : EVM.State) (n x array : UInt256) (tail : Stack UInt256) :=
  NativeSourceArrayReadEntry.expansion pre + NativeSourceCheckedArrayAllocation.storeExpansion pre n x array tail +
    lengthExpansion pre n x array tail

def stored (pre : EVM.State) (n x array : UInt256) (tail : Stack UInt256) :=
  NativeSourceArrayLengthStorePrefix.stored (allocated pre n x array tail) array n x
    (NativeSourceCheckedArrayAllocation.base pre) tail

theorem execute (fuel : Nat) (pre : EVM.State) (n x array : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 273)
    (stack : pre.stack = n :: x :: array :: tail)
    (bound : (NativeSourceCheckedArrayAllocation.base pre).toNat +
      (NativeSourceCheckedAllocatorFullDecision.amount (NativeSourceCheckedArrayAllocation.size n)).toNat ≤ 2^64-1)
    (gas : 127 + expansion pre n x array tail ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1015) :
    EVM.X (fuel + 39) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      EVM.X (fuel + 1) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) (stored pre n x array tail) := by
  have budget : 117 + NativeSourceArrayReadEntry.expansion pre +
      NativeSourceCheckedArrayAllocation.storeExpansion pre n x array tail ≤ pre.gasAvailable.toNat := by
    unfold expansion at gas; omega
  have charged := NativeSourceCheckedArrayAllocation.gas_exact pre n x array tail budget
  change (allocated pre n x array tail).gasAvailable.toNat = _ at charged
  have shape := NativeSourceCheckedArrayAllocationFrame.original_frame pre n x array tail
  rw [NativeSourceCheckedArrayAllocation.execute (fuel + 4) pre n x array tail code pc stack bound budget depth]
  exact NativeSourceArrayLengthStorePrefix.execute fuel _ (allocated pre n x array tail) array n x
    (NativeSourceCheckedArrayAllocation.base pre) tail code shape.1 shape.2.1
    (by change 10 + lengthExpansion pre n x array tail ≤ _; unfold expansion at gas; omega) (by omega)

theorem gas_exact (pre : EVM.State) (n x array : UInt256) (tail : Stack UInt256)
    (gas : 127 + expansion pre n x array tail ≤ pre.gasAvailable.toNat) :
    (stored pre n x array tail).gasAvailable.toNat = pre.gasAvailable.toNat - expansion pre n x array tail - 127 := by
  have budget : 117 + NativeSourceArrayReadEntry.expansion pre +
      NativeSourceCheckedArrayAllocation.storeExpansion pre n x array tail ≤ pre.gasAvailable.toNat := by
    unfold expansion at gas; omega
  have charged := NativeSourceCheckedArrayAllocation.gas_exact pre n x array tail budget
  change (allocated pre n x array tail).gasAvailable.toNat = _ at charged
  have final := NativeSourceArrayLengthStorePrefix.gas_exact (allocated pre n x array tail) array n x
    (NativeSourceCheckedArrayAllocation.base pre) tail
    (by change 10 + lengthExpansion pre n x array tail ≤ _; unfold expansion at gas; omega)
  change (stored pre n x array tail).gasAvailable.toNat =
    (allocated pre n x array tail).gasAvailable.toNat - lengthExpansion pre n x array tail - 10 at final
  unfold expansion
  omega

end Compiler.Proofs.IRGeneration.NativeSourceArrayAllocatedLength

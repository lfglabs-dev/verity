import Compiler.Proofs.IRGeneration.NativeSourceCheckedAllocatorReturn

namespace Compiler.Proofs.IRGeneration.NativeSourceCheckedAllocatorExit
open EvmYul EVM EVM.Proof

def pushed (pre : EVM.State) := NativeSourceAllocatorReturn.pushed 3 pre

def expansion (pre : EVM.State) := memoryExpansionCost (pushed pre) .MSTORE

def stored (pre : EVM.State) (pointer : UInt256) (tail : Stack UInt256) :=
  mstorePost 3 (NativeSourceFieldStoreChecks.expanded (pushed pre))
    (UInt256.ofNat 292 :: tail) (UInt256.ofNat 64) pointer

def returned (pre : EVM.State) (pointer : UInt256) (tail : Stack UInt256) :=
  NativeSourceCheckedAllocatorReturn.jumped (stored pre pointer tail) tail

theorem push_pc (pre : EVM.State) (pc : pre.pc = UInt256.ofNat 940) :
    (pushed pre).pc = UInt256.ofNat 942 := by
  change pre.pc + UInt256.ofNat 2 = _
  rw [pc]; decide

theorem store_pc (pre : EVM.State) (pointer : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 940) : (stored pre pointer tail).pc = UInt256.ofNat 943 := by
  change (pushed pre).pc + UInt256.ofNat 1 = _
  rw [push_pc pre pc]; decide

theorem gas_chain (pre : EVM.State) (pointer : UInt256) (tail : Stack UInt256)
    (gas : 14 + expansion pre ≤ pre.gasAvailable.toNat) :
    (pushed pre).gasAvailable.toNat = pre.gasAvailable.toNat - 3 ∧
    (stored pre pointer tail).gasAvailable.toNat = pre.gasAvailable.toNat - expansion pre - 6 := by
  have first : (pushed pre).gasAvailable.toNat = pre.gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have enough : memoryExpansionCost (pushed pre) .MSTORE + 3 ≤ (pushed pre).gasAvailable.toNat := by
    change expansion pre + 3 ≤ _; omega
  have second := NativeSourceCheckedAllocatorStore.store_gas (pushed pre) pointer (UInt256.ofNat 292 :: tail) enough
  change (stored pre pointer tail).gasAvailable.toNat = (pushed pre).gasAvailable.toNat - expansion pre - 3 at second
  exact ⟨first, by omega⟩

theorem execute (fuel : Nat) (pre : EVM.State) (pointer : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 940)
    (stack : pre.stack = pointer :: UInt256.ofNat 292 :: tail)
    (gas : 14 + expansion pre ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1021) :
    EVM.X (fuel + 4) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      EVM.X (fuel + 1) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) (returned pre pointer tail) := by
  have charged := gas_chain pre pointer tail gas
  rw [NativeSourceCheckedAllocatorStore.push_continue (fuel + 2) _ pre code pc (by omega)
    (by simp only [stack, List.length_cons]; omega)]
  change EVM.X ((fuel + 1) + 2) _ (pushed pre) = _
  rw [NativeSourceCheckedAllocatorStore.store_continue (fuel + 1) _ (pushed pre) pointer
    (UInt256.ofNat 292 :: tail) code (push_pc pre pc) (by change UInt256.ofNat 64 :: pre.stack = _; rw [stack])
    (by change expansion pre + 3 ≤ _; omega) (by simp only [List.length_cons]; omega)]
  exact NativeSourceCheckedAllocatorReturn.jump_continue fuel (stored pre pointer tail) tail code
    (store_pc pre pointer tail pc) rfl (by omega) (by omega)

theorem gas_exact (pre : EVM.State) (pointer : UInt256) (tail : Stack UInt256)
    (gas : 14 + expansion pre ≤ pre.gasAvailable.toNat) :
    (returned pre pointer tail).gasAvailable.toNat = pre.gasAvailable.toNat - expansion pre - 14 := by
  have charged := (gas_chain pre pointer tail gas).2
  have final := NativeSourceCheckedAllocatorReturn.jump_gas (stored pre pointer tail) tail (by omega)
  change (returned pre pointer tail).gasAvailable.toNat = _ at final
  omega

end Compiler.Proofs.IRGeneration.NativeSourceCheckedAllocatorExit

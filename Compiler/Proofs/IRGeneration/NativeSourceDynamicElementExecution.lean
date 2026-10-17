import Compiler.Proofs.IRGeneration.NativeSourceDynamicFourthStore

namespace Compiler.Proofs.IRGeneration.NativeSourceDynamicElementExecution
open EvmYul EVM.Proof NativeSourcePreludeDecoded

abbrev two (cost : Nat) (pre : EVM.State) (source mask dest spare : UInt256) (tail : Stack UInt256) :=
  NativeSourceDynamicTwoStores.second cost pre source (UInt256.ofNat 96) mask dest spare tail
abbrev three (cost : Nat) (pre : EVM.State) (source mask dest spare : UInt256) (tail : Stack UInt256) :=
  NativeSourceDynamicThirdStore.s8 cost (two cost pre source mask dest spare tail)
    (pre.toMachineState.lookupMemory source) (UInt256.ofNat 96) mask dest spare (UInt256.ofNat 32) tail
abbrev four (cost : Nat) (pre : EVM.State) (source mask dest spare : UInt256) (tail : Stack UInt256) :=
  NativeSourceDynamicFourthStore.s7 cost (three cost pre source mask dest spare tail)
    (pre.toMachineState.lookupMemory source) (UInt256.ofNat 96) mask dest spare (UInt256.ofNat 32) tail

theorem two_pc (cost : Nat) (pre : EVM.State) (source mask dest spare : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 741) :
    (two cost pre source mask dest spare tail).pc = UInt256.ofNat 756 := by
  have first := NativeSourceDynamicTwoStores.first_pc cost pre source (UInt256.ofNat 96) mask dest spare tail pc
  change ((((((((NativeSourceDynamicTwoStores.first cost pre source (UInt256.ofNat 96) mask dest spare tail).pc +
    UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) +
    UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1 = _
  rw [first]; decide

theorem three_pc (cost : Nat) (pre : EVM.State) (source mask dest spare : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 741) :
    (three cost pre source mask dest spare tail).pc = UInt256.ofNat 766 := by
  change ((((((((two cost pre source mask dest spare tail).pc + UInt256.ofNat 2) + UInt256.ofNat 1) +
    UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 2) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1 = _
  rw [two_pc cost pre source mask dest spare tail pc]; decide

theorem execute_three (fuel cost : Nat) (pre : EVM.State) (source mask dest spare : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 741)
    (stack : pre.stack = source :: UInt256.ofNat 96 :: mask :: dest :: spare :: UInt256.ofNat 32 :: tail) :
    run fuel cost 23 pre = .ok (three cost pre source mask dest spare tail) := by
  exact NativeSourceSizedPacking.compose fuel cost 15 8 pre _ _
    (NativeSourceDynamicTwoStores.execute fuel cost pre source (UInt256.ofNat 96) mask dest spare tail code pc stack)
    (NativeSourceDynamicThirdStore.execute fuel cost _ _ (UInt256.ofNat 96) mask dest spare (UInt256.ofNat 32) tail
      code (two_pc cost pre source mask dest spare tail pc) (by rfl))

theorem execute (fuel cost : Nat) (pre : EVM.State) (source mask dest spare : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 741)
    (stack : pre.stack = source :: UInt256.ofNat 96 :: mask :: dest :: spare :: UInt256.ofNat 32 :: tail) :
    run fuel cost 30 pre = .ok (four cost pre source mask dest spare tail) := by
  exact NativeSourceSizedPacking.compose fuel cost 23 7 pre _ _
    (execute_three fuel cost pre source mask dest spare tail code pc stack)
    (NativeSourceDynamicFourthStore.execute fuel cost _ _ (UInt256.ofNat 96) mask dest spare (UInt256.ofNat 32) tail
      code (three_pc cost pre source mask dest spare tail pc) (by rfl))

theorem output_stack (cost : Nat) (pre : EVM.State) (source mask dest spare : UInt256) (tail : Stack UInt256) :
    (four cost pre source mask dest spare tail).stack = dest :: spare :: UInt256.ofNat 32 :: tail := by
  rfl

theorem endpoint_inside (cost : Nat) (pre : EVM.State) (source mask dest spare : UInt256) (tail : Stack UInt256)
    (platform : 64 ≤ System.Platform.numBits) (bounded : dest.toNat + 96 < 2 ^ 64) :
    dest.toNat + 128 ≤ (four cost pre source mask dest spare tail).memory.size := by
  have offset := NativeSourceFieldGeometry.offset_toNat dest 96 (by decide) (by omega)
  have addressBound : (dest + UInt256.ofNat 96).toNat < 2 ^ 64 := by rw [offset]; omega
  rw [NativeSourceDynamicFourthStore.memory]
  rw [NativeSourceDynamicElementCarrier.store_extent _ _ _ platform addressBound, offset]
  omega

end Compiler.Proofs.IRGeneration.NativeSourceDynamicElementExecution

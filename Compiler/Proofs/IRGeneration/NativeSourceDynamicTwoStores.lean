import Compiler.Proofs.IRGeneration.NativeSourceDynamicSecondStore

namespace Compiler.Proofs.IRGeneration.NativeSourceDynamicTwoStores
open EvmYul EVM.Proof NativeSourcePreludeDecoded

abbrev first (cost : Nat) (pre : EVM.State) (source x mask dest spare : UInt256) (tail : Stack UInt256) :=
  NativeSourceDynamicFirstStore.stored cost
    (NativeSourceDynamicFirstLoad.ready cost pre source x mask dest spare (UInt256.ofNat 32 :: tail))
    (pre.toMachineState.lookupMemory source) mask (pre.toMachineState.lookupMemory source) x mask dest
    (spare :: UInt256.ofNat 32 :: tail)

abbrev second (cost : Nat) (pre : EVM.State) (source x mask dest spare : UInt256) (tail : Stack UInt256) :=
  NativeSourceDynamicSecondStore.s8 cost (first cost pre source x mask dest spare tail)
    (pre.toMachineState.lookupMemory source) x mask dest spare (UInt256.ofNat 32) tail

theorem first_pc (cost : Nat) (pre : EVM.State) (source x mask dest spare : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 741) :
    (first cost pre source x mask dest spare tail).pc = UInt256.ofNat 748 := by
  have ready := NativeSourceDynamicFirstLoad.ready_pc cost pre source x mask dest spare
    (UInt256.ofNat 32 :: tail) pc
  change ((((NativeSourceDynamicFirstLoad.ready cost pre source x mask dest spare
    (UInt256.ofNat 32 :: tail)).pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1 = _
  rw [ready]; decide

theorem first_stack (cost : Nat) (pre : EVM.State) (source x mask dest spare : UInt256) (tail : Stack UInt256) :
    (first cost pre source x mask dest spare tail).stack =
      pre.toMachineState.lookupMemory source :: x :: mask :: dest :: spare :: UInt256.ofNat 32 :: tail := by
  rfl

theorem execute (fuel cost : Nat) (pre : EVM.State) (source x mask dest spare : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 741)
    (stack : pre.stack = source :: x :: mask :: dest :: spare :: UInt256.ofNat 32 :: tail) :
    run fuel cost 15 pre = .ok (second cost pre source x mask dest spare tail) := by
  exact NativeSourceSizedPacking.compose fuel cost 7 8 pre _ _
    (NativeSourceDynamicFirstLoad.execute_store fuel cost pre source x mask dest spare
      (UInt256.ofNat 32 :: tail) code pc stack)
    (NativeSourceDynamicSecondStore.execute fuel cost _ _ x mask dest spare (UInt256.ofNat 32) tail
      code (first_pc cost pre source x mask dest spare tail pc)
      (first_stack cost pre source x mask dest spare tail))

theorem second_memory (cost : Nat) (pre : EVM.State) (source x mask dest spare : UInt256) (tail : Stack UInt256) :
    (second cost pre source x mask dest spare tail).memory =
      ((first cost pre source x mask dest spare tail).toMachineState.mstore (dest + UInt256.ofNat 32)
        ((first cost pre source x mask dest spare tail).toMachineState.lookupMemory
          (pre.toMachineState.lookupMemory source + UInt256.ofNat 32))).memory := by
  exact NativeSourceDynamicSecondStore.memory cost _ _ x mask dest spare (UInt256.ofNat 32) tail

end Compiler.Proofs.IRGeneration.NativeSourceDynamicTwoStores

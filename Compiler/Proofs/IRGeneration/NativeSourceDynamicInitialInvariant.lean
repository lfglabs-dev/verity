import Compiler.Proofs.IRGeneration.NativeSourceDynamicHeaderSetup

namespace Compiler.Proofs.IRGeneration.NativeSourceDynamicInitialInvariant
open EvmYul EVM.Proof NativeSourcePreludeDecoded NativeSourceDynamicLoopInduction

abbrev stored (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (tail : Stack UInt256) := NativeSourceDynamicLengthStore.s5 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 (x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: tail)
abbrev ready (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (tail : Stack UInt256) := NativeSourceDynamicHeaderSetup.s8 cost (stored cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail) (pre.toMachineState.lookupMemory x9) x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail
def registers (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) : Registers :=
  { x0 := UInt256.ofNat 0, x1 := pre.toMachineState.lookupMemory x9, x2 := x9 + UInt256.ofNat 32,
    x3 := x1, x4 := x2, x5 := x3, x6 := x4, x7 := x5, x8 := x6, x9 := x7, x10 := x8,
    x11 := x7 + UInt256.ofNat 352, x12 := x10, x13 := x11, x14 := x12, x15 := x13 }

theorem stored_pc (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (tail : Stack UInt256) (pc : pre.pc = UInt256.ofNat 535) :
    (stored cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail).pc = UInt256.ofNat 540 := by
  change (((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
  rw [pc]; decide

theorem execute (fuel cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 535)
    (stack : pre.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: tail) :
    run fuel cost 13 pre = .ok (ready cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail) := by
  exact NativeSourceSizedPacking.compose fuel cost 5 8 pre _ _
    (NativeSourceDynamicLengthStore.execute fuel cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 (x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: tail) code pc stack)
    (NativeSourceDynamicHeaderSetup.execute fuel cost _ (pre.toMachineState.lookupMemory x9) x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail code (stored_pc cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail pc) (by rfl))

theorem endpoint_inside (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (tail : Stack UInt256)
    (platform : 64 ≤ System.Platform.numBits) (bounded : x7.toNat + 352 < 2 ^ 64)
    (target : x0 = x7 + UInt256.ofNat 320) :
    (x7 + UInt256.ofNat 352).toNat ≤ (ready cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail).memory.size := by
  subst x0
  have address := NativeSourceFieldGeometry.offset_toNat x7 320 (by decide) (by omega)
  have finish := NativeSourceFieldGeometry.offset_toNat x7 352 (by decide) (by omega)
  have bound : (x7 + UInt256.ofNat 320).toNat < 2 ^ 64 := by rw [address]; omega
  have extent := NativeSourceDynamicLengthStore.extent cost pre (x7 + UInt256.ofNat 320) x1 x2 x3 x4 x5 x6 x7 x8 x9 (x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: tail) platform bound
  rw [address] at extent
  change (x7 + UInt256.ofNat 352).toNat ≤ (NativeSourceDynamicHeaderSetup.s8 cost _ (pre.toMachineState.lookupMemory x9) x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail).memory.size
  rw [NativeSourceDynamicHeaderSetup.memory, finish]
  omega

theorem initial_invariant (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 535)
    (platform : 64 ≤ System.Platform.numBits) (bounded : x7.toNat + 352 < 2 ^ 64)
    (target : x0 = x7 + UInt256.ofNat 320) :
    Invariant (registers pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15) (ready cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail) (x14 :: x15 :: tail) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact code
  · exact NativeSourceDynamicHeaderSetup.header_pc cost _ (pre.toMachineState.lookupMemory x9) x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail (stored_pc cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail pc)
  · exact NativeSourceDynamicHeaderSetup.output_stack cost _ (pre.toMachineState.lookupMemory x9) x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail
  · exact endpoint_inside cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail platform bounded target

end Compiler.Proofs.IRGeneration.NativeSourceDynamicInitialInvariant

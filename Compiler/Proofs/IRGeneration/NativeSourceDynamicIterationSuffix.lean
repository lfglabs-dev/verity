import Compiler.Proofs.IRGeneration.NativeSourceDynamicBackedge

namespace Compiler.Proofs.IRGeneration.NativeSourceDynamicIterationSuffix
open EvmYul EVM.Proof NativeSourcePreludeDecoded

abbrev written (cost : Nat) (pre : EVM.State) (source mask dest spare x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (tail : Stack UInt256) :=
  NativeSourceDynamicElementExecution.four cost pre source mask dest spare (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: tail)
abbrev updated (cost : Nat) (pre : EVM.State) (source mask dest spare x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (tail : Stack UInt256) :=
  NativeSourceDynamicIncrements.s8 cost (written cost pre source mask dest spare x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail) dest spare (UInt256.ofNat 32) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail
abbrev returned (cost : Nat) (pre : EVM.State) (source mask dest spare x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (tail : Stack UInt256) :=
  NativeSourceDynamicBackedge.returned cost (updated cost pre source mask dest spare x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail)

theorem written_pc (cost : Nat) (pre : EVM.State) (source mask dest spare x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (tail : Stack UInt256) (pc : pre.pc = UInt256.ofNat 741) :
    (written cost pre source mask dest spare x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail).pc = UInt256.ofNat 774 := by
  have third := NativeSourceDynamicElementExecution.three_pc cost pre source mask dest spare (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: tail) pc
  change (((((((NativeSourceDynamicElementExecution.three cost pre source mask dest spare (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: tail)).pc +
    UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 2) + UInt256.ofNat 1) +
    UInt256.ofNat 1) + UInt256.ofNat 1 = _
  rw [third]; decide

theorem updated_pc (cost : Nat) (pre : EVM.State) (source mask dest spare x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (tail : Stack UInt256) (pc : pre.pc = UInt256.ofNat 741) :
    (updated cost pre source mask dest spare x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail).pc = UInt256.ofNat 782 := by
  change ((((((((written cost pre source mask dest spare x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail).pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) +
    UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1 = _
  rw [written_pc cost pre source mask dest spare x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail pc]; decide

theorem execute_updated (fuel cost : Nat) (pre : EVM.State) (source mask dest spare x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 741)
    (stack : pre.stack = source :: UInt256.ofNat 96 :: mask :: dest :: spare :: UInt256.ofNat 32 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: tail) :
    run fuel cost 38 pre = .ok (updated cost pre source mask dest spare x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail) := by
  exact NativeSourceSizedPacking.compose fuel cost 30 8 pre _ _
    (NativeSourceDynamicElementExecution.execute fuel cost pre source mask dest spare (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: tail) code pc stack)
    (NativeSourceDynamicIncrements.execute fuel cost _ dest spare (UInt256.ofNat 32) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail
      code (written_pc cost pre source mask dest spare x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail pc) (by rfl))

theorem execute (fuel cost : Nat) (pre : EVM.State) (source mask dest spare x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 741)
    (stack : pre.stack = source :: UInt256.ofNat 96 :: mask :: dest :: spare :: UInt256.ofNat 32 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: tail) :
    run fuel cost 40 pre = .ok (returned cost pre source mask dest spare x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail) := by
  exact NativeSourceSizedPacking.compose fuel cost 38 2 pre _ _
    (execute_updated fuel cost pre source mask dest spare x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail code pc stack)
    (NativeSourceDynamicBackedge.execute fuel cost _ code (updated_pc cost pre source mask dest spare x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail pc))

theorem memory (cost : Nat) (pre : EVM.State) (source mask dest spare x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (tail : Stack UInt256) :
    (returned cost pre source mask dest spare x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail).memory = (written cost pre source mask dest spare x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail).memory := by
  rw [NativeSourceDynamicBackedge.memory, NativeSourceDynamicIncrements.memory]

theorem endpoint_inside (cost : Nat) (pre : EVM.State) (source mask dest spare x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (tail : Stack UInt256)
    (platform : 64 ≤ System.Platform.numBits) (bounded : dest.toNat + 96 < 2 ^ 64) :
    dest.toNat + 128 ≤ (returned cost pre source mask dest spare x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail).memory.size := by
  rw [memory]
  exact NativeSourceDynamicElementExecution.endpoint_inside cost pre source mask dest spare (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: tail) platform bounded

theorem header_pc (cost : Nat) (pre : EVM.State) (source mask dest spare x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (tail : Stack UInt256) :
    (returned cost pre source mask dest spare x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail).pc = UInt256.ofNat 551 := by
  rfl

end Compiler.Proofs.IRGeneration.NativeSourceDynamicIterationSuffix

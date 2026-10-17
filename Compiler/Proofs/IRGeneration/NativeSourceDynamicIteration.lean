import Compiler.Proofs.IRGeneration.NativeSourceDynamicExit

namespace Compiler.Proofs.IRGeneration.NativeSourceDynamicIteration
open EvmYul EVM.Proof NativeSourcePreludeDecoded

abbrev tested (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (tail : Stack UInt256) := NativeSourceDynamicHeader.s6 cost pre x0 x1 (x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: tail)
abbrev returned (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (tail : Stack UInt256) := NativeSourceDynamicBody.returned cost (tested cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail

theorem execute (fuel cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 551)
    (stack : pre.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: tail) (less : x0 < x1) :
    run fuel cost 62 pre = .ok (returned cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail) := by
  exact NativeSourceSizedPacking.compose fuel cost 6 56 pre _ _
    (NativeSourceDynamicHeader.execute fuel cost pre x0 x1 (x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: tail) code pc stack)
    (NativeSourceDynamicBody.execute fuel cost _ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail code
      (NativeSourceDynamicHeader.continue_pc cost pre x0 x1 (x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: tail) less)
      (NativeSourceDynamicHeader.output_stack cost pre x0 x1 (x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: tail)))

theorem output_stack (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (tail : Stack UInt256) :
    (returned cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail).stack =
      (x0 + UInt256.ofNat 1) :: x1 :: (x2 + UInt256.ofNat 32) :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 ::
      (x11 + UInt256.ofNat 128) :: x12 :: x13 :: x14 :: x15 :: tail := by
  exact NativeSourceDynamicBody.output_stack cost _ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail

theorem endpoint_inside (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (tail : Stack UInt256)
    (platform : 64 ≤ System.Platform.numBits) (bounded : x11.toNat + 96 < 2 ^ 64) :
    x11.toNat + 128 ≤ (returned cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail).memory.size := by
  exact NativeSourceDynamicBody.endpoint_inside cost _ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail platform bounded

theorem header_pc (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (tail : Stack UInt256) : (returned cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail).pc = UInt256.ofNat 551 := by
  exact NativeSourceDynamicBody.header_pc cost _ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail

theorem code (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (tail : Stack UInt256) : (returned cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail).executionEnv.code = pre.executionEnv.code := by
  rfl

end Compiler.Proofs.IRGeneration.NativeSourceDynamicIteration

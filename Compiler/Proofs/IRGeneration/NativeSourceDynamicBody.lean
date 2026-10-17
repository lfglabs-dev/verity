import Compiler.Proofs.IRGeneration.NativeSourceDynamicEntry

namespace Compiler.Proofs.IRGeneration.NativeSourceDynamicBody
open EvmYul EVM.Proof NativeSourcePreludeDecoded

abbrev mask : UInt256 := ((UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) - UInt256.ofNat 1)
abbrev ready (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (tail : Stack UInt256) := NativeSourceDynamicEntry.s16 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail
abbrev returned (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (tail : Stack UInt256) := NativeSourceDynamicIterationSuffix.returned cost (ready cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail) x2 mask x11 (UInt256.ofNat 128) (UInt256.ofNat 1) x0 x1 x3 x4 x5 x6 x7 x8 x9 x10 x2 x12 (x13 :: x14 :: x15 :: tail)

theorem backedge_stack (cost : Nat) (pre : EVM.State) :
    (NativeSourceDynamicBackedge.returned cost pre).stack = pre.stack := by
  rfl

theorem ready_pc (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (tail : Stack UInt256) (pc : pre.pc = UInt256.ofNat 718) :
    (ready cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail).pc = UInt256.ofNat 741 := by
  change ((((((((((((((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 2) + UInt256.ofNat 2) + UInt256.ofNat 2) + UInt256.ofNat 1) + UInt256.ofNat 2) + UInt256.ofNat 2) + UInt256.ofNat 2) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 2) + UInt256.ofNat 1) = _
  rw [pc]; decide

theorem execute (fuel cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 718)
    (stack : pre.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: tail) :
    run fuel cost 56 pre = .ok (returned cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail) := by
  exact NativeSourceSizedPacking.compose fuel cost 16 40 pre _ _
    (NativeSourceDynamicEntry.execute fuel cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail code pc stack)
    (NativeSourceDynamicIterationSuffix.execute fuel cost _ x2 mask x11 (UInt256.ofNat 128) (UInt256.ofNat 1) x0 x1 x3 x4 x5 x6 x7 x8 x9 x10 x2 x12 (x13 :: x14 :: x15 :: tail)
      code (ready_pc cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail pc) (NativeSourceDynamicEntry.output_stack cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail))

theorem output_stack (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (tail : Stack UInt256) :
    (returned cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail).stack =
      (x0 + UInt256.ofNat 1) :: x1 :: (x2 + UInt256.ofNat 32) :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 ::
      (x11 + UInt256.ofNat 128) :: x12 :: x13 :: x14 :: x15 :: tail := by
  rw [backedge_stack, NativeSourceDynamicIncrements.output_stack]

theorem endpoint_inside (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (tail : Stack UInt256)
    (platform : 64 ≤ System.Platform.numBits) (bounded : x11.toNat + 96 < 2 ^ 64) :
    x11.toNat + 128 ≤ (returned cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail).memory.size := by
  exact NativeSourceDynamicIterationSuffix.endpoint_inside cost _ x2 mask x11 (UInt256.ofNat 128) (UInt256.ofNat 1) x0 x1 x3 x4 x5 x6 x7 x8 x9 x10 x2 x12 (x13 :: x14 :: x15 :: tail) platform bounded

theorem header_pc (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (tail : Stack UInt256) : (returned cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail).pc = UInt256.ofNat 551 := by
  exact NativeSourceDynamicIterationSuffix.header_pc cost _ x2 mask x11 (UInt256.ofNat 128) (UInt256.ofNat 1) x0 x1 x3 x4 x5 x6 x7 x8 x9 x10 x2 x12 (x13 :: x14 :: x15 :: tail)

end Compiler.Proofs.IRGeneration.NativeSourceDynamicBody

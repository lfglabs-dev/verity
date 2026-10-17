import Compiler.Proofs.IRGeneration.NativeSourceDynamicSourceSetup

namespace Compiler.Proofs.IRGeneration.NativeSourceDynamicSourceReturn
open EvmYul EVM.Proof NativeSourcePreludeDecoded

abbrev prepared (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (tail : Stack UInt256) := NativeSourceDynamicSourceSetup.s8 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 (x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: tail)
abbrev entry (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (tail : Stack UInt256) := NativeSourceDynamicTransportReturn.entry cost (prepared cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail) x7 x1 x0 x1 x2 x3 x4 x5 x6 (x9 + UInt256.ofNat 32) x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 (x18 :: x19 :: tail)
abbrev arrayPointer (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (tail : Stack UInt256) := NativeSourceDynamicTransportReturn.lastLoad cost (prepared cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail) x7 x1 x0 x1 x2 x3 x4 x5 x6 (x9 + UInt256.ofNat 32) x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 (x18 :: x19 :: tail)
abbrev count (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (tail : Stack UInt256) := NativeSourceDynamicInitialReturn.count (entry cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail) (arrayPointer cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail)
abbrev result (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (tail : Stack UInt256) := NativeSourceDynamicTransportReturn.result cost (prepared cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail) x7 x1 x0 x1 x2 x3 x4 x5 x6 (x9 + UInt256.ofNat 32) x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 (x18 :: x19 :: tail)

abbrev registers (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (tail : Stack UInt256) := NativeSourceDynamicInitialInvariant.registers (entry cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail) (x9 + UInt256.ofNat 320) x3 x4 x5 x6 (x9 + UInt256.ofNat 32) x8 x9 x10 (arrayPointer cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail) x12 x13 x14 x15 x16 x17

theorem prepared_pc (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (tail : Stack UInt256) (pc : pre.pc = UInt256.ofNat 489) : (prepared cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail).pc = UInt256.ofNat 499 := by
  change ((((((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 2) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 2) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
  rw [pc]; decide

theorem execute (fuel : Nat) (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 489)
    (stack : pre.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: tail)
    (platform : 64 ≤ System.Platform.numBits) (countBound : (count cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail) < 2 ^ 64)
    (endpoint : x9.toNat + 352 + 128 * (count cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail) < 2 ^ 64) :
    run fuel cost (8 + (28 + (13 + (62 * (count cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail) + 17)))) pre = .ok (result cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail) := by
  exact NativeSourceSizedPacking.compose fuel cost 8 _ pre _ _
    (NativeSourceDynamicSourceSetup.execute fuel cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 (x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: tail) code pc stack)
    (NativeSourceDynamicTransportReturn.execute fuel cost (prepared cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail) x7 x1 x0 x1 x2 x3 x4 x5 x6 (x9 + UInt256.ofNat 32) x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 (x18 :: x19 :: tail) code (prepared_pc cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail pc) (by rfl) platform countBound endpoint)

theorem source_value (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (tail : Stack UInt256) (bounded : x9.toNat + 32 < 2 ^ 256) :
    (registers cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail).x7.toNat = (registers cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail).x9.toNat + 32 := by
  exact NativeSourceFieldGeometry.offset_toNat x9 32 (by decide) bounded

theorem initial_order (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (tail : Stack UInt256) (bounded : x9.toNat + 352 < 2 ^ 256) :
    (registers cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail).x9.toNat + 32 ≤ (registers cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail).x11.toNat := by
  change x9.toNat + 32 ≤ (x9 + UInt256.ofNat 352).toNat
  rw [NativeSourceFieldGeometry.offset_toNat x9 352 (by decide) bounded]
  omega

end Compiler.Proofs.IRGeneration.NativeSourceDynamicSourceReturn

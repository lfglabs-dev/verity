import Compiler.Proofs.IRGeneration.NativeSourcePreparedSecondLength
import Compiler.Proofs.IRGeneration.NativeSourceContextFieldSourceExtract

namespace Compiler.Proofs.IRGeneration.NativeSourcePreparedSourceWindow
open EvmYul NativeSourceDynamicSourceReturn NativeSourcePreparedSecondGeometry

theorem fields_monotone (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256)
    (platform : 64 ≤ System.Platform.numBits) (fields : c.toNat + 288 < 2 ^ 64) :
    pre.memory.size ≤ (NativeSourceFourthField.stored cost pre a b c d e f g h i j k tail).memory.size := by
  have power : 2 ^ 64 ≤ 2 ^ System.Platform.numBits := Nat.pow_le_pow_right (by decide) platform
  have fits : c.toNat + 288 < 2 ^ 256 := by omega
  have p0 := NativeSourceBoundedPadding.field_padding c pre.memory (by omega) (by omega)
  have p1 := NativeSourceFieldPadding.second_padding cost pre a b c d e f g h i j k tail fits p0
  have p2 := NativeSourceFieldPadding.third_padding cost pre a b c d e f g h i j k tail fits p1
  have p3 := NativeSourceFieldPadding.fourth_padding cost pre a b c d e f g h i j k tail fits p2
  exact (NativeSourceContextMemorySize.first cost pre a b c d e f g h i j k tail p0).trans
    ((NativeSourceContextMemorySize.second cost pre a b c d e f g h i j k tail p1).trans
      ((NativeSourceContextMemorySize.third cost pre a b c d e f g h i j k tail p2).trans
        (NativeSourceContextMemorySize.fourth cost pre a b c d e f g h i j k tail p3)))

theorem source_finish (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (tail : Stack UInt256)
    (countBound : (count cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail) < 2 ^ 64) (bounded : x9.toNat + 352 + 128 * (count cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail) < 2 ^ 64) :
    (advanced cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail).x7.toNat + (320 + 128 * (count cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail)) = (advanced cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail).x11.toNat := by
  have source := NativeSourcePreparedSecondGeometry.source_value cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail (by omega)
  have finish := NativeSourcePreparedSecondLength.endpoint_value cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail countBound bounded
  have base : (advanced cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail).x9 = x9 := (NativeSourceDynamicMappedEndpoint.stable_source_base (count cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail) (registers cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail)).2
  rw [source, base, finish]
  omega

theorem fourth_inside (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 489)
    (platform : 64 ≤ System.Platform.numBits) (countBound : (count cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail) < 2 ^ 64)
    (bounded : x9.toNat + 352 + 128 * (count cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail) < 2 ^ 64) :
    (advanced cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail).x7.toNat + (320 + 128 * (count cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail)) ≤ (NativeSourceFourthField.stored cost (result cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail) NativeSourceDynamicMappedEndpoint.mask (advanced cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail).x11 (advanced cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail).x9 (advanced cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail).x3 (advanced cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail).x4 (advanced cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail).x5 (advanced cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail).x6 (advanced cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail).x7 (advanced cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail).x8 (advanced cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail).x9 (advanced cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail).x10 (NativeSourceDynamicMappedEndpoint.mask :: ((advanced cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail).x12 :: (advanced cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail).x13 :: (advanced cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail).x14 :: (advanced cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail).x15 :: x16 :: x17 :: x18 :: x19 :: tail))).memory.size := by
  rw [source_finish cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail countBound bounded]
  have inside := endpoint_inside cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail code pc platform countBound bounded
  have base : (advanced cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail).x9 = x9 := (NativeSourceDynamicMappedEndpoint.stable_source_base (count cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail) (registers cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail)).2
  exact inside.trans (fields_monotone cost (result cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail) NativeSourceDynamicMappedEndpoint.mask (advanced cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail).x11 (advanced cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail).x9 (advanced cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail).x3 (advanced cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail).x4 (advanced cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail).x5 (advanced cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail).x6 (advanced cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail).x7 (advanced cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail).x8 (advanced cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail).x9 (advanced cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail).x10 (NativeSourceDynamicMappedEndpoint.mask :: ((advanced cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail).x12 :: (advanced cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail).x13 :: (advanced cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail).x14 :: (advanced cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail).x15 :: x16 :: x17 :: x18 :: x19 :: tail)) platform (by rw [base]; omega))

theorem word_below (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (tail : Stack UInt256)
    (bounded : x9.toNat + 32 < 2 ^ 256) :
    (advanced cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail).x9.toNat + 32 ≤ (advanced cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail).x7.toNat := by
  exact (NativeSourcePreparedSecondGeometry.source_value cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail bounded).symm.le

end Compiler.Proofs.IRGeneration.NativeSourcePreparedSourceWindow

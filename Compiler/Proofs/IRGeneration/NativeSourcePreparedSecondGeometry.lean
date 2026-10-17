import Compiler.Proofs.IRGeneration.NativeSourceDynamicSourceInvariant
import Compiler.Proofs.IRGeneration.NativeSourceDynamicMappedEndpoint

namespace Compiler.Proofs.IRGeneration.NativeSourcePreparedSecondGeometry
open EvmYul NativeSourceDynamicSourceReturn NativeSourceDynamicLoopInduction

abbrev advanced (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (tail : Stack UInt256) := advance (count cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail) (registers cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail)

theorem source_value (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (tail : Stack UInt256) (bounded : x9.toNat + 32 < 2 ^ 256) :
    (advanced cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail).x7.toNat = (advanced cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail).x9.toNat + 32 := by
  exact NativeSourceDynamicMappedEndpoint.source_value (count cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail) (registers cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail)
    (NativeSourceDynamicSourceReturn.source_value cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail bounded)

theorem ordered (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (tail : Stack UInt256)
    (countBound : (count cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail) < 2 ^ 64)
    (bounded : x9.toNat + 352 + 128 * (count cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail) < 2 ^ 64) :
    (advanced cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail).x9.toNat + 32 ≤ (advanced cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail).x11.toNat := by
  apply NativeSourceDynamicMappedEndpoint.ordered (count cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail) (registers cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail)
  · have remaining := NativeSourceDynamicSourceInvariant.remaining cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail
    change (registers cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail).x0.toNat + (count cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail) < 2 ^ 256
    have zero : (registers cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail).x0.toNat = 0 := by rfl
    omega
  · exact NativeSourceDynamicSourceInvariant.endpoint_bound cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail bounded
  · exact NativeSourceDynamicSourceReturn.initial_order cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail (by omega)

theorem endpoint_inside (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 489)
    (platform : 64 ≤ System.Platform.numBits) (countBound : (count cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail) < 2 ^ 64)
    (bounded : x9.toNat + 352 + 128 * (count cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail) < 2 ^ 64) :
    (advanced cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail).x11.toNat ≤ (result cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail).memory.size := by
  have values := NativeSourceDynamicLoopGeometry.advance_values (count cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail) (registers cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail)
    (by have zero : (registers cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail).x0.toNat = 0 := by rfl
        rw [zero]
        omega)
    (NativeSourceDynamicSourceInvariant.endpoint_bound cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail bounded)
  rw [values.2]
  exact NativeSourceDynamicSourceInvariant.endpoint_inside cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail code pc platform countBound bounded

end Compiler.Proofs.IRGeneration.NativeSourcePreparedSecondGeometry

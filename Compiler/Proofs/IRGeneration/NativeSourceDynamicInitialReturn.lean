import Compiler.Proofs.IRGeneration.NativeSourceDynamicInitialInvariant
import Compiler.Proofs.IRGeneration.NativeSourceDynamicLoopReturn

namespace Compiler.Proofs.IRGeneration.NativeSourceDynamicInitialReturn
open EvmYul EVM.Proof NativeSourcePreludeDecoded NativeSourceDynamicLoopInduction
open NativeSourceDynamicInitialInvariant

variable (cost : Nat) (pre : EVM.State)
  (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (tail : Stack UInt256)

abbrev count := (pre.toMachineState.lookupMemory x9).toNat
abbrev initial := ready cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail
abbrev regs := registers pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15
abbrev returned := NativeSourceDynamicLoopReturn.returned (count pre x9) cost
  (regs pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15)
  (initial cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail) (x14 :: x15 :: tail)

theorem execute (fuel : Nat)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 535)
    (stack : pre.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: tail)
    (platform : 64 ≤ System.Platform.numBits) (target : x0 = x7 + UInt256.ofNat 320)
    (countBound : count pre x9 < 2 ^ 64)
    (endpoint : x7.toNat + 352 + 128 * count pre x9 < 2 ^ 64) :
    run fuel cost (13 + (62 * count pre x9 + 17)) pre =
      .ok (returned cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail) := by
  have bounded : x7.toNat + 352 < 2 ^ 64 := by omega
  have finish := NativeSourceFieldGeometry.offset_toNat x7 352 (by decide) (by omega)
  have inv := initial_invariant cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail code pc platform bounded target
  apply NativeSourceSizedPacking.compose fuel cost 13 (62 * count pre x9 + 17) pre _ _
  · exact NativeSourceDynamicInitialInvariant.execute fuel cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail code pc stack
  · apply NativeSourceDynamicLoopReturn.execute _ fuel cost _ _ _ platform inv countBound
    · change (UInt256.ofNat 0).toNat + count pre x9 = count pre x9
      have zero : (UInt256.ofNat 0).toNat = 0 := by decide
      rw [zero, Nat.zero_add]
    · change (x7 + UInt256.ofNat 352).toNat + 128 * count pre x9 < 2 ^ 64
      rw [finish]
      exact endpoint

end Compiler.Proofs.IRGeneration.NativeSourceDynamicInitialReturn

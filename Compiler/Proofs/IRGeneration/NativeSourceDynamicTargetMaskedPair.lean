import Compiler.Proofs.IRGeneration.NativeSourceDynamicTargetMaskedSecond

namespace Compiler.Proofs.IRGeneration.NativeSourceDynamicTargetMaskedPair
open EvmYul EVM.Proof NativeSourcePreludeDecoded

abbrev first (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (tail : Stack UInt256) := NativeSourceDynamicTargetMaskedFirst.s6 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail
abbrev result (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (tail : Stack UInt256) := NativeSourceDynamicTargetMaskedSecond.s6 cost (first cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail) x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail

theorem first_pc (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (tail : Stack UInt256) (pc : pre.pc = UInt256.ofNat 511) :
    (first cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail).pc = UInt256.ofNat 518 := by
  change ((((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 2) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
  rw [pc]; decide

theorem execute (fuel : Nat) (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 511)
    (stack : pre.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: tail) :
    run fuel cost 12 pre = .ok (result cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail) := by
  exact NativeSourceSizedPacking.compose fuel cost 6 6 pre _ _
    (NativeSourceDynamicTargetMaskedFirst.execute fuel cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail code pc stack)
    (NativeSourceDynamicTargetMaskedSecond.execute fuel cost (first cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail) x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail code (first_pc cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail pc) (by rfl))

theorem memory (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (tail : Stack UInt256) :
    (result cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail).memory =
      ((first cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail).toMachineState.mstore (x11 + UInt256.ofNat 128)
        (((first cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail).toMachineState.lookupMemory x2).land x3)).memory := by
  exact NativeSourceDynamicTargetMaskedSecond.memory cost (first cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail) x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail

theorem target_register (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (tail : Stack UInt256) : (result cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail).stack[9]? = some x13 := by
  exact NativeSourceDynamicTargetMaskedSecond.target_register cost (first cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail) x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail

end Compiler.Proofs.IRGeneration.NativeSourceDynamicTargetMaskedPair

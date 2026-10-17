import Compiler.Proofs.IRGeneration.NativeSourceDynamicTargetSuffix

namespace Compiler.Proofs.IRGeneration.NativeSourceDynamicTargetTransport
open EvmYul EVM.Proof NativeSourcePreludeDecoded

abbrev targeted (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (tail : Stack UInt256) := NativeSourceDynamicTarget.s4 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail
abbrev field (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (tail : Stack UInt256) := NativeSourceDynamicTargetField.s5 cost (targeted cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail) x13 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 (x11 + UInt256.ofNat 320) tail
abbrev paired (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (tail : Stack UInt256) := NativeSourceDynamicTargetMaskedPair.result cost (field cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 (x11 + UInt256.ofNat 320) tail
abbrev result (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (tail : Stack UInt256) := NativeSourceDynamicTargetSuffix.s7 cost (paired cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail) x4 x5 x6 x7 x8 x9 x10 x11 x12 (x11 + UInt256.ofNat 320) tail

theorem target_pc (cost : Nat) (pre : EVM.State) (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 : UInt256) (tail : Stack UInt256) (pc : pre.pc = UInt256.ofNat 499) :
    (NativeSourceDynamicTarget.s4 cost pre a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 tail).pc = UInt256.ofNat 505 := by
  change ((((pre.pc + UInt256.ofNat 3) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
  rw [pc]; decide

theorem target_code (cost : Nat) (pre : EVM.State) (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 : UInt256) (tail : Stack UInt256) : (NativeSourceDynamicTarget.s4 cost pre a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 tail).executionEnv.code = pre.executionEnv.code := by
  rfl

theorem field_pc (cost : Nat) (pre : EVM.State) (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 : UInt256) (tail : Stack UInt256) (pc : pre.pc = UInt256.ofNat 505) :
    (NativeSourceDynamicTargetField.s5 cost pre a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 tail).pc = UInt256.ofNat 511 := by
  change (((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 2) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
  rw [pc]; decide

theorem field_code (cost : Nat) (pre : EVM.State) (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 : UInt256) (tail : Stack UInt256) : (NativeSourceDynamicTargetField.s5 cost pre a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 tail).executionEnv.code = pre.executionEnv.code := by
  rfl

theorem pair_pc (cost : Nat) (pre : EVM.State) (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 : UInt256) (tail : Stack UInt256) (pc : pre.pc = UInt256.ofNat 511) :
    (NativeSourceDynamicTargetMaskedPair.result cost pre a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 tail).pc = UInt256.ofNat 525 := by
  change ((((((((((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 2) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 2) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
  rw [pc]; decide

theorem pair_code (cost : Nat) (pre : EVM.State) (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 : UInt256) (tail : Stack UInt256) : (NativeSourceDynamicTargetMaskedPair.result cost pre a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 tail).executionEnv.code = pre.executionEnv.code := by
  rfl

theorem suffix_pc (cost : Nat) (pre : EVM.State) (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : UInt256) (tail : Stack UInt256) (pc : pre.pc = UInt256.ofNat 525) :
    (NativeSourceDynamicTargetSuffix.s7 cost pre a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 tail).pc = UInt256.ofNat 535 := by
  change (((((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 3) + UInt256.ofNat 2) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
  rw [pc]; decide

theorem suffix_code (cost : Nat) (pre : EVM.State) (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : UInt256) (tail : Stack UInt256) : (NativeSourceDynamicTargetSuffix.s7 cost pre a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 tail).executionEnv.code = pre.executionEnv.code := by
  rfl

theorem execute_field (fuel : Nat) (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 499)
    (stack : pre.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: tail) : run fuel cost 9 pre = .ok (field cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail) := by
  exact NativeSourceSizedPacking.compose fuel cost 4 5 pre _ _
    (NativeSourceDynamicTarget.execute fuel cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail code pc stack)
    (NativeSourceDynamicTargetField.execute fuel cost (targeted cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail) x13 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 (x11 + UInt256.ofNat 320) tail
      ((target_code cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail).trans code) (target_pc cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail pc) (by rfl))

theorem execute_pair (fuel : Nat) (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 499)
    (stack : pre.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: tail) : run fuel cost 21 pre = .ok (paired cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail) := by
  have code1 := (target_code cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail).trans code
  have pc1 := target_pc cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail pc
  exact NativeSourceSizedPacking.compose fuel cost 9 12 pre _ _
    (execute_field fuel cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail code pc stack)
    (NativeSourceDynamicTargetMaskedPair.execute fuel cost (field cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 (x11 + UInt256.ofNat 320) tail
      ((field_code cost (targeted cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail) x13 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 (x11 + UInt256.ofNat 320) tail).trans code1)
      (field_pc cost (targeted cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail) x13 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 (x11 + UInt256.ofNat 320) tail pc1) (by rfl))

theorem execute (fuel : Nat) (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 499)
    (stack : pre.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: tail) : run fuel cost 28 pre = .ok (result cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail) := by
  have code1 := (target_code cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail).trans code
  have pc1 := target_pc cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail pc
  have code2 := (field_code cost (targeted cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail) x13 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 (x11 + UInt256.ofNat 320) tail).trans code1
  have pc2 := field_pc cost (targeted cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail) x13 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 (x11 + UInt256.ofNat 320) tail pc1
  exact NativeSourceSizedPacking.compose fuel cost 21 7 pre _ _
    (execute_pair fuel cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail code pc stack)
    (NativeSourceDynamicTargetSuffix.execute fuel cost (paired cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail) x4 x5 x6 x7 x8 x9 x10 x11 x12 (x11 + UInt256.ofNat 320) tail
      ((pair_code cost (field cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 (x11 + UInt256.ofNat 320) tail).trans code2)
      (pair_pc cost (field cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 (x11 + UInt256.ofNat 320) tail pc2) (by rfl))

theorem target_relation (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (tail : Stack UInt256) :
    (result cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail).stack[0]? = ((result cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 tail).stack[7]?).map (fun base => base + UInt256.ofNat 320) := by
  rfl

end Compiler.Proofs.IRGeneration.NativeSourceDynamicTargetTransport

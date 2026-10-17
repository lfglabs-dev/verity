import Compiler.Proofs.IRGeneration.NativeSourceDynamicTargetTransport

namespace Compiler.Proofs.IRGeneration.NativeSourceDynamicTransportReturn
open EvmYul EVM.Proof NativeSourcePreludeDecoded

abbrev entry (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (tail : Stack UInt256) := NativeSourceDynamicTargetTransport.result cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 (x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: tail)
abbrev lastLoad (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (tail : Stack UInt256) := (NativeSourceDynamicTargetTransport.paired cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 (x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: tail)).toMachineState.lookupMemory x4
abbrev result (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (tail : Stack UInt256) := NativeSourceDynamicInitialReturn.returned cost (entry cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail) (x11 + UInt256.ofNat 320) x5 x6 x7 x8 x9 x10 x11 x12 (lastLoad cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail) x14 x15 x16 x17 x18 x19 tail

theorem entry_pc (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (tail : Stack UInt256) (pc : pre.pc = UInt256.ofNat 499) : (entry cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail).pc = UInt256.ofNat 535 := by
  have pc1 := NativeSourceDynamicTargetTransport.target_pc cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 (x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: tail) pc
  have pc2 := NativeSourceDynamicTargetTransport.field_pc cost (NativeSourceDynamicTargetTransport.targeted cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 (x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: tail)) x13 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 (x11 + UInt256.ofNat 320) (x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: tail) pc1
  have pc3 := NativeSourceDynamicTargetTransport.pair_pc cost (NativeSourceDynamicTargetTransport.field cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 (x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: tail)) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 (x11 + UInt256.ofNat 320) (x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: tail) pc2
  exact NativeSourceDynamicTargetTransport.suffix_pc cost (NativeSourceDynamicTargetTransport.paired cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 (x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: tail)) x4 x5 x6 x7 x8 x9 x10 x11 x12 (x11 + UInt256.ofNat 320) (x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: tail) pc3

theorem entry_code (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (tail : Stack UInt256) : (entry cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail).executionEnv.code = pre.executionEnv.code := by
  rfl

theorem entry_stack (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (tail : Stack UInt256) :
    (entry cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail).stack = (x11 + UInt256.ofNat 320) :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: lastLoad cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: tail := by
  exact NativeSourceDynamicTargetSuffix.output_stack cost (NativeSourceDynamicTargetTransport.paired cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 (x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: tail)) x4 x5 x6 x7 x8 x9 x10 x11 x12 (x11 + UInt256.ofNat 320) (x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: tail)

theorem execute (fuel : Nat) (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 499)
    (stack : pre.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: tail)
    (platform : 64 ≤ System.Platform.numBits)
    (countBound : NativeSourceDynamicInitialReturn.count (entry cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail) (lastLoad cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail) < 2 ^ 64)
    (endpoint : x11.toNat + 352 + 128 * NativeSourceDynamicInitialReturn.count (entry cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail) (lastLoad cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail) < 2 ^ 64) :
    run fuel cost (28 + (13 + (62 * NativeSourceDynamicInitialReturn.count (entry cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail) (lastLoad cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail) + 17))) pre = .ok (result cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail) := by
  exact NativeSourceSizedPacking.compose fuel cost 28 _ pre _ _
    (NativeSourceDynamicTargetTransport.execute fuel cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 (x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: tail) code pc stack)
    (NativeSourceDynamicInitialReturn.execute cost (entry cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail) (x11 + UInt256.ofNat 320) x5 x6 x7 x8 x9 x10 x11 x12 (lastLoad cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail) x14 x15 x16 x17 x18 x19 tail fuel
      ((entry_code cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail).trans code) (entry_pc cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail pc) (entry_stack cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 tail) platform rfl countBound endpoint)

end Compiler.Proofs.IRGeneration.NativeSourceDynamicTransportReturn

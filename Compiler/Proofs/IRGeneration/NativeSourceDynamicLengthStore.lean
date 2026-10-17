import Compiler.Proofs.IRGeneration.NativeSourceLoopFirstPayload

namespace Compiler.Proofs.IRGeneration.NativeSourceDynamicLengthStore
open EvmYul EVM.Proof NativeSourcePreludeDecoded

theorem decode535 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 535) = some (.DUP10, none) := by
  have byte : NativeSourceAbiWrite.code.get? 535 = some 137 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 535).toNat = 535 by decide, byte]
  decide

theorem decode536 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 536) = some (.MLOAD, none) := by
  have byte : NativeSourceAbiWrite.code.get? 536 = some 81 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 536).toNat = 536 by decide, byte]
  decide

theorem decode537 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 537) = some (.DUP1, none) := by
  have byte : NativeSourceAbiWrite.code.get? 537 = some 128 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 537).toNat = 537 by decide, byte]
  decide

theorem decode538 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 538) = some (.SWAP2, none) := by
  have byte : NativeSourceAbiWrite.code.get? 538 = some 145 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 538).toNat = 538 by decide, byte]
  decide

theorem decode539 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 539) = some (.MSTORE, none) := by
  have byte : NativeSourceAbiWrite.code.get? 539 = some 82 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 539).toNat = 539 by decide, byte]
  decide

def s1 (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256) (tail : Stack UInt256) :=
  (stepPre cost pre).replaceStackAndIncrPC (x9 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: tail)
def s2 (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256) (tail : Stack UInt256) :=
  NativeSourceLoadStep.loaded cost (s1 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail) x9 (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: tail)
def s3 (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256) (tail : Stack UInt256) :=
  (stepPre cost (s2 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail)).replaceStackAndIncrPC (((s1 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail).toMachineState.lookupMemory x9) :: ((s1 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail).toMachineState.lookupMemory x9) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: tail)
def s4 (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256) (tail : Stack UInt256) :=
  (stepPre cost (s3 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail)).replaceStackAndIncrPC (x0 :: ((s1 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail).toMachineState.lookupMemory x9) :: ((s1 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail).toMachineState.lookupMemory x9) :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: tail)
def s5 (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256) (tail : Stack UInt256) :=
  let charged := stepPre cost (s4 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail)
  ({ charged with toMachineState := (charged.toMachineState.mstore x0 ((s1 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail).toMachineState.lookupMemory x9)) } : EVM.State).replaceStackAndIncrPC
    (((s1 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail).toMachineState.lookupMemory x9) :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: tail)

theorem transition1 (fuel cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 535)
    (stack : pre.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt pre)) pre = .ok (s1 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail) := by
  have atPC : pre.pc = UInt256.ofNat 535 := by
    exact pc
  have decoded : decodeAt pre = (.DUP10, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code pre.pc).getD _ = _
    rw [code, atPC, decode535]; rfl
  rw [decoded]
  change EvmYul.dup 10 (stepPre cost pre) = _
  unfold EvmYul.dup
  simp only [stepPre, stack]
  rfl

theorem transition2 (fuel cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 535)
    (stack : pre.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s1 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail))) (s1 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail) = .ok (s2 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail) := by
  have atPC : (s1 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail).pc = UInt256.ofNat 536 := by
    change (pre.pc + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s1 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail) = (.MLOAD, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s1 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail).pc).getD _ = _
    rw [code, atPC, decode536]; rfl
  rw [decoded]
  exact NativeSourceLoadStep.step fuel cost (s1 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail) x9 _ (by rfl)

theorem transition3 (fuel cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 535)
    (stack : pre.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s2 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail))) (s2 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail) = .ok (s3 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail) := by
  have atPC : (s2 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail).pc = UInt256.ofNat 537 := by
    change ((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s2 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail) = (.DUP1, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s2 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail).pc).getD _ = _
    rw [code, atPC, decode537]; rfl
  rw [decoded]
  change EvmYul.dup 1 (stepPre cost (s2 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail)) = _
  unfold EvmYul.dup
  rfl

theorem transition4 (fuel cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 535)
    (stack : pre.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s3 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail))) (s3 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail) = .ok (s4 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail) := by
  have atPC : (s3 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail).pc = UInt256.ofNat 538 := by
    change (((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s3 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail) = (.SWAP2, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s3 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail).pc).getD _ = _
    rw [code, atPC, decode538]; rfl
  rw [decoded]
  change EvmYul.swap 2 (stepPre cost (s3 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail)) = _
  unfold EvmYul.swap
  rfl

theorem transition5 (fuel cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 535)
    (stack : pre.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s4 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail))) (s4 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail) = .ok (s5 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail) := by
  have atPC : (s4 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail).pc = UInt256.ofNat 539 := by
    change ((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s4 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail) = (.MSTORE, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s4 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail).pc).getD _ = _
    rw [code, atPC, decode539]; rfl
  rw [decoded]
  exact step_MSTORE fuel cost (s4 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail) (((s1 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail).toMachineState.lookupMemory x9) :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: tail) x0 ((s1 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail).toMachineState.lookupMemory x9) (by rfl)

theorem execute (fuel cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 535)
    (stack : pre.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: tail) : run fuel cost 5 pre = .ok (s5 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail) := by
  rw [run, transition1 fuel cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition2 fuel cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition3 fuel cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition4 fuel cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition5 fuel cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rfl

theorem memory (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256) (tail : Stack UInt256) :
    (s5 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail).memory = (pre.toMachineState.mstore x0 (pre.toMachineState.lookupMemory x9)).memory := by
  rfl

theorem extent (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256) (tail : Stack UInt256)
    (platform : 64 ≤ System.Platform.numBits) (bounded : x0.toNat < 2 ^ 64) :
    x0.toNat + 32 ≤ (s5 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 tail).memory.size := by
  rw [memory, NativeSourceDynamicElementCarrier.store_extent _ _ _ platform bounded]
  exact Nat.le_max_right _ _

end Compiler.Proofs.IRGeneration.NativeSourceDynamicLengthStore

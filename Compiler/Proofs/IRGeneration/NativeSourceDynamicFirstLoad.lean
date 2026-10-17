import Compiler.Proofs.IRGeneration.NativeSourceDynamicFirstStore

namespace Compiler.Proofs.IRGeneration.NativeSourceDynamicFirstLoad
open EvmYul EVM.Proof NativeSourcePreludeDecoded

theorem decode742 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 742) = some (.DUP3, none) := by
  have byte : NativeSourceAbiWrite.code.get? 742 = some 130 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 742).toNat = 742 by decide, byte]
  decide

theorem decode743 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 743) = some (.DUP2, none) := by
  have byte : NativeSourceAbiWrite.code.get? 743 = some 129 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 743).toNat = 743 by decide, byte]
  decide

def loaded (cost : Nat) (pre : EVM.State) (source x mask dest spare : UInt256) (tail : Stack UInt256) :=
  NativeSourceLoadStep.loaded cost pre source (x :: mask :: dest :: spare :: tail)

def firstDup (cost : Nat) (pre : EVM.State) (source x mask dest spare : UInt256) (tail : Stack UInt256) :=
  (stepPre cost (loaded cost pre source x mask dest spare tail)).replaceStackAndIncrPC
    (mask :: pre.toMachineState.lookupMemory source :: x :: mask :: dest :: spare :: tail)

def ready (cost : Nat) (pre : EVM.State) (source x mask dest spare : UInt256) (tail : Stack UInt256) :=
  (stepPre cost (firstDup cost pre source x mask dest spare tail)).replaceStackAndIncrPC
    (pre.toMachineState.lookupMemory source :: mask :: pre.toMachineState.lookupMemory source :: x :: mask :: dest :: spare :: tail)

theorem load_step (fuel cost : Nat) (pre : EVM.State) (source x mask dest spare : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 741)
    (stack : pre.stack = source :: x :: mask :: dest :: spare :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt pre)) pre = .ok (loaded cost pre source x mask dest spare tail) := by
  have decoded : decodeAt pre = (.MLOAD, none) := by
    unfold decodeAt
    rw [code, pc, NativeSourceDynamicLoopDecode.decode741]
    rfl
  rw [decoded]
  exact NativeSourceLoadStep.step fuel cost pre source _ stack

theorem dup3_step (fuel cost : Nat) (pre : EVM.State) (source x mask dest spare : UInt256) (tail : Stack UInt256) :
    EVM.step (fuel + 1) cost (some (.DUP3, none)) (loaded cost pre source x mask dest spare tail) =
      .ok (firstDup cost pre source x mask dest spare tail) := by
  change EvmYul.dup 3 (stepPre cost (loaded cost pre source x mask dest spare tail)) = _
  unfold EvmYul.dup
  rfl

theorem dup2_step (fuel cost : Nat) (pre : EVM.State) (source x mask dest spare : UInt256) (tail : Stack UInt256) :
    EVM.step (fuel + 1) cost (some (.DUP2, none)) (firstDup cost pre source x mask dest spare tail) =
      .ok (ready cost pre source x mask dest spare tail) := by
  change EvmYul.dup 2 (stepPre cost (firstDup cost pre source x mask dest spare tail)) = _
  unfold EvmYul.dup
  rfl

theorem execute (fuel cost : Nat) (pre : EVM.State) (source x mask dest spare : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 741)
    (stack : pre.stack = source :: x :: mask :: dest :: spare :: tail) :
    run fuel cost 3 pre = .ok (ready cost pre source x mask dest spare tail) := by
  have pc1 : (loaded cost pre source x mask dest spare tail).pc = UInt256.ofNat 742 := by
    change pre.pc + UInt256.ofNat 1 = _
    rw [pc]; decide
  have pc2 : (firstDup cost pre source x mask dest spare tail).pc = UInt256.ofNat 743 := by
    change (loaded cost pre source x mask dest spare tail).pc + UInt256.ofNat 1 = _
    rw [pc1]; decide
  have d1 : decodeAt (loaded cost pre source x mask dest spare tail) = (.DUP3, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (loaded cost pre source x mask dest spare tail).pc).getD _ = _
    rw [code, pc1, decode742]; rfl
  have d2 : decodeAt (firstDup cost pre source x mask dest spare tail) = (.DUP2, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (firstDup cost pre source x mask dest spare tail).pc).getD _ = _
    rw [code, pc2, decode743]; rfl
  rw [run, load_step fuel cost pre source x mask dest spare tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, d1, dup3_step]
  simp only [Bind.bind, Except.bind]
  rw [run, d2, dup2_step]
  rfl

theorem ready_stack (cost : Nat) (pre : EVM.State) (source x mask dest spare : UInt256) (tail : Stack UInt256) :
    (ready cost pre source x mask dest spare tail).stack =
      pre.toMachineState.lookupMemory source :: mask :: pre.toMachineState.lookupMemory source :: x :: mask :: dest :: spare :: tail := by
  rfl

theorem ready_pc (cost : Nat) (pre : EVM.State) (source x mask dest spare : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 741) :
    (ready cost pre source x mask dest spare tail).pc = UInt256.ofNat 744 := by
  change ((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1 = _
  rw [pc]; decide

theorem execute_store (fuel cost : Nat) (pre : EVM.State) (source x mask dest spare : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 741)
    (stack : pre.stack = source :: x :: mask :: dest :: spare :: tail) :
    run fuel cost 7 pre = .ok (NativeSourceDynamicFirstStore.stored cost
      (ready cost pre source x mask dest spare tail) (pre.toMachineState.lookupMemory source)
      mask (pre.toMachineState.lookupMemory source) x mask dest (spare :: tail)) := by
  exact NativeSourceSizedPacking.compose fuel cost 3 4 pre _ _
    (execute fuel cost pre source x mask dest spare tail code pc stack)
    (NativeSourceDynamicFirstStore.execute fuel cost _ _ mask _ x mask dest (spare :: tail)
      code (ready_pc cost pre source x mask dest spare tail pc) (by rfl))

end Compiler.Proofs.IRGeneration.NativeSourceDynamicFirstLoad

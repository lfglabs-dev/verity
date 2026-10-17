import Compiler.Proofs.IRGeneration.NativeSourceDynamicLoopDecode

namespace Compiler.Proofs.IRGeneration.NativeSourceDynamicFirstStore
open EvmYul EVM.Proof NativeSourcePreludeDecoded

theorem decode745 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 745) = some (.AND, none) := by
  have byte : NativeSourceAbiWrite.code.get? 745 = some 22 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 745).toNat = 745 by decide, byte]
  decide

theorem decode746 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 746) = some (.DUP5, none) := by
  have byte : NativeSourceAbiWrite.code.get? 746 = some 132 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 746).toNat = 746 by decide, byte]
  decide

def loaded (cost : Nat) (pre : EVM.State) (address mask x y z pos : UInt256) (tail : Stack UInt256) :=
  NativeSourceLoadStep.loaded cost pre address (mask :: x :: y :: z :: pos :: tail)

def masked (cost : Nat) (pre : EVM.State) (address mask x y z pos : UInt256) (tail : Stack UInt256) :=
  (stepPre cost (loaded cost pre address mask x y z pos tail)).replaceStackAndIncrPC
    ((pre.toMachineState.lookupMemory address).land mask :: x :: y :: z :: pos :: tail)

def duplicated (cost : Nat) (pre : EVM.State) (address mask x y z pos : UInt256) (tail : Stack UInt256) :=
  (stepPre cost (masked cost pre address mask x y z pos tail)).replaceStackAndIncrPC
    (pos :: (pre.toMachineState.lookupMemory address).land mask :: x :: y :: z :: pos :: tail)

def stored (cost : Nat) (pre : EVM.State) (address mask x y z pos : UInt256) (tail : Stack UInt256) :=
  let charged := stepPre cost (duplicated cost pre address mask x y z pos tail)
  ({ charged with toMachineState := (charged.toMachineState.mstore pos
    ((pre.toMachineState.lookupMemory address).land mask)) } : EVM.State).replaceStackAndIncrPC
      (x :: y :: z :: pos :: tail)

theorem load_step (fuel cost : Nat) (pre : EVM.State) (address mask x y z pos : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 744)
    (stack : pre.stack = address :: mask :: x :: y :: z :: pos :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt pre)) pre = .ok (loaded cost pre address mask x y z pos tail) := by
  have decoded : decodeAt pre = (.MLOAD, none) := by
    unfold decodeAt
    rw [code, pc, NativeSourceDynamicLoopDecode.decode744]
    rfl
  rw [decoded]
  exact NativeSourceLoadStep.step fuel cost pre address _ stack

theorem mask_step (fuel cost : Nat) (pre : EVM.State) (address mask x y z pos : UInt256) (tail : Stack UInt256) :
    EVM.step (fuel + 1) cost (some (.AND, none)) (loaded cost pre address mask x y z pos tail) =
      .ok (masked cost pre address mask x y z pos tail) := by
  change EVM.execBinOp UInt256.land (stepPre cost (loaded cost pre address mask x y z pos tail)) = _
  unfold EVM.execBinOp
  rfl

theorem dup_step (fuel cost : Nat) (pre : EVM.State) (address mask x y z pos : UInt256) (tail : Stack UInt256) :
    EVM.step (fuel + 1) cost (some (.DUP5, none)) (masked cost pre address mask x y z pos tail) =
      .ok (duplicated cost pre address mask x y z pos tail) := by
  change EvmYul.dup 5 (stepPre cost (masked cost pre address mask x y z pos tail)) = _
  unfold EvmYul.dup
  rfl

theorem store_step (fuel cost : Nat) (pre : EVM.State) (address mask x y z pos : UInt256) (tail : Stack UInt256) :
    EVM.step (fuel + 1) cost (some (.MSTORE, none)) (duplicated cost pre address mask x y z pos tail) =
      .ok (stored cost pre address mask x y z pos tail) := by
  exact step_MSTORE fuel cost (duplicated cost pre address mask x y z pos tail)
    (x :: y :: z :: pos :: tail) pos ((pre.toMachineState.lookupMemory address).land mask) (by rfl)

theorem memory (cost : Nat) (pre : EVM.State) (address mask x y z pos : UInt256) (tail : Stack UInt256) :
    (stored cost pre address mask x y z pos tail).memory =
      (pre.toMachineState.mstore pos ((pre.toMachineState.lookupMemory address).land mask)).memory := by
  rfl

theorem execute (fuel cost : Nat) (pre : EVM.State) (address mask x y z pos : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 744)
    (stack : pre.stack = address :: mask :: x :: y :: z :: pos :: tail) :
    run fuel cost 4 pre = .ok (stored cost pre address mask x y z pos tail) := by
  have pc1 : (loaded cost pre address mask x y z pos tail).pc = UInt256.ofNat 745 := by
    change pre.pc + UInt256.ofNat 1 = _
    rw [pc]; decide
  have pc2 : (masked cost pre address mask x y z pos tail).pc = UInt256.ofNat 746 := by
    change (loaded cost pre address mask x y z pos tail).pc + UInt256.ofNat 1 = _
    rw [pc1]; decide
  have pc3 : (duplicated cost pre address mask x y z pos tail).pc = UInt256.ofNat 747 := by
    change (masked cost pre address mask x y z pos tail).pc + UInt256.ofNat 1 = _
    rw [pc2]; decide
  have d1 : decodeAt (loaded cost pre address mask x y z pos tail) = (.AND, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (loaded cost pre address mask x y z pos tail).pc).getD _ = _
    rw [code, pc1, decode745]; rfl
  have d2 : decodeAt (masked cost pre address mask x y z pos tail) = (.DUP5, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (masked cost pre address mask x y z pos tail).pc).getD _ = _
    rw [code, pc2, decode746]; rfl
  have d3 : decodeAt (duplicated cost pre address mask x y z pos tail) = (.MSTORE, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (duplicated cost pre address mask x y z pos tail).pc).getD _ = _
    rw [code, pc3, NativeSourceDynamicLoopDecode.decode747]; rfl
  rw [run, load_step fuel cost pre address mask x y z pos tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, d1, mask_step]
  simp only [Bind.bind, Except.bind]
  rw [run, d2, dup_step]
  simp only [Bind.bind, Except.bind]
  rw [run, d3, store_step]
  rfl

end Compiler.Proofs.IRGeneration.NativeSourceDynamicFirstStore

import Compiler.Proofs.IRGeneration.NativeSourceDynamicFirstLoad

namespace Compiler.Proofs.IRGeneration.NativeSourceDynamicSecondStore
open EvmYul EVM.Proof NativeSourcePreludeDecoded

theorem decode748 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 748) = some (.DUP6, none) := by
  have byte : NativeSourceAbiWrite.code.get? 748 = some 133 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 748).toNat = 748 by decide, byte]
  decide

theorem decode749 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 749) = some (.DUP2, none) := by
  have byte : NativeSourceAbiWrite.code.get? 749 = some 129 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 749).toNat = 749 by decide, byte]
  decide

theorem decode750 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 750) = some (.ADD, none) := by
  have byte : NativeSourceAbiWrite.code.get? 750 = some 1 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 750).toNat = 750 by decide, byte]
  decide

theorem decode751 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 751) = some (.MLOAD, none) := by
  have byte : NativeSourceAbiWrite.code.get? 751 = some 81 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 751).toNat = 751 by decide, byte]
  decide

theorem decode752 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 752) = some (.DUP7, none) := by
  have byte : NativeSourceAbiWrite.code.get? 752 = some 134 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 752).toNat = 752 by decide, byte]
  decide

theorem decode753 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 753) = some (.DUP6, none) := by
  have byte : NativeSourceAbiWrite.code.get? 753 = some 133 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 753).toNat = 753 by decide, byte]
  decide

theorem decode754 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 754) = some (.ADD, none) := by
  have byte : NativeSourceAbiWrite.code.get? 754 = some 1 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 754).toNat = 754 by decide, byte]
  decide

theorem decode755 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 755) = some (.MSTORE, none) := by
  have byte : NativeSourceAbiWrite.code.get? 755 = some 82 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 755).toNat = 755 by decide, byte]
  decide

def s1 (cost : Nat) (pre : EVM.State) (a b c d e f : UInt256) (tail : Stack UInt256) :=
  (stepPre cost pre).replaceStackAndIncrPC
    (f :: a :: b :: c :: d :: e :: f :: tail)

def s2 (cost : Nat) (pre : EVM.State) (a b c d e f : UInt256) (tail : Stack UInt256) :=
  (stepPre cost (s1 cost pre a b c d e f tail)).replaceStackAndIncrPC
    (a :: f :: a :: b :: c :: d :: e :: f :: tail)

def s3 (cost : Nat) (pre : EVM.State) (a b c d e f : UInt256) (tail : Stack UInt256) :=
  (stepPre cost (s2 cost pre a b c d e f tail)).replaceStackAndIncrPC
    ((a + f) :: a :: b :: c :: d :: e :: f :: tail)

def s4 (cost : Nat) (pre : EVM.State) (a b c d e f : UInt256) (tail : Stack UInt256) :=
  NativeSourceLoadStep.loaded cost (s3 cost pre a b c d e f tail) (a + f) (a :: b :: c :: d :: e :: f :: tail)

def s5 (cost : Nat) (pre : EVM.State) (a b c d e f : UInt256) (tail : Stack UInt256) :=
  (stepPre cost (s4 cost pre a b c d e f tail)).replaceStackAndIncrPC
    (f :: ((s3 cost pre a b c d e f tail).toMachineState.lookupMemory (a + f)) :: a :: b :: c :: d :: e :: f :: tail)

def s6 (cost : Nat) (pre : EVM.State) (a b c d e f : UInt256) (tail : Stack UInt256) :=
  (stepPre cost (s5 cost pre a b c d e f tail)).replaceStackAndIncrPC
    (d :: f :: ((s3 cost pre a b c d e f tail).toMachineState.lookupMemory (a + f)) :: a :: b :: c :: d :: e :: f :: tail)

def s7 (cost : Nat) (pre : EVM.State) (a b c d e f : UInt256) (tail : Stack UInt256) :=
  (stepPre cost (s6 cost pre a b c d e f tail)).replaceStackAndIncrPC
    ((d + f) :: ((s3 cost pre a b c d e f tail).toMachineState.lookupMemory (a + f)) :: a :: b :: c :: d :: e :: f :: tail)

def s8 (cost : Nat) (pre : EVM.State) (a b c d e f : UInt256) (tail : Stack UInt256) :=
  let charged := stepPre cost (s7 cost pre a b c d e f tail)
  ({ charged with toMachineState := (charged.toMachineState.mstore (d + f) ((s3 cost pre a b c d e f tail).toMachineState.lookupMemory (a + f))) } : EVM.State).replaceStackAndIncrPC
    (a :: b :: c :: d :: e :: f :: tail)

theorem transition1 (fuel cost : Nat) (pre : EVM.State) (a b c d e f : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 748)
    (stack : pre.stack = a :: b :: c :: d :: e :: f :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt pre)) pre = .ok (s1 cost pre a b c d e f tail) := by
  have atPC : pre.pc = UInt256.ofNat 748 := by
    exact pc
  have decoded : decodeAt pre = (.DUP6, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code pre.pc).getD _ = _
    rw [code, atPC, decode748]; rfl
  rw [decoded]
  change EvmYul.dup 6 (stepPre cost pre) = _
  unfold EvmYul.dup
  simp only [stepPre, stack]
  rfl

theorem transition2 (fuel cost : Nat) (pre : EVM.State) (a b c d e f : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 748)
    (stack : pre.stack = a :: b :: c :: d :: e :: f :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s1 cost pre a b c d e f tail))) (s1 cost pre a b c d e f tail) = .ok (s2 cost pre a b c d e f tail) := by
  have atPC : (s1 cost pre a b c d e f tail).pc = UInt256.ofNat 749 := by
    change (pre.pc + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s1 cost pre a b c d e f tail) = (.DUP2, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s1 cost pre a b c d e f tail).pc).getD _ = _
    rw [code, atPC, decode749]; rfl
  rw [decoded]
  change EvmYul.dup 2 (stepPre cost (s1 cost pre a b c d e f tail)) = _
  unfold EvmYul.dup
  rfl

theorem transition3 (fuel cost : Nat) (pre : EVM.State) (a b c d e f : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 748)
    (stack : pre.stack = a :: b :: c :: d :: e :: f :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s2 cost pre a b c d e f tail))) (s2 cost pre a b c d e f tail) = .ok (s3 cost pre a b c d e f tail) := by
  have atPC : (s2 cost pre a b c d e f tail).pc = UInt256.ofNat 750 := by
    change ((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s2 cost pre a b c d e f tail) = (.ADD, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s2 cost pre a b c d e f tail).pc).getD _ = _
    rw [code, atPC, decode750]; rfl
  rw [decoded]
  change EVM.execBinOp UInt256.add (stepPre cost (s2 cost pre a b c d e f tail)) = _
  unfold EVM.execBinOp
  rfl

theorem transition4 (fuel cost : Nat) (pre : EVM.State) (a b c d e f : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 748)
    (stack : pre.stack = a :: b :: c :: d :: e :: f :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s3 cost pre a b c d e f tail))) (s3 cost pre a b c d e f tail) = .ok (s4 cost pre a b c d e f tail) := by
  have atPC : (s3 cost pre a b c d e f tail).pc = UInt256.ofNat 751 := by
    change (((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s3 cost pre a b c d e f tail) = (.MLOAD, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s3 cost pre a b c d e f tail).pc).getD _ = _
    rw [code, atPC, decode751]; rfl
  rw [decoded]
  exact NativeSourceLoadStep.step fuel cost (s3 cost pre a b c d e f tail) (a + f) _ (by rfl)

theorem transition5 (fuel cost : Nat) (pre : EVM.State) (a b c d e f : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 748)
    (stack : pre.stack = a :: b :: c :: d :: e :: f :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s4 cost pre a b c d e f tail))) (s4 cost pre a b c d e f tail) = .ok (s5 cost pre a b c d e f tail) := by
  have atPC : (s4 cost pre a b c d e f tail).pc = UInt256.ofNat 752 := by
    change ((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s4 cost pre a b c d e f tail) = (.DUP7, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s4 cost pre a b c d e f tail).pc).getD _ = _
    rw [code, atPC, decode752]; rfl
  rw [decoded]
  change EvmYul.dup 7 (stepPre cost (s4 cost pre a b c d e f tail)) = _
  unfold EvmYul.dup
  rfl

theorem transition6 (fuel cost : Nat) (pre : EVM.State) (a b c d e f : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 748)
    (stack : pre.stack = a :: b :: c :: d :: e :: f :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s5 cost pre a b c d e f tail))) (s5 cost pre a b c d e f tail) = .ok (s6 cost pre a b c d e f tail) := by
  have atPC : (s5 cost pre a b c d e f tail).pc = UInt256.ofNat 753 := by
    change (((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s5 cost pre a b c d e f tail) = (.DUP6, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s5 cost pre a b c d e f tail).pc).getD _ = _
    rw [code, atPC, decode753]; rfl
  rw [decoded]
  change EvmYul.dup 6 (stepPre cost (s5 cost pre a b c d e f tail)) = _
  unfold EvmYul.dup
  rfl

theorem transition7 (fuel cost : Nat) (pre : EVM.State) (a b c d e f : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 748)
    (stack : pre.stack = a :: b :: c :: d :: e :: f :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s6 cost pre a b c d e f tail))) (s6 cost pre a b c d e f tail) = .ok (s7 cost pre a b c d e f tail) := by
  have atPC : (s6 cost pre a b c d e f tail).pc = UInt256.ofNat 754 := by
    change ((((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s6 cost pre a b c d e f tail) = (.ADD, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s6 cost pre a b c d e f tail).pc).getD _ = _
    rw [code, atPC, decode754]; rfl
  rw [decoded]
  change EVM.execBinOp UInt256.add (stepPre cost (s6 cost pre a b c d e f tail)) = _
  unfold EVM.execBinOp
  rfl

theorem transition8 (fuel cost : Nat) (pre : EVM.State) (a b c d e f : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 748)
    (stack : pre.stack = a :: b :: c :: d :: e :: f :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s7 cost pre a b c d e f tail))) (s7 cost pre a b c d e f tail) = .ok (s8 cost pre a b c d e f tail) := by
  have atPC : (s7 cost pre a b c d e f tail).pc = UInt256.ofNat 755 := by
    change (((((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s7 cost pre a b c d e f tail) = (.MSTORE, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s7 cost pre a b c d e f tail).pc).getD _ = _
    rw [code, atPC, decode755]; rfl
  rw [decoded]
  exact step_MSTORE fuel cost (s7 cost pre a b c d e f tail) (a :: b :: c :: d :: e :: f :: tail) (d + f) _ (by rfl)

theorem execute (fuel cost : Nat) (pre : EVM.State) (a b c d e f : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 748)
    (stack : pre.stack = a :: b :: c :: d :: e :: f :: tail) :
    run fuel cost 8 pre = .ok (s8 cost pre a b c d e f tail) := by
  rw [run, transition1 fuel cost pre a b c d e f tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition2 fuel cost pre a b c d e f tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition3 fuel cost pre a b c d e f tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition4 fuel cost pre a b c d e f tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition5 fuel cost pre a b c d e f tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition6 fuel cost pre a b c d e f tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition7 fuel cost pre a b c d e f tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition8 fuel cost pre a b c d e f tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rfl

theorem memory (cost : Nat) (pre : EVM.State) (a b c d e f : UInt256) (tail : Stack UInt256) :
    (s8 cost pre a b c d e f tail).memory =
      (pre.toMachineState.mstore (d + f) (pre.toMachineState.lookupMemory (a + f))).memory := by
  rfl

end Compiler.Proofs.IRGeneration.NativeSourceDynamicSecondStore

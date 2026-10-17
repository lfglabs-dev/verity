import Compiler.Proofs.IRGeneration.NativeSourceDynamicElementExecution

namespace Compiler.Proofs.IRGeneration.NativeSourceDynamicIncrements
open EvmYul EVM.Proof NativeSourcePreludeDecoded

theorem decode774 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 774) = some (.ADD, none) := by
  have byte : NativeSourceAbiWrite.code.get? 774 = some 1 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 774).toNat = 774 by decide, byte]
  decide

theorem decode775 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 775) = some (.SWAP13, none) := by
  have byte : NativeSourceAbiWrite.code.get? 775 = some 156 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 775).toNat = 775 by decide, byte]
  decide

theorem decode776 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 776) = some (.ADD, none) := by
  have byte : NativeSourceAbiWrite.code.get? 776 = some 1 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 776).toNat = 776 by decide, byte]
  decide

theorem decode777 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 777) = some (.SWAP2, none) := by
  have byte : NativeSourceAbiWrite.code.get? 777 = some 145 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 777).toNat = 777 by decide, byte]
  decide

theorem decode778 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 778) = some (.ADD, none) := by
  have byte : NativeSourceAbiWrite.code.get? 778 = some 1 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 778).toNat = 778 by decide, byte]
  decide

theorem decode779 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 779) = some (.SWAP2, none) := by
  have byte : NativeSourceAbiWrite.code.get? 779 = some 145 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 779).toNat = 779 by decide, byte]
  decide

theorem decode780 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 780) = some (.SWAP1, none) := by
  have byte : NativeSourceAbiWrite.code.get? 780 = some 144 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 780).toNat = 780 by decide, byte]
  decide

theorem decode781 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 781) = some (.SWAP2, none) := by
  have byte : NativeSourceAbiWrite.code.get? 781 = some 145 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 781).toNat = 781 by decide, byte]
  decide

def s1 (cost : Nat) (pre : EVM.State) (a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (tail : Stack UInt256) :=
  (stepPre cost pre).replaceStackAndIncrPC
    ((a + b) :: c :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: tail)

def s2 (cost : Nat) (pre : EVM.State) (a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (tail : Stack UInt256) :=
  (stepPre cost (s1 cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail)).replaceStackAndIncrPC
    (x11 :: c :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: (a + b) :: x12 :: tail)

def s3 (cost : Nat) (pre : EVM.State) (a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (tail : Stack UInt256) :=
  (stepPre cost (s2 cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail)).replaceStackAndIncrPC
    ((x11 + c) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: (a + b) :: x12 :: tail)

def s4 (cost : Nat) (pre : EVM.State) (a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (tail : Stack UInt256) :=
  (stepPre cost (s3 cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail)).replaceStackAndIncrPC
    (x1 :: x0 :: (x11 + c) :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: (a + b) :: x12 :: tail)

def s5 (cost : Nat) (pre : EVM.State) (a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (tail : Stack UInt256) :=
  (stepPre cost (s4 cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail)).replaceStackAndIncrPC
    ((x1 + x0) :: (x11 + c) :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: (a + b) :: x12 :: tail)

def s6 (cost : Nat) (pre : EVM.State) (a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (tail : Stack UInt256) :=
  (stepPre cost (s5 cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail)).replaceStackAndIncrPC
    (x2 :: (x11 + c) :: (x1 + x0) :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: (a + b) :: x12 :: tail)

def s7 (cost : Nat) (pre : EVM.State) (a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (tail : Stack UInt256) :=
  (stepPre cost (s6 cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail)).replaceStackAndIncrPC
    ((x11 + c) :: x2 :: (x1 + x0) :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: (a + b) :: x12 :: tail)

def s8 (cost : Nat) (pre : EVM.State) (a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (tail : Stack UInt256) :=
  (stepPre cost (s7 cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail)).replaceStackAndIncrPC
    ((x1 + x0) :: x2 :: (x11 + c) :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: (a + b) :: x12 :: tail)

theorem transition1 (fuel cost : Nat) (pre : EVM.State) (a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 774)
    (stack : pre.stack = a :: b :: c :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt pre)) pre = .ok (s1 cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail) := by
  have atPC : pre.pc = UInt256.ofNat 774 := by
    exact pc
  have decoded : decodeAt pre = (.ADD, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code pre.pc).getD _ = _
    rw [code, atPC, decode774]; rfl
  rw [decoded]
  change EVM.execBinOp UInt256.add (stepPre cost pre) = _
  unfold EVM.execBinOp
  simp only [stepPre, stack]
  rfl

theorem transition2 (fuel cost : Nat) (pre : EVM.State) (a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 774)
    (stack : pre.stack = a :: b :: c :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s1 cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail))) (s1 cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail) = .ok (s2 cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail) := by
  have atPC : (s1 cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail).pc = UInt256.ofNat 775 := by
    change (pre.pc + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s1 cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail) = (.SWAP13, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s1 cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail).pc).getD _ = _
    rw [code, atPC, decode775]; rfl
  rw [decoded]
  change EvmYul.swap 13 (stepPre cost (s1 cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail)) = _
  unfold EvmYul.swap
  rfl

theorem transition3 (fuel cost : Nat) (pre : EVM.State) (a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 774)
    (stack : pre.stack = a :: b :: c :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s2 cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail))) (s2 cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail) = .ok (s3 cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail) := by
  have atPC : (s2 cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail).pc = UInt256.ofNat 776 := by
    change ((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s2 cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail) = (.ADD, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s2 cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail).pc).getD _ = _
    rw [code, atPC, decode776]; rfl
  rw [decoded]
  change EVM.execBinOp UInt256.add (stepPre cost (s2 cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail)) = _
  unfold EVM.execBinOp
  rfl

theorem transition4 (fuel cost : Nat) (pre : EVM.State) (a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 774)
    (stack : pre.stack = a :: b :: c :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s3 cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail))) (s3 cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail) = .ok (s4 cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail) := by
  have atPC : (s3 cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail).pc = UInt256.ofNat 777 := by
    change (((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s3 cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail) = (.SWAP2, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s3 cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail).pc).getD _ = _
    rw [code, atPC, decode777]; rfl
  rw [decoded]
  change EvmYul.swap 2 (stepPre cost (s3 cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail)) = _
  unfold EvmYul.swap
  rfl

theorem transition5 (fuel cost : Nat) (pre : EVM.State) (a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 774)
    (stack : pre.stack = a :: b :: c :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s4 cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail))) (s4 cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail) = .ok (s5 cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail) := by
  have atPC : (s4 cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail).pc = UInt256.ofNat 778 := by
    change ((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s4 cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail) = (.ADD, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s4 cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail).pc).getD _ = _
    rw [code, atPC, decode778]; rfl
  rw [decoded]
  change EVM.execBinOp UInt256.add (stepPre cost (s4 cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail)) = _
  unfold EVM.execBinOp
  rfl

theorem transition6 (fuel cost : Nat) (pre : EVM.State) (a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 774)
    (stack : pre.stack = a :: b :: c :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s5 cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail))) (s5 cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail) = .ok (s6 cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail) := by
  have atPC : (s5 cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail).pc = UInt256.ofNat 779 := by
    change (((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s5 cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail) = (.SWAP2, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s5 cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail).pc).getD _ = _
    rw [code, atPC, decode779]; rfl
  rw [decoded]
  change EvmYul.swap 2 (stepPre cost (s5 cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail)) = _
  unfold EvmYul.swap
  rfl

theorem transition7 (fuel cost : Nat) (pre : EVM.State) (a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 774)
    (stack : pre.stack = a :: b :: c :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s6 cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail))) (s6 cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail) = .ok (s7 cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail) := by
  have atPC : (s6 cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail).pc = UInt256.ofNat 780 := by
    change ((((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s6 cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail) = (.SWAP1, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s6 cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail).pc).getD _ = _
    rw [code, atPC, decode780]; rfl
  rw [decoded]
  change EvmYul.swap 1 (stepPre cost (s6 cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail)) = _
  unfold EvmYul.swap
  rfl

theorem transition8 (fuel cost : Nat) (pre : EVM.State) (a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 774)
    (stack : pre.stack = a :: b :: c :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s7 cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail))) (s7 cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail) = .ok (s8 cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail) := by
  have atPC : (s7 cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail).pc = UInt256.ofNat 781 := by
    change (((((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s7 cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail) = (.SWAP2, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s7 cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail).pc).getD _ = _
    rw [code, atPC, decode781]; rfl
  rw [decoded]
  change EvmYul.swap 2 (stepPre cost (s7 cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail)) = _
  unfold EvmYul.swap
  rfl

theorem execute (fuel cost : Nat) (pre : EVM.State) (a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 774)
    (stack : pre.stack = a :: b :: c :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: tail) :
    run fuel cost 8 pre = .ok (s8 cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail) := by
  rw [run, transition1 fuel cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition2 fuel cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition3 fuel cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition4 fuel cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition5 fuel cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition6 fuel cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition7 fuel cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition8 fuel cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rfl

theorem memory (cost : Nat) (pre : EVM.State) (a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (tail : Stack UInt256) :
    (s8 cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail).memory = pre.memory := by
  rfl

theorem output_stack (cost : Nat) (pre : EVM.State) (a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (tail : Stack UInt256) :
    (s8 cost pre a b c x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail).stack = (x1 + x0) :: x2 :: (x11 + c) :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: (a + b) :: x12 :: tail := by
  rfl

end Compiler.Proofs.IRGeneration.NativeSourceDynamicIncrements

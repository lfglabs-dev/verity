import Compiler.Proofs.IRGeneration.NativeSourceDynamicEntryDecode

namespace Compiler.Proofs.IRGeneration.NativeSourceDynamicEntry
open EvmYul EVM.Proof NativeSourcePreludeDecoded

def s1 (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (tail : Stack UInt256) :=
  (stepPre cost pre).replaceStackAndIncrPC
    (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: tail)

def s2 (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (tail : Stack UInt256) :=
  (stepPre cost (s1 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail)).replaceStackAndIncrPC
    (x1 :: x0 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: tail)

def s3 (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (tail : Stack UInt256) :=
  (stepPre cost (s2 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail)).replaceStackAndIncrPC
    (x2 :: x0 :: x1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: tail)

def s4 (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (tail : Stack UInt256) :=
  (stepPre cost (s3 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail)).replaceStackAndIncrPC
    (x11 :: x0 :: x1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x2 :: x12 :: x13 :: x14 :: x15 :: tail)

def s5 (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (tail : Stack UInt256) :=
  (stepPre cost (s4 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail)).replaceStackAndIncrPC
    (UInt256.ofNat 32 :: x11 :: x0 :: x1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x2 :: x12 :: x13 :: x14 :: x15 :: tail) 2

def s6 (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (tail : Stack UInt256) :=
  (stepPre cost (s5 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail)).replaceStackAndIncrPC
    (UInt256.ofNat 128 :: UInt256.ofNat 32 :: x11 :: x0 :: x1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x2 :: x12 :: x13 :: x14 :: x15 :: tail) 2

def s7 (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (tail : Stack UInt256) :=
  (stepPre cost (s6 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail)).replaceStackAndIncrPC
    (UInt256.ofNat 1 :: UInt256.ofNat 128 :: UInt256.ofNat 32 :: x11 :: x0 :: x1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x2 :: x12 :: x13 :: x14 :: x15 :: tail) 2

def s8 (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (tail : Stack UInt256) :=
  (stepPre cost (s7 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail)).replaceStackAndIncrPC
    (x11 :: UInt256.ofNat 128 :: UInt256.ofNat 32 :: UInt256.ofNat 1 :: x0 :: x1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x2 :: x12 :: x13 :: x14 :: x15 :: tail)

def s9 (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (tail : Stack UInt256) :=
  (stepPre cost (s8 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail)).replaceStackAndIncrPC
    (UInt256.ofNat 1 :: x11 :: UInt256.ofNat 128 :: UInt256.ofNat 32 :: UInt256.ofNat 1 :: x0 :: x1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x2 :: x12 :: x13 :: x14 :: x15 :: tail) 2

def s10 (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (tail : Stack UInt256) :=
  (stepPre cost (s9 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail)).replaceStackAndIncrPC
    (UInt256.ofNat 1 :: UInt256.ofNat 1 :: x11 :: UInt256.ofNat 128 :: UInt256.ofNat 32 :: UInt256.ofNat 1 :: x0 :: x1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x2 :: x12 :: x13 :: x14 :: x15 :: tail) 2

def s11 (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (tail : Stack UInt256) :=
  (stepPre cost (s10 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail)).replaceStackAndIncrPC
    (UInt256.ofNat 160 :: UInt256.ofNat 1 :: UInt256.ofNat 1 :: x11 :: UInt256.ofNat 128 :: UInt256.ofNat 32 :: UInt256.ofNat 1 :: x0 :: x1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x2 :: x12 :: x13 :: x14 :: x15 :: tail) 2

def s12 (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (tail : Stack UInt256) :=
  (stepPre cost (s11 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail)).replaceStackAndIncrPC
    ((UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) :: UInt256.ofNat 1 :: x11 :: UInt256.ofNat 128 :: UInt256.ofNat 32 :: UInt256.ofNat 1 :: x0 :: x1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x2 :: x12 :: x13 :: x14 :: x15 :: tail)

def s13 (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (tail : Stack UInt256) :=
  (stepPre cost (s12 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail)).replaceStackAndIncrPC
    (((UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) - UInt256.ofNat 1) :: x11 :: UInt256.ofNat 128 :: UInt256.ofNat 32 :: UInt256.ofNat 1 :: x0 :: x1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x2 :: x12 :: x13 :: x14 :: x15 :: tail)

def s14 (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (tail : Stack UInt256) :=
  (stepPre cost (s13 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail)).replaceStackAndIncrPC
    (x2 :: ((UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) - UInt256.ofNat 1) :: x11 :: UInt256.ofNat 128 :: UInt256.ofNat 32 :: UInt256.ofNat 1 :: x0 :: x1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x2 :: x12 :: x13 :: x14 :: x15 :: tail)

def s15 (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (tail : Stack UInt256) :=
  (stepPre cost (s14 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail)).replaceStackAndIncrPC
    (UInt256.ofNat 96 :: x2 :: ((UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) - UInt256.ofNat 1) :: x11 :: UInt256.ofNat 128 :: UInt256.ofNat 32 :: UInt256.ofNat 1 :: x0 :: x1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x2 :: x12 :: x13 :: x14 :: x15 :: tail) 2

def s16 (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (tail : Stack UInt256) :=
  (stepPre cost (s15 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail)).replaceStackAndIncrPC
    (x2 :: UInt256.ofNat 96 :: ((UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) - UInt256.ofNat 1) :: x11 :: UInt256.ofNat 128 :: UInt256.ofNat 32 :: UInt256.ofNat 1 :: x0 :: x1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x2 :: x12 :: x13 :: x14 :: x15 :: tail)

theorem transition1 (fuel cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 718)
    (stack : pre.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt pre)) pre = .ok (s1 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail) := by
  have atPC : pre.pc = UInt256.ofNat 718 := by
    exact pc
  have decoded : decodeAt pre = (.JUMPDEST, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code pre.pc).getD _ = _
    rw [code, atPC, decode718]; rfl
  rw [decoded]
  rw [step_JUMPDEST]
  simp only [stepPre, stack]
  rfl

theorem transition2 (fuel cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 718)
    (stack : pre.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s1 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail))) (s1 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail) = .ok (s2 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail) := by
  have atPC : (s1 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail).pc = UInt256.ofNat 719 := by
    change (pre.pc + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s1 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail) = (.SWAP1, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s1 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail).pc).getD _ = _
    rw [code, atPC, decode719]; rfl
  rw [decoded]
  change EvmYul.swap 1 (stepPre cost (s1 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail)) = _
  unfold EvmYul.swap
  rfl

theorem transition3 (fuel cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 718)
    (stack : pre.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s2 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail))) (s2 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail) = .ok (s3 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail) := by
  have atPC : (s2 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail).pc = UInt256.ofNat 720 := by
    change ((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s2 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail) = (.SWAP2, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s2 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail).pc).getD _ = _
    rw [code, atPC, decode720]; rfl
  rw [decoded]
  change EvmYul.swap 2 (stepPre cost (s2 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail)) = _
  unfold EvmYul.swap
  rfl

theorem transition4 (fuel cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 718)
    (stack : pre.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s3 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail))) (s3 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail) = .ok (s4 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail) := by
  have atPC : (s3 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail).pc = UInt256.ofNat 721 := by
    change (((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s3 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail) = (.SWAP11, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s3 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail).pc).getD _ = _
    rw [code, atPC, decode721]; rfl
  rw [decoded]
  change EvmYul.swap 11 (stepPre cost (s3 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail)) = _
  unfold EvmYul.swap
  rfl

theorem transition5 (fuel cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 718)
    (stack : pre.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s4 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail))) (s4 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail) = .ok (s5 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail) := by
  have atPC : (s4 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail).pc = UInt256.ofNat 722 := by
    change ((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s4 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail) = (.Push .PUSH1, some (UInt256.ofNat 32, 1)) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s4 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail).pc).getD _ = _
    rw [code, atPC, decode722]; rfl
  rw [decoded]
  exact NativeMidnightConstructor.step_PUSH1 fuel cost _ (UInt256.ofNat 32)

theorem transition6 (fuel cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 718)
    (stack : pre.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s5 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail))) (s5 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail) = .ok (s6 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail) := by
  have atPC : (s5 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail).pc = UInt256.ofNat 724 := by
    change (((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 2) = _
    rw [pc]; decide
  have decoded : decodeAt (s5 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail) = (.Push .PUSH1, some (UInt256.ofNat 128, 1)) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s5 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail).pc).getD _ = _
    rw [code, atPC, decode724]; rfl
  rw [decoded]
  exact NativeMidnightConstructor.step_PUSH1 fuel cost _ (UInt256.ofNat 128)

theorem transition7 (fuel cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 718)
    (stack : pre.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s6 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail))) (s6 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail) = .ok (s7 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail) := by
  have atPC : (s6 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail).pc = UInt256.ofNat 726 := by
    change ((((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 2) + UInt256.ofNat 2) = _
    rw [pc]; decide
  have decoded : decodeAt (s6 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail) = (.Push .PUSH1, some (UInt256.ofNat 1, 1)) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s6 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail).pc).getD _ = _
    rw [code, atPC, decode726]; rfl
  rw [decoded]
  exact NativeMidnightConstructor.step_PUSH1 fuel cost _ (UInt256.ofNat 1)

theorem transition8 (fuel cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 718)
    (stack : pre.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s7 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail))) (s7 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail) = .ok (s8 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail) := by
  have atPC : (s7 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail).pc = UInt256.ofNat 728 := by
    change (((((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 2) + UInt256.ofNat 2) + UInt256.ofNat 2) = _
    rw [pc]; decide
  have decoded : decodeAt (s7 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail) = (.SWAP3, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s7 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail).pc).getD _ = _
    rw [code, atPC, decode728]; rfl
  rw [decoded]
  change EvmYul.swap 3 (stepPre cost (s7 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail)) = _
  unfold EvmYul.swap
  rfl

theorem transition9 (fuel cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 718)
    (stack : pre.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s8 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail))) (s8 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail) = .ok (s9 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail) := by
  have atPC : (s8 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail).pc = UInt256.ofNat 729 := by
    change ((((((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 2) + UInt256.ofNat 2) + UInt256.ofNat 2) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s8 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail) = (.Push .PUSH1, some (UInt256.ofNat 1, 1)) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s8 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail).pc).getD _ = _
    rw [code, atPC, decode729]; rfl
  rw [decoded]
  exact NativeMidnightConstructor.step_PUSH1 fuel cost _ (UInt256.ofNat 1)

theorem transition10 (fuel cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 718)
    (stack : pre.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s9 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail))) (s9 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail) = .ok (s10 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail) := by
  have atPC : (s9 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail).pc = UInt256.ofNat 731 := by
    change (((((((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 2) + UInt256.ofNat 2) + UInt256.ofNat 2) + UInt256.ofNat 1) + UInt256.ofNat 2) = _
    rw [pc]; decide
  have decoded : decodeAt (s9 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail) = (.Push .PUSH1, some (UInt256.ofNat 1, 1)) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s9 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail).pc).getD _ = _
    rw [code, atPC, decode731]; rfl
  rw [decoded]
  exact NativeMidnightConstructor.step_PUSH1 fuel cost _ (UInt256.ofNat 1)

theorem transition11 (fuel cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 718)
    (stack : pre.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s10 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail))) (s10 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail) = .ok (s11 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail) := by
  have atPC : (s10 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail).pc = UInt256.ofNat 733 := by
    change ((((((((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 2) + UInt256.ofNat 2) + UInt256.ofNat 2) + UInt256.ofNat 1) + UInt256.ofNat 2) + UInt256.ofNat 2) = _
    rw [pc]; decide
  have decoded : decodeAt (s10 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail) = (.Push .PUSH1, some (UInt256.ofNat 160, 1)) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s10 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail).pc).getD _ = _
    rw [code, atPC, decode733]; rfl
  rw [decoded]
  exact NativeMidnightConstructor.step_PUSH1 fuel cost _ (UInt256.ofNat 160)

theorem transition12 (fuel cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 718)
    (stack : pre.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s11 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail))) (s11 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail) = .ok (s12 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail) := by
  have atPC : (s11 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail).pc = UInt256.ofNat 735 := by
    change (((((((((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 2) + UInt256.ofNat 2) + UInt256.ofNat 2) + UInt256.ofNat 1) + UInt256.ofNat 2) + UInt256.ofNat 2) + UInt256.ofNat 2) = _
    rw [pc]; decide
  have decoded : decodeAt (s11 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail) = (.SHL, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s11 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail).pc).getD _ = _
    rw [code, atPC, decode735]; rfl
  rw [decoded]
  change EVM.execBinOp (flip UInt256.shiftLeft) (stepPre cost (s11 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail)) = _
  unfold EVM.execBinOp
  rfl

theorem transition13 (fuel cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 718)
    (stack : pre.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s12 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail))) (s12 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail) = .ok (s13 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail) := by
  have atPC : (s12 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail).pc = UInt256.ofNat 736 := by
    change ((((((((((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 2) + UInt256.ofNat 2) + UInt256.ofNat 2) + UInt256.ofNat 1) + UInt256.ofNat 2) + UInt256.ofNat 2) + UInt256.ofNat 2) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s12 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail) = (.SUB, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s12 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail).pc).getD _ = _
    rw [code, atPC, decode736]; rfl
  rw [decoded]
  change EVM.execBinOp UInt256.sub (stepPre cost (s12 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail)) = _
  unfold EVM.execBinOp
  rfl

theorem transition14 (fuel cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 718)
    (stack : pre.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s13 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail))) (s13 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail) = .ok (s14 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail) := by
  have atPC : (s13 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail).pc = UInt256.ofNat 737 := by
    change (((((((((((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 2) + UInt256.ofNat 2) + UInt256.ofNat 2) + UInt256.ofNat 1) + UInt256.ofNat 2) + UInt256.ofNat 2) + UInt256.ofNat 2) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s13 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail) = (.DUP16, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s13 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail).pc).getD _ = _
    rw [code, atPC, decode737]; rfl
  rw [decoded]
  change EvmYul.dup 16 (stepPre cost (s13 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail)) = _
  unfold EvmYul.dup
  rfl

theorem transition15 (fuel cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 718)
    (stack : pre.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s14 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail))) (s14 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail) = .ok (s15 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail) := by
  have atPC : (s14 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail).pc = UInt256.ofNat 738 := by
    change ((((((((((((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 2) + UInt256.ofNat 2) + UInt256.ofNat 2) + UInt256.ofNat 1) + UInt256.ofNat 2) + UInt256.ofNat 2) + UInt256.ofNat 2) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s14 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail) = (.Push .PUSH1, some (UInt256.ofNat 96, 1)) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s14 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail).pc).getD _ = _
    rw [code, atPC, decode738]; rfl
  rw [decoded]
  exact NativeMidnightConstructor.step_PUSH1 fuel cost _ (UInt256.ofNat 96)

theorem transition16 (fuel cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 718)
    (stack : pre.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s15 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail))) (s15 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail) = .ok (s16 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail) := by
  have atPC : (s15 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail).pc = UInt256.ofNat 740 := by
    change (((((((((((((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 2) + UInt256.ofNat 2) + UInt256.ofNat 2) + UInt256.ofNat 1) + UInt256.ofNat 2) + UInt256.ofNat 2) + UInt256.ofNat 2) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 2) = _
    rw [pc]; decide
  have decoded : decodeAt (s15 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail) = (.SWAP1, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s15 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail).pc).getD _ = _
    rw [code, atPC, decode740]; rfl
  rw [decoded]
  change EvmYul.swap 1 (stepPre cost (s15 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail)) = _
  unfold EvmYul.swap
  rfl

theorem execute (fuel cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 718)
    (stack : pre.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: tail) :
    run fuel cost 16 pre = .ok (s16 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail) := by
  rw [run, transition1 fuel cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition2 fuel cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition3 fuel cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition4 fuel cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition5 fuel cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition6 fuel cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition7 fuel cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition8 fuel cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition9 fuel cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition10 fuel cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition11 fuel cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition12 fuel cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition13 fuel cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition14 fuel cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition15 fuel cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition16 fuel cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rfl

theorem memory (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (tail : Stack UInt256) : (s16 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail).memory = pre.memory := by
  rfl

theorem output_stack (cost : Nat) (pre : EVM.State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (tail : Stack UInt256) :
    (s16 cost pre x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 tail).stack = x2 :: UInt256.ofNat 96 :: ((UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) - UInt256.ofNat 1) :: x11 :: UInt256.ofNat 128 :: UInt256.ofNat 32 :: UInt256.ofNat 1 :: x0 :: x1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x2 :: x12 :: x13 :: x14 :: x15 :: tail := by
  rfl

end Compiler.Proofs.IRGeneration.NativeSourceDynamicEntry

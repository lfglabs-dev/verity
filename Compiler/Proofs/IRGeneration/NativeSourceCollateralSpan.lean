import Compiler.Proofs.IRGeneration.NativeSourceOffsetCertificate

namespace Compiler.Proofs.IRGeneration.NativeSourceCollateralSpan
open EvmYul EVM EVM.Proof

def array (a offset : UInt256) := a + offset
def size (pre : EVM.State) := UInt256.ofNat pre.executionEnv.calldata.size
def flag (pre : EVM.State) (a offset : UInt256) :=
  UInt256.isZero (UInt256.slt (array a offset + UInt256.ofNat 35) (size pre))

theorem immediate243 : NativeSourceAbiWrite.code.extract' 244 245 = ⟨#[35]⟩ := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[244]? = some 35 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  apply ByteArray.ext
  simp only [ByteArray.extract', show (244 < 2^64 && 245 < 2^64) = true by decide, if_true, ByteArray.data_extract]
  apply Array.ext
  · simp only [Array.size_extract, size, ByteArray.size_data]; decide
  · intro index left right
    have bound : index < 1 := by simpa using right
    have zero : index = 0 := by omega
    subst index
    simp only [Array.getElem_extract, Nat.add_zero]
    exact Option.some.inj ((Array.getElem?_eq_getElem (by change 244 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte)

theorem immediate249 : NativeSourceAbiWrite.code.extract' 250 252 = ⟨#[0, 91]⟩ := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]
    decide
  have byte1 : NativeSourceAbiWrite.code.data[250]? = some 0 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have byte2 : NativeSourceAbiWrite.code.data[251]? = some 91 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  apply ByteArray.ext
  simp only [ByteArray.extract', show (250 < 2^64 && 252 < 2^64) = true by decide, if_true,
    ByteArray.data_extract]
  apply Array.ext
  · simp only [Array.size_extract, size, ByteArray.size_data]
    decide
  · intro index left right
    have bound : index < 2 := by simpa using right
    have cases : index = 0 ∨ index = 1 := by omega
    rcases cases with zero | one
    · subst index
      simp only [Array.getElem_extract, Nat.add_zero]
      exact Option.some.inj ((Array.getElem?_eq_getElem (by change 250 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte1)
    · subst index
      simp only [Array.getElem_extract]
      exact Option.some.inj ((Array.getElem?_eq_getElem (by change 251 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte2)

theorem decode239 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 239) = some (.DUP4, none) := by
  have byte : NativeSourceAbiWrite.code.get? 239 = some 131 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 239).toNat = 239 by decide, byte]
  decide

theorem decode240 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 240) = some (.ADD, none) := by
  have byte : NativeSourceAbiWrite.code.get? 240 = some 1 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 240).toNat = 240 by decide, byte]
  decide

theorem decode241 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 241) = some (.SWAP1, none) := by
  have byte : NativeSourceAbiWrite.code.get? 241 = some 144 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 241).toNat = 241 by decide, byte]
  decide

theorem decode242 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 242) = some (.CALLDATASIZE, none) := by
  have byte : NativeSourceAbiWrite.code.get? 242 = some 54 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 242).toNat = 242 by decide, byte]
  decide

theorem decode243 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 243) = some (.Push .PUSH1, some (UInt256.ofNat 35, 1)) := by
  have byte : NativeSourceAbiWrite.code.get? 243 = some 96 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 243).toNat = 243 by decide, byte]
  change some (Operation.Push Operation.POp.PUSH1, some (uInt256OfByteArray (NativeSourceAbiWrite.code.extract' 244 245), 1)) = _
  rw [immediate243]
  decide

theorem decode245 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 245) = some (.DUP4, none) := by
  have byte : NativeSourceAbiWrite.code.get? 245 = some 131 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 245).toNat = 245 by decide, byte]
  decide

theorem decode246 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 246) = some (.ADD, none) := by
  have byte : NativeSourceAbiWrite.code.get? 246 = some 1 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 246).toNat = 246 by decide, byte]
  decide

theorem decode247 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 247) = some (.SLT, none) := by
  have byte : NativeSourceAbiWrite.code.get? 247 = some 18 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 247).toNat = 247 by decide, byte]
  decide

theorem decode248 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 248) = some (.ISZERO, none) := by
  have byte : NativeSourceAbiWrite.code.get? 248 = some 21 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 248).toNat = 248 by decide, byte]
  decide

theorem decode249 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 249) = some (.Push .PUSH2, some (UInt256.ofNat 91, 2)) := by
  have byte : NativeSourceAbiWrite.code.get? 249 = some 97 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 249).toNat = 249 by decide, byte]
  change some (Operation.Push Operation.POp.PUSH2, some (uInt256OfByteArray (NativeSourceAbiWrite.code.extract' 250 252), 2)) = _
  rw [immediate249]
  decide

theorem decode252 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 252) = some (.JUMPI, none) := by
  have byte : NativeSourceAbiWrite.code.get? 252 = some 87 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 252).toNat = 252 by decide, byte]
  decide

def s1 (pre : EVM.State) (offset x y a base : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 pre).replaceStackAndIncrPC (a :: offset :: x :: y :: a :: base :: tail) 1

def s2 (pre : EVM.State) (offset x y a base : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 (s1 pre offset x y a base tail)).replaceStackAndIncrPC (array a offset :: x :: y :: a :: base :: tail) 1

def s3 (pre : EVM.State) (offset x y a base : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 (s2 pre offset x y a base tail)).replaceStackAndIncrPC (x :: array a offset :: y :: a :: base :: tail) 1

def s4 (pre : EVM.State) (offset x y a base : UInt256) (tail : Stack UInt256) :=
  (stepPre 2 (s3 pre offset x y a base tail)).replaceStackAndIncrPC (size pre :: x :: array a offset :: y :: a :: base :: tail) 1

def s5 (pre : EVM.State) (offset x y a base : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 (s4 pre offset x y a base tail)).replaceStackAndIncrPC (UInt256.ofNat 35 :: size pre :: x :: array a offset :: y :: a :: base :: tail) 2

def s6 (pre : EVM.State) (offset x y a base : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 (s5 pre offset x y a base tail)).replaceStackAndIncrPC (array a offset :: UInt256.ofNat 35 :: size pre :: x :: array a offset :: y :: a :: base :: tail) 1

def s7 (pre : EVM.State) (offset x y a base : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 (s6 pre offset x y a base tail)).replaceStackAndIncrPC ((array a offset + UInt256.ofNat 35) :: size pre :: x :: array a offset :: y :: a :: base :: tail) 1

def s8 (pre : EVM.State) (offset x y a base : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 (s7 pre offset x y a base tail)).replaceStackAndIncrPC (UInt256.slt (array a offset + UInt256.ofNat 35) (size pre) :: x :: array a offset :: y :: a :: base :: tail) 1

def s9 (pre : EVM.State) (offset x y a base : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 (s8 pre offset x y a base tail)).replaceStackAndIncrPC (flag pre a offset :: x :: array a offset :: y :: a :: base :: tail) 1

def s10 (pre : EVM.State) (offset x y a base : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 (s9 pre offset x y a base tail)).replaceStackAndIncrPC (UInt256.ofNat 91 :: flag pre a offset :: x :: array a offset :: y :: a :: base :: tail) 3

theorem transition1 (fuel : Nat) (pre : EVM.State) (offset x y a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 239)
    (stack : pre.stack = offset :: x :: y :: a :: base :: tail) :
    EVM.step (fuel + 1) 3 (some (decodeAt pre)) pre = .ok (s1 pre offset x y a base tail) := by
  have atPC : pre.pc = UInt256.ofNat 239 := by
    exact pc
  have decoded : decodeAt pre = (.DUP4, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code pre.pc).getD _ = _
    rw [code, atPC, decode239]; rfl
  rw [decoded]
  change EvmYul.dup 4 (stepPre 3 pre) = _
  unfold EvmYul.dup
  simp only [stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack]
  rfl

theorem transition2 (fuel : Nat) (pre : EVM.State) (offset x y a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 239)
    (stack : pre.stack = offset :: x :: y :: a :: base :: tail) :
    EVM.step (fuel + 1) 3 (some (decodeAt (s1 pre offset x y a base tail))) (s1 pre offset x y a base tail) = .ok (s2 pre offset x y a base tail) := by
  have atPC : (s1 pre offset x y a base tail).pc = UInt256.ofNat 240 := by
    simp only [s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s1 pre offset x y a base tail) = (.ADD, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s1 pre offset x y a base tail).pc).getD _ = _
    rw [code, atPC, decode240]; rfl
  rw [decoded]
  change EvmYul.step (τ := .EVM) .ADD none (stepPre 3 (s1 pre offset x y a base tail)) = _
  unfold EvmYul.step
  simp only [s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack]
  rfl

theorem transition3 (fuel : Nat) (pre : EVM.State) (offset x y a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 239)
    (stack : pre.stack = offset :: x :: y :: a :: base :: tail) :
    EVM.step (fuel + 1) 3 (some (decodeAt (s2 pre offset x y a base tail))) (s2 pre offset x y a base tail) = .ok (s3 pre offset x y a base tail) := by
  have atPC : (s2 pre offset x y a base tail).pc = UInt256.ofNat 241 := by
    simp only [s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s2 pre offset x y a base tail) = (.SWAP1, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s2 pre offset x y a base tail).pc).getD _ = _
    rw [code, atPC, decode241]; rfl
  rw [decoded]
  change EvmYul.swap 1 (stepPre 3 (s2 pre offset x y a base tail)) = _
  unfold EvmYul.swap
  simp only [s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack]
  rfl

theorem transition4 (fuel : Nat) (pre : EVM.State) (offset x y a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 239)
    (stack : pre.stack = offset :: x :: y :: a :: base :: tail) :
    EVM.step (fuel + 1) 2 (some (decodeAt (s3 pre offset x y a base tail))) (s3 pre offset x y a base tail) = .ok (s4 pre offset x y a base tail) := by
  have atPC : (s3 pre offset x y a base tail).pc = UInt256.ofNat 242 := by
    simp only [s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s3 pre offset x y a base tail) = (.CALLDATASIZE, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s3 pre offset x y a base tail).pc).getD _ = _
    rw [code, atPC, decode242]; rfl
  rw [decoded]
  change EvmYul.step (τ := .EVM) .CALLDATASIZE none (stepPre 2 (s3 pre offset x y a base tail)) = _
  unfold EvmYul.step
  simp only [s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack]
  rfl

theorem transition5 (fuel : Nat) (pre : EVM.State) (offset x y a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 239)
    (_stack : pre.stack = offset :: x :: y :: a :: base :: tail) :
    EVM.step (fuel + 1) 3 (some (decodeAt (s4 pre offset x y a base tail))) (s4 pre offset x y a base tail) = .ok (s5 pre offset x y a base tail) := by
  have atPC : (s4 pre offset x y a base tail).pc = UInt256.ofNat 243 := by
    simp only [s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s4 pre offset x y a base tail) = (.Push .PUSH1, some (UInt256.ofNat 35, 1)) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s4 pre offset x y a base tail).pc).getD _ = _
    rw [code, atPC, decode243]; rfl
  rw [decoded]
  rfl

theorem transition6 (fuel : Nat) (pre : EVM.State) (offset x y a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 239)
    (stack : pre.stack = offset :: x :: y :: a :: base :: tail) :
    EVM.step (fuel + 1) 3 (some (decodeAt (s5 pre offset x y a base tail))) (s5 pre offset x y a base tail) = .ok (s6 pre offset x y a base tail) := by
  have atPC : (s5 pre offset x y a base tail).pc = UInt256.ofNat 245 := by
    simp only [s5, s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s5 pre offset x y a base tail) = (.DUP4, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s5 pre offset x y a base tail).pc).getD _ = _
    rw [code, atPC, decode245]; rfl
  rw [decoded]
  change EvmYul.dup 4 (stepPre 3 (s5 pre offset x y a base tail)) = _
  unfold EvmYul.dup
  simp only [s5, s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack]
  rfl

theorem transition7 (fuel : Nat) (pre : EVM.State) (offset x y a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 239)
    (stack : pre.stack = offset :: x :: y :: a :: base :: tail) :
    EVM.step (fuel + 1) 3 (some (decodeAt (s6 pre offset x y a base tail))) (s6 pre offset x y a base tail) = .ok (s7 pre offset x y a base tail) := by
  have atPC : (s6 pre offset x y a base tail).pc = UInt256.ofNat 246 := by
    simp only [s6, s5, s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s6 pre offset x y a base tail) = (.ADD, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s6 pre offset x y a base tail).pc).getD _ = _
    rw [code, atPC, decode246]; rfl
  rw [decoded]
  change EvmYul.step (τ := .EVM) .ADD none (stepPre 3 (s6 pre offset x y a base tail)) = _
  unfold EvmYul.step
  simp only [s6, s5, s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack]
  rfl

theorem transition8 (fuel : Nat) (pre : EVM.State) (offset x y a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 239)
    (stack : pre.stack = offset :: x :: y :: a :: base :: tail) :
    EVM.step (fuel + 1) 3 (some (decodeAt (s7 pre offset x y a base tail))) (s7 pre offset x y a base tail) = .ok (s8 pre offset x y a base tail) := by
  have atPC : (s7 pre offset x y a base tail).pc = UInt256.ofNat 247 := by
    simp only [s7, s6, s5, s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s7 pre offset x y a base tail) = (.SLT, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s7 pre offset x y a base tail).pc).getD _ = _
    rw [code, atPC, decode247]; rfl
  rw [decoded]
  change EvmYul.step (τ := .EVM) .SLT none (stepPre 3 (s7 pre offset x y a base tail)) = _
  unfold EvmYul.step
  simp only [s7, s6, s5, s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack]
  rfl

theorem transition9 (fuel : Nat) (pre : EVM.State) (offset x y a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 239)
    (stack : pre.stack = offset :: x :: y :: a :: base :: tail) :
    EVM.step (fuel + 1) 3 (some (decodeAt (s8 pre offset x y a base tail))) (s8 pre offset x y a base tail) = .ok (s9 pre offset x y a base tail) := by
  have atPC : (s8 pre offset x y a base tail).pc = UInt256.ofNat 248 := by
    simp only [s8, s7, s6, s5, s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s8 pre offset x y a base tail) = (.ISZERO, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s8 pre offset x y a base tail).pc).getD _ = _
    rw [code, atPC, decode248]; rfl
  rw [decoded]
  change EvmYul.step (τ := .EVM) .ISZERO none (stepPre 3 (s8 pre offset x y a base tail)) = _
  unfold EvmYul.step
  simp only [s8, s7, s6, s5, s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack]
  rfl

theorem transition10 (fuel : Nat) (pre : EVM.State) (offset x y a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 239)
    (_stack : pre.stack = offset :: x :: y :: a :: base :: tail) :
    EVM.step (fuel + 1) 3 (some (decodeAt (s9 pre offset x y a base tail))) (s9 pre offset x y a base tail) = .ok (s10 pre offset x y a base tail) := by
  have atPC : (s9 pre offset x y a base tail).pc = UInt256.ofNat 249 := by
    simp only [s9, s8, s7, s6, s5, s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s9 pre offset x y a base tail) = (.Push .PUSH2, some (UInt256.ofNat 91, 2)) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s9 pre offset x y a base tail).pc).getD _ = _
    rw [code, atPC, decode249]; rfl
  rw [decoded]
  rfl

theorem frame (pre : EVM.State) (offset x y a base : UInt256) (tail : Stack UInt256) :
    (s10 pre offset x y a base tail).stack = UInt256.ofNat 91 :: flag pre a offset :: x :: array a offset :: y :: a :: base :: tail ∧
      (s10 pre offset x y a base tail).toState = pre.toState ∧ (s10 pre offset x y a base tail).memory = pre.memory := by
  exact ⟨rfl, rfl, rfl⟩

theorem output_pc (pre : EVM.State) (offset x y a base : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 239) : (s10 pre offset x y a base tail).pc = UInt256.ofNat 252 := by
  simp only [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, stepPre,
    EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
  rw [pc]; decide

theorem prefix_gas (pre : EVM.State) (offset x y a base : UInt256) (tail : Stack UInt256)
    (gas : 29 ≤ pre.gasAvailable.toNat) :
    (s10 pre offset x y a base tail).gasAvailable.toNat = pre.gasAvailable.toNat - 29 := by
  have g1 : (s1 pre offset x y a base tail).gasAvailable.toNat = pre.gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g2 : (s2 pre offset x y a base tail).gasAvailable.toNat = (s1 pre offset x y a base tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g3 : (s3 pre offset x y a base tail).gasAvailable.toNat = (s2 pre offset x y a base tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g4 : (s4 pre offset x y a base tail).gasAvailable.toNat = (s3 pre offset x y a base tail).gasAvailable.toNat - 2 :=
    NativeSourceCheckedRejection.gas_sub _ 2 (by decide) (by omega)
  have g5 : (s5 pre offset x y a base tail).gasAvailable.toNat = (s4 pre offset x y a base tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g6 : (s6 pre offset x y a base tail).gasAvailable.toNat = (s5 pre offset x y a base tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g7 : (s7 pre offset x y a base tail).gasAvailable.toNat = (s6 pre offset x y a base tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g8 : (s8 pre offset x y a base tail).gasAvailable.toNat = (s7 pre offset x y a base tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g9 : (s9 pre offset x y a base tail).gasAvailable.toNat = (s8 pre offset x y a base tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g10 : (s10 pre offset x y a base tail).gasAvailable.toNat = (s9 pre offset x y a base tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  omega

end Compiler.Proofs.IRGeneration.NativeSourceCollateralSpan



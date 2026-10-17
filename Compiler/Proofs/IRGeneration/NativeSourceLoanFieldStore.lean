import Compiler.Proofs.IRGeneration.NativeSourceLoanCallCertificate

namespace Compiler.Proofs.IRGeneration.NativeSourceLoanFieldStore
open EvmYul EVM EVM.Proof

theorem immediate212 : NativeSourceAbiWrite.code.extract' 213 214 = ⟨#[64]⟩ := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[213]? = some 64 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  apply ByteArray.ext
  simp only [ByteArray.extract', show (213 < 2^64 && 214 < 2^64) = true by decide, if_true, ByteArray.data_extract]
  apply Array.ext
  · simp only [Array.size_extract, size, ByteArray.size_data]; decide
  · intro index left right
    have bound : index < 1 := by simpa using right
    have zero : index = 0 := by omega
    subst index
    simp only [Array.getElem_extract, Nat.add_zero]
    exact Option.some.inj ((Array.getElem?_eq_getElem (by change 213 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte)

theorem decode210 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 210) = some (.JUMPDEST, none) := by
  have byte : NativeSourceAbiWrite.code.get? 210 = some 91 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 210).toNat = 210 by decide, byte]
  decide

theorem decode211 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 211) = some (.SWAP1, none) := by
  have byte : NativeSourceAbiWrite.code.get? 211 = some 144 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 211).toNat = 211 by decide, byte]
  decide

theorem decode212 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 212) = some ((.Push .PUSH1), some (UInt256.ofNat 64, 1)) := by
  have byte : NativeSourceAbiWrite.code.get? 212 = some 96 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 212).toNat = 212 by decide, byte]
  change some (Operation.Push Operation.POp.PUSH1, some (uInt256OfByteArray (NativeSourceAbiWrite.code.extract' 213 214), 1)) = _
  rw [immediate212]
  decide

theorem decode214 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 214) = some (.DUP5, none) := by
  have byte : NativeSourceAbiWrite.code.get? 214 = some 132 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 214).toNat = 214 by decide, byte]
  decide

theorem decode215 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 215) = some (.ADD, none) := by
  have byte : NativeSourceAbiWrite.code.get? 215 = some 1 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 215).toNat = 215 by decide, byte]
  decide

theorem decode216 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 216) = some (.SWAP2, none) := by
  have byte : NativeSourceAbiWrite.code.get? 216 = some 145 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 216).toNat = 216 by decide, byte]
  decide

theorem decode217 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 217) = some (.DUP3, none) := by
  have byte : NativeSourceAbiWrite.code.get? 217 = some 130 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 217).toNat = 217 by decide, byte]
  decide

theorem decode218 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 218) = some (.MSTORE, none) := by
  have byte : NativeSourceAbiWrite.code.get? 218 = some 82 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 218).toNat = 218 by decide, byte]
  decide

def s1 (pre : EVM.State) (_word _x _a _base : UInt256) (_tail : Stack UInt256) :=
  (stepPre 1 pre).incrPC

def s2 (pre : EVM.State) (word x a base : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 (s1 pre word x a base tail)).replaceStackAndIncrPC (x :: word :: a :: base :: tail)

def s3 (pre : EVM.State) (word x a base : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 (s2 pre word x a base tail)).replaceStackAndIncrPC (UInt256.ofNat 64 :: x :: word :: a :: base :: tail) 2

def s4 (pre : EVM.State) (word x a base : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 (s3 pre word x a base tail)).replaceStackAndIncrPC (base :: UInt256.ofNat 64 :: x :: word :: a :: base :: tail)

def s5 (pre : EVM.State) (word x a base : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 (s4 pre word x a base tail)).replaceStackAndIncrPC ((base + UInt256.ofNat 64) :: x :: word :: a :: base :: tail)

def s6 (pre : EVM.State) (word x a base : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 (s5 pre word x a base tail)).replaceStackAndIncrPC (word :: x :: (base + UInt256.ofNat 64) :: a :: base :: tail)

def s7 (pre : EVM.State) (word x a base : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 (s6 pre word x a base tail)).replaceStackAndIncrPC ((base + UInt256.ofNat 64) :: word :: x :: (base + UInt256.ofNat 64) :: a :: base :: tail)

def stored (pre : EVM.State) (word x a base : UInt256) (tail : Stack UInt256) :=
  mstorePost 3 (NativeSourceFieldStoreChecks.expanded (s7 pre word x a base tail))
    (x :: (base + UInt256.ofNat 64) :: a :: base :: tail) (base + UInt256.ofNat 64) word

theorem transition1 (fuel : Nat) (pre : EVM.State) (word x a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 210)
    (_stack : pre.stack = word :: x :: a :: base :: tail) :
    EVM.step (fuel + 1) 1 (some (decodeAt pre)) pre = .ok (s1 pre word x a base tail) := by
  have atPC : pre.pc = UInt256.ofNat 210 := by
    exact pc
  have decoded : decodeAt pre = (.JUMPDEST, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code pre.pc).getD _ = _
    rw [code, atPC, decode210]; rfl
  rw [decoded]
  exact step_JUMPDEST fuel 1 pre

theorem transition2 (fuel : Nat) (pre : EVM.State) (word x a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 210)
    (stack : pre.stack = word :: x :: a :: base :: tail) :
    EVM.step (fuel + 1) 3 (some (decodeAt (s1 pre word x a base tail))) (s1 pre word x a base tail) = .ok (s2 pre word x a base tail) := by
  have atPC : (s1 pre word x a base tail).pc = UInt256.ofNat 211 := by
    simp only [s1, stepPre, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s1 pre word x a base tail) = (.SWAP1, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s1 pre word x a base tail).pc).getD _ = _
    rw [code, atPC, decode211]; rfl
  rw [decoded]
  change EvmYul.swap 1 (stepPre 3 (s1 pre word x a base tail)) = _
  unfold EvmYul.swap
  simp only [s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack]
  rfl

theorem transition3 (fuel : Nat) (pre : EVM.State) (word x a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 210)
    (_stack : pre.stack = word :: x :: a :: base :: tail) :
    EVM.step (fuel + 1) 3 (some (decodeAt (s2 pre word x a base tail))) (s2 pre word x a base tail) = .ok (s3 pre word x a base tail) := by
  have atPC : (s2 pre word x a base tail).pc = UInt256.ofNat 212 := by
    simp only [s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s2 pre word x a base tail) = (.Push .PUSH1, some (UInt256.ofNat 64, 1)) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s2 pre word x a base tail).pc).getD _ = _
    rw [code, atPC, decode212]; rfl
  rw [decoded]
  rfl

theorem transition4 (fuel : Nat) (pre : EVM.State) (word x a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 210)
    (stack : pre.stack = word :: x :: a :: base :: tail) :
    EVM.step (fuel + 1) 3 (some (decodeAt (s3 pre word x a base tail))) (s3 pre word x a base tail) = .ok (s4 pre word x a base tail) := by
  have atPC : (s3 pre word x a base tail).pc = UInt256.ofNat 214 := by
    simp only [s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s3 pre word x a base tail) = (.DUP5, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s3 pre word x a base tail).pc).getD _ = _
    rw [code, atPC, decode214]; rfl
  rw [decoded]
  change EvmYul.dup 5 (stepPre 3 (s3 pre word x a base tail)) = _
  unfold EvmYul.dup
  simp only [s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack]
  rfl

theorem transition5 (fuel : Nat) (pre : EVM.State) (word x a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 210)
    (stack : pre.stack = word :: x :: a :: base :: tail) :
    EVM.step (fuel + 1) 3 (some (decodeAt (s4 pre word x a base tail))) (s4 pre word x a base tail) = .ok (s5 pre word x a base tail) := by
  have atPC : (s4 pre word x a base tail).pc = UInt256.ofNat 215 := by
    simp only [s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s4 pre word x a base tail) = (.ADD, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s4 pre word x a base tail).pc).getD _ = _
    rw [code, atPC, decode215]; rfl
  rw [decoded]
  change EvmYul.step (τ := .EVM) .ADD none (stepPre 3 (s4 pre word x a base tail)) = _
  unfold EvmYul.step
  simp only [s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack]
  rfl

theorem transition6 (fuel : Nat) (pre : EVM.State) (word x a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 210)
    (stack : pre.stack = word :: x :: a :: base :: tail) :
    EVM.step (fuel + 1) 3 (some (decodeAt (s5 pre word x a base tail))) (s5 pre word x a base tail) = .ok (s6 pre word x a base tail) := by
  have atPC : (s5 pre word x a base tail).pc = UInt256.ofNat 216 := by
    simp only [s5, s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s5 pre word x a base tail) = (.SWAP2, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s5 pre word x a base tail).pc).getD _ = _
    rw [code, atPC, decode216]; rfl
  rw [decoded]
  change EvmYul.swap 2 (stepPre 3 (s5 pre word x a base tail)) = _
  unfold EvmYul.swap
  simp only [s5, s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack]
  rfl

theorem transition7 (fuel : Nat) (pre : EVM.State) (word x a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 210)
    (stack : pre.stack = word :: x :: a :: base :: tail) :
    EVM.step (fuel + 1) 3 (some (decodeAt (s6 pre word x a base tail))) (s6 pre word x a base tail) = .ok (s7 pre word x a base tail) := by
  have atPC : (s6 pre word x a base tail).pc = UInt256.ofNat 217 := by
    simp only [s6, s5, s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s6 pre word x a base tail) = (.DUP3, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s6 pre word x a base tail).pc).getD _ = _
    rw [code, atPC, decode217]; rfl
  rw [decoded]
  change EvmYul.dup 3 (stepPre 3 (s6 pre word x a base tail)) = _
  unfold EvmYul.dup
  simp only [s6, s5, s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack]
  rfl

theorem dup5_check (jumps : Array UInt256) (pre : EVM.State)
    (gas : 3 ≤ (pre.gasAvailable - UInt256.ofNat 0).toNat)
    (depth : 5 ≤ pre.stack.length ∧ pre.stack.length ≤ 1023) :
    Z jumps .DUP5 pre = .ok ({ pre with gasAvailable := pre.gasAvailable - UInt256.ofNat 0 }, 3) := by
  have cost (state : EVM.State) : C' state .DUP5 = 3 := by rfl
  simp only [Z, W, memoryExpansionCost, memoryExpansionCost.μᵢ', Nat.sub_self, cost]
  rw [if_neg (by omega), if_neg (by omega)]
  simp only [δ, α, Option.getD_some, Operation.isCreate, reduceIte, reduceCtorEq, false_and, Bind.bind, Except.bind,
    pure, Except.pure]
  simp [show ¬pre.stack.length < 5 by omega, show ¬pre.stack.length - 5 + 6 > 1024 by omega]

theorem swap2_check (jumps : Array UInt256) (pre : EVM.State)
    (gas : 3 ≤ (pre.gasAvailable - UInt256.ofNat 0).toNat)
    (depth : 3 ≤ pre.stack.length ∧ pre.stack.length ≤ 1024) :
    Z jumps .SWAP2 pre = .ok ({ pre with gasAvailable := pre.gasAvailable - UInt256.ofNat 0 }, 3) := by
  have cost (state : EVM.State) : C' state .SWAP2 = 3 := by rfl
  simp only [Z, W, memoryExpansionCost, memoryExpansionCost.μᵢ', Nat.sub_self, cost]
  rw [if_neg (by omega), if_neg (by omega)]
  simp only [δ, α, Option.getD_some, Operation.isCreate, reduceIte, reduceCtorEq, false_and, Bind.bind, Except.bind,
    pure, Except.pure]
  simp [show ¬pre.stack.length < 3 by omega, show ¬pre.stack.length - 3 + 3 > 1024 by omega]

theorem continue1 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (word x a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 210)
    (stack : pre.stack = word :: x :: a :: base :: tail)
    (gas : 1 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1016) :
    EVM.X (fuel + 2) jumps pre = EVM.X (fuel + 1) jumps (s1 pre word x a base tail) := by
  have atPC : pre.pc = UInt256.ofNat 210 := by
    exact pc
  have decoded : decodeAt pre = (.JUMPDEST, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code pre.pc).getD _ = _
    rw [code, atPC, decode210]; rfl
  have check := Z_JUMPDEST jumps pre
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word, GasConstants.Gjumpdest] using gas)
    (by simp only [stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := transition1 fuel pre word x a base tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step (H_JUMPDEST _)

theorem continue2 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (word x a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 210)
    (stack : pre.stack = word :: x :: a :: base :: tail)
    (gas : 3 ≤ (s1 pre word x a base tail).gasAvailable.toNat) (depth : tail.length ≤ 1016) :
    EVM.X (fuel + 2) jumps (s1 pre word x a base tail) = EVM.X (fuel + 1) jumps (s2 pre word x a base tail) := by
  have atPC : (s1 pre word x a base tail).pc = UInt256.ofNat 211 := by
    simp only [s1, stepPre, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s1 pre word x a base tail) = (.SWAP1, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s1 pre word x a base tail).pc).getD _ = _
    rw [code, atPC, decode211]; rfl
  have check := NativeSourceGuardChecks.swap1 jumps (s1 pre word x a base tail)
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [s1, stepPre, EVM.State.incrPC, stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := transition2 fuel pre word x a base tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem continue3 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (word x a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 210)
    (stack : pre.stack = word :: x :: a :: base :: tail)
    (gas : 3 ≤ (s2 pre word x a base tail).gasAvailable.toNat) (depth : tail.length ≤ 1016) :
    EVM.X (fuel + 2) jumps (s2 pre word x a base tail) = EVM.X (fuel + 1) jumps (s3 pre word x a base tail) := by
  have atPC : (s2 pre word x a base tail).pc = UInt256.ofNat 212 := by
    simp only [s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s2 pre word x a base tail) = (.Push .PUSH1, some (UInt256.ofNat 64, 1)) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s2 pre word x a base tail).pc).getD _ = _
    rw [code, atPC, decode212]; rfl
  have check := NativeSourceGuardChecks.push1 jumps (s2 pre word x a base tail)
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := transition3 fuel pre word x a base tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem continue4 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (word x a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 210)
    (stack : pre.stack = word :: x :: a :: base :: tail)
    (gas : 3 ≤ (s3 pre word x a base tail).gasAvailable.toNat) (depth : tail.length ≤ 1016) :
    EVM.X (fuel + 2) jumps (s3 pre word x a base tail) = EVM.X (fuel + 1) jumps (s4 pre word x a base tail) := by
  have atPC : (s3 pre word x a base tail).pc = UInt256.ofNat 214 := by
    simp only [s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s3 pre word x a base tail) = (.DUP5, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s3 pre word x a base tail).pc).getD _ = _
    rw [code, atPC, decode214]; rfl
  have check := dup5_check jumps (s3 pre word x a base tail)
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := transition4 fuel pre word x a base tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem continue5 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (word x a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 210)
    (stack : pre.stack = word :: x :: a :: base :: tail)
    (gas : 3 ≤ (s4 pre word x a base tail).gasAvailable.toNat) (depth : tail.length ≤ 1016) :
    EVM.X (fuel + 2) jumps (s4 pre word x a base tail) = EVM.X (fuel + 1) jumps (s5 pre word x a base tail) := by
  have atPC : (s4 pre word x a base tail).pc = UInt256.ofNat 215 := by
    simp only [s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s4 pre word x a base tail) = (.ADD, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s4 pre word x a base tail).pc).getD _ = _
    rw [code, atPC, decode215]; rfl
  have check := NativeSourceFieldStoreChecks.add jumps (s4 pre word x a base tail)
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := transition5 fuel pre word x a base tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem continue6 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (word x a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 210)
    (stack : pre.stack = word :: x :: a :: base :: tail)
    (gas : 3 ≤ (s5 pre word x a base tail).gasAvailable.toNat) (depth : tail.length ≤ 1016) :
    EVM.X (fuel + 2) jumps (s5 pre word x a base tail) = EVM.X (fuel + 1) jumps (s6 pre word x a base tail) := by
  have atPC : (s5 pre word x a base tail).pc = UInt256.ofNat 216 := by
    simp only [s5, s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s5 pre word x a base tail) = (.SWAP2, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s5 pre word x a base tail).pc).getD _ = _
    rw [code, atPC, decode216]; rfl
  have check := swap2_check jumps (s5 pre word x a base tail)
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [s5, s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := transition6 fuel pre word x a base tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem continue7 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (word x a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 210)
    (stack : pre.stack = word :: x :: a :: base :: tail)
    (gas : 3 ≤ (s6 pre word x a base tail).gasAvailable.toNat) (depth : tail.length ≤ 1016) :
    EVM.X (fuel + 2) jumps (s6 pre word x a base tail) = EVM.X (fuel + 1) jumps (s7 pre word x a base tail) := by
  have atPC : (s6 pre word x a base tail).pc = UInt256.ofNat 217 := by
    simp only [s6, s5, s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s6 pre word x a base tail) = (.DUP3, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s6 pre word x a base tail).pc).getD _ = _
    rw [code, atPC, decode217]; rfl
  have check := NativeSourceGuardChecks.dup3 jumps (s6 pre word x a base tail)
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [s6, s5, s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := transition7 fuel pre word x a base tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem gas_chain (pre : EVM.State) (word x a base : UInt256) (tail : Stack UInt256)
    (gas : 19 ≤ pre.gasAvailable.toNat) :
    (s1 pre word x a base tail).gasAvailable.toNat = pre.gasAvailable.toNat - 1 ∧
      (s2 pre word x a base tail).gasAvailable.toNat = pre.gasAvailable.toNat - 4 ∧
      (s3 pre word x a base tail).gasAvailable.toNat = pre.gasAvailable.toNat - 7 ∧
      (s4 pre word x a base tail).gasAvailable.toNat = pre.gasAvailable.toNat - 10 ∧
      (s5 pre word x a base tail).gasAvailable.toNat = pre.gasAvailable.toNat - 13 ∧
      (s6 pre word x a base tail).gasAvailable.toNat = pre.gasAvailable.toNat - 16 ∧
      (s7 pre word x a base tail).gasAvailable.toNat = pre.gasAvailable.toNat - 19 := by
  have g1 : (s1 pre word x a base tail).gasAvailable.toNat = pre.gasAvailable.toNat - 1 :=
    NativeSourceCheckedRejection.gas_sub _ 1 (by decide) (by omega)
  have g2 : (s2 pre word x a base tail).gasAvailable.toNat = (s1 pre word x a base tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g3 : (s3 pre word x a base tail).gasAvailable.toNat = (s2 pre word x a base tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g4 : (s4 pre word x a base tail).gasAvailable.toNat = (s3 pre word x a base tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g5 : (s5 pre word x a base tail).gasAvailable.toNat = (s4 pre word x a base tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g6 : (s6 pre word x a base tail).gasAvailable.toNat = (s5 pre word x a base tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g7 : (s7 pre word x a base tail).gasAvailable.toNat = (s6 pre word x a base tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  omega

theorem execute_prefix (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (word x a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 210)
    (stack : pre.stack = word :: x :: a :: base :: tail)
    (gas : 19 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1016) :
    EVM.X (fuel + 8) jumps pre = EVM.X (fuel + 1) jumps (s7 pre word x a base tail) := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := gas_chain pre word x a base tail gas
  rw [continue1 (fuel + 6) jumps pre word x a base tail code pc stack (by omega) depth]
  rw [continue2 (fuel + 5) jumps pre word x a base tail code pc stack (by omega) depth]
  rw [continue3 (fuel + 4) jumps pre word x a base tail code pc stack (by omega) depth]
  rw [continue4 (fuel + 3) jumps pre word x a base tail code pc stack (by omega) depth]
  rw [continue5 (fuel + 2) jumps pre word x a base tail code pc stack (by omega) depth]
  rw [continue6 (fuel + 1) jumps pre word x a base tail code pc stack (by omega) depth]
  rw [continue7 (fuel + 0) jumps pre word x a base tail code pc stack (by omega) depth]

theorem store_continue (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (offset word : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 218)
    (stack : pre.stack = offset :: word :: tail)
    (gas : memoryExpansionCost pre .MSTORE + 3 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1022) :
    EVM.X (fuel + 2) jumps pre = EVM.X (fuel + 1) jumps
      (mstorePost 3 (NativeSourceFieldStoreChecks.expanded pre) tail offset word) := by
  have decoded : decodeAt pre = (.MSTORE, none) := by
    unfold decodeAt; rw [code, pc, decode218]; rfl
  have check := NativeSourceFieldStoreChecks.mstore jumps pre gas (by simp only [stack, List.length_cons]; omega)
  exact X_succ_of_continue decoded check (step_MSTORE fuel 3 (NativeSourceFieldStoreChecks.expanded pre)
    tail offset word (by change pre.stack.pop2 = _; rw [stack]; rfl)) rfl

theorem execute (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (word x a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 210)
    (stack : pre.stack = word :: x :: a :: base :: tail)
    (gas : 22 + memoryExpansionCost (s7 pre word x a base tail) .MSTORE ≤ pre.gasAvailable.toNat)
    (depth : tail.length ≤ 1016) :
    EVM.X (fuel + 9) jumps pre = EVM.X (fuel + 1) jumps (stored pre word x a base tail) := by
  have charged := (gas_chain pre word x a base tail (by omega)).2.2.2.2.2.2
  have atPC : (s7 pre word x a base tail).pc = UInt256.ofNat 218 := by
    simp only [s7, s6, s5, s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  rw [execute_prefix (fuel + 1) jumps pre word x a base tail code pc stack (by omega) depth]
  exact store_continue fuel jumps _ _ _ _ code atPC rfl (by omega)
    (by simp only [List.length_cons]; omega)

end Compiler.Proofs.IRGeneration.NativeSourceLoanFieldStore



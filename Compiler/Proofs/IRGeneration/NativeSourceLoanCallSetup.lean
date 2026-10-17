import Compiler.Proofs.IRGeneration.NativeSourceMidnightDecodedStore

namespace Compiler.Proofs.IRGeneration.NativeSourceLoanCallSetup
open EvmYul EVM EVM.Proof

theorem immediate199 : NativeSourceAbiWrite.code.extract' 200 202 = ⟨#[0, 210]⟩ := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte0 : NativeSourceAbiWrite.code.data[200]? = some 0 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have byte1 : NativeSourceAbiWrite.code.data[201]? = some 210 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  apply ByteArray.ext
  simp only [ByteArray.extract', show (200 < 2^64 && 202 < 2^64) = true by decide, if_true, ByteArray.data_extract]
  apply Array.ext
  · simp only [Array.size_extract, size, ByteArray.size_data]; decide
  · intro index left right
    have bound : index < 2 := by simpa using right
    have cases : index = 0 ∨ index = 1 := by omega
    rcases cases with rfl | rfl
    · simp only [Array.getElem_extract, Nat.add_zero]
      exact Option.some.inj ((Array.getElem?_eq_getElem (by change 200 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte0)
    · simp only [Array.getElem_extract]
      exact Option.some.inj ((Array.getElem?_eq_getElem (by change 201 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte1)

theorem decode199 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 199) = some ((.Push .PUSH2), some (UInt256.ofNat 210, 2)) := by
  have byte : NativeSourceAbiWrite.code.get? 199 = some 97 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 199).toNat = 199 by decide, byte]
  change some (Operation.Push Operation.POp.PUSH2, some (uInt256OfByteArray (NativeSourceAbiWrite.code.extract' 200 202), 2)) = _
  rw [immediate199]
  decide

theorem immediate202 : NativeSourceAbiWrite.code.extract' 203 204 = ⟨#[68]⟩ := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte0 : NativeSourceAbiWrite.code.data[203]? = some 68 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  apply ByteArray.ext
  simp only [ByteArray.extract', show (203 < 2^64 && 204 < 2^64) = true by decide, if_true, ByteArray.data_extract]
  apply Array.ext
  · simp only [Array.size_extract, size, ByteArray.size_data]; decide
  · intro index left right
    have bound : index < 1 := by simpa using right
    have zero : index = 0 := by omega
    subst index
    simp only [Array.getElem_extract, Nat.add_zero]
    exact Option.some.inj ((Array.getElem?_eq_getElem (by change 203 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte0)

theorem decode202 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 202) = some ((.Push .PUSH1), some (UInt256.ofNat 68, 1)) := by
  have byte : NativeSourceAbiWrite.code.get? 202 = some 96 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 202).toNat = 202 by decide, byte]
  change some (Operation.Push Operation.POp.PUSH1, some (uInt256OfByteArray (NativeSourceAbiWrite.code.extract' 203 204), 1)) = _
  rw [immediate202]
  decide

theorem decode204 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 204) = some (.DUP4, none) := by
  have byte : NativeSourceAbiWrite.code.get? 204 = some 131 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 204).toNat = 204 by decide, byte]
  decide

theorem decode205 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 205) = some (.ADD, none) := by
  have byte : NativeSourceAbiWrite.code.get? 205 = some 1 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 205).toNat = 205 by decide, byte]
  decide

theorem immediate206 : NativeSourceAbiWrite.code.extract' 207 209 = ⟨#[3, 176]⟩ := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte0 : NativeSourceAbiWrite.code.data[207]? = some 3 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have byte1 : NativeSourceAbiWrite.code.data[208]? = some 176 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  apply ByteArray.ext
  simp only [ByteArray.extract', show (207 < 2^64 && 209 < 2^64) = true by decide, if_true, ByteArray.data_extract]
  apply Array.ext
  · simp only [Array.size_extract, size, ByteArray.size_data]; decide
  · intro index left right
    have bound : index < 2 := by simpa using right
    have cases : index = 0 ∨ index = 1 := by omega
    rcases cases with rfl | rfl
    · simp only [Array.getElem_extract, Nat.add_zero]
      exact Option.some.inj ((Array.getElem?_eq_getElem (by change 207 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte0)
    · simp only [Array.getElem_extract]
      exact Option.some.inj ((Array.getElem?_eq_getElem (by change 208 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte1)

theorem decode206 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 206) = some ((.Push .PUSH2), some (UInt256.ofNat 944, 2)) := by
  have byte : NativeSourceAbiWrite.code.get? 206 = some 97 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 206).toNat = 206 by decide, byte]
  change some (Operation.Push Operation.POp.PUSH2, some (uInt256OfByteArray (NativeSourceAbiWrite.code.extract' 207 209), 2)) = _
  rw [immediate206]
  decide

theorem decode209 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 209) = some (.JUMP, none) := by
  have byte : NativeSourceAbiWrite.code.get? 209 = some 86 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 209).toNat = 209 by decide, byte]
  decide

def s1 (pre : EVM.State) (x a base : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 pre).replaceStackAndIncrPC (UInt256.ofNat 210 :: x :: a :: base :: tail) 3

def s2 (pre : EVM.State) (x a base : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 (s1 pre x a base tail)).replaceStackAndIncrPC (UInt256.ofNat 68 :: UInt256.ofNat 210 :: x :: a :: base :: tail) 2

def s3 (pre : EVM.State) (x a base : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 (s2 pre x a base tail)).replaceStackAndIncrPC (a :: UInt256.ofNat 68 :: UInt256.ofNat 210 :: x :: a :: base :: tail)

def s4 (pre : EVM.State) (x a base : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 (s3 pre x a base tail)).replaceStackAndIncrPC ((a + UInt256.ofNat 68) :: UInt256.ofNat 210 :: x :: a :: base :: tail)

def s5 (pre : EVM.State) (x a base : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 (s4 pre x a base tail)).replaceStackAndIncrPC (UInt256.ofNat 944 :: (a + UInt256.ofNat 68) :: UInt256.ofNat 210 :: x :: a :: base :: tail) 3

def s6 (pre : EVM.State) (x a base : UInt256) (tail : Stack UInt256) :=
  { stepPre 8 (s5 pre x a base tail) with pc := UInt256.ofNat 944, stack := (a + UInt256.ofNat 68) :: UInt256.ofNat 210 :: x :: a :: base :: tail }

theorem transition1 (fuel : Nat) (pre : EVM.State) (x a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 199)
    (stack : pre.stack = x :: a :: base :: tail) :
    EVM.step (fuel + 1) 3 (some (decodeAt pre)) pre = .ok (s1 pre x a base tail) := by
  have atPC : pre.pc = UInt256.ofNat 199 := by
    exact pc
  have decoded : decodeAt pre = (.Push .PUSH2, some (UInt256.ofNat 210, 2)) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code pre.pc).getD _ = _
    rw [code, atPC, decode199]; rfl
  rw [decoded]
  change Except.ok ((stepPre 3 pre).replaceStackAndIncrPC (UInt256.ofNat 210 :: pre.stack) 3) = _
  rw [stack]; rfl

theorem transition2 (fuel : Nat) (pre : EVM.State) (x a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 199)
    (_stack : pre.stack = x :: a :: base :: tail) :
    EVM.step (fuel + 1) 3 (some (decodeAt (s1 pre x a base tail))) (s1 pre x a base tail) = .ok (s2 pre x a base tail) := by
  have atPC : (s1 pre x a base tail).pc = UInt256.ofNat 202 := by
    simp only [s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s1 pre x a base tail) = (.Push .PUSH1, some (UInt256.ofNat 68, 1)) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s1 pre x a base tail).pc).getD _ = _
    rw [code, atPC, decode202]; rfl
  rw [decoded]
  rfl

theorem transition3 (fuel : Nat) (pre : EVM.State) (x a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 199)
    (stack : pre.stack = x :: a :: base :: tail) :
    EVM.step (fuel + 1) 3 (some (decodeAt (s2 pre x a base tail))) (s2 pre x a base tail) = .ok (s3 pre x a base tail) := by
  have atPC : (s2 pre x a base tail).pc = UInt256.ofNat 204 := by
    simp only [s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s2 pre x a base tail) = (.DUP4, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s2 pre x a base tail).pc).getD _ = _
    rw [code, atPC, decode204]; rfl
  rw [decoded]
  change EvmYul.dup 4 (stepPre 3 (s2 pre x a base tail)) = _
  unfold EvmYul.dup
  simp only [s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack]
  rfl

theorem transition4 (fuel : Nat) (pre : EVM.State) (x a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 199)
    (stack : pre.stack = x :: a :: base :: tail) :
    EVM.step (fuel + 1) 3 (some (decodeAt (s3 pre x a base tail))) (s3 pre x a base tail) = .ok (s4 pre x a base tail) := by
  have atPC : (s3 pre x a base tail).pc = UInt256.ofNat 205 := by
    simp only [s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s3 pre x a base tail) = (.ADD, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s3 pre x a base tail).pc).getD _ = _
    rw [code, atPC, decode205]; rfl
  rw [decoded]
  change EvmYul.step (τ := .EVM) .ADD none (stepPre 3 (s3 pre x a base tail)) = _
  unfold EvmYul.step
  simp only [s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack]
  rfl

theorem transition5 (fuel : Nat) (pre : EVM.State) (x a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 199)
    (_stack : pre.stack = x :: a :: base :: tail) :
    EVM.step (fuel + 1) 3 (some (decodeAt (s4 pre x a base tail))) (s4 pre x a base tail) = .ok (s5 pre x a base tail) := by
  have atPC : (s4 pre x a base tail).pc = UInt256.ofNat 206 := by
    simp only [s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s4 pre x a base tail) = (.Push .PUSH2, some (UInt256.ofNat 944, 2)) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s4 pre x a base tail).pc).getD _ = _
    rw [code, atPC, decode206]; rfl
  rw [decoded]
  rfl

theorem transition6 (fuel : Nat) (pre : EVM.State) (x a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 199)
    (stack : pre.stack = x :: a :: base :: tail) :
    EVM.step (fuel + 1) 8 (some (decodeAt (s5 pre x a base tail))) (s5 pre x a base tail) = .ok (s6 pre x a base tail) := by
  have atPC : (s5 pre x a base tail).pc = UInt256.ofNat 209 := by
    simp only [s5, s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s5 pre x a base tail) = (.JUMP, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s5 pre x a base tail).pc).getD _ = _
    rw [code, atPC, decode209]; rfl
  rw [decoded]
  change EvmYul.step (τ := .EVM) .JUMP none (stepPre 8 (s5 pre x a base tail)) = _
  unfold EvmYul.step
  simp only [s5, s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack]
  rfl

theorem frame (pre : EVM.State) (x a base : UInt256) (tail : Stack UInt256) :
    (s6 pre x a base tail).pc = UInt256.ofNat 944 ∧
      (s6 pre x a base tail).stack = (a + UInt256.ofNat 68) :: UInt256.ofNat 210 :: x :: a :: base :: tail ∧
      (s6 pre x a base tail).toState = pre.toState ∧ (s6 pre x a base tail).memory = pre.memory := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem continue1 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (x a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 199)
    (stack : pre.stack = x :: a :: base :: tail)
    (gas : 3 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1017) :
    EVM.X (fuel + 2) jumps pre = EVM.X (fuel + 1) jumps (s1 pre x a base tail) := by
  have atPC : pre.pc = UInt256.ofNat 199 := by
    exact pc
  have decoded : decodeAt pre = (.Push .PUSH2, some (UInt256.ofNat 210, 2)) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code pre.pc).getD _ = _
    rw [code, atPC, decode199]; rfl
  have check := NativeSourceCheckedPushRejection.push2_check jumps pre
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := transition1 fuel pre x a base tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem continue2 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (x a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 199)
    (stack : pre.stack = x :: a :: base :: tail)
    (gas : 3 ≤ (s1 pre x a base tail).gasAvailable.toNat) (depth : tail.length ≤ 1017) :
    EVM.X (fuel + 2) jumps (s1 pre x a base tail) = EVM.X (fuel + 1) jumps (s2 pre x a base tail) := by
  have atPC : (s1 pre x a base tail).pc = UInt256.ofNat 202 := by
    simp only [s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s1 pre x a base tail) = (.Push .PUSH1, some (UInt256.ofNat 68, 1)) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s1 pre x a base tail).pc).getD _ = _
    rw [code, atPC, decode202]; rfl
  have check := NativeSourceGuardChecks.push1 jumps (s1 pre x a base tail)
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := transition2 fuel pre x a base tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem continue3 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (x a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 199)
    (stack : pre.stack = x :: a :: base :: tail)
    (gas : 3 ≤ (s2 pre x a base tail).gasAvailable.toNat) (depth : tail.length ≤ 1017) :
    EVM.X (fuel + 2) jumps (s2 pre x a base tail) = EVM.X (fuel + 1) jumps (s3 pre x a base tail) := by
  have atPC : (s2 pre x a base tail).pc = UInt256.ofNat 204 := by
    simp only [s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s2 pre x a base tail) = (.DUP4, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s2 pre x a base tail).pc).getD _ = _
    rw [code, atPC, decode204]; rfl
  have check := NativeSourceFieldStoreChecks.dup4 jumps (s2 pre x a base tail)
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := transition3 fuel pre x a base tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem continue4 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (x a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 199)
    (stack : pre.stack = x :: a :: base :: tail)
    (gas : 3 ≤ (s3 pre x a base tail).gasAvailable.toNat) (depth : tail.length ≤ 1017) :
    EVM.X (fuel + 2) jumps (s3 pre x a base tail) = EVM.X (fuel + 1) jumps (s4 pre x a base tail) := by
  have atPC : (s3 pre x a base tail).pc = UInt256.ofNat 205 := by
    simp only [s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s3 pre x a base tail) = (.ADD, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s3 pre x a base tail).pc).getD _ = _
    rw [code, atPC, decode205]; rfl
  have check := NativeSourceFieldStoreChecks.add jumps (s3 pre x a base tail)
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := transition4 fuel pre x a base tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem continue5 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (x a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 199)
    (stack : pre.stack = x :: a :: base :: tail)
    (gas : 3 ≤ (s4 pre x a base tail).gasAvailable.toNat) (depth : tail.length ≤ 1017) :
    EVM.X (fuel + 2) jumps (s4 pre x a base tail) = EVM.X (fuel + 1) jumps (s5 pre x a base tail) := by
  have atPC : (s4 pre x a base tail).pc = UInt256.ofNat 206 := by
    simp only [s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s4 pre x a base tail) = (.Push .PUSH2, some (UInt256.ofNat 944, 2)) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s4 pre x a base tail).pc).getD _ = _
    rw [code, atPC, decode206]; rfl
  have check := NativeSourceCheckedPushRejection.push2_check jumps (s4 pre x a base tail)
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := transition5 fuel pre x a base tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem continue6 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (x a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 199)
    (stack : pre.stack = x :: a :: base :: tail)
    (gas : 8 ≤ (s5 pre x a base tail).gasAvailable.toNat) (depth : tail.length ≤ 1017)
    (destination : UInt256.ofNat 944 ∈ jumps) :
    EVM.X (fuel + 2) jumps (s5 pre x a base tail) = EVM.X (fuel + 1) jumps (s6 pre x a base tail) := by
  have atPC : (s5 pre x a base tail).pc = UInt256.ofNat 209 := by
    simp only [s5, s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s5 pre x a base tail) = (.JUMP, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s5 pre x a base tail).pc).getD _ = _
    rw [code, atPC, decode209]; rfl
  have lookup : EVM.X.notIn (s5 pre x a base tail).stack[0]? jumps = false := by
    change (!jumps.contains (UInt256.ofNat 944)) = false
    rw [NativeSourceJumpChecks.contains_of_mem jumps _ destination]; rfl
  have check := NativeSourceCheckedReturn.jump_check jumps (s5 pre x a base tail)
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [s5, s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack, List.length_cons]; omega) lookup
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := transition6 fuel pre x a base tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem gas_chain (pre : EVM.State) (x a base : UInt256) (tail : Stack UInt256)
    (gas : 23 ≤ pre.gasAvailable.toNat) :
    (s1 pre x a base tail).gasAvailable.toNat = pre.gasAvailable.toNat - 3 ∧
      (s2 pre x a base tail).gasAvailable.toNat = pre.gasAvailable.toNat - 6 ∧
      (s3 pre x a base tail).gasAvailable.toNat = pre.gasAvailable.toNat - 9 ∧
      (s4 pre x a base tail).gasAvailable.toNat = pre.gasAvailable.toNat - 12 ∧
      (s5 pre x a base tail).gasAvailable.toNat = pre.gasAvailable.toNat - 15 ∧
      (s6 pre x a base tail).gasAvailable.toNat = pre.gasAvailable.toNat - 23 := by
  have g1 : (s1 pre x a base tail).gasAvailable.toNat = pre.gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g2 : (s2 pre x a base tail).gasAvailable.toNat = (s1 pre x a base tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g3 : (s3 pre x a base tail).gasAvailable.toNat = (s2 pre x a base tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g4 : (s4 pre x a base tail).gasAvailable.toNat = (s3 pre x a base tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g5 : (s5 pre x a base tail).gasAvailable.toNat = (s4 pre x a base tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g6 : (s6 pre x a base tail).gasAvailable.toNat = (s5 pre x a base tail).gasAvailable.toNat - 8 :=
    NativeSourceCheckedRejection.gas_sub _ 8 (by decide) (by omega)
  omega

theorem execute (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (x a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 199)
    (stack : pre.stack = x :: a :: base :: tail)
    (gas : 23 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1017)
    (destination : UInt256.ofNat 944 ∈ jumps) :
    EVM.X (fuel + 7) jumps pre = EVM.X (fuel + 1) jumps (s6 pre x a base tail) := by
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := gas_chain pre x a base tail gas
  rw [continue1 (fuel + 5) jumps pre x a base tail code pc stack (by omega) depth]
  rw [continue2 (fuel + 4) jumps pre x a base tail code pc stack (by omega) depth]
  rw [continue3 (fuel + 3) jumps pre x a base tail code pc stack (by omega) depth]
  rw [continue4 (fuel + 2) jumps pre x a base tail code pc stack (by omega) depth]
  rw [continue5 (fuel + 1) jumps pre x a base tail code pc stack (by omega) depth]
  rw [continue6 (fuel + 0) jumps pre x a base tail code pc stack (by omega) depth destination]

end Compiler.Proofs.IRGeneration.NativeSourceLoanCallSetup



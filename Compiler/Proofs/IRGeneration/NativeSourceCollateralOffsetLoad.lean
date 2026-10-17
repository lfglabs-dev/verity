import Compiler.Proofs.IRGeneration.NativeSourceGrowingMemoryFrame

namespace Compiler.Proofs.IRGeneration.NativeSourceCollateralOffsetLoad
open EvmYul EVM EVM.Proof Compiler.Proofs.YulGeneration.Backends

theorem immediate219 : NativeSourceAbiWrite.code.extract' 220 221 = ⟨#[100]⟩ := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[220]? = some 100 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  apply ByteArray.ext
  simp only [ByteArray.extract', show (220 < 2^64 && 221 < 2^64) = true by decide, if_true, ByteArray.data_extract]
  apply Array.ext
  · simp only [Array.size_extract, size, ByteArray.size_data]; decide
  · intro index left right
    have bound : index < 1 := by simpa using right
    have zero : index = 0 := by omega
    subst index
    simp only [Array.getElem_extract, Nat.add_zero]
    exact Option.some.inj ((Array.getElem?_eq_getElem (by change 220 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte)

theorem decode219 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 219) = some (.Push .PUSH1, some (UInt256.ofNat 100, 1)) := by
  have byte : NativeSourceAbiWrite.code.get? 219 = some 96 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 219).toNat = 219 by decide, byte]
  change some (Operation.Push Operation.POp.PUSH1, some (uInt256OfByteArray (NativeSourceAbiWrite.code.extract' 220 221), 1)) = _
  rw [immediate219]
  decide

theorem decode221 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 221) = some (.DUP4, none) := by
  have byte : NativeSourceAbiWrite.code.get? 221 = some 131 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 221).toNat = 221 by decide, byte]
  decide

theorem decode222 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 222) = some (.ADD, none) := by
  have byte : NativeSourceAbiWrite.code.get? 222 = some 1 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 222).toNat = 222 by decide, byte]
  decide

theorem decode223 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 223) = some (.CALLDATALOAD, none) := by
  have byte : NativeSourceAbiWrite.code.get? 223 = some 53 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 223).toNat = 223 by decide, byte]
  decide

def s1 (pre : EVM.State) (x y a base : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 pre).replaceStackAndIncrPC (UInt256.ofNat 100 :: x :: y :: a :: base :: tail) 2

def s2 (pre : EVM.State) (x y a base : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 (s1 pre x y a base tail)).replaceStackAndIncrPC (a :: UInt256.ofNat 100 :: x :: y :: a :: base :: tail)

def s3 (pre : EVM.State) (x y a base : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 (s2 pre x y a base tail)).replaceStackAndIncrPC ((a + UInt256.ofNat 100) :: x :: y :: a :: base :: tail)

def s4 (pre : EVM.State) (x y a base : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 (s3 pre x y a base tail)).replaceStackAndIncrPC (pre.toState.calldataload (a + UInt256.ofNat 100) :: x :: y :: a :: base :: tail)

theorem transition1 (fuel : Nat) (pre : EVM.State) (x y a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 219)
    (stack : pre.stack = x :: y :: a :: base :: tail) :
    EVM.step (fuel + 1) 3 (some (decodeAt pre)) pre = .ok (s1 pre x y a base tail) := by
  have atPC : pre.pc = UInt256.ofNat 219 := by
    exact pc
  have decoded : decodeAt pre = (.Push .PUSH1, some (UInt256.ofNat 100, 1)) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code pre.pc).getD _ = _
    rw [code, atPC, decode219]; rfl
  rw [decoded]
  change Except.ok ((stepPre 3 pre).replaceStackAndIncrPC (UInt256.ofNat 100 :: pre.stack) 2) = _
  rw [stack]; rfl

theorem continue1 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State) (x y a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 219)
    (stack : pre.stack = x :: y :: a :: base :: tail)
    (gas : 3 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1018) :
    EVM.X (fuel + 2) jumps pre = EVM.X (fuel + 1) jumps (s1 pre x y a base tail) := by
  have atPC : pre.pc = UInt256.ofNat 219 := by
    exact pc
  have decoded : decodeAt pre = (.Push .PUSH1, some (UInt256.ofNat 100, 1)) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code pre.pc).getD _ = _
    rw [code, atPC, decode219]; rfl
  have check := NativeSourceGuardChecks.push1 jumps pre
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := transition1 fuel pre x y a base tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem transition2 (fuel : Nat) (pre : EVM.State) (x y a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 219)
    (stack : pre.stack = x :: y :: a :: base :: tail) :
    EVM.step (fuel + 1) 3 (some (decodeAt (s1 pre x y a base tail))) (s1 pre x y a base tail) = .ok (s2 pre x y a base tail) := by
  have atPC : (s1 pre x y a base tail).pc = UInt256.ofNat 221 := by
    simp only [s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s1 pre x y a base tail) = (.DUP4, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s1 pre x y a base tail).pc).getD _ = _
    rw [code, atPC, decode221]; rfl
  rw [decoded]
  change EvmYul.dup 4 (stepPre 3 (s1 pre x y a base tail)) = _
  unfold EvmYul.dup
  simp only [s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack]
  rfl

theorem continue2 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State) (x y a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 219)
    (stack : pre.stack = x :: y :: a :: base :: tail)
    (gas : 3 ≤ (s1 pre x y a base tail).gasAvailable.toNat) (depth : tail.length ≤ 1018) :
    EVM.X (fuel + 2) jumps (s1 pre x y a base tail) = EVM.X (fuel + 1) jumps (s2 pre x y a base tail) := by
  have atPC : (s1 pre x y a base tail).pc = UInt256.ofNat 221 := by
    simp only [s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s1 pre x y a base tail) = (.DUP4, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s1 pre x y a base tail).pc).getD _ = _
    rw [code, atPC, decode221]; rfl
  have check := NativeSourceFieldStoreChecks.dup4 jumps (s1 pre x y a base tail)
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := transition2 fuel pre x y a base tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem transition3 (fuel : Nat) (pre : EVM.State) (x y a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 219)
    (stack : pre.stack = x :: y :: a :: base :: tail) :
    EVM.step (fuel + 1) 3 (some (decodeAt (s2 pre x y a base tail))) (s2 pre x y a base tail) = .ok (s3 pre x y a base tail) := by
  have atPC : (s2 pre x y a base tail).pc = UInt256.ofNat 222 := by
    simp only [s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s2 pre x y a base tail) = (.ADD, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s2 pre x y a base tail).pc).getD _ = _
    rw [code, atPC, decode222]; rfl
  rw [decoded]
  change EvmYul.step (τ := .EVM) .ADD none (stepPre 3 (s2 pre x y a base tail)) = _
  unfold EvmYul.step
  simp only [s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack]
  rfl

theorem continue3 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State) (x y a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 219)
    (stack : pre.stack = x :: y :: a :: base :: tail)
    (gas : 3 ≤ (s2 pre x y a base tail).gasAvailable.toNat) (depth : tail.length ≤ 1018) :
    EVM.X (fuel + 2) jumps (s2 pre x y a base tail) = EVM.X (fuel + 1) jumps (s3 pre x y a base tail) := by
  have atPC : (s2 pre x y a base tail).pc = UInt256.ofNat 222 := by
    simp only [s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s2 pre x y a base tail) = (.ADD, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s2 pre x y a base tail).pc).getD _ = _
    rw [code, atPC, decode222]; rfl
  have check := NativeSourceFieldStoreChecks.add jumps (s2 pre x y a base tail)
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := transition3 fuel pre x y a base tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem transition4 (fuel : Nat) (pre : EVM.State) (x y a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 219)
    (stack : pre.stack = x :: y :: a :: base :: tail) :
    EVM.step (fuel + 1) 3 (some (decodeAt (s3 pre x y a base tail))) (s3 pre x y a base tail) = .ok (s4 pre x y a base tail) := by
  have atPC : (s3 pre x y a base tail).pc = UInt256.ofNat 223 := by
    simp only [s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s3 pre x y a base tail) = (.CALLDATALOAD, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s3 pre x y a base tail).pc).getD _ = _
    rw [code, atPC, decode223]; rfl
  rw [decoded]
  change EvmYul.step (τ := .EVM) .CALLDATALOAD none (stepPre 3 (s3 pre x y a base tail)) = _
  unfold EvmYul.step
  simp only [s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack]
  rfl

theorem continue4 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State) (x y a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 219)
    (stack : pre.stack = x :: y :: a :: base :: tail)
    (gas : 3 ≤ (s3 pre x y a base tail).gasAvailable.toNat) (depth : tail.length ≤ 1018) :
    EVM.X (fuel + 2) jumps (s3 pre x y a base tail) = EVM.X (fuel + 1) jumps (s4 pre x y a base tail) := by
  have atPC : (s3 pre x y a base tail).pc = UInt256.ofNat 223 := by
    simp only [s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s3 pre x y a base tail) = (.CALLDATALOAD, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s3 pre x y a base tail).pc).getD _ = _
    rw [code, atPC, decode223]; rfl
  have check := NativeSourceCheckedInputRejection.load_check jumps (s3 pre x y a base tail)
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := transition4 fuel pre x y a base tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem gas_chain (pre : EVM.State) (x y a base : UInt256) (tail : Stack UInt256)
    (gas : 12 ≤ pre.gasAvailable.toNat) :
    (s1 pre x y a base tail).gasAvailable.toNat = pre.gasAvailable.toNat - 3 ∧
      (s2 pre x y a base tail).gasAvailable.toNat = pre.gasAvailable.toNat - 6 ∧
      (s3 pre x y a base tail).gasAvailable.toNat = pre.gasAvailable.toNat - 9 ∧
      (s4 pre x y a base tail).gasAvailable.toNat = pre.gasAvailable.toNat - 12 := by
  have g1 : (s1 pre x y a base tail).gasAvailable.toNat = pre.gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g2 : (s2 pre x y a base tail).gasAvailable.toNat = (s1 pre x y a base tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g3 : (s3 pre x y a base tail).gasAvailable.toNat = (s2 pre x y a base tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g4 : (s4 pre x y a base tail).gasAvailable.toNat = (s3 pre x y a base tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  omega

theorem execute (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (x y a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 219)
    (stack : pre.stack = x :: y :: a :: base :: tail)
    (gas : 12 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1018) :
    EVM.X (fuel + 5) jumps pre = EVM.X (fuel + 1) jumps (s4 pre x y a base tail) := by
  obtain ⟨g1, g2, g3, g4⟩ := gas_chain pre x y a base tail gas
  rw [continue1 (fuel + 3) jumps pre x y a base tail code pc stack (by omega) depth]
  rw [continue2 (fuel + 2) jumps pre x y a base tail code pc stack (by omega) depth]
  rw [continue3 (fuel + 1) jumps pre x y a base tail code pc stack (by omega) depth]
  rw [continue4 (fuel + 0) jumps pre x y a base tail code pc stack (by omega) depth]

theorem frame (pre : EVM.State) (x y a base : UInt256) (tail : Stack UInt256) :
    (s4 pre x y a base tail).stack = pre.toState.calldataload (a + UInt256.ofNat 100) :: x :: y :: a :: base :: tail ∧
      (s4 pre x y a base tail).toState = pre.toState ∧ (s4 pre x y a base tail).memory = pre.memory := by
  exact ⟨rfl, rfl, rfl⟩

theorem canonical_offset (pre : EVM.State) (x y base : UInt256) (tail : Stack UInt256)
    (selector key value : Nat) (market : NativeSourceMarketCalldata.Market)
    (encoded : pre.executionEnv.calldata = StateBridge.calldataToByteArray selector
      (NativeSourceMarketCalldata.arguments market key value)) :
    (s4 pre x y (UInt256.ofNat 96) base tail).stack =
      UInt256.ofNat 256 :: x :: y :: UInt256.ofNat 96 :: base :: tail := by
  rw [(frame pre x y (UInt256.ofNat 96) base tail).1,
    show UInt256.ofNat 96 + UInt256.ofNat 100 = UInt256.ofNat 196 by decide]
  have loaded := (NativeSourceMarketCalldata.header pre selector key value market encoded).2.2.2.1
  have value : (pre.toState.calldataload (UInt256.ofNat 196)).toNat = 256 := by
    exact loaded.trans (by decide)
  rw [NativeSourceMidnightDecodedStore.word_of_nat _ 256 value]

end Compiler.Proofs.IRGeneration.NativeSourceCollateralOffsetLoad


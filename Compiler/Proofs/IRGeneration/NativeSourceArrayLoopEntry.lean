import Compiler.Proofs.IRGeneration.NativeSourceArrayCalldataOutcome

namespace Compiler.Proofs.IRGeneration.NativeSourceArrayLoopEntry
open EvmYul EVM EVM.Proof

theorem immediate319 : NativeSourceAbiWrite.code.extract' 320 321 = ⟨#[36]⟩ := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[320]? = some 36 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  apply ByteArray.ext
  simp only [ByteArray.extract', show (320 < 2^64 && 321 < 2^64) = true by decide, if_true, ByteArray.data_extract]
  apply Array.ext
  · simp only [Array.size_extract, size, ByteArray.size_data]; decide
  · intro index left right
    have zero : index = 0 := by simpa using right
    subst index
    simp only [Array.getElem_extract, Nat.add_zero]
    exact Option.some.inj ((Array.getElem?_eq_getElem (by change 320 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte)

theorem decode319 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 319) = some (.Push .PUSH1, some (UInt256.ofNat 36, 1)) := by
  have byte : NativeSourceAbiWrite.code.get? 319 = some 96 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 319).toNat = 319 by decide, byte]
  change some (Operation.Push Operation.POp.PUSH1, some (uInt256OfByteArray (NativeSourceAbiWrite.code.extract' 320 321), 1)) = _
  rw [immediate319]
  decide

theorem decode321 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 321) = some (.ADD, none) := by
  have byte : NativeSourceAbiWrite.code.get? 321 = some 1 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 321).toNat = 321 by decide, byte]
  decide

theorem decode322 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 322) = some (.SWAP2, none) := by
  have byte : NativeSourceAbiWrite.code.get? 322 = some 145 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 322).toNat = 322 by decide, byte]
  decide

theorem decode323 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 323) = some (.JUMPDEST, none) := by
  have byte : NativeSourceAbiWrite.code.get? 323 = some 91 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 323).toNat = 323 by decide, byte]
  decide

theorem continue319 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 319)
    (stack : pre.stack = tail) (gas : 3 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1023) :
    EVM.X (fuel + 2) jumps pre =
      EVM.X (fuel + 1) jumps ((stepPre 3 pre).replaceStackAndIncrPC (UInt256.ofNat 36 :: tail) 2) := by
  have decoded : decodeAt pre = (.Push .PUSH1, some (UInt256.ofNat 36, 1)) := by
    unfold decodeAt; rw [code, pc, decode319]; rfl
  have check := NativeSourceGuardChecks.push1 jumps pre
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [stack]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step : EVM.step (fuel + 1) 3 (some (.Push .PUSH1, some (UInt256.ofNat 36, 1))) pre =
      .ok ((stepPre 3 pre).replaceStackAndIncrPC (UInt256.ofNat 36 :: tail) 2) := by
    change Except.ok ((stepPre 3 pre).replaceStackAndIncrPC (_ :: pre.stack) _) = _
    rw [stack]
  exact X_succ_of_continue decoded check step rfl

theorem continue321 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State) (a b : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 321)
    (stack : pre.stack = a :: b :: tail) (gas : 3 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1022) :
    EVM.X (fuel + 2) jumps pre =
      EVM.X (fuel + 1) jumps ((stepPre 3 pre).replaceStackAndIncrPC ((a + b) :: tail) 1) := by
  have decoded : decodeAt pre = (.ADD, none) := by
    unfold decodeAt; rw [code, pc, decode321]; rfl
  have check := NativeSourceFieldStoreChecks.add jumps pre
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step : EVM.step (fuel + 1) 3 (some (.ADD, none)) pre =
      .ok ((stepPre 3 pre).replaceStackAndIncrPC ((a + b) :: tail) 1) := by
    change EVM.execBinOp UInt256.add (stepPre 3 pre) = _
    unfold EVM.execBinOp
    simp only [stepPre, stack]
    rfl
  exact X_succ_of_continue decoded check step rfl

theorem continue322 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State) (a b c : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 322)
    (stack : pre.stack = a :: b :: c :: tail) (gas : 3 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1021) :
    EVM.X (fuel + 2) jumps pre =
      EVM.X (fuel + 1) jumps ((stepPre 3 pre).replaceStackAndIncrPC (c :: b :: a :: tail) 1) := by
  have decoded : decodeAt pre = (.SWAP2, none) := by
    unfold decodeAt; rw [code, pc, decode322]; rfl
  have check := NativeSourceLoanFieldStore.swap2_check jumps pre
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step : EVM.step (fuel + 1) 3 (some (.SWAP2, none)) pre =
      .ok ((stepPre 3 pre).replaceStackAndIncrPC (c :: b :: a :: tail) 1) := by
    change EvmYul.swap 2 (stepPre 3 pre) = _
    unfold EvmYul.swap
    simp only [stepPre, stack]
    rfl
  exact X_succ_of_continue decoded check step rfl

theorem continue323 (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 323)
    (gas : 1 ≤ pre.gasAvailable.toNat) (depth : pre.stack.length ≤ 1024) :
    EVM.X (fuel + 2) jumps pre = EVM.X (fuel + 1) jumps ((stepPre 1 pre).incrPC) := by
  have decoded : decodeAt pre = (.JUMPDEST, none) := by
    unfold decodeAt; rw [code, pc, decode323]; rfl
  have check := Z_JUMPDEST jumps pre
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word, GasConstants.Gjumpdest] using gas) depth
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  exact X_succ_of_continue decoded check (step_JUMPDEST fuel 1 pre) (H_JUMPDEST _)

end Compiler.Proofs.IRGeneration.NativeSourceArrayLoopEntry

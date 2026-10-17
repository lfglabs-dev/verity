import Compiler.Proofs.IRGeneration.NativeSourceMappingExecution

namespace Compiler.Proofs.IRGeneration.NativeSourceStorageBytecode
open EvmYul

/-- Storage decoding is determined by the actual byte at the machine PC. -/
theorem storage_decode (machine : EVM.State) (transient : Bool)
    (fetched : machine.executionEnv.code.get? machine.pc.toNat =
      some (if transient then 0x5d else 0x55)) :
    EVM.Proof.decodeAt machine = ((if transient then .TSTORE else .SSTORE), none) := by
  cases transient <;> simp only [Bool.false_eq_true, if_false, if_true] at fetched ⊢
  all_goals simp only [EVM.Proof.decodeAt, EVM.decode, fetched, Bind.bind, Option.bind]
  all_goals rfl

/-- PUSH32 reads the actual following bytes, rather than a supplied operand oracle. -/
theorem push32_decode (machine : EVM.State)
    (fetched : machine.executionEnv.code.get? machine.pc.toNat = some 0x7f) :
    EVM.Proof.decodeAt machine = (.Push .PUSH32, some
      (uInt256OfByteArray (machine.executionEnv.code.extract' machine.pc.toNat.succ
        (machine.pc.toNat.succ + 32)), 32)) := by
  simp only [EVM.Proof.decodeAt, EVM.decode, fetched, Bind.bind, Option.bind,
    EVM.parseInstr, EVM.argOnNBytesOfInstr, beq_iff_eq, OfNat.ofNat,
    Option.getD]
  rfl

/-- Exact primitive PUSH32 state, retaining real execution counting and gas. -/
theorem step_push32 (machine : EVM.State) (value : UInt256) (cost : Nat) :
    EVM.step 1 cost (some (.Push .PUSH32, some (value, 32))) machine =
      .ok ({ machine with
        execLength := machine.execLength + 1
        gasAvailable := machine.gasAvailable - UInt256.ofNat cost }.replaceStackAndIncrPC
          (value :: machine.stack) (pcΔ := 33)) := by
  rfl

/-- A real successful checked PUSH32 derives its stack, PC and code frame. -/
theorem checked_push32 (machine after : EVM.State) (value : UInt256)
    (success : CreationCaller.checkedStep machine (.Push .PUSH32) (some (value, 32)) = .ok after) :
    after.stack = value :: machine.stack ∧ after.pc = machine.pc + UInt256.ofNat 33 ∧
      after.toState = machine.toState := by
  have stepped := NativeCreationStorageOpcodes.checkedStep_delegates machine after
    (.Push .PUSH32) (some (value, 32)) success
  dsimp only at stepped
  rw [step_push32] at stepped
  cases Except.ok.inj stepped
  exact ⟨rfl, rfl, rfl⟩

/-- The decoded checked step gets its operand solely from the current code. -/
theorem checked_push32_bytes (machine after : EVM.State)
    (fetched : machine.executionEnv.code.get? machine.pc.toNat = some 0x7f)
    (success : CreationCaller.checkedStep machine (EVM.Proof.decodeAt machine).1
      (EVM.Proof.decodeAt machine).2 = .ok after) :
    after.stack = uInt256OfByteArray (machine.executionEnv.code.extract' machine.pc.toNat.succ
      (machine.pc.toNat.succ + 32)) :: machine.stack ∧
      after.pc = machine.pc + UInt256.ofNat 33 ∧ after.toState = machine.toState := by
  rw [push32_decode machine fetched] at success
  exact checked_push32 machine after _ success

/-- A byte-authenticated checked PUSH32 is the actual native iterator step. -/
theorem push32_native_x (machine after : EVM.State) (fuel : Nat)
    (bounded : machine.executionEnv.code.size < UInt256.size)
    (fetched : machine.executionEnv.code.get? machine.pc.toNat = some 0x7f)
    (success : CreationCaller.checkedStep machine (EVM.Proof.decodeAt machine).1
      (EVM.Proof.decodeAt machine).2 = .ok after) :
    EVM.X (fuel + 2) (EVM.D_J machine.executionEnv.code (UInt256.ofNat 0)) machine =
      EVM.X (fuel + 1) (EVM.D_J machine.executionEnv.code (UInt256.ofNat 0)) after := by
  have decoded := push32_decode machine fetched
  rw [decoded] at success
  exact NativePairedCallerChecks.checked_native_x fuel machine after _ _ bounded
    (by simp [CreationCaller.supported, Operation.isPush]) decoded success

/-- Two actual byte-authenticated PUSH32 steps derive both storage operands.
The intermediate state is produced by checked execution; no final-stack premise. -/
theorem two_push32_stack (initial middle final : EVM.State)
    (firstByte : initial.executionEnv.code.get? initial.pc.toNat = some 0x7f)
    (secondByte : middle.executionEnv.code.get? middle.pc.toNat = some 0x7f)
    (first : CreationCaller.checkedStep initial (EVM.Proof.decodeAt initial).1
      (EVM.Proof.decodeAt initial).2 = .ok middle)
    (second : CreationCaller.checkedStep middle (EVM.Proof.decodeAt middle).1
      (EVM.Proof.decodeAt middle).2 = .ok final) :
    final.stack = uInt256OfByteArray (initial.executionEnv.code.extract'
      (initial.pc + UInt256.ofNat 33).toNat.succ
      ((initial.pc + UInt256.ofNat 33).toNat.succ + 32)) ::
      uInt256OfByteArray (initial.executionEnv.code.extract' initial.pc.toNat.succ
        (initial.pc.toNat.succ + 32)) :: initial.stack ∧
      final.pc = (initial.pc + UInt256.ofNat 33) + UInt256.ofNat 33 ∧
      final.toState = initial.toState := by
  obtain ⟨firstStack, firstPc, firstWorld⟩ := checked_push32_bytes initial middle firstByte first
  obtain ⟨secondStack, secondPc, secondWorld⟩ := checked_push32_bytes middle final secondByte second
  have code : middle.executionEnv.code = initial.executionEnv.code :=
    congrArg (fun state : State .EVM => state.executionEnv.code) firstWorld
  exact ⟨by simpa only [firstStack, code, firstPc] using secondStack,
    by simpa only [firstPc] using secondPc, secondWorld.trans firstWorld⟩

/-- The same two byte-authenticated steps compose in the real native iterator. -/
theorem two_push32_native_x (initial middle final : EVM.State) (fuel : Nat)
    (bounded : initial.executionEnv.code.size < UInt256.size)
    (firstByte : initial.executionEnv.code.get? initial.pc.toNat = some 0x7f)
    (secondByte : middle.executionEnv.code.get? middle.pc.toNat = some 0x7f)
    (first : CreationCaller.checkedStep initial (EVM.Proof.decodeAt initial).1
      (EVM.Proof.decodeAt initial).2 = .ok middle)
    (second : CreationCaller.checkedStep middle (EVM.Proof.decodeAt middle).1
      (EVM.Proof.decodeAt middle).2 = .ok final) :
    EVM.X (fuel + 3) (EVM.D_J initial.executionEnv.code (UInt256.ofNat 0)) initial =
      EVM.X (fuel + 1) (EVM.D_J initial.executionEnv.code (UInt256.ofNat 0)) final := by
  have frame := (checked_push32_bytes initial middle firstByte first).2.2
  have code : middle.executionEnv.code = initial.executionEnv.code :=
    congrArg (fun state : State .EVM => state.executionEnv.code) frame
  have nextBound : middle.executionEnv.code.size < UInt256.size := by rw [code]; exact bounded
  have firstX := push32_native_x initial middle (fuel + 1) bounded firstByte first
  have secondX := push32_native_x middle final fuel nextBound secondByte second
  rw [code] at secondX
  exact firstX.trans secondX

end Compiler.Proofs.IRGeneration.NativeSourceStorageBytecode

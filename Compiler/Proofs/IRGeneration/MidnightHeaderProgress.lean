import Compiler.Proofs.IRGeneration.MidnightHeaderDecode

/-! Native primitive PC facts for the constructor termination rank. -/
namespace Compiler.Proofs.IRGeneration.NativeInitcodeFrames
open EvmYul

private theorem binary_pc (op : Primop.Binary) (before after : EVM.State)
    (success : EVM.execBinOp op before = .ok after) :
    after.pc = before.pc + UInt256.ofNat 1 := by
  unfold EVM.execBinOp at success
  split at success
  · cases success; rfl
  · cases success

private theorem environment_pc (op : ExecutionEnv .EVM → UInt256) (before after : EVM.State)
    (success : EVM.executionEnvOp op before = .ok after) :
    after.pc = before.pc + UInt256.ofNat 1 := by
  unfold EVM.executionEnvOp at success
  cases success
  rfl

private theorem copy_pc
    (op : SharedState .EVM → UInt256 → UInt256 → UInt256 → SharedState .EVM)
    (before after : EVM.State)
    (success : EVM.ternaryCopyOp op before = .ok after) :
    after.pc = before.pc + UInt256.ofNat 1 := by
  unfold EVM.ternaryCopyOp at success
  split at success
  · cases success; rfl
  · cases success

/-- Header fixed-width nonhalting instructions advance exactly one byte. -/
theorem header_fixed_step_pc (op : Operation .EVM) (before after : EVM.State)
    (arg : Option (UInt256 × Nat)) (gasCost : Nat)
    (allowed : op ∈ [.SIGNEXTEND, .CODESIZE, .SUB, .DUP1, .CODECOPY, .Push .PUSH0])
    (success : EVM.step 1 gasCost (some (op, arg)) before = .ok after) :
    after.pc = before.pc + UInt256.ofNat 1 := by
  let charged := { before with
    gasAvailable := before.gasAvailable - UInt256.ofNat gasCost
    execLength := before.execLength + 1 }
  simp only [List.mem_cons, List.not_mem_nil, or_false] at allowed
  rcases allowed with rfl | rfl | rfl | rfl | rfl | rfl
  · exact binary_pc _ charged after success
  · exact environment_pc _ charged after success
  · exact binary_pc _ charged after success
  · change EvmYul.dup 1 charged = .ok after at success
    unfold EvmYul.dup at success
    dsimp only at success
    split at success
    · cases success; rfl
    · cases success
  · exact copy_pc _ charged after success
  · change Except.ok _ = Except.ok after at success
    cases success
    rfl

/-- The real PUSH1 has the decoder-provided argument width, without evaluating
its word value or assuming a particular payload. -/
theorem push1_step_pc (before after : EVM.State) (word : UInt256) (gasCost : Nat)
    (success : EVM.step 1 gasCost (some (.Push .PUSH1, some (word, 1))) before = .ok after) :
    after.pc = before.pc + UInt256.ofNat 2 := by
  change Except.ok _ = Except.ok after at success
  cases success
  rfl

end Compiler.Proofs.IRGeneration.NativeInitcodeFrames


namespace Compiler.Proofs.IRGeneration.NativeInitcodeFrames
open EvmYul
open Verity.Core.Model.MidnightInitcode

/-- Native decoder-provided PUSH1 arguments always carry width1. -/
theorem decode_push1_width (code : ByteArray) (pc : UInt256)
    (arg : Option (UInt256 × Nat))
    (decoded : EVM.decode code pc = some (.Push .PUSH1, arg)) :
    ∃ word, arg = some (word, 1) := by
  unfold EVM.decode at decoded
  cases fetched : (code.get? pc.toNat >>= EVM.parseInstr) with
  | none => simp only [fetched] at decoded; cases decoded
  | some actual =>
    simp only [fetched] at decoded
    have same : actual = .Push .PUSH1 := congrArg (fun x => x.1) (Option.some.inj decoded)
    subst actual
    have args := congrArg (fun x => x.2) (Option.some.inj decoded)
    exact ⟨_, args.symm⟩

/-- The two-byte instruction can occur only at offsets0 or5, so it cannot
cross the constructor boundary. -/
theorem header_push1_position (payload : ByteArray) (pc : UInt256)
    (arg : Option (UInt256 × Nat)) (inside : pc.toNat < 11)
    (decoded : EVM.decode (initcode payload) pc = some (.Push .PUSH1, arg)) :
    pc.toNat = 0 ∨ pc.toNat = 5 := by
  have parsed := native_decode_opcode _ _ _ _ decoded
  rw [native_header_byte payload pc.toNat inside] at parsed
  have positions : pc.toNat = 0 ∨ pc.toNat = 1 ∨ pc.toNat = 2 ∨
      pc.toNat = 3 ∨ pc.toNat = 4 ∨ pc.toNat = 5 ∨ pc.toNat = 6 ∨
      pc.toNat = 7 ∨ pc.toNat = 8 ∨ pc.toNat = 9 ∨ pc.toNat = 10 := by omega
  rcases positions with h | h | h | h | h | h | h | h | h | h | h
  all_goals first
    | exact Or.inl h
    | exact Or.inr h
    | (rw [h] at parsed; contradiction)

/-- At these small PCs and widths, native UInt256 addition does not wrap. -/
theorem header_pc_add (pc : UInt256) (width : Nat)
    (inside : pc.toNat < 11) (small : width ≤ 2) :
    (pc + UInt256.ofNat width).toNat = pc.toNat + width := by
  have modulus : 13 < UInt256.size := by decide
  change (pc.toNat + width % UInt256.size) % UInt256.size = pc.toNat + width
  have widthMod : width % UInt256.size = width := Nat.mod_eq_of_lt (by omega)
  rw [widthMod, Nat.mod_eq_of_lt (by omega)]

end Compiler.Proofs.IRGeneration.NativeInitcodeFrames

namespace Compiler.Proofs.IRGeneration.NativeInitcodeFrames
open EvmYul
open Verity.Core.Model.MidnightInitcode

private theorem header_ops (payload : ByteArray) (pc : UInt256)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat)) (inside : pc.toNat < 11)
    (decoded : EVM.decode (initcode payload) pc = some (op, arg)) :
    op ∈ [.Push .PUSH1, .SIGNEXTEND, .CODESIZE, .SUB, .DUP1, .Push .PUSH0, .CODECOPY, .RETURN] := by
  have parsed := native_decode_opcode _ _ _ _ decoded
  rw [native_header_byte payload pc.toNat inside] at parsed
  have positions : pc.toNat = 0 ∨ pc.toNat = 1 ∨ pc.toNat = 2 ∨
      pc.toNat = 3 ∨ pc.toNat = 4 ∨ pc.toNat = 5 ∨ pc.toNat = 6 ∨
      pc.toNat = 7 ∨ pc.toNat = 8 ∨ pc.toNat = 9 ∨ pc.toNat = 10 := by omega
  rcases positions with h | h | h | h | h | h | h | h | h | h | h
  all_goals rw [h] at parsed
  all_goals first
    | change some (Operation.Push .PUSH1) = some op at parsed
    | change some (Operation.SIGNEXTEND) = some op at parsed
    | change some (Operation.CODESIZE) = some op at parsed
    | change some (Operation.SUB) = some op at parsed
    | change some (Operation.DUP1) = some op at parsed
    | change some (Operation.Push .PUSH0) = some op at parsed
    | change some (Operation.CODECOPY) = some op at parsed
    | change some (Operation.RETURN) = some op at parsed
  all_goals cases Option.some.inj parsed; decide

/-- An actual successful nonreturning native step inside the constructor
strictly advances its PC and stays inside the header. No runtime payload
opcode can be reached along a continuing constructor step. -/
theorem header_step_progress (payload : ByteArray) (before after : EVM.State)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat)) (gasCost : Nat)
    (inside : before.pc.toNat < 11)
    (decoded : EVM.decode (initcode payload) before.pc = some (op, arg))
    (nonreturn : op ≠ .RETURN)
    (success : EVM.step 1 gasCost (some (op, arg)) before = .ok after) :
    before.pc.toNat < after.pc.toNat ∧ after.pc.toNat < 11 := by
  have below : before.pc.toNat < 10 := by
    by_contra outside
    have tenth : before.pc.toNat = 10 := by omega
    have parsed := native_decode_opcode _ _ _ _ decoded
    rw [native_header_byte payload before.pc.toNat inside, tenth] at parsed
    change some Operation.RETURN = some op at parsed
    exact nonreturn (Option.some.inj parsed).symm
  by_cases push : op = .Push .PUSH1
  · subst op
    obtain ⟨word, rfl⟩ := decode_push1_width _ _ _ decoded
    have pcEq := push1_step_pc before after word gasCost success
    have positions := header_push1_position payload before.pc _ inside decoded
    rw [pcEq, header_pc_add before.pc 2 inside (by decide)]
    omega
  · have selected := header_ops payload before.pc op arg inside decoded
    have fixed : op ∈ [.SIGNEXTEND, .CODESIZE, .SUB, .DUP1, .CODECOPY, .Push .PUSH0] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at selected
      rcases selected with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | contradiction | decide
    have pcEq := header_fixed_step_pc op before after arg gasCost fixed success
    rw [pcEq, header_pc_add before.pc 1 inside (by decide)]
    omega

/-- Progress also holds for any actual successful positive-fuel step; zero
fuel supplies no success evidence. -/
theorem header_step_progress_any (payload : ByteArray) (fuel gasCost : Nat)
    (before after : EVM.State) (op : Operation .EVM)
    (arg : Option (UInt256 × Nat)) (inside : before.pc.toNat < 11)
    (decoded : EVM.decode (initcode payload) before.pc = some (op, arg))
    (nonreturn : op ≠ .RETURN)
    (success : EVM.step fuel gasCost (some (op, arg)) before = .ok after) :
    before.pc.toNat < after.pc.toNat ∧ after.pc.toNat < 11 := by
  cases fuel with
  | zero => simp only [EVM.step] at success; cases success
  | succ fuel =>
    have allowed := native_header_local payload before.pc op arg inside decoded
    have supported : CreationCaller.supported op = true := allowed.resolve_right nonreturn
    rw [supported_step_fuel fuel op before arg gasCost supported] at success
    exact header_step_progress payload before after op arg gasCost inside decoded nonreturn success

/-- The concrete code/PC invariant and rank are preserved by every actual
successful continuing constructor step. The rank is the byte distance to11;
no fabricated poststate or runtime payload interpretation is assumed. -/
theorem header_invariant_step (payload : ByteArray) (fuel gasCost : Nat)
    (before after : EVM.State) (op : Operation .EVM)
    (arg : Option (UInt256 × Nat))
    (code : before.executionEnv.code = initcode payload)
    (inside : before.pc.toNat < 11)
    (decoded : EVM.decode before.executionEnv.code before.pc = some (op, arg))
    (nonreturn : op ≠ .RETURN)
    (success : EVM.step fuel gasCost (some (op, arg)) before = .ok after) :
    after.executionEnv.code = initcode payload ∧ after.pc.toNat < 11 ∧
      11 - after.pc.toNat < 11 - before.pc.toNat := by
  rw [code] at decoded
  have world := native_header_step_state payload fuel gasCost before after op arg inside decoded success
  have progress := header_step_progress_any payload fuel gasCost before after op arg inside decoded nonreturn success
  have codeFrame := congrArg (fun state : EvmYul.State .EVM => state.executionEnv.code) world
  refine ⟨codeFrame.trans code, progress.2, ?_⟩
  omega

private theorem binary_noFuel (op : Primop.Binary) (before : EVM.State) :
    EVM.execBinOp op before ≠ .error .OutOfFuel := by
  unfold EVM.execBinOp
  split <;> intro impossible <;> cases impossible

private theorem environment_noFuel (op : ExecutionEnv .EVM → UInt256) (before : EVM.State) :
    EVM.executionEnvOp op before ≠ .error .OutOfFuel := by
  unfold EVM.executionEnvOp
  intro impossible; cases impossible

private theorem copy_noFuel
    (op : SharedState .EVM → UInt256 → UInt256 → UInt256 → SharedState .EVM)
    (before : EVM.State) : EVM.ternaryCopyOp op before ≠ .error .OutOfFuel := by
  unfold EVM.ternaryCopyOp
  split <;> intro impossible <;> cases impossible

private theorem return_noFuel
    (op : MachineState → UInt256 → UInt256 → MachineState) (before : EVM.State) :
    EVM.binaryMachineStateOp op before ≠ .error .OutOfFuel := by
  unfold EVM.binaryMachineStateOp
  split <;> intro impossible <;> cases impossible

/-- No header instruction can itself report interpreter fuel exhaustion at
positive step fuel, including exceptional stack paths. This rules out the
recursive-call failure that fuel-independence alone would not exclude. -/
theorem header_step_ne_outOfFuel (payload : ByteArray) (before : EVM.State)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat)) (gasCost : Nat)
    (inside : before.pc.toNat < 11)
    (decoded : EVM.decode (initcode payload) before.pc = some (op, arg)) :
    EVM.step 1 gasCost (some (op, arg)) before ≠ .error .OutOfFuel := by
  let charged := { before with
    gasAvailable := before.gasAvailable - UInt256.ofNat gasCost
    execLength := before.execLength + 1 }
  have selected := header_ops payload before.pc op arg inside decoded
  simp only [List.mem_cons, List.not_mem_nil, or_false] at selected
  rcases selected with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨word, rfl⟩ := decode_push1_width _ _ _ decoded
    change Except.ok _ ≠ Except.error EVM.ExecutionException.OutOfFuel
    intro impossible; cases impossible
  · exact binary_noFuel _ charged
  · exact environment_noFuel _ charged
  · exact binary_noFuel _ charged
  · change EvmYul.dup 1 charged ≠ .error .OutOfFuel
    unfold EvmYul.dup
    dsimp only
    split <;> intro impossible <;> cases impossible
  · change Except.ok _ ≠ Except.error EVM.ExecutionException.OutOfFuel
    intro impossible; cases impossible
  · exact copy_noFuel _ charged
  · exact return_noFuel _ charged

end Compiler.Proofs.IRGeneration.NativeInitcodeFrames

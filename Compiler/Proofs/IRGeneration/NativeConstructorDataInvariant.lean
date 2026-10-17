import Compiler.Proofs.IRGeneration.NativeMidnightConstructorData

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul EVM.Proof NativeInitcodeFrames
open Verity.Core.Model.MidnightInitcode

/-- Only real instruction boundaries of Midnight's constructor are states of
this invariant; PUSH1 immediate bytes are never executable continuations. -/
def stagePC : Fin 9 → Nat
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 3
  | ⟨3, _⟩ => 4
  | ⟨4, _⟩ => 5
  | ⟨5, _⟩ => 7
  | ⟨6, _⟩ => 8
  | ⟨7, _⟩ => 9
  | ⟨8, _⟩ => 10

def stageStack (size : Nat) : Fin 9 → Stack UInt256
  | ⟨0, _⟩ => []
  | ⟨1, _⟩ => [.ofNat 11]
  | ⟨2, _⟩ => [.ofNat (11 + size), .ofNat 11]
  | ⟨3, _⟩ => [.ofNat size]
  | ⟨4, _⟩ => [.ofNat size, .ofNat size]
  | ⟨5, _⟩ => [.ofNat 11, .ofNat size, .ofNat size]
  | ⟨6, _⟩ => [.ofNat 0, .ofNat 11, .ofNat size, .ofNat size]
  | ⟨7, _⟩ => [.ofNat size]
  | ⟨8, _⟩ => [.ofNat 0, .ofNat size]

/-- The memory equality concerns the actual native bytes, not a canonical
memory substituted for them. It becomes available only after CODECOPY. -/
def DataAt (payload : ByteArray) (stage : Fin 9) (state : EVM.State) : Prop :=
  state.executionEnv.code = initcode payload ∧ state.pc.toNat = stagePC stage ∧
  state.stack = stageStack payload.size stage ∧
  (7 ≤ stage.val → state.memory.readWithPadding 0 payload.size = payload)

def DataInvariant (payload : ByteArray) (state : EVM.State) : Prop :=
  ∃ stage, DataAt payload stage state

theorem dataAt_charge (payload : ByteArray) (stage : Fin 9) (state : EVM.State)
    (gas : UInt256) (holds : DataAt payload stage state) :
    DataAt payload stage { state with gasAvailable := gas } := holds

theorem dataInvariant_charge (payload : ByteArray) (state : EVM.State)
    (gas : UInt256) (holds : DataInvariant payload state) :
    DataInvariant payload { state with gasAvailable := gas } := by
  obtain ⟨stage, holds⟩ := holds
  exact ⟨stage, dataAt_charge payload stage state gas holds⟩

theorem data_initial (payload : ByteArray) (state : EVM.State)
    (code : state.executionEnv.code = initcode payload) (pc : state.pc.toNat = 0)
    (stack : state.stack = []) : DataInvariant payload state := by
  refine ⟨⟨0, by decide⟩, code, pc, stack, ?_⟩
  intro impossible
  change 7 ≤ (0 : Nat) at impossible
  omega

/-- Once the actual continuing run reaches RETURN, its real stack and memory
force the returned bytes. Native integer representation is bounded explicitly. -/
theorem data_return_payload (payload : ByteArray) (pre post : EVM.State)
    (fuel gasCost : Nat) (holds : DataAt payload ⟨8, by decide⟩ pre)
    (bounded : payload.size < UInt256.size)
    (success : EVM.step (fuel + 1) gasCost (some (.RETURN, none)) pre = .ok post) :
    H post.toMachineState .RETURN = some payload := by
  have popped : pre.stack.pop2 = some ([], UInt256.ofNat 0, UInt256.ofNat payload.size) := by
    rw [holds.2.2.1]
    rfl
  have exactStep := EVM.Proof.step_RETURN fuel gasCost pre [] (.ofNat 0)
    (.ofNat payload.size) popped
  have same := Except.ok.inj (exactStep.symm.trans success)
  subst post
  change some (pre.memory.readWithPadding 0 (UInt256.ofNat payload.size).toNat) = some payload
  have value : (UInt256.ofNat payload.size).toNat = payload.size := Nat.mod_eq_of_lt bounded
  rw [value]
  exact congrArg some (holds.2.2.2 (by decide))

/-- Actual CODECOPY establishes the payload memory fact at stage seven. -/
theorem data_copy_step (payload : ByteArray) (pre post : EVM.State)
    (fuel gasCost : Nat) (holds : DataAt payload ⟨6, by decide⟩ pre)
    (bounded : payload.size < 2^64)
    (success : EVM.step (fuel + 1) gasCost (some (.CODECOPY, none)) pre = .ok post) :
    DataAt payload ⟨7, by decide⟩ post := by
  have sizeBound : payload.size < UInt256.size := by
    have huge : 2^64 < UInt256.size := by decide
    omega
  have value : (UInt256.ofNat payload.size).toNat = payload.size := Nat.mod_eq_of_lt sizeBound
  have popped : pre.stack.pop3 = some ([UInt256.ofNat payload.size],
      UInt256.ofNat 0, UInt256.ofNat 11, UInt256.ofNat payload.size) := by
    rw [holds.2.2.1]; rfl
  have exactStep := step_CODECOPY fuel gasCost pre [.ofNat payload.size] (.ofNat 0)
    (.ofNat 11) (.ofNat payload.size) popped
  have same := Except.ok.inj (exactStep.symm.trans success)
  subst post
  refine ⟨holds.1, ?_, rfl, ?_⟩
  · change (pre.pc + UInt256.ofNat 1).toNat = 9
    have pc : pre.pc.toNat = 8 := holds.2.1
    rw [header_pc_add pre.pc 1 (by omega) (by decide), pc]
  · intro _relevant
    change (pre.executionEnv.code.write 11 pre.memory 0 (UInt256.ofNat payload.size).toNat).readWithPadding 0 payload.size = payload
    rw [holds.1, value]
    exact read_copied_payload payload pre.memory bounded

/-- The final real PUSH0 preserves copied bytes and sets up RETURN's operands. -/
theorem data_return_setup (payload : ByteArray) (pre post : EVM.State)
    (fuel gasCost : Nat) (holds : DataAt payload ⟨7, by decide⟩ pre)
    (success : EVM.step (fuel + 1) gasCost (some (.Push .PUSH0, none)) pre = .ok post) :
    DataAt payload ⟨8, by decide⟩ post := by
  have exactStep := step_PUSH0 fuel gasCost pre
  have same := Except.ok.inj (exactStep.symm.trans success)
  subst post
  refine ⟨holds.1, ?_, ?_, fun _ => holds.2.2.2 (by decide)⟩
  · change (pre.pc + UInt256.ofNat 1).toNat = 10
    have pc : pre.pc.toNat = 9 := holds.2.1
    rw [header_pc_add pre.pc 1 (by omega) (by decide), pc]
  · change UInt256.ofNat 0 :: pre.stack = [.ofNat 0, .ofNat payload.size]
    rw [holds.2.2.1]
    rfl

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor

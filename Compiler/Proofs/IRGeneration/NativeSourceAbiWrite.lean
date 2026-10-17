import Compiler.Proofs.IRGeneration.NativeCapturedMappingHelper
import Compiler.Proofs.IRGeneration.NativeCreationWorldCaller

namespace Compiler.Proofs.IRGeneration.NativeSourceAbiWrite
open EvmYul CapturedMappingHelper NativeMappingStorageExecution NativeMappingKeccak

/-- Exact pinned source runtime, not a fabricated helper or selected trace. -/
def code : ByteArray :=
  ⟨#[0x60, 0x80, 0x80, 0x60, 0x40, 0x52, 0x60, 0x04, 0x36, 0x10, 0x15, 0x61, 0x00, 0x12, 0x57, 0x5f, 0x80, 0xfd, 0x5b, 0x5f, 0x35, 0x60, 0xe0, 0x1c, 0x90, 0x81, 0x63, 0x30, 0xcc, 0xca, 0x8f, 0x14, 0x61, 0x00, 0x5f, 0x57, 0x50, 0x63, 0x5e, 0x38, 0x3d, 0x21, 0x14, 0x61, 0x00, 0x32, 0x57, 0x5f, 0x80, 0xfd, 0x5b, 0x34, 0x61, 0x00, 0x5b, 0x57, 0x60, 0x20, 0x36, 0x60, 0x03, 0x19, 0x01, 0x12, 0x61, 0x00, 0x5b, 0x57, 0x60, 0x04, 0x35, 0x5f, 0x52, 0x5f, 0x60, 0x20, 0x52, 0x60, 0x20, 0x60, 0x40, 0x5f, 0x20, 0x54, 0x60, 0x40, 0x51, 0x90, 0x81, 0x52, 0xf3, 0x5b, 0x5f, 0x80, 0xfd, 0x5b]⟩ ++
  ⟨#[0x34, 0x61, 0x00, 0x5b, 0x57, 0x60, 0x60, 0x36, 0x60, 0x03, 0x19, 0x01, 0x12, 0x61, 0x00, 0x5b, 0x57, 0x60, 0x04, 0x35, 0x67, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x81, 0x11, 0x61, 0x00, 0x5b, 0x57, 0x61, 0x01, 0x00, 0x60, 0x03, 0x19, 0x82, 0x36, 0x03, 0x01, 0x12, 0x61, 0x00, 0x5b, 0x57, 0x61, 0x01, 0x00, 0x82, 0x01, 0x82, 0x81, 0x10, 0x67, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x82, 0x11, 0x17, 0x61, 0x03, 0x12, 0x57, 0x60, 0x40, 0x52, 0x80, 0x60, 0x04, 0x01, 0x35, 0x82, 0x52, 0x61, 0x00, 0xbf, 0x60, 0x24, 0x82, 0x01, 0x61, 0x03, 0xb0, 0x56, 0x5b]⟩ ++
  ⟨#[0x60, 0x20, 0x83, 0x01, 0x90, 0x81, 0x52, 0x61, 0x00, 0xd2, 0x60, 0x44, 0x83, 0x01, 0x61, 0x03, 0xb0, 0x56, 0x5b, 0x90, 0x60, 0x40, 0x84, 0x01, 0x91, 0x82, 0x52, 0x60, 0x64, 0x83, 0x01, 0x35, 0x67, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x81, 0x11, 0x61, 0x00, 0x5b, 0x57, 0x83, 0x01, 0x90, 0x36, 0x60, 0x23, 0x83, 0x01, 0x12, 0x15, 0x61, 0x00, 0x5b, 0x57, 0x60, 0x04, 0x82, 0x01, 0x35, 0x67, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x81, 0x11, 0x61, 0x03, 0x12, 0x57, 0x60, 0x40, 0x51, 0x92, 0x61, 0x01, 0x24, 0x60, 0x20, 0x83, 0x60, 0x05, 0x1b, 0x01, 0x85]⟩ ++
  ⟨#[0x61, 0x03, 0x8e, 0x56, 0x5b, 0x81, 0x84, 0x52, 0x60, 0x20, 0x60, 0x04, 0x81, 0x86, 0x01, 0x93, 0x60, 0x07, 0x1b, 0x83, 0x01, 0x01, 0x01, 0x90, 0x36, 0x82, 0x11, 0x61, 0x00, 0x5b, 0x57, 0x60, 0x24, 0x01, 0x91, 0x5b, 0x81, 0x83, 0x10, 0x61, 0x03, 0x26, 0x57, 0x50, 0x50, 0x50, 0x60, 0x60, 0x85, 0x01, 0x91, 0x82, 0x52, 0x60, 0x80, 0x85, 0x01, 0x93, 0x60, 0x84, 0x81, 0x01, 0x35, 0x85, 0x52, 0x60, 0xa0, 0x86, 0x01, 0x90, 0x60, 0xa4, 0x81, 0x01, 0x35, 0x82, 0x52, 0x61, 0x01, 0x8b, 0x60, 0xe4, 0x61, 0x01, 0x7d, 0x60, 0xc4, 0x84, 0x01, 0x61, 0x03, 0xb0, 0x56, 0x5b, 0x92, 0x60]⟩ ++
  ⟨#[0xc0, 0x8a, 0x01, 0x93, 0x84, 0x52, 0x01, 0x61, 0x03, 0xb0, 0x56, 0x5b, 0x91, 0x60, 0xe0, 0x88, 0x01, 0x92, 0x83, 0x52, 0x60, 0x24, 0x35, 0x5f, 0x52, 0x5f, 0x60, 0x20, 0x52, 0x60, 0x44, 0x35, 0x60, 0x40, 0x5f, 0x20, 0x55, 0x60, 0x40, 0x51, 0x96, 0x60, 0x40, 0x88, 0x01, 0x88, 0x81, 0x10, 0x67, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x82, 0x11, 0x17, 0x61, 0x03, 0x12, 0x57, 0x60, 0x40, 0x52, 0x60, 0x0b, 0x88, 0x52, 0x60, 0x20, 0x88, 0x01, 0x95, 0x6a, 0x60, 0x0b, 0x38, 0x03, 0x80, 0x60, 0x0b, 0x5f, 0x39, 0x5f, 0xf3, 0x60, 0xa8, 0x1b, 0x87, 0x52, 0x60, 0x01, 0x60]⟩ ++
  ⟨#[0x01, 0x60, 0xa0, 0x1b, 0x03, 0x60, 0x40, 0x51, 0x98, 0x81, 0x60, 0x20, 0x8b, 0x01, 0x98, 0x60, 0x20, 0x8a, 0x52, 0x61, 0x01, 0x40, 0x8c, 0x01, 0x9d, 0x51, 0x60, 0x40, 0x8d, 0x01, 0x52, 0x51, 0x16, 0x60, 0x60, 0x8b, 0x01, 0x52, 0x51, 0x16, 0x60, 0x80, 0x89, 0x01, 0x52, 0x51, 0x98, 0x61, 0x01, 0x00, 0x60, 0xa0, 0x89, 0x01, 0x52, 0x89, 0x51, 0x80, 0x91, 0x52, 0x60, 0x20, 0x61, 0x01, 0x60, 0x89, 0x01, 0x9a, 0x01, 0x90, 0x5f, 0x5b, 0x81, 0x81, 0x10, 0x61, 0x02, 0xce, 0x57, 0x50, 0x50, 0x50, 0x86, 0x60, 0x01, 0x60, 0x01, 0x60, 0xa0, 0x1b, 0x03, 0x99, 0x8a, 0x5f, 0x9a, 0x99]⟩ ++
  ⟨#[0x98, 0x96, 0x81, 0x60, 0x20, 0x97, 0x61, 0x02, 0xa9, 0x9a, 0x97, 0x61, 0x02, 0x78, 0x97, 0x51, 0x60, 0xc0, 0x88, 0x01, 0x52, 0x51, 0x60, 0xe0, 0x87, 0x01, 0x52, 0x51, 0x16, 0x61, 0x01, 0x00, 0x85, 0x01, 0x52, 0x51, 0x16, 0x61, 0x01, 0x20, 0x83, 0x01, 0x52, 0x03, 0x60, 0x1f, 0x19, 0x81, 0x01, 0x87, 0x52, 0x86, 0x61, 0x03, 0x8e, 0x56, 0x5b, 0x60, 0x40, 0x51, 0x94, 0x85, 0x93, 0x83, 0x85, 0x01, 0x97, 0x51, 0x80, 0x91, 0x89, 0x5e, 0x84, 0x01, 0x90, 0x83, 0x82, 0x01, 0x90, 0x89, 0x82, 0x52, 0x51, 0x92, 0x83, 0x91, 0x5e, 0x01, 0x01, 0x85, 0x81, 0x52, 0x03, 0x60, 0x1f, 0x19]⟩ ++
  ⟨#[0x81, 0x01, 0x83, 0x52, 0x82, 0x61, 0x03, 0x8e, 0x56, 0x5b, 0x51, 0x90, 0x82, 0xf5, 0x16, 0x80, 0x15, 0x61, 0x02, 0xbf, 0x57, 0x60, 0x20, 0x90, 0x60, 0x40, 0x51, 0x90, 0x81, 0x52, 0xf3, 0x5b, 0x63, 0x41, 0xb2, 0xcc, 0xbf, 0x60, 0xe1, 0x1b, 0x5f, 0x52, 0x60, 0x04, 0x5f, 0xfd, 0x5b, 0x90, 0x91, 0x9a, 0x60, 0x20, 0x60, 0x80, 0x60, 0x01, 0x92, 0x60, 0x01, 0x60, 0x01, 0x60, 0xa0, 0x1b, 0x03, 0x8f, 0x60, 0x60, 0x90, 0x51, 0x82, 0x81, 0x51, 0x16, 0x84, 0x52, 0x85, 0x81, 0x01, 0x51, 0x86, 0x85, 0x01, 0x52, 0x60, 0x40, 0x81, 0x01, 0x51, 0x60, 0x40, 0x85, 0x01, 0x52, 0x01, 0x51]⟩ ++
  ⟨#[0x16, 0x60, 0x60, 0x82, 0x01, 0x52, 0x01, 0x9c, 0x01, 0x91, 0x01, 0x91, 0x90, 0x91, 0x61, 0x02, 0x27, 0x56, 0x5b, 0x63, 0x4e, 0x48, 0x7b, 0x71, 0x60, 0xe0, 0x1b, 0x5f, 0x52, 0x60, 0x41, 0x60, 0x04, 0x52, 0x60, 0x24, 0x5f, 0xfd, 0x5b, 0x60, 0x80, 0x83, 0x36, 0x03, 0x12, 0x61, 0x00, 0x5b, 0x57, 0x60, 0x40, 0x51, 0x90, 0x60, 0x80, 0x82, 0x01, 0x90, 0x82, 0x82, 0x10, 0x67, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x83, 0x11, 0x17, 0x61, 0x03, 0x12, 0x57, 0x60, 0x80, 0x92, 0x60, 0x20, 0x92, 0x60, 0x40, 0x52, 0x61, 0x03, 0x5e, 0x86, 0x61, 0x03, 0xb0, 0x56, 0x5b, 0x81]⟩ ++
  ⟨#[0x52, 0x82, 0x86, 0x01, 0x35, 0x83, 0x82, 0x01, 0x52, 0x60, 0x40, 0x86, 0x01, 0x35, 0x60, 0x40, 0x82, 0x01, 0x52, 0x61, 0x03, 0x7e, 0x60, 0x60, 0x87, 0x01, 0x61, 0x03, 0xb0, 0x56, 0x5b, 0x60, 0x60, 0x82, 0x01, 0x52, 0x81, 0x52, 0x01, 0x92, 0x01, 0x91, 0x61, 0x01, 0x43, 0x56, 0x5b, 0x90, 0x60, 0x1f, 0x80, 0x19, 0x91, 0x01, 0x16, 0x81, 0x01, 0x90, 0x81, 0x10, 0x67, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x82, 0x11, 0x17, 0x61, 0x03, 0x12, 0x57, 0x60, 0x40, 0x52, 0x56, 0x5b, 0x35, 0x90, 0x60, 0x01, 0x60, 0x01, 0x60, 0xa0, 0x1b, 0x03, 0x82, 0x16, 0x82, 0x03, 0x61]⟩ ++
  ⟨#[0x00, 0x5b, 0x57, 0x56, 0xfe, 0xa1, 0x64, 0x73, 0x6f, 0x6c, 0x63, 0x43, 0x00, 0x08, 0x22, 0x00, 0x0a]⟩

def instructions : Array (Nat × EVM.Proof.Instruction) := #[
 (404, (.Push .PUSH1, some (UInt256.ofNat 36, 1))),
 (406, (.CALLDATALOAD, none)), (407, (.Push .PUSH0, none)), (408, (.MSTORE, none)),
 (409, (.Push .PUSH0, none)), (410, (.Push .PUSH1, some (UInt256.ofNat 32, 1))),
 (412, (.MSTORE, none)), (413, (.Push .PUSH1, some (UInt256.ofNat 68, 1))),
 (415, (.CALLDATALOAD, none)), (416, (.Push .PUSH1, some (UInt256.ofNat 64, 1))),
 (418, (.Push .PUSH0, none)), (419, (.KECCAK256, none)), (420, (.SSTORE, none))]

set_option maxRecDepth 8192 in
/-- Only thirteen fixed decodes are kernel reduced, never a full execution. -/
theorem source_decode : ∀ i : Fin 13,
    EVM.decode code (UInt256.ofNat instructions[i].1) = some instructions[i].2 := by
  intro i
  obtain ⟨i, bound⟩ := i
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +revert

theorem decode_at (machine : EVM.State) (i : Fin 13)
    (same : machine.executionEnv.code = code)
    (pc : machine.pc = UInt256.ofNat instructions[i].1) :
    EVM.Proof.decodeAt machine = instructions[i].2 := by
  unfold EVM.Proof.decodeAt
  rw [same, pc, source_decode i]
  rfl

private theorem next_step (count : Nat) (initial final : EVM.State) (i : Fin 13)
    (same : initial.executionEnv.code = code)
    (pc : initial.pc = UInt256.ofNat instructions[i].1)
    (success : checkedSteps (count + 1) initial = .ok final) :
    ∃ next, CreationCaller.checkedStep initial instructions[i].2.1 instructions[i].2.2 = .ok next ∧
      checkedSteps count next = .ok final := by
  obtain ⟨next, step, rest⟩ := checkedSteps_success count initial final success
  rw [decode_at initial i same pc] at step
  exact ⟨next, step, rest⟩

/-- Four actual source instructions derive the key from calldata and store it at zero. -/
theorem key_store (initial final : EVM.State)
    (same : initial.executionEnv.code = code) (pc : initial.pc = UInt256.ofNat 404)
    (success : checkedSteps 4 initial = .ok final) :
    final.stack = initial.stack ∧ final.toState = initial.toState ∧
      final.pc = UInt256.ofNat 409 ∧
      final.memory = (initial.toMachineState.mstore (UInt256.ofNat 0)
        (initial.toState.calldataload (UInt256.ofNat 36))).memory := by
  obtain ⟨one, first, rest⟩ := next_step 3 initial final ⟨0, by decide⟩ same pc success
  obtain ⟨s1, w1, p1, m1⟩ := checked_push1_shape initial one _ first
  have c1 : one.executionEnv.code = code := by rw [w1]; exact same
  have at1 : one.pc = UInt256.ofNat 406 := by rw [p1, pc]; rfl
  obtain ⟨two, second, rest⟩ := next_step 2 one final ⟨1, by decide⟩ c1 at1 rest
  obtain ⟨s2, w2, p2, m2⟩ := checked_calldataload_shape one two _ _ s1 second
  have c2 : two.executionEnv.code = code := by rw [w2, w1]; exact same
  have at2 : two.pc = UInt256.ofNat 407 := by rw [p2, at1]; rfl
  obtain ⟨three, third, rest⟩ := next_step 1 two final ⟨2, by decide⟩ c2 at2 rest
  obtain ⟨s3, w3, p3, m3⟩ := checked_push0_shape two three third
  have c3 : three.executionEnv.code = code := by rw [w3, w2, w1]; exact same
  have at3 : three.pc = UInt256.ofNat 408 := by rw [p3, at2]; rfl
  obtain ⟨four, fourth, rest⟩ := next_step 0 three final ⟨3, by decide⟩ c3 at3 rest
  have eq : four = final := Except.ok.inj rest
  subst four
  have stack : three.stack = UInt256.ofNat 0 :: initial.toState.calldataload (UInt256.ofNat 36) :: initial.stack := by
    rw [s3, s2, w1]
  obtain ⟨s4, w4, p4⟩ := checked_mstore_shape three final _ _ _ stack fourth
  have mem := checked_mstore_memory three final _ _ _ stack fourth
  refine ⟨s4, w4.trans (w3.trans (w2.trans w1)), ?_, ?_⟩
  · rw [p4, at3]; rfl
  · change final.memory = ByteArray.write _ 0 initial.memory 0 32
    change final.memory = ByteArray.write _ 0 three.memory 0 32 at mem
    simpa only [m3, m2, m1] using mem

/-- The source's next three instructions store the constant mapping base. -/
theorem base_store (initial final : EVM.State)
    (same : initial.executionEnv.code = code) (pc : initial.pc = UInt256.ofNat 409)
    (success : checkedSteps 3 initial = .ok final) :
    final.stack = initial.stack ∧ final.toState = initial.toState ∧
      final.pc = UInt256.ofNat 413 ∧
      final.memory = (initial.toMachineState.mstore (UInt256.ofNat 32) (UInt256.ofNat 0)).memory := by
  obtain ⟨one, first, rest⟩ := next_step 2 initial final ⟨4, by decide⟩ same pc success
  obtain ⟨s1, w1, p1, m1⟩ := checked_push0_shape initial one first
  have c1 : one.executionEnv.code = code := by rw [w1]; exact same
  have at1 : one.pc = UInt256.ofNat 410 := by rw [p1, pc]; rfl
  obtain ⟨two, second, rest⟩ := next_step 1 one final ⟨5, by decide⟩ c1 at1 rest
  obtain ⟨s2, w2, p2, m2⟩ := checked_push1_shape one two _ second
  have c2 : two.executionEnv.code = code := by rw [w2, w1]; exact same
  have at2 : two.pc = UInt256.ofNat 412 := by rw [p2, at1]; rfl
  obtain ⟨three, third, rest⟩ := next_step 0 two final ⟨6, by decide⟩ c2 at2 rest
  have eq : three = final := Except.ok.inj rest
  subst three
  have stack : two.stack = UInt256.ofNat 32 :: UInt256.ofNat 0 :: initial.stack := by rw [s2, s1]
  obtain ⟨s3, w3, p3⟩ := checked_mstore_shape two final _ _ _ stack third
  have mem := checked_mstore_memory two final _ _ _ stack third
  refine ⟨s3, w3.trans (w2.trans w1), ?_, ?_⟩
  · rw [p3, at2]; rfl
  · change final.memory = ByteArray.write _ 0 initial.memory 32 32
    change final.memory = ByteArray.write _ 0 two.memory 32 32 at mem
    simpa only [m2, m1] using mem

/-- The value operand comes from the original calldata, without a supplied stack. -/
theorem value_load (initial final : EVM.State)
    (same : initial.executionEnv.code = code) (pc : initial.pc = UInt256.ofNat 413)
    (success : checkedSteps 2 initial = .ok final) :
    final.stack = initial.toState.calldataload (UInt256.ofNat 68) :: initial.stack ∧
      final.toState = initial.toState ∧ final.pc = UInt256.ofNat 416 ∧ final.memory = initial.memory := by
  obtain ⟨one, first, rest⟩ := next_step 1 initial final ⟨7, by decide⟩ same pc success
  obtain ⟨s1, w1, p1, m1⟩ := checked_push1_shape initial one _ first
  have c1 : one.executionEnv.code = code := by rw [w1]; exact same
  have at1 : one.pc = UInt256.ofNat 415 := by rw [p1, pc]; rfl
  obtain ⟨two, second, rest⟩ := next_step 0 one final ⟨8, by decide⟩ c1 at1 rest
  have eq : two = final := Except.ok.inj rest
  subst two
  obtain ⟨s2, w2, p2, m2⟩ := checked_calldataload_shape one final _ _ s1 second
  refine ⟨?_, w2.trans w1, ?_, m2.trans m1⟩
  · simpa only [w1] using s2
  · rw [p2, at1]; rfl

/-- The checked hash consumes exactly the actual scratch memory of this fragment. -/
theorem hash_memory (initial final : EVM.State)
    (same : initial.executionEnv.code = code) (pc : initial.pc = UInt256.ofNat 416)
    (success : checkedSteps 3 initial = .ok final) :
    final.stack = UInt256.ofNat (fromByteArrayBigEndian (ffi.KEC
      (initial.memory.readWithPadding 0 64))) :: initial.stack ∧
      final.toState = initial.toState ∧ final.pc = UInt256.ofNat 420 ∧ final.memory = initial.memory := by
  obtain ⟨one, first, rest⟩ := next_step 2 initial final ⟨9, by decide⟩ same pc success
  obtain ⟨s1, w1, p1, m1⟩ := checked_push1_shape initial one _ first
  have c1 : one.executionEnv.code = code := by rw [w1]; exact same
  have at1 : one.pc = UInt256.ofNat 418 := by rw [p1, pc]; rfl
  obtain ⟨two, second, rest⟩ := next_step 1 one final ⟨10, by decide⟩ c1 at1 rest
  obtain ⟨s2, w2, p2, m2⟩ := checked_push0_shape one two second
  have c2 : two.executionEnv.code = code := by rw [w2, w1]; exact same
  have at2 : two.pc = UInt256.ofNat 419 := by rw [p2, at1]; rfl
  obtain ⟨three, third, rest⟩ := next_step 0 two final ⟨11, by decide⟩ c2 at2 rest
  have eq : three = final := Except.ok.inj rest
  subst three
  have stack : two.stack = UInt256.ofNat 0 :: UInt256.ofNat 64 :: initial.stack := by rw [s2, s1]
  obtain ⟨s3, w3, m3, p3⟩ := checked_keccak two final _ _ _ stack third
  refine ⟨?_, w3.trans (w2.trans w1), ?_, m3.trans (m2.trans m1)⟩
  · change final.stack = UInt256.ofNat (fromByteArrayBigEndian (ffi.KEC (two.memory.readWithPadding 0 64))) :: _ at s3
    simpa only [m2, m1] using s3
  · rw [p3, at2]; rfl

/-- Successful execution supplies the intermediate state when a fragment is split. -/
theorem split_steps (left right : Nat) (initial final : EVM.State)
    (success : checkedSteps (left + right) initial = .ok final) :
    ∃ middle, checkedSteps left initial = .ok middle ∧ checkedSteps right middle = .ok final := by
  rw [checkedSteps_add] at success
  cases step : checkedSteps left initial with
  | error reason => simp only [step, Bind.bind, Except.bind] at success; cases success
  | ok middle => exact ⟨middle, rfl, by simpa only [step, Bind.bind, Except.bind] using success⟩

/-- Seven actual instructions materialize exactly ABI key followed by zero base. -/
theorem preimage (initial final : EVM.State)
    (same : initial.executionEnv.code = code) (pc : initial.pc = UInt256.ofNat 404)
    (success : checkedSteps 7 initial = .ok final) :
    final.stack = initial.stack ∧ final.toState = initial.toState ∧ final.pc = UInt256.ofNat 413 ∧
      final.memory.readWithPadding 0 64 =
        (initial.toState.calldataload (UInt256.ofNat 36)).toByteArray ++ (UInt256.ofNat 0).toByteArray := by
  obtain ⟨middle, first, second⟩ := split_steps 4 3 initial final success
  obtain ⟨s1, w1, p1, m1⟩ := key_store initial middle same pc first
  have c1 : middle.executionEnv.code = code := by rw [w1]; exact same
  obtain ⟨s2, w2, p2, m2⟩ := base_store middle final c1 p1 second
  refine ⟨s2.trans s1, w2.trans w1, p2, ?_⟩
  change final.memory = ByteArray.write _ 0 middle.memory 32 32 at m2
  rw [m1] at m2
  rw [m2]
  exact mapping_preimage initial.toMachineState _ _

/-- The next five instructions load the value and hash the actual memory. -/
theorem value_hash (initial final : EVM.State)
    (same : initial.executionEnv.code = code) (pc : initial.pc = UInt256.ofNat 413)
    (success : checkedSteps 5 initial = .ok final) :
    final.stack = UInt256.ofNat (fromByteArrayBigEndian (ffi.KEC
      (initial.memory.readWithPadding 0 64))) ::
        initial.toState.calldataload (UInt256.ofNat 68) :: initial.stack ∧
      final.toState = initial.toState ∧ final.pc = UInt256.ofNat 420 := by
  obtain ⟨middle, first, second⟩ := split_steps 2 3 initial final success
  obtain ⟨s1, w1, p1, m1⟩ := value_load initial middle same pc first
  have c1 : middle.executionEnv.code = code := by rw [w1]; exact same
  obtain ⟨s2, w2, p2, _⟩ := hash_memory middle final c1 p1 second
  exact ⟨by simpa only [s1, m1] using s2, w2.trans w1, p2⟩

/-- The SSTORE operands are derived from original calldata and the two actual stores.
This requires no hash premise: it exposes precisely the FFI preimage. -/
theorem store_operands (initial final : EVM.State)
    (same : initial.executionEnv.code = code) (pc : initial.pc = UInt256.ofNat 404)
    (success : checkedSteps 12 initial = .ok final) :
    final.stack = UInt256.ofNat (fromByteArrayBigEndian (ffi.KEC
      ((initial.toState.calldataload (UInt256.ofNat 36)).toByteArray ++ (UInt256.ofNat 0).toByteArray))) ::
        initial.toState.calldataload (UInt256.ofNat 68) :: initial.stack ∧
      final.toState = initial.toState ∧ final.pc = UInt256.ofNat 420 := by
  obtain ⟨middle, first, second⟩ := split_steps 7 5 initial final success
  obtain ⟨s1, w1, p1, m1⟩ := preimage initial middle same pc first
  have c1 : middle.executionEnv.code = code := by rw [w1]; exact same
  obtain ⟨s2, w2, p2⟩ := value_hash middle final c1 p1 second
  exact ⟨by simpa only [m1, w1, s1] using s2, w2.trans w1, p2⟩

/-- Only pointwise native/pure Keccak agreement identifies the already derived slot. -/
theorem model_operands (initial final : EVM.State)
    (same : initial.executionEnv.code = code) (pc : initial.pc = UInt256.ofNat 404)
    (success : checkedSteps 12 initial = .ok final)
    (hash : ffi.KEC (Compiler.Proofs.abiEncodeMappingSlot 0
      (initial.toState.calldataload (UInt256.ofNat 36)).toNat) =
        KeccakEngine.keccak256 (Compiler.Proofs.abiEncodeMappingSlot 0
          (initial.toState.calldataload (UInt256.ofNat 36)).toNat)) :
    final.stack = UInt256.ofNat (Compiler.Proofs.solidityMappingSlot 0
      (initial.toState.calldataload (UInt256.ofNat 36)).toNat) ::
        initial.toState.calldataload (UInt256.ofNat 68) :: initial.stack ∧
      final.toState = initial.toState ∧ final.pc = UInt256.ofNat 420 := by
  obtain ⟨stack, world, position⟩ := store_operands initial final same pc success
  have bytes : Compiler.Proofs.abiEncodeMappingSlot 0
      (initial.toState.calldataload (UInt256.ofNat 36)).toNat =
        (initial.toState.calldataload (UInt256.ofNat 36)).toByteArray ++ (UInt256.ofNat 0).toByteArray := by
    unfold Compiler.Proofs.abiEncodeMappingSlot
    rw [native_word_roundtrip]
  rw [← bytes, hash] at stack
  exact ⟨stack, world, position⟩

/-- Thirteen real source instructions write the slot/value derived from original ABI.
No chosen intermediate stack, successful store result, or postworld is a premise. -/
theorem source_write (world : Verity.ContractState) (initial final : EVM.State)
    (warm : Verity.Core.Model.Create2Access.WarmAccounts) (account : Account .EVM)
    (same : initial.executionEnv.code = code) (pc : initial.pc = UInt256.ofNat 404)
    (present : initial.toState.lookupAccount initial.executionEnv.codeOwner = some account)
    (agrees : NativeCreationWorld.Agreement world initial warm)
    (success : checkedSteps 13 initial = .ok final)
    (hash : ffi.KEC (Compiler.Proofs.abiEncodeMappingSlot 0
      (initial.toState.calldataload (UInt256.ofNat 36)).toNat) =
        KeccakEngine.keccak256 (Compiler.Proofs.abiEncodeMappingSlot 0
          (initial.toState.calldataload (UInt256.ofNat 36)).toNat)) :
    NativeCreationWorld.Agreement
      (world.writeSlot (Compiler.Proofs.solidityMappingSlot 0
        (initial.toState.calldataload (UInt256.ofNat 36)).toNat)
        (Verity.Core.Uint256.ofNat (initial.toState.calldataload (UInt256.ofNat 68)).toNat)) final warm := by
  obtain ⟨middle, firstTwelve, last⟩ := split_steps 12 1 initial final success
  obtain ⟨stack, frame, position⟩ := model_operands initial middle same pc firstTwelve hash
  have c1 : middle.executionEnv.code = code := by rw [frame]; exact same
  obtain ⟨after, stored, rest⟩ := next_step 0 middle final ⟨12, by decide⟩ c1 position last
  have eq : after = final := Except.ok.inj rest
  subst after
  have current := NativeCreationLocalFrames.agreement_of_state_eq world initial middle warm agrees frame
  have existsAccount : middle.toState.lookupAccount middle.executionEnv.codeOwner = some account := by
    rw [frame]; exact present
  have restored : { middle with stack := (UInt256.ofNat
      (Compiler.Proofs.Storage.HashedMappingLayout.Entry.location
        (0, [(initial.toState.calldataload (UInt256.ofNat 36)).toNat], 0)) ::
          initial.toState.calldataload (UInt256.ofNat 68) :: initial.stack) } = middle := by
    rw [singleton_location, ← stack]
  change CreationCaller.checkedStep middle .SSTORE none = .ok final at stored
  have actual := NativeSourceMappingWrites.checked_source_chain_write world middle final warm account
    existsAccount current 0 [(initial.toState.calldataload (UInt256.ofNat 36)).toNat]
    (initial.toState.calldataload (UInt256.ofNat 68)) initial.stack (by simpa only [restored] using stored)
  simpa only [NativeSourceMappingWrites.source_chain_write, singleton_location] using actual

/-- The paired native instrument performs the exact complete canonical-world write,
not only a raw storage agreement or selected-slot observation. -/
theorem source_paired_write (world : Verity.ContractState) (initial final : EVM.State)
    (warm : Verity.Core.Model.Create2Access.WarmAccounts) (account : Account .EVM)
    (same : initial.executionEnv.code = code) (pc : initial.pc = UInt256.ofNat 404)
    (present : initial.toState.lookupAccount initial.executionEnv.codeOwner = some account)
    (success : checkedSteps 13 initial = .ok final)
    (hash : ffi.KEC (Compiler.Proofs.abiEncodeMappingSlot 0
      (initial.toState.calldataload (UInt256.ofNat 36)).toNat) =
        KeccakEngine.keccak256 (Compiler.Proofs.abiEncodeMappingSlot 0
          (initial.toState.calldataload (UInt256.ofNat 36)).toNat)) :
    ∃ middle, checkedSteps 12 initial = .ok middle ∧
      CreationCaller.checkedStep middle .SSTORE none = .ok final ∧
      NativeCreationWorldCaller.worldAfter ⟨world, middle, warm⟩ .SSTORE = .ok
        (world.writeSlot (Compiler.Proofs.solidityMappingSlot 0
          (initial.toState.calldataload (UInt256.ofNat 36)).toNat)
          (Verity.Core.Uint256.ofNat (initial.toState.calldataload (UInt256.ofNat 68)).toNat)) := by
  obtain ⟨middle, firstTwelve, last⟩ := split_steps 12 1 initial final success
  obtain ⟨stack, frame, position⟩ := model_operands initial middle same pc firstTwelve hash
  have c1 : middle.executionEnv.code = code := by rw [frame]; exact same
  obtain ⟨after, stored, rest⟩ := next_step 0 middle final ⟨12, by decide⟩ c1 position last
  have eq : after = final := Except.ok.inj rest
  subst after
  change CreationCaller.checkedStep middle .SSTORE none = .ok final at stored
  have existsAccount : middle.toState.lookupAccount middle.executionEnv.codeOwner = some account := by
    rw [frame]; exact present
  have slot : (UInt256.ofNat (Compiler.Proofs.solidityMappingSlot 0
      (initial.toState.calldataload (UInt256.ofNat 36)).toNat)).toNat =
        Compiler.Proofs.solidityMappingSlot 0 (initial.toState.calldataload (UInt256.ofNat 36)).toNat := by
    rw [← singleton_location]
    exact NativeHashedStorageAgreement.location_word _
  refine ⟨middle, firstTwelve, stored, ?_⟩
  simp only [NativeCreationWorldCaller.worldAfter, stack, existsAccount, slot,
    decide_true, Bool.true_or, ↓reduceIte, Option.isNone_some, Bool.false_eq_true,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

end Compiler.Proofs.IRGeneration.NativeSourceAbiWrite











import Verity.Core.Model.DenoteMemory

/-!
# Bounded initcode execution

Executable bytecode semantics for the instructions in Midnight's eleven-byte
SSTORE2 initcode. Unsupported opcodes are explicit errors, not approximations.
This module is a prerequisite for deployment denotation: it neither admits
CREATE2 in the importer nor chooses an adversary-supplied runtime byte string.

The model is functional: gas, call depth, initcode/code size limits, account
collision, code-deposit checks and world rollback belong to the deployment
transition, which is not yet integrated. No equivalence with a full EVM executor
is asserted here. Fuel bounds execution independently of kernel reduction.
-/

namespace Compiler.CompilationModel.InitCodeExecution

open Verity.Core
open Compiler.CompilationModel.DenoteMemory

structure Machine where
  pc : Nat := 0
  stack : List Uint256 := []
  memory : Memory := Memory.empty

inductive Error where
  | unsupportedOpcode (opcode : Nat)
  | stackUnderflow
  | stackOverflow
  | outOfFuel
  deriving DecidableEq, Repr

inductive Result where
  | running (state : Machine)
  | returned (data : List Byte)
  | failed (error : Error)

/-- EVM CODECOPY zero-extends code and does not expand memory for zero size. -/
def codeCopy (memory : Memory) (code : List Byte) (dest source size : Nat) : Memory :=
  if size = 0 then memory else memory.copyFrom (listByte code) dest source size

@[simp] theorem codeCopy_zero (memory : Memory) (code : List Byte) (dest source : Nat) :
    codeCopy memory code dest source 0 = memory := by
  simp [codeCopy]

private def push (state : Machine) (value : Uint256) (nextPc : Nat) : Result :=
  if state.stack.length < 1024 then
    .running { state with pc := nextPc, stack := value :: state.stack }
  else .failed .stackOverflow

/-- One decoded instruction. The head of `stack` is the top EVM operand. -/
def step (code : List Byte) (state : Machine) : Result :=
  match (listByte code state.pc).val with
  | 0x00 => .returned []
  | 0x60 => push state (Uint256.ofNat (listByte code (state.pc + 1)).val) (state.pc + 2)
  | 0x5f => push state 0 (state.pc + 1)
  | 0x38 => push state (Uint256.ofNat code.length) (state.pc + 1)
  | 0x03 =>
      match state.stack with
      | a :: b :: rest => .running { state with pc := state.pc + 1, stack := Uint256.sub a b :: rest }
      | _ => .failed .stackUnderflow
  | 0x80 =>
      match state.stack with
      | top :: _ => push state top (state.pc + 1)
      | _ => .failed .stackUnderflow
  | 0x39 =>
      match state.stack with
      | dest :: source :: size :: rest =>
          .running { state with
            pc := state.pc + 1
            stack := rest
            memory := codeCopy state.memory code dest.val source.val size.val }
      | _ => .failed .stackUnderflow
  | 0xf3 =>
      match state.stack with
      | offset :: size :: _ => .returned (state.memory.slice offset.val size.val)
      | _ => .failed .stackUnderflow
  | opcode => .failed (.unsupportedOpcode opcode)

/-- A total interpreter with a caller-selected instruction bound. -/
def run : Nat → List Byte → Machine → Result
  | 0, _, _ => .failed .outOfFuel
  | fuel + 1, code, state =>
      match step code state with
      | .running next => run fuel code next
      | .returned bytes => .returned bytes
      | .failed error => .failed error

theorem run_succ (fuel : Nat) (code : List Byte) (state : Machine) :
    run (fuel + 1) code state =
      match step code state with
      | .running next => run fuel code next
      | .returned bytes => .returned bytes
      | .failed error => .failed error := rfl

theorem run_after_step {code : List Byte} {state next : Machine} (fuel : Nat)
    (transition : step code state = .running next) :
    run (fuel + 1) code state = run fuel code next := by
  rw [run_succ, transition]

/-- Exact bytes from pinned IdLib: PUSH1 11; CODESIZE; SUB; DUP1;
PUSH1 11; PUSH0; CODECOPY; PUSH0; RETURN. No contract-name recognition. -/
def midnightPrefix : List Byte :=
  [⟨0x60, by decide⟩, ⟨0x0b, by decide⟩, ⟨0x38, by decide⟩,
   ⟨0x03, by decide⟩, ⟨0x80, by decide⟩, ⟨0x60, by decide⟩,
   ⟨0x0b, by decide⟩, ⟨0x5f, by decide⟩, ⟨0x39, by decide⟩,
   ⟨0x5f, by decide⟩, ⟨0xf3, by decide⟩]

def midnightInitcode (payload : List Byte) : List Byte := midnightPrefix ++ payload

@[simp] theorem midnightInitcode_length (payload : List Byte) :
    (midnightInitcode payload).length = 11 + payload.length := by
  simp [midnightInitcode, midnightPrefix]
  omega

/-- This predicate inspects bytes; it does not accept a library/function name. -/
def hasMidnightPrefix (code : List Byte) : Bool :=
  code.take 11 == midnightPrefix

@[simp] theorem hasMidnightPrefix_initcode (payload : List Byte) :
    hasMidnightPrefix (midnightInitcode payload) = true := by
  simp [hasMidnightPrefix, midnightInitcode, midnightPrefix]

theorem expandedLength_ge (endOffset : Nat) : endOffset ≤ expandedLength endOffset := by
  by_cases h : endOffset = 0
  · simp [expandedLength, h]
  · simp only [expandedLength, h, if_false]
    omega

/-- A copied byte is readable inside expanded memory, not merely in its
backing function. This is the bridge needed by CODECOPY followed by RETURN. -/
theorem copyFrom_readByte_at (memory : Memory) (source : Nat → Byte)
    (destOffset sourceOffset size : Nat) (index : Fin size) :
    (memory.copyFrom source destOffset sourceOffset size).readByte (destOffset + index) =
      source (sourceOffset + index) := by
  have he : destOffset + size ≤ (memory.copyFrom source destOffset sourceOffset size).size :=
    Nat.le_trans (expandedLength_ge _) (Nat.le_max_right _ _)
  have hi : destOffset + index.val < (memory.copyFrom source destOffset sourceOffset size).size :=
    Nat.lt_of_lt_of_le (Nat.add_lt_add_left index.isLt _) he
  rw [Memory.readByte, if_pos hi]
  exact Memory.copyFrom_at memory source destOffset sourceOffset size index

/-- Byte-level frame lemma: a copy preserves every read outside its destination. -/
theorem copyFrom_readByte_outside (memory : Memory) (source : Nat → Byte)
    (destOffset sourceOffset size address : Nat)
    (outside : address < destOffset ∨ destOffset + size ≤ address) :
    (memory.copyFrom source destOffset sourceOffset size).readByte address = memory.readByte address := by
  have ho : ¬(destOffset ≤ address ∧ address < destOffset + size) := by omega
  have hg : memory.size ≤ (memory.copyFrom source destOffset sourceOffset size).size :=
    Nat.le_max_left _ _
  by_cases hi : address < (memory.copyFrom source destOffset sourceOffset size).size
  · rw [Memory.readByte, if_pos hi]
    simp only [Memory.copyFrom, dif_neg ho]
  · have hOld : ¬ address < memory.size := by omega
    rw [Memory.readByte, if_neg hi, Memory.readByte, if_neg hOld]

theorem codeCopy_readByte_at (memory : Memory) (code : List Byte)
    (dest source size : Nat) (index : Fin size) :
    (codeCopy memory code dest source size).readByte (dest + index) = listByte code (source + index) := by
  have hn : size ≠ 0 := by have := index.isLt; omega
  simp only [codeCopy, hn, if_false]
  exact copyFrom_readByte_at memory (listByte code) dest source size index

theorem codeCopy_readByte_outside (memory : Memory) (code : List Byte)
    (dest source size address : Nat) (outside : address < dest ∨ dest + size ≤ address) :
    (codeCopy memory code dest source size).readByte address = memory.readByte address := by
  by_cases hn : size = 0
  · simp [codeCopy, hn]
  · simp only [codeCopy, hn, if_false]
    exact copyFrom_readByte_outside memory (listByte code) dest source size address outside

/-- Symbolic subtraction avoids reducing a whole generated model in the kernel. -/
theorem prefix_sub_length (size : Nat) (fits : 11 + size < Uint256.modulus) :
    Uint256.sub (Uint256.ofNat (11 + size)) 11 = Uint256.ofNat size := by
  have h11 : 11 < Uint256.modulus := by decide
  change Uint256.sub (Uint256.ofNat (11 + size)) (Uint256.ofNat 11) = Uint256.ofNat size
  unfold Uint256.sub
  simp only [Uint256.val_ofNat, Nat.mod_eq_of_lt fits, Nat.mod_eq_of_lt h11]
  rw [if_pos (by omega)]
  congr 1
  omega

private def s1 : Machine := { pc := 2, stack := [11] }
private def s2 (size : Nat) : Machine := { pc := 3, stack := [Uint256.ofNat (11 + size), 11] }
private def s3 (size : Nat) : Machine := { pc := 4, stack := [Uint256.ofNat size] }
private def s4 (size : Nat) : Machine := { pc := 5, stack := [Uint256.ofNat size, Uint256.ofNat size] }
private def s5 (size : Nat) : Machine := { pc := 7, stack := [11, Uint256.ofNat size, Uint256.ofNat size] }
private def s6 (size : Nat) : Machine := { pc := 8, stack := [0, 11, Uint256.ofNat size, Uint256.ofNat size] }
private def s7 (payload : List Byte) : Machine :=
  { pc := 9, stack := [Uint256.ofNat payload.length],
    memory := codeCopy Memory.empty (midnightInitcode payload) 0 11 payload.length }
private def s8 (payload : List Byte) : Machine :=
  { pc := 10, stack := [0, Uint256.ofNat payload.length],
    memory := codeCopy Memory.empty (midnightInitcode payload) 0 11 payload.length }

private theorem step1 (payload : List Byte) :
    step (midnightInitcode payload) {} = .running s1 := rfl

private theorem step2 (payload : List Byte) :
    step (midnightInitcode payload) s1 = .running (s2 payload.length) := by
  change Result.running { pc := 3, stack := [Uint256.ofNat (midnightInitcode payload).length, 11] } = _
  rw [midnightInitcode_length]
  rfl

private theorem step3 (payload : List Byte) (fits : 11 + payload.length < Uint256.modulus) :
    step (midnightInitcode payload) (s2 payload.length) = .running (s3 payload.length) := by
  change Result.running { pc := 4, stack := [Uint256.sub (Uint256.ofNat (11 + payload.length)) 11] } = _
  rw [prefix_sub_length _ fits]
  rfl

private theorem step4 (payload : List Byte) :
    step (midnightInitcode payload) (s3 payload.length) = .running (s4 payload.length) := rfl

private theorem step5 (payload : List Byte) :
    step (midnightInitcode payload) (s4 payload.length) = .running (s5 payload.length) := rfl

private theorem step6 (payload : List Byte) :
    step (midnightInitcode payload) (s5 payload.length) = .running (s6 payload.length) := rfl

private theorem step7 (payload : List Byte) (fits : payload.length < Uint256.modulus) :
    step (midnightInitcode payload) (s6 payload.length) = .running (s7 payload) := by
  change Result.running {
    pc := 9
    stack := [Uint256.ofNat payload.length]
    memory := codeCopy Memory.empty (midnightInitcode payload) 0 11 (Uint256.ofNat payload.length).val } = _
  rw [Uint256.val_ofNat, Nat.mod_eq_of_lt fits]
  rfl

private theorem step8 (payload : List Byte) :
    step (midnightInitcode payload) (s7 payload) = .running (s8 payload) := rfl

private theorem step9 (payload : List Byte) (fits : payload.length < Uint256.modulus) :
    step (midnightInitcode payload) (s8 payload) =
      .returned ((codeCopy Memory.empty (midnightInitcode payload) 0 11 payload.length).slice 0 payload.length) := by
  change Result.returned ((codeCopy Memory.empty (midnightInitcode payload) 0 11 payload.length).slice 0
    (Uint256.ofNat payload.length).val) = _
  rw [Uint256.val_ofNat, Nat.mod_eq_of_lt fits]

theorem midnight_run (payload : List Byte) (fits : 11 + payload.length < Uint256.modulus) :
    run 9 (midnightInitcode payload) {} =
      .returned ((codeCopy Memory.empty (midnightInitcode payload) 0 11 payload.length).slice 0 payload.length) := by
  have hsize : payload.length < Uint256.modulus := by omega
  rw [run_after_step 8 (step1 payload), run_after_step 7 (step2 payload),
      run_after_step 6 (step3 payload fits), run_after_step 5 (step4 payload),
      run_after_step 4 (step5 payload), run_after_step 3 (step6 payload),
      run_after_step 2 (step7 payload hsize), run_after_step 1 (step8 payload),
      run_succ, step9 _ hsize]

theorem midnight_codeByte (payload : List Byte) (index : Nat) :
    listByte (midnightInitcode payload) (11 + index) = listByte payload index := by
  rw [Nat.add_comm 11 index]
  rfl

theorem midnight_slice (payload : List Byte) :
    (codeCopy Memory.empty (midnightInitcode payload) 0 11 payload.length).slice 0 payload.length = payload := by
  apply List.ext_getElem
  · simp only [Memory.slice, List.length_map, List.length_range]
  · intro index _ hi
    simp only [Memory.slice, List.getElem_map, List.getElem_range, Nat.zero_add]
    rw [List.getElem_eq_getD zeroByte]
    have h := codeCopy_readByte_at Memory.empty (midnightInitcode payload) 0 11 payload.length ⟨index, hi⟩
    simp only [Nat.zero_add] at h
    rw [midnight_codeByte] at h
    exact h

/-- Nine decoded instructions return exactly the appended payload for every
bounded input, including an empty payload. No runtime-code oracle is involved. -/
theorem midnight_returns_payload (payload : List Byte) (fits : 11 + payload.length < Uint256.modulus) :
    run 9 (midnightInitcode payload) {} = .returned payload := by
  rw [midnight_run _ fits, midnight_slice]

end Compiler.CompilationModel.InitCodeExecution

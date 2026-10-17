import Verity.Core.Model.PhysicalCopy
import Init.Data.ByteArray.Lemmas

/-! Bounded operational interpreter for the actual Midnight constructor prefix.
The metered runner computes callee opcode and memory charges. CREATE2 entry
and code-deposit charges are outside this component. Unsupported instructions
and stack underflow fail explicitly. Callee memory is fresh. -/
namespace Verity.Core.Model.MidnightInitcode
open Compiler.CompilationModel.DenoteMemory

def modulus : Nat := 2^256

def codeByte (code : ByteArray) (offset : Nat) : Byte :=
  let value := (code.data[offset]?).getD 0
  ⟨value.toNat, UInt8.toNat_lt_size value⟩

def memorySlice (memory : Memory) (offset size : Nat) : ByteArray :=
  ⟨Array.ofFn (fun index : Fin size => UInt8.ofNat (memory.readByte (offset + index.val)).val)⟩

structure Frame where
  pc : Nat
  stack : List Nat
  memory : Memory

inductive Step where
  | next (frame : Frame)
  | returned (data : ByteArray) (memory : Memory)

def advance (frame : Frame) (stack : List Nat) (width : Nat := 1) : Step :=
  .next { frame with pc := frame.pc + width, stack := stack }

/-- RETURN expands only a nonempty active window; zero-size RETURN never
expands memory, even at a huge offset. -/
def returnMemory (memory : Memory) (offset size : Nat) : Memory :=
  if size = 0 ∨ offset + size ≤ memory.size then memory else memory.expand (offset + size)

theorem returnMemory_copy (source : Nat → Byte) (size : Nat) :
    returnMemory (Memory.empty.copyFrom source 0 11 size) 0 size =
      Memory.empty.copyFrom source 0 11 size := by
  by_cases empty : size = 0
  · simp only [returnMemory, empty, true_or, if_true]
  · have extent : size ≤ (Memory.empty.copyFrom source 0 11 size).size := by
      simp only [Memory.copyFrom, empty, if_false, Memory.expand]
      exact Nat.le_trans (by simpa using expandedLength_covers size) (Nat.le_max_right _ _)
    simp only [returnMemory, Nat.zero_add, extent, or_true, if_true]

def step (code : ByteArray) (frame : Frame) : Except String Step :=
  match (codeByte code frame.pc).val, frame.stack with
  | 0x60, stack => .ok (advance frame ((codeByte code (frame.pc + 1)).val :: stack) 2)
  | 0x38, stack => .ok (advance frame (code.size % modulus :: stack))
  | 0x03, a :: b :: rest => .ok (advance frame ((a + modulus - b) % modulus :: rest))
  | 0x80, a :: rest => .ok (advance frame (a :: a :: rest))
  | 0x5f, stack => .ok (advance frame (0 :: stack))
  | 0x39, dest :: source :: size :: rest =>
      .ok (.next { pc := frame.pc + 1, stack := rest, memory := frame.memory.copyFrom (codeByte code) dest source size })
  | 0xf3, offset :: size :: _ =>
      let memory := returnMemory frame.memory offset size
      .ok (.returned (memorySlice memory offset size) memory)
  | _, _ => .error "unsupported initcode instruction or stack underflow"

def run : Nat → ByteArray → Frame → Except String Step
  | 0, _, _ => .error "initcode instruction budget exhausted"
  | fuel + 1, code, frame =>
      match step code frame with
      | .error message => .error message
      | .ok (.returned data memory) => .ok (.returned data memory)
      | .ok (.next next) => run fuel code next

def initial : Frame := { pc := 0, stack := [], memory := Memory.empty }

def header : ByteArray := ⟨#[0x60, 0x0b, 0x38, 0x03, 0x80, 0x60, 0x0b, 0x5f, 0x39, 0x5f, 0xf3]⟩

def initcode (payload : ByteArray) : ByteArray := ⟨header.data ++ payload.data⟩

@[simp] theorem initcode_size (payload : ByteArray) :
    (initcode payload).size = 11 + payload.size := by
  change (header.data ++ payload.data).size = 11 + payload.data.size
  rw [Array.size_append]
  rfl

theorem codeByte_header (payload : ByteArray) (offset : Nat) (inside : offset < 11) :
    codeByte (initcode payload) offset = codeByte header offset := by
  unfold codeByte initcode
  rw [Array.getElem?_append_left (by simpa [header] using inside)]

theorem codeByte_payload (payload : ByteArray) (index : Fin payload.size) :
    UInt8.ofNat (codeByte (initcode payload) (11 + index.val)).val = payload.data[index.val] := by
  unfold codeByte initcode
  rw [Array.getElem?_append_right (by simp [header])]
  change UInt8.ofNat ((payload.data[11 + index.val - 11]?).getD 0).toNat = _
  have inside : index.val < payload.data.size := index.isLt
  simp only [Nat.add_sub_cancel_left, Array.getElem?_eq_getElem inside, Option.getD_some, UInt8.ofNat_toNat]

theorem copied_payload (payload : ByteArray) :
    memorySlice (Memory.empty.copyFrom (codeByte (initcode payload)) 0 11 payload.size)
      0 payload.size = payload := by
  apply ByteArray.ext
  change Array.ofFn _ = payload.data
  have bytes : (fun index : Fin payload.size =>
      UInt8.ofNat ((Memory.empty.copyFrom (codeByte (initcode payload)) 0 11 payload.size).readByte
        (0 + index.val)).val) = (fun index : Fin payload.size => payload.data[index.val]) := by
    funext index
    rw [Memory.readByte_copyFrom_at]
    exact codeByte_payload payload index
  rw [bytes]
  exact Array.ofFn_getElem

private theorem fetch0 (payload : ByteArray) :
    (codeByte (initcode payload) 0).val = 96 := by
  rw [codeByte_header payload 0 (by decide)]
  rfl

private theorem fetch1 (payload : ByteArray) :
    (codeByte (initcode payload) 1).val = 11 := by
  rw [codeByte_header payload 1 (by decide)]
  rfl

private theorem fetch2 (payload : ByteArray) :
    (codeByte (initcode payload) 2).val = 56 := by
  rw [codeByte_header payload 2 (by decide)]
  rfl

private theorem fetch3 (payload : ByteArray) :
    (codeByte (initcode payload) 3).val = 3 := by
  rw [codeByte_header payload 3 (by decide)]
  rfl

private theorem fetch4 (payload : ByteArray) :
    (codeByte (initcode payload) 4).val = 128 := by
  rw [codeByte_header payload 4 (by decide)]
  rfl

private theorem fetch5 (payload : ByteArray) :
    (codeByte (initcode payload) 5).val = 96 := by
  rw [codeByte_header payload 5 (by decide)]
  rfl

private theorem fetch6 (payload : ByteArray) :
    (codeByte (initcode payload) 6).val = 11 := by
  rw [codeByte_header payload 6 (by decide)]
  rfl

private theorem fetch7 (payload : ByteArray) :
    (codeByte (initcode payload) 7).val = 95 := by
  rw [codeByte_header payload 7 (by decide)]
  rfl

private theorem fetch8 (payload : ByteArray) :
    (codeByte (initcode payload) 8).val = 57 := by
  rw [codeByte_header payload 8 (by decide)]
  rfl

private theorem fetch9 (payload : ByteArray) :
    (codeByte (initcode payload) 9).val = 95 := by
  rw [codeByte_header payload 9 (by decide)]
  rfl

private theorem fetch10 (payload : ByteArray) :
    (codeByte (initcode payload) 10).val = 243 := by
  rw [codeByte_header payload 10 (by decide)]
  rfl

theorem payload_length_sub (n : Nat) (bounded : n < modulus) :
    (11 + n + modulus - 11) % modulus = n := by
  have arith : 11 + n + modulus - 11 = n + modulus := by omega
  rw [arith, Nat.add_mod]
  simp only [Nat.mod_self, Nat.add_zero, Nat.mod_eq_of_lt bounded]

theorem run_prefix (payload : ByteArray) (bounded : 11 + payload.size < modulus) :
    run 9 (initcode payload) initial =
      .ok (.returned
        (memorySlice (Memory.empty.copyFrom (codeByte (initcode payload)) 0 11 payload.size) 0 payload.size)
        (Memory.empty.copyFrom (codeByte (initcode payload)) 0 11 payload.size)) := by
  have sizeWord : (11 + payload.size) % modulus = 11 + payload.size := Nat.mod_eq_of_lt bounded
  have payloadBound : payload.size < modulus := by omega
  simp [run, step, advance, initial, fetch0, fetch1, fetch2, fetch3, fetch4, fetch5,
    fetch6, fetch7, fetch8, fetch9, fetch10, initcode_size, sizeWord,
    payload_length_sub payload.size payloadBound, returnMemory_copy]

theorem run_returns_payload (payload : ByteArray) (bounded : 11 + payload.size < modulus) :
    run 9 (initcode payload) initial =
      .ok (.returned payload (Memory.empty.copyFrom (codeByte (initcode payload)) 0 11 payload.size)) := by
  rw [run_prefix payload bounded, copied_payload]

/-- The Shanghai initcode limit is sufficient for the word bound above. The
entry evaluator still has to charge its gas and enforce this cap itself. -/
theorem run_returns_payload_capped (payload : ByteArray) (cap : 11 + payload.size ≤ 49152) :
    run 9 (initcode payload) initial =
      .ok (.returned payload (Memory.empty.copyFrom (codeByte (initcode payload)) 0 11 payload.size)) := by
  apply run_returns_payload
  have wordCap : 49152 < modulus := by decide
  omega

theorem step_unsupported :
    step (⟨#[0xfe]⟩ : ByteArray) initial =
      .error "unsupported initcode instruction or stack underflow" := rfl

theorem step_underflow :
    step (⟨#[0x39]⟩ : ByteArray) initial =
      .error "unsupported initcode instruction or stack underflow" := rfl

/-- EVM memory and copy charges, post-Shanghai schedule. -/
def words (bytes : Nat) : Nat := (bytes + 31) / 32

def memoryCost (wordCount : Nat) : Nat := 3 * wordCount + wordCount * wordCount / 512

def expansionCost (memory : Memory) (offset size : Nat) : Nat :=
  if size = 0 then 0 else
    memoryCost (max (words memory.size) (words (offset + size))) - memoryCost (words memory.size)

/-- Cost decoding fails on the same unsupported instructions/underflow as step.
Gas for CREATE2 itself, EIP-3860 and code deposit is outside this callee arm. -/
def instructionCost (code : ByteArray) (frame : Frame) : Except String Nat :=
  match (codeByte code frame.pc).val, frame.stack with
  | 0x60, _ => .ok 3
  | 0x38, _ => .ok 2
  | 0x03, _ :: _ :: _ => .ok 3
  | 0x80, _ :: _ => .ok 3
  | 0x5f, _ => .ok 2
  | 0x39, dest :: _ :: size :: _ => .ok (3 + 3 * words size + expansionCost frame.memory dest size)
  | 0xf3, offset :: size :: _ => .ok (expansionCost frame.memory offset size)
  | _, _ => .error "unsupported initcode instruction or stack underflow"

inductive MeteredStep where
  | returned (data : ByteArray) (memory : Memory) (gasLeft : Nat)
  | outOfGas

/-- A host instruction-budget error remains distinct from an EVM OOG. -/
def runMetered : Nat → ByteArray → Frame → Nat → Except String MeteredStep
  | 0, _, _, _ => .error "initcode instruction budget exhausted"
  | fuel + 1, code, frame, gas =>
      match instructionCost code frame with
      | .error message => .error message
      | .ok charge =>
          if gas < charge then .ok .outOfGas else
          match step code frame with
          | .error message => .error message
          | .ok (.returned data memory) => .ok (.returned data memory (gas - charge))
          | .ok (.next next) => runMetered fuel code next (gas - charge)

/-- Exact charge measured by executing instructions, not a supplied gas
certificate. Used to prove sufficient-gas agreement for the metered runner. -/
def runWithCost : Nat → ByteArray → Frame → Except String (ByteArray × Memory × Nat)
  | 0, _, _ => .error "initcode instruction budget exhausted"
  | fuel + 1, code, frame =>
      match instructionCost code frame with
      | .error message => .error message
      | .ok charge =>
          match step code frame with
          | .error message => .error message
          | .ok (.returned data memory) => .ok (data, memory, charge)
          | .ok (.next next) =>
              match runWithCost fuel code next with
              | .error message => .error message
              | .ok (data, memory, rest) => .ok (data, memory, charge + rest)

theorem metered_sufficient (fuel : Nat) (code : ByteArray) (frame : Frame)
    (data : ByteArray) (memory : Memory) (cost gas : Nat)
    (execution : runWithCost fuel code frame = .ok (data, memory, cost))
    (enough : cost ≤ gas) :
    runMetered fuel code frame gas = .ok (.returned data memory (gas - cost)) := by
  induction fuel generalizing frame cost gas with
  | zero => simp only [runWithCost, reduceCtorEq] at execution
  | succ fuel ih =>
      cases hc : instructionCost code frame with
      | error message => simp [runWithCost, hc] at execution
      | ok charge =>
          cases hs : step code frame with
          | error message => simp [runWithCost, hc, hs] at execution
          | ok result =>
              cases result with
              | returned bytes mem =>
                  simp [runWithCost, hc, hs] at execution
                  rcases execution with ⟨rfl, rfl, rfl⟩
                  simp [runMetered, hc, hs, Nat.not_lt.mpr enough]
              | next next =>
                  cases hr : runWithCost fuel code next with
                  | error message => simp [runWithCost, hc, hs, hr] at execution
                  | ok result =>
                      rcases result with ⟨bytes, mem, rest⟩
                      simp [runWithCost, hc, hs, hr] at execution
                      rcases execution with ⟨rfl, rfl, rfl⟩
                      have enoughCharge : ¬ gas < charge := by omega
                      have enoughRest : rest ≤ gas - charge := by omega
                      have tail := ih next rest (gas - charge) hr enoughRest
                      simp only [runMetered, hc, hs, enoughCharge, if_false]
                      rw [tail]
                      congr 2
                      omega

theorem metered_insufficient (fuel : Nat) (code : ByteArray) (frame : Frame)
    (data : ByteArray) (memory : Memory) (cost gas : Nat)
    (execution : runWithCost fuel code frame = .ok (data, memory, cost))
    (insufficient : gas < cost) :
    runMetered fuel code frame gas = .ok .outOfGas := by
  induction fuel generalizing frame cost gas with
  | zero => simp only [runWithCost, reduceCtorEq] at execution
  | succ fuel ih =>
      cases hc : instructionCost code frame with
      | error message => simp [runWithCost, hc] at execution
      | ok charge =>
          cases hs : step code frame with
          | error message => simp [runWithCost, hc, hs] at execution
          | ok result =>
              cases result with
              | returned bytes mem =>
                  simp [runWithCost, hc, hs] at execution
                  rcases execution with ⟨rfl, rfl, rfl⟩
                  simp [runMetered, hc, insufficient]
              | next next =>
                  cases hr : runWithCost fuel code next with
                  | error message => simp [runWithCost, hc, hs, hr] at execution
                  | ok result =>
                      rcases result with ⟨bytes, mem, rest⟩
                      simp [runWithCost, hc, hs, hr] at execution
                      rcases execution with ⟨rfl, rfl, rfl⟩
                      by_cases exhausted : gas < charge
                      · simp [runMetered, hc, exhausted]
                      · have deficit : gas - charge < rest := by omega
                        simpa only [runMetered, hc, exhausted, if_false, hs] using
                          ih next rest (gas - charge) hr deficit

theorem words_mono {a b : Nat} (bounded : a ≤ b) : words a ≤ words b := by
  unfold words
  omega

theorem expansionCost_covered (memory : Memory) (offset size : Nat)
    (covered : offset + size ≤ memory.size) : expansionCost memory offset size = 0 := by
  have bound := words_mono covered
  simp only [expansionCost, Nat.max_eq_left bound, Nat.sub_self, ite_self]

theorem expansionCost_fresh (size : Nat) :
    expansionCost Memory.empty 0 size = memoryCost (words size) := by
  by_cases empty : size = 0
  · simp [expansionCost, empty, words, memoryCost]
  · have zero : words Memory.empty.size = 0 := rfl
    simp only [expansionCost, empty, if_false, zero, Nat.zero_add, Nat.zero_max]
    rfl

theorem copied_extent (source : Nat → Byte) (size : Nat) :
    size ≤ (Memory.empty.copyFrom source 0 11 size).size := by
  by_cases empty : size = 0
  · simp only [empty, Nat.zero_le]
  · simp only [Memory.copyFrom, empty, if_false, Memory.expand, Nat.zero_add]
    exact Nat.le_trans (expandedLength_covers _) (Nat.le_max_right _ _)

theorem expansionCost_copied (source : Nat → Byte) (size : Nat) :
    expansionCost (Memory.empty.copyFrom source 0 11 size) 0 size = 0 := by
  apply expansionCost_covered
  simpa only [Nat.zero_add] using copied_extent source size

def prefixCost (payloadSize : Nat) : Nat :=
  21 + 3 * words payloadSize + memoryCost (words payloadSize)

theorem run_prefix_cost (payload : ByteArray) (bounded : 11 + payload.size < modulus) :
    runWithCost 9 (initcode payload) initial =
      .ok (payload, Memory.empty.copyFrom (codeByte (initcode payload)) 0 11 payload.size,
        prefixCost payload.size) := by
  have sizeWord : (11 + payload.size) % modulus = 11 + payload.size := Nat.mod_eq_of_lt bounded
  have payloadBound : payload.size < modulus := by omega
  simp [runWithCost, instructionCost, step, advance, initial, fetch0, fetch1, fetch2,
    fetch3, fetch4, fetch5, fetch6, fetch7, fetch8, fetch9, fetch10, initcode_size,
    sizeWord, payload_length_sub payload.size payloadBound, returnMemory_copy,
    copied_payload, expansionCost_copied, expansionCost_fresh, prefixCost]
  omega

theorem metered_prefix (payload : ByteArray) (bounded : 11 + payload.size < modulus)
    (gas : Nat) :
    runMetered 9 (initcode payload) initial gas =
      if gas < prefixCost payload.size then .ok .outOfGas else
        .ok (.returned payload
          (Memory.empty.copyFrom (codeByte (initcode payload)) 0 11 payload.size)
          (gas - prefixCost payload.size)) := by
  by_cases exhausted : gas < prefixCost payload.size
  · simpa only [exhausted, if_true] using
      metered_insufficient 9 (initcode payload) initial payload _ _ gas
        (run_prefix_cost payload bounded) exhausted
  · simpa only [exhausted, if_false] using
      metered_sufficient 9 (initcode payload) initial payload _ _ gas
        (run_prefix_cost payload bounded) (Nat.le_of_not_lt exhausted)

end Verity.Core.Model.MidnightInitcode

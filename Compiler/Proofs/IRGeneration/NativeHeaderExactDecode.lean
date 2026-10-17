import Compiler.Proofs.IRGeneration.NativeMidnightConstructorData

/-! Actual native PUSH immediates as well as opcodes are header-local. -/
namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul NativeInitcodeFrames
open Verity.Core.Model.MidnightInitcode

private theorem header_extract (payload : ByteArray) (start stop : Nat)
    (ordered : start ≤ stop) (inside : stop ≤ 11) :
    (initcode payload).extract start stop = header.extract start stop := by
  apply ByteArray.ext
  simp only [ByteArray.data_extract, initcode]
  have rest : payload.data.extract (start - header.data.size) (stop - header.data.size) = #[] := by
    have begins : start - header.data.size = 0 := by change start - 11 = 0; omega
    have ends : stop - header.data.size = 0 := by change stop - 11 = 0; omega
    rw [begins, ends]
    simp
  rw [Array.extract_append, rest, Array.append_empty]

private theorem header_extract' (payload : ByteArray) (start stop : Nat)
    (ordered : start ≤ stop) (inside : stop ≤ 11) :
    (initcode payload).extract' start stop = header.extract' start stop := by
  have smallStart : start < 2^64 := by omega
  have smallStop : stop < 2^64 := by omega
  simp only [ByteArray.extract', smallStart, smallStop, decide_true, Bool.true_and, if_true]
  exact header_extract payload start stop ordered inside

private theorem decode_from_fetch (code : ByteArray) (pc : UInt256)
    (op : Operation .EVM) (fetch : (code.get? pc.toNat >>= EVM.parseInstr) = some op) :
    EVM.decode code pc = some (op, if EVM.argOnNBytesOfInstr op == 0 then none
      else some (uInt256OfByteArray (code.extract' pc.toNat.succ
        (pc.toNat.succ + EVM.argOnNBytesOfInstr op)), EVM.argOnNBytesOfInstr op)) := by
  unfold EVM.decode
  simp only [fetch]
  rfl

private theorem push_decode_congr (payload : ByteArray) (pc : UInt256)
    (position : pc.toNat = 0 ∨ pc.toNat = 5) :
    EVM.decode (initcode payload) pc = EVM.decode header pc := by
  have fetched : (header.get? pc.toNat >>= EVM.parseInstr) = some (Operation.Push .PUSH1) := by
    rcases position with h | h <;> rw [h] <;> rfl
  have fetchedCode : ((initcode payload).get? pc.toNat >>= EVM.parseInstr) =
      some (Operation.Push .PUSH1) := by
    rw [native_header_byte payload pc.toNat (by rcases position with h | h <;> omega)]
    exact fetched
  rw [decode_from_fetch _ _ _ fetchedCode, decode_from_fetch _ _ _ fetched]
  have same : (initcode payload).extract' pc.toNat.succ (pc.toNat.succ + 1) =
      header.extract' pc.toNat.succ (pc.toNat.succ + 1) := by
    apply header_extract'
    · omega
    · rcases position with h | h <;> omega
  exact congrArg (fun (bytes : ByteArray) => some (Operation.Push .PUSH1,
    some (uInt256OfByteArray bytes, (1 : Nat)))) same

private theorem decode_zero_width (code : ByteArray) (pc : UInt256) (op : Operation .EVM)
    (fetch : (code.get? pc.toNat >>= EVM.parseInstr) = some op)
    (zero : EVM.argOnNBytesOfInstr op = 0) :
    EVM.decode code pc = some (op, none) := by
  rw [decode_from_fetch code pc op fetch]
  simp only [zero, beq_self_eq_true, if_true]

/-- Native decoding of the exact header includes its actual PUSH1 word. -/
theorem decode_exact_header (payload : ByteArray) (pc : UInt256) (inside : pc.toNat < 11) :
    EVM.decode (initcode payload) pc = EVM.decode header pc := by
  by_cases push : pc.toNat = 0 ∨ pc.toNat = 5
  · exact push_decode_congr payload pc push
  have positions : pc.toNat = 1 ∨ pc.toNat = 2 ∨ pc.toNat = 3 ∨ pc.toNat = 4 ∨
      pc.toNat = 6 ∨ pc.toNat = 7 ∨ pc.toNat = 8 ∨ pc.toNat = 9 ∨ pc.toNat = 10 := by omega
  have fetch : ∃ op, (header.get? pc.toNat >>= EVM.parseInstr) = some op ∧
      EVM.argOnNBytesOfInstr op = 0 := by
    rcases positions with h | h | h | h | h | h | h | h | h
    all_goals rw [h]
    all_goals first
      | exact ⟨.SIGNEXTEND, rfl, rfl⟩
      | exact ⟨.CODESIZE, rfl, rfl⟩
      | exact ⟨.SUB, rfl, rfl⟩
      | exact ⟨.DUP1, rfl, rfl⟩
      | exact ⟨.Push .PUSH0, rfl, rfl⟩
      | exact ⟨.CODECOPY, rfl, rfl⟩
      | exact ⟨.RETURN, rfl, rfl⟩
  obtain ⟨op, parsed, zero⟩ := fetch
  have parsedCode : ((initcode payload).get? pc.toNat >>= EVM.parseInstr) = some op := by
    rw [native_header_byte payload pc.toNat inside]; exact parsed
  rw [decode_zero_width _ _ _ parsedCode zero, decode_zero_width _ _ _ parsed zero]

/-- At both actual PUSH1 positions the immediate is eleven, not payload data. -/
theorem decode_push_eleven (payload : ByteArray) (pc : UInt256)
    (position : pc.toNat = 0 ∨ pc.toNat = 5) :
    EVM.decode (initcode payload) pc =
      some (.Push .PUSH1, some (UInt256.ofNat 11, 1)) := by
  rw [decode_exact_header payload pc (by rcases position with h | h <;> omega)]
  rcases position with h | h
  all_goals simp only [EVM.decode, h]
  all_goals rfl

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor

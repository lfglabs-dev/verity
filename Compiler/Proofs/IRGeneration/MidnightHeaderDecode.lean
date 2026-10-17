import Compiler.Proofs.IRGeneration.NativeInitcodeFrames
import Verity.Core.Model.MidnightInitcode

/-! Actual native decoding of the Midnight constructor header. The payload is
arbitrary, and PUSH immediate bytes are included in the byte-index invariant. -/
namespace Compiler.Proofs.IRGeneration.NativeInitcodeFrames
open EvmYul
open Verity.Core.Model.MidnightInitcode

/-- Fetching a header byte never inspects the appended runtime payload. -/
theorem native_header_byte (payload : ByteArray) (offset : Nat) (inside : offset < 11) :
    (initcode payload).get? offset = header.get? offset := by
  have inHeader : offset < header.size := by change offset < 11; exact inside
  have inCode : offset < (initcode payload).size := by rw [initcode_size]; omega
  simp only [ByteArray.get?, inHeader, inCode, dif_pos]
  apply congrArg some
  change (header.data ++ payload.data)[offset] = header.data[offset]
  exact Array.getElem_append_left inHeader

/-- Native decode's opcode depends only on the instruction byte, independently
of the optional PUSH argument, which may read following bytes. -/
theorem native_decode_opcode (code : ByteArray) (pc : UInt256)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (decoded : EVM.decode code pc = some (op, arg)) :
    (code.get? pc.toNat >>= EVM.parseInstr) = some op := by
  unfold EVM.decode at decoded
  cases fetched : (code.get? pc.toNat >>= EVM.parseInstr) with
  | none => simp only [fetched] at decoded; cases decoded
  | some actual =>
    simp only [fetched] at decoded
    have same : actual = op := congrArg (fun x => x.1) (Option.some.inj decoded)
    simp only [same]

/-- Every byte below the header boundary decodes to a local instruction or
RETURN. Even the immediate byte 0x0b is local (SIGNEXTEND). -/
theorem native_header_local (payload : ByteArray) (pc : UInt256)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (inside : pc.toNat < 11)
    (decoded : EVM.decode (initcode payload) pc = some (op, arg)) :
    CreationCaller.supported op = true ∨ op = .RETURN := by
  have parsed := native_decode_opcode _ _ _ _ decoded
  rw [native_header_byte payload pc.toNat inside] at parsed
  have positions : pc.toNat = 0 ∨ pc.toNat = 1 ∨ pc.toNat = 2 ∨
      pc.toNat = 3 ∨ pc.toNat = 4 ∨ pc.toNat = 5 ∨ pc.toNat = 6 ∨
      pc.toNat = 7 ∨ pc.toNat = 8 ∨ pc.toNat = 9 ∨ pc.toNat = 10 := by omega
  rcases positions with position | position | position | position | position |
    position | position | position | position | position | position
  all_goals rw [position] at parsed
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

/-- A successful actual native step decoded anywhere inside the header cannot
change account state. This includes RETURN and arbitrary initial stack/memory;
control-flow preservation is a separate obligation. -/
theorem native_header_step_state (payload : ByteArray) (fuel gasCost : Nat)
    (before after : EVM.State) (op : Operation .EVM)
    (arg : Option (UInt256 × Nat))
    (inside : before.pc.toNat < 11)
    (decoded : EVM.decode (initcode payload) before.pc = some (op, arg))
    (success : EVM.step fuel gasCost (some (op, arg)) before = .ok after) :
    after.toState = before.toState := by
  have admitted : localOperation op = true := by
    rcases native_header_local payload before.pc op arg inside decoded with allowed | returning
    · simp only [localOperation, allowed, Bool.true_or]
    · subst op; decide
  exact local_step_state fuel op before after arg gasCost admitted success

end Compiler.Proofs.IRGeneration.NativeInitcodeFrames

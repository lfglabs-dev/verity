import Compiler.Proofs.IRGeneration.NativeSourceDynamicBody

namespace Compiler.Proofs.IRGeneration.NativeSourceDynamicHeader
open EvmYul EVM.Proof NativeSourcePreludeDecoded

theorem immediate555 : NativeSourceAbiWrite.code.extract' 556 558 = ⟨#[2, 206]⟩ := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]
    decide
  have byte0 : NativeSourceAbiWrite.code.data[556]? = some 2 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have byte1 : NativeSourceAbiWrite.code.data[557]? = some 206 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  apply ByteArray.ext
  simp only [ByteArray.extract', show (556 < 2^64 && 558 < 2^64) = true by decide, if_true,
    ByteArray.data_extract]
  apply Array.ext
  · simp only [Array.size_extract, size, ByteArray.size_data]
    decide
  · intro index left right
    have bound : index < 2 := by simpa using right
    have cases : index = 0 ∨ index = 1 := by omega
    rcases cases with zero | one
    · subst index
      simp only [Array.getElem_extract]
      exact Option.some.inj ((Array.getElem?_eq_getElem (by change 556 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte0)
    · subst index
      simp only [Array.getElem_extract]
      exact Option.some.inj ((Array.getElem?_eq_getElem (by change 557 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte1)

theorem decode551 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 551) = some (.JUMPDEST, none) := by
  have byte : NativeSourceAbiWrite.code.get? 551 = some 91 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 551).toNat = 551 by decide, byte]
  decide

theorem decode552 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 552) = some (.DUP2, none) := by
  have byte : NativeSourceAbiWrite.code.get? 552 = some 129 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 552).toNat = 552 by decide, byte]
  decide

theorem decode553 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 553) = some (.DUP2, none) := by
  have byte : NativeSourceAbiWrite.code.get? 553 = some 129 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 553).toNat = 553 by decide, byte]
  decide

theorem decode554 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 554) = some (.LT, none) := by
  have byte : NativeSourceAbiWrite.code.get? 554 = some 16 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 554).toNat = 554 by decide, byte]
  decide

theorem decode555 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 555) = some (.Push .PUSH2, some (UInt256.ofNat 718, 2)) := by
  have byte : NativeSourceAbiWrite.code.get? 555 = some 97 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 555).toNat = 555 by decide, byte]
  change some (Operation.Push Operation.POp.PUSH2, some (uInt256OfByteArray (NativeSourceAbiWrite.code.extract' 556 558), 2)) = _
  rw [immediate555]
  decide

theorem decode558 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 558) = some (.JUMPI, none) := by
  have byte : NativeSourceAbiWrite.code.get? 558 = some 87 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 558).toNat = 558 by decide, byte]
  decide

def s1 (cost : Nat) (pre : EVM.State) (index count : UInt256) (tail : Stack UInt256) :=
  (stepPre cost pre).replaceStackAndIncrPC (index :: count :: tail)

def s2 (cost : Nat) (pre : EVM.State) (index count : UInt256) (tail : Stack UInt256) :=
  (stepPre cost (s1 cost pre index count tail)).replaceStackAndIncrPC (count :: index :: count :: tail)

def s3 (cost : Nat) (pre : EVM.State) (index count : UInt256) (tail : Stack UInt256) :=
  (stepPre cost (s2 cost pre index count tail)).replaceStackAndIncrPC (index :: count :: index :: count :: tail)

def s4 (cost : Nat) (pre : EVM.State) (index count : UInt256) (tail : Stack UInt256) :=
  (stepPre cost (s3 cost pre index count tail)).replaceStackAndIncrPC (UInt256.lt index count :: index :: count :: tail)

def s5 (cost : Nat) (pre : EVM.State) (index count : UInt256) (tail : Stack UInt256) :=
  (stepPre cost (s4 cost pre index count tail)).replaceStackAndIncrPC (UInt256.ofNat 718 :: UInt256.lt index count :: index :: count :: tail) 3

def s6 (cost : Nat) (pre : EVM.State) (index count : UInt256) (tail : Stack UInt256) : EVM.State :=
  { stepPre cost (s5 cost pre index count tail) with
    pc := if UInt256.lt index count != ⟨0⟩ then UInt256.ofNat 718 else (s5 cost pre index count tail).pc + ⟨1⟩,
    stack := index :: count :: tail }

theorem transition1 (fuel cost : Nat) (pre : EVM.State) (index count : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 551)
    (stack : pre.stack = index :: count :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt pre)) pre = .ok (s1 cost pre index count tail) := by
  have atPC : pre.pc = UInt256.ofNat 551 := by
    exact pc
  have decoded : decodeAt pre = (.JUMPDEST, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code pre.pc).getD _ = _
    rw [code, atPC, decode551]; rfl
  rw [decoded]
  rw [step_JUMPDEST]
  simp only [stepPre, stack]
  rfl

theorem transition2 (fuel cost : Nat) (pre : EVM.State) (index count : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 551)
    (stack : pre.stack = index :: count :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s1 cost pre index count tail))) (s1 cost pre index count tail) = .ok (s2 cost pre index count tail) := by
  have atPC : (s1 cost pre index count tail).pc = UInt256.ofNat 552 := by
    change (pre.pc + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s1 cost pre index count tail) = (.DUP2, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s1 cost pre index count tail).pc).getD _ = _
    rw [code, atPC, decode552]; rfl
  rw [decoded]
  change EvmYul.dup 2 (stepPre cost (s1 cost pre index count tail)) = _
  unfold EvmYul.dup
  rfl

theorem transition3 (fuel cost : Nat) (pre : EVM.State) (index count : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 551)
    (stack : pre.stack = index :: count :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s2 cost pre index count tail))) (s2 cost pre index count tail) = .ok (s3 cost pre index count tail) := by
  have atPC : (s2 cost pre index count tail).pc = UInt256.ofNat 553 := by
    change ((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s2 cost pre index count tail) = (.DUP2, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s2 cost pre index count tail).pc).getD _ = _
    rw [code, atPC, decode553]; rfl
  rw [decoded]
  change EvmYul.dup 2 (stepPre cost (s2 cost pre index count tail)) = _
  unfold EvmYul.dup
  rfl

theorem transition4 (fuel cost : Nat) (pre : EVM.State) (index count : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 551)
    (stack : pre.stack = index :: count :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s3 cost pre index count tail))) (s3 cost pre index count tail) = .ok (s4 cost pre index count tail) := by
  have atPC : (s3 cost pre index count tail).pc = UInt256.ofNat 554 := by
    change (((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s3 cost pre index count tail) = (.LT, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s3 cost pre index count tail).pc).getD _ = _
    rw [code, atPC, decode554]; rfl
  rw [decoded]
  change EVM.execBinOp UInt256.lt (stepPre cost (s3 cost pre index count tail)) = _
  unfold EVM.execBinOp
  rfl

theorem transition5 (fuel cost : Nat) (pre : EVM.State) (index count : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 551)
    (stack : pre.stack = index :: count :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s4 cost pre index count tail))) (s4 cost pre index count tail) = .ok (s5 cost pre index count tail) := by
  have atPC : (s4 cost pre index count tail).pc = UInt256.ofNat 555 := by
    change ((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
    rw [pc]; decide
  have decoded : decodeAt (s4 cost pre index count tail) = (.Push .PUSH2, some (UInt256.ofNat 718, 2)) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s4 cost pre index count tail).pc).getD _ = _
    rw [code, atPC, decode555]; rfl
  rw [decoded]
  rfl

theorem transition6 (fuel cost : Nat) (pre : EVM.State) (index count : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 551)
    (stack : pre.stack = index :: count :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s5 cost pre index count tail))) (s5 cost pre index count tail) = .ok (s6 cost pre index count tail) := by
  have atPC : (s5 cost pre index count tail).pc = UInt256.ofNat 558 := by
    change (((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 3) = _
    rw [pc]; decide
  have decoded : decodeAt (s5 cost pre index count tail) = (.JUMPI, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s5 cost pre index count tail).pc).getD _ = _
    rw [code, atPC, decode558]; rfl
  rw [decoded]
  rfl

theorem execute (fuel cost : Nat) (pre : EVM.State) (index count : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 551)
    (stack : pre.stack = index :: count :: tail) :
    run fuel cost 6 pre = .ok (s6 cost pre index count tail) := by
  rw [run, transition1 fuel cost pre index count tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition2 fuel cost pre index count tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition3 fuel cost pre index count tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition4 fuel cost pre index count tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition5 fuel cost pre index count tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition6 fuel cost pre index count tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rfl

theorem memory (cost : Nat) (pre : EVM.State) (index count : UInt256) (tail : Stack UInt256) : (s6 cost pre index count tail).memory = pre.memory := by
  rfl

theorem output_stack (cost : Nat) (pre : EVM.State) (index count : UInt256) (tail : Stack UInt256) : (s6 cost pre index count tail).stack = index :: count :: tail := by
  rfl

theorem continue_pc (cost : Nat) (pre : EVM.State) (index count : UInt256) (tail : Stack UInt256)
    (less : index < count) : (s6 cost pre index count tail).pc = UInt256.ofNat 718 := by
  change (if UInt256.lt index count != ⟨0⟩ then _ else _) = _
  have value : UInt256.lt index count = UInt256.ofNat 1 := by
    simp [UInt256.lt, UInt256.fromBool, Bool.toUInt256, less]
  rw [value, show (UInt256.ofNat 1 != (⟨0⟩ : UInt256)) = true by decide]
  rfl

theorem exit_pc (cost : Nat) (pre : EVM.State) (index count : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 551) (done : ¬index < count) :
    (s6 cost pre index count tail).pc = UInt256.ofNat 559 := by
  change (if UInt256.lt index count != ⟨0⟩ then _ else _) = _
  have value : UInt256.lt index count = UInt256.ofNat 0 := by
    simp [UInt256.lt, UInt256.fromBool, Bool.toUInt256, done]
  rw [value, show (UInt256.ofNat 0 != (⟨0⟩ : UInt256)) = false by decide]
  change (((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 3) + ⟨1⟩ = _
  rw [pc]; decide

end Compiler.Proofs.IRGeneration.NativeSourceDynamicHeader

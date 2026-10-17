import Compiler.Proofs.IRGeneration.NativeSourceAddressGuardExecution

namespace Compiler.Proofs.IRGeneration.NativeSourceAddressBranch
open EvmYul EVM.Proof NativeSourcePreludeDecoded

theorem immediate : NativeSourceAbiWrite.code.extract' 960 962 = ⟨#[0, 91]⟩ := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]
    decide
  have byte1 : NativeSourceAbiWrite.code.data[960]? = some 0 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have byte2 : NativeSourceAbiWrite.code.data[961]? = some 91 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  apply ByteArray.ext
  simp only [ByteArray.extract', show (960 < 2^64 && 962 < 2^64) = true by decide, if_true,
    ByteArray.data_extract]
  apply Array.ext
  · simp only [Array.size_extract, size, ByteArray.size_data]
    decide
  · intro index left right
    have bound : index < 2 := by simpa using right
    have cases : index = 0 ∨ index = 1 := by omega
    rcases cases with zero | one
    · subst index
      simp only [Array.getElem_extract, Nat.add_zero]
      exact Option.some.inj ((Array.getElem?_eq_getElem (by change 960 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte1)
    · subst index
      simp only [Array.getElem_extract]
      exact Option.some.inj ((Array.getElem?_eq_getElem (by change 961 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte2)

theorem decode959 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 959) =
    some (.Push .PUSH2, some (UInt256.ofNat 91, 2)) := by
  have byte : NativeSourceAbiWrite.code.get? 959 = some 97 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 959).toNat = 959 by decide, byte]
  change some (Operation.Push Operation.POp.PUSH2, some (uInt256OfByteArray (NativeSourceAbiWrite.code.extract' 960 962), 2)) = _
  rw [immediate]
  decide


theorem decode962 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 962) = some (.JUMPI, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 962).toNat = some 87 := by
    have index : (UInt256.ofNat 962).toNat = 962 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

def pushed (cost : Nat) (pre : EVM.State) :=
  (stepPre cost pre).replaceStackAndIncrPC (UInt256.ofNat 91 :: pre.stack) 3

def branched (cost : Nat) (pre : EVM.State) (condition : UInt256) (rest : Stack UInt256) : EVM.State :=
  { stepPre cost (pushed cost pre) with
    pc := if condition != ⟨0⟩ then UInt256.ofNat 91 else (pushed cost pre).pc + ⟨1⟩,
    stack := rest }

theorem push (fuel cost : Nat) (pre : EVM.State)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 959) :
    EVM.step (fuel + 1) cost (some (decodeAt pre)) pre = .ok (pushed cost pre) := by
  have decoded : decodeAt pre = (.Push .PUSH2, some (UInt256.ofNat 91, 2)) := by
    unfold decodeAt
    rw [code, pc, decode959]
    rfl
  rw [decoded]
  rfl

theorem jump (fuel cost : Nat) (pre : EVM.State) (condition : UInt256) (rest : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 959)
    (stack : pre.stack = condition :: rest) :
    EVM.step (fuel + 1) cost (some (decodeAt (pushed cost pre))) (pushed cost pre) =
      .ok (branched cost pre condition rest) := by
  have atPC : (pushed cost pre).pc = UInt256.ofNat 962 := by
    change pre.pc + UInt256.ofNat 3 = _
    rw [pc]; decide
  have decoded : decodeAt (pushed cost pre) = (.JUMPI, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (pushed cost pre).pc).getD _ = _
    rw [code, atPC, decode962]
    rfl
  rw [decoded]
  change EvmYul.step (τ := .EVM) .JUMPI none (stepPre cost (pushed cost pre)) = _
  unfold EvmYul.step
  simp only [stepPre, pushed, EVM.State.replaceStackAndIncrPC, stack]
  rfl

theorem execute (fuel cost : Nat) (pre : EVM.State) (condition : UInt256) (rest : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 959)
    (stack : pre.stack = condition :: rest) :
    run fuel cost 2 pre = .ok (branched cost pre condition rest) := by
  rw [run, push fuel cost pre code pc]
  simp only [Bind.bind, Except.bind]
  rw [run, jump fuel cost pre condition rest code pc stack]
  rfl

theorem destinations (cost : Nat) (pre : EVM.State) (condition : UInt256) (rest : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 959) :
    (branched cost pre condition rest).pc =
      if condition != ⟨0⟩ then UInt256.ofNat 91 else UInt256.ofNat 963 := by
  change (if condition != ⟨0⟩ then UInt256.ofNat 91 else
    (pre.pc + UInt256.ofNat 3) + ⟨1⟩) = _
  rw [pc]
  rfl

theorem memory (cost : Nat) (pre : EVM.State) (condition : UInt256) (rest : Stack UInt256) :
    (branched cost pre condition rest).memory = pre.memory := by rfl

theorem output_stack (cost : Nat) (pre : EVM.State) (condition : UInt256) (rest : Stack UInt256) :
    (branched cost pre condition rest).stack = rest := by rfl

theorem nonzero_flag (word : UInt256) :
    (word != ⟨0⟩) = true ↔ word ≠ UInt256.ofNat 0 := by
  cases word with
  | mk value =>
    change (value != 0) = true ↔ UInt256.mk value ≠ UInt256.mk 0
    rw [ne_eq, UInt256.mk.injEq]
    simp

theorem address_destinations (cost : Nat) (pre : EVM.State) (word ret : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 959) :
    (branched cost pre (word - word.land NativeSourceAddressCanonicality.mask) (ret :: word :: tail)).pc =
      if word.toNat < 2 ^ 160 then UInt256.ofNat 963 else UInt256.ofNat 91 := by
  rw [destinations cost pre _ _ pc]
  by_cases canonical : word.toNat < 2 ^ 160
  · have zero := (NativeSourceAddressCanonicality.difference_zero_iff word).mpr canonical
    rw [if_pos canonical, zero]
    decide
  · have nonzero : word - word.land NativeSourceAddressCanonicality.mask ≠ UInt256.ofNat 0 := by
      intro zero
      exact canonical ((NativeSourceAddressCanonicality.difference_zero_iff word).mp zero)
    rw [if_neg canonical, if_pos ((nonzero_flag _).mpr nonzero)]

theorem decode963 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 963) = some (.JUMP, none) := by
  have byte : NativeSourceAbiWrite.code.get? 963 = some 86 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 963).toNat = 963 by decide, byte]
  decide

def returned (cost : Nat) (pre : EVM.State) (ret word : UInt256) (tail : Stack UInt256) : EVM.State :=
  { stepPre cost pre with pc := ret, stack := word :: tail }

theorem return_step (fuel cost : Nat) (pre : EVM.State) (ret word : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 963)
    (stack : pre.stack = ret :: word :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt pre)) pre = .ok (returned cost pre ret word tail) := by
  have decoded : decodeAt pre = (.JUMP, none) := by
    unfold decodeAt
    rw [code, pc, decode963]; rfl
  rw [decoded]
  change EvmYul.step (τ := .EVM) .JUMP none (stepPre cost pre) = _
  unfold EvmYul.step
  simp only [stepPre, stack]
  rfl

end Compiler.Proofs.IRGeneration.NativeSourceAddressBranch

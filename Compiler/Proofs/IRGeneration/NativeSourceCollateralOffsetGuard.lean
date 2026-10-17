import Mathlib.Tactic.IntervalCases
import Compiler.Proofs.IRGeneration.NativeSourceCollateralOffsetLoad

namespace Compiler.Proofs.IRGeneration.NativeSourceCollateralOffsetGuard
open EvmYul EVM EVM.Proof

def limit := UInt256.ofNat (2^64-1)
def flag (offset : UInt256) := UInt256.gt offset limit

theorem immediate224 : NativeSourceAbiWrite.code.extract' 225 233 = ⟨#[255,255,255,255,255,255,255,255]⟩ := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte (i : Nat) (bound : i < 8) : NativeSourceAbiWrite.code.data[225+i]? = some 255 := by
    interval_cases i <;> simp only [NativeSourceAbiWrite.code, ByteArray.data_append,
      Array.getElem?_append, Array.size_append] <;> norm_num
  apply ByteArray.ext
  simp only [ByteArray.extract', show (225 < 2^64 && 233 < 2^64) = true by decide, if_true, ByteArray.data_extract]
  apply Array.ext
  · simp only [Array.size_extract, size, ByteArray.size_data]; decide
  · intro index left right
    have bound : index < 8 := by simpa using right
    have constant : (#[255,255,255,255,255,255,255,255] : Array UInt8)[index] = 255 := by
      interval_cases index <;> rfl
    simp only [Array.getElem_extract, constant]
    exact Option.some.inj ((Array.getElem?_eq_getElem (by change 225+index < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans (byte index bound))

theorem immediate235 : NativeSourceAbiWrite.code.extract' 236 238 = ⟨#[0, 91]⟩ := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]
    decide
  have byte1 : NativeSourceAbiWrite.code.data[236]? = some 0 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have byte2 : NativeSourceAbiWrite.code.data[237]? = some 91 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  apply ByteArray.ext
  simp only [ByteArray.extract', show (236 < 2^64 && 238 < 2^64) = true by decide, if_true,
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
      exact Option.some.inj ((Array.getElem?_eq_getElem (by change 236 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte1)
    · subst index
      simp only [Array.getElem_extract]
      exact Option.some.inj ((Array.getElem?_eq_getElem (by change 237 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte2)

theorem decode224 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 224) = some (.Push .PUSH8, some (limit, 8)) := by
  have byte : NativeSourceAbiWrite.code.get? 224 = some 103 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 224).toNat = 224 by decide, byte]
  change some (Operation.Push Operation.POp.PUSH8, some (uInt256OfByteArray (NativeSourceAbiWrite.code.extract' 225 233), 8)) = _
  rw [immediate224]
  decide

theorem decode233 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 233) = some (.DUP2, none) := by
  have byte : NativeSourceAbiWrite.code.get? 233 = some 129 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 233).toNat = 233 by decide, byte]
  decide

theorem decode234 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 234) = some (.GT, none) := by
  have byte : NativeSourceAbiWrite.code.get? 234 = some 17 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 234).toNat = 234 by decide, byte]
  decide

theorem decode235 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 235) = some (.Push .PUSH2, some (UInt256.ofNat 91, 2)) := by
  have byte : NativeSourceAbiWrite.code.get? 235 = some 97 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 235).toNat = 235 by decide, byte]
  change some (Operation.Push Operation.POp.PUSH2, some (uInt256OfByteArray (NativeSourceAbiWrite.code.extract' 236 238), 2)) = _
  rw [immediate235]
  decide

theorem decode238 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 238) = some (.JUMPI, none) := by
  have byte : NativeSourceAbiWrite.code.get? 238 = some 87 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 238).toNat = 238 by decide, byte]
  decide

def s1 (pre : EVM.State) (offset : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 pre).replaceStackAndIncrPC (limit :: offset :: tail) 9

def s2 (pre : EVM.State) (offset : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 (s1 pre offset tail)).replaceStackAndIncrPC (offset :: limit :: offset :: tail) 1

def s3 (pre : EVM.State) (offset : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 (s2 pre offset tail)).replaceStackAndIncrPC (flag offset :: offset :: tail) 1

def s4 (pre : EVM.State) (offset : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 (s3 pre offset tail)).replaceStackAndIncrPC (UInt256.ofNat 91 :: flag offset :: offset :: tail) 3

theorem transition1 (fuel : Nat) (pre : EVM.State) (offset : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 224)
    (stack : pre.stack = offset :: tail) :
    EVM.step (fuel + 1) 3 (some (decodeAt pre)) pre = .ok (s1 pre offset tail) := by
  have atPC : pre.pc = UInt256.ofNat 224 := by
    exact pc
  have decoded : decodeAt pre = (.Push .PUSH8, some (limit, 8)) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code pre.pc).getD _ = _
    rw [code, atPC, decode224]; rfl
  rw [decoded]
  change Except.ok ((stepPre 3 pre).replaceStackAndIncrPC (limit :: pre.stack) 9) = _
  rw [stack]; rfl

theorem transition2 (fuel : Nat) (pre : EVM.State) (offset : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 224)
    (stack : pre.stack = offset :: tail) :
    EVM.step (fuel + 1) 3 (some (decodeAt (s1 pre offset tail))) (s1 pre offset tail) = .ok (s2 pre offset tail) := by
  have atPC : (s1 pre offset tail).pc = UInt256.ofNat 233 := by
    simp only [s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s1 pre offset tail) = (.DUP2, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s1 pre offset tail).pc).getD _ = _
    rw [code, atPC, decode233]; rfl
  rw [decoded]
  change EvmYul.dup 2 (stepPre 3 (s1 pre offset tail)) = _
  unfold EvmYul.dup
  simp only [s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack]
  rfl

theorem transition3 (fuel : Nat) (pre : EVM.State) (offset : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 224)
    (stack : pre.stack = offset :: tail) :
    EVM.step (fuel + 1) 3 (some (decodeAt (s2 pre offset tail))) (s2 pre offset tail) = .ok (s3 pre offset tail) := by
  have atPC : (s2 pre offset tail).pc = UInt256.ofNat 234 := by
    simp only [s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s2 pre offset tail) = (.GT, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s2 pre offset tail).pc).getD _ = _
    rw [code, atPC, decode234]; rfl
  rw [decoded]
  change EvmYul.step (τ := .EVM) .GT none (stepPre 3 (s2 pre offset tail)) = _
  unfold EvmYul.step
  simp only [s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack]
  rfl

theorem transition4 (fuel : Nat) (pre : EVM.State) (offset : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 224)
    (_stack : pre.stack = offset :: tail) :
    EVM.step (fuel + 1) 3 (some (decodeAt (s3 pre offset tail))) (s3 pre offset tail) = .ok (s4 pre offset tail) := by
  have atPC : (s3 pre offset tail).pc = UInt256.ofNat 235 := by
    simp only [s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s3 pre offset tail) = (.Push .PUSH2, some (UInt256.ofNat 91, 2)) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s3 pre offset tail).pc).getD _ = _
    rw [code, atPC, decode235]; rfl
  rw [decoded]
  rfl

theorem flag_zero (offset : UInt256) (valid : offset.toNat ≤ 2^64-1) : flag offset = UInt256.ofNat 0 := by
  have limitNat : limit.toNat = 2^64-1 := by decide
  have ordered : ¬offset > limit := by change ¬offset.val > limit.val; change ¬offset.toNat > limit.toNat; omega
  simp [flag, UInt256.gt, UInt256.fromBool, ordered]

theorem flag_nonzero (offset : UInt256) (invalid : 2^64-1 < offset.toNat) : flag offset ≠ UInt256.ofNat 0 := by
  have limitNat : limit.toNat = 2^64-1 := by decide
  have ordered : offset > limit := by change offset.val > limit.val; change offset.toNat > limit.toNat; omega
  simp [flag, UInt256.gt, UInt256.fromBool, ordered]
  decide

end Compiler.Proofs.IRGeneration.NativeSourceCollateralOffsetGuard


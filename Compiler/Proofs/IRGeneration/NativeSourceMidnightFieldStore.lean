import Compiler.Proofs.IRGeneration.NativeSourceAddressEntryCertificate

namespace Compiler.Proofs.IRGeneration.NativeSourceMidnightFieldStore
open EvmYul EVM EVM.Proof

theorem immediate192 : NativeSourceAbiWrite.code.extract' 193 194 = ⟨#[32]⟩ := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[193]? = some 32 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  apply ByteArray.ext
  simp only [ByteArray.extract', show (193 < 2^64 && 194 < 2^64) = true by decide, if_true, ByteArray.data_extract]
  apply Array.ext
  · simp only [Array.size_extract, size, ByteArray.size_data]; decide
  · intro index left right
    have bound : index < 1 := by simpa using right
    have zero : index = 0 := by omega
    subst index
    simp only [Array.getElem_extract, Nat.add_zero]
    exact Option.some.inj ((Array.getElem?_eq_getElem (by change 193 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte)

theorem decode191 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 191) = some (.JUMPDEST, none) := by
  have byte : NativeSourceAbiWrite.code.get? 191 = some 91 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 191).toNat = 191 by decide, byte]
  decide

theorem decode192 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 192) = some ((.Push .PUSH1), some (UInt256.ofNat 32, 1)) := by
  have byte : NativeSourceAbiWrite.code.get? 192 = some 96 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 192).toNat = 192 by decide, byte]
  change some (Operation.Push Operation.POp.PUSH1, some (uInt256OfByteArray (NativeSourceAbiWrite.code.extract' 193 194), 1)) = _
  rw [immediate192]
  decide

theorem decode194 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 194) = some (.DUP4, none) := by
  have byte : NativeSourceAbiWrite.code.get? 194 = some 131 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 194).toNat = 194 by decide, byte]
  decide

theorem decode195 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 195) = some (.ADD, none) := by
  have byte : NativeSourceAbiWrite.code.get? 195 = some 1 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 195).toNat = 195 by decide, byte]
  decide

theorem decode196 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 196) = some (.SWAP1, none) := by
  have byte : NativeSourceAbiWrite.code.get? 196 = some 144 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 196).toNat = 196 by decide, byte]
  decide

theorem decode197 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 197) = some (.DUP2, none) := by
  have byte : NativeSourceAbiWrite.code.get? 197 = some 129 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 197).toNat = 197 by decide, byte]
  decide

theorem decode198 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 198) = some (.MSTORE, none) := by
  have byte : NativeSourceAbiWrite.code.get? 198 = some 82 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 198).toNat = 198 by decide, byte]
  decide

def s1 (pre : EVM.State) := (stepPre 1 pre).incrPC

def s2 (pre : EVM.State) (word a base : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 (s1 pre)).replaceStackAndIncrPC (UInt256.ofNat 32 :: word :: a :: base :: tail) 2

def s3 (pre : EVM.State) (word a base : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 (s2 pre word a base tail)).replaceStackAndIncrPC (base :: UInt256.ofNat 32 :: word :: a :: base :: tail)

def s4 (pre : EVM.State) (word a base : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 (s3 pre word a base tail)).replaceStackAndIncrPC ((base + UInt256.ofNat 32) :: word :: a :: base :: tail)

def s5 (pre : EVM.State) (word a base : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 (s4 pre word a base tail)).replaceStackAndIncrPC (word :: (base + UInt256.ofNat 32) :: a :: base :: tail)

def s6 (pre : EVM.State) (word a base : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 (s5 pre word a base tail)).replaceStackAndIncrPC ((base + UInt256.ofNat 32) :: word :: (base + UInt256.ofNat 32) :: a :: base :: tail)

def stored (cost : Nat) (pre : EVM.State) (word a base : UInt256) (tail : Stack UInt256) :=
  mstorePost cost (s6 pre word a base tail) ((base + UInt256.ofNat 32) :: a :: base :: tail) (base + UInt256.ofNat 32) word

theorem transition1 (fuel cost : Nat) (pre : EVM.State) (word a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 191)
    (stack : pre.stack = word :: a :: base :: tail) :
    EVM.step (fuel + 1) 1 (some (decodeAt pre)) pre = .ok (s1 pre) := by
  have atPC : pre.pc = UInt256.ofNat 191 := by
    exact pc
  have decoded : decodeAt pre = (.JUMPDEST, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code pre.pc).getD _ = _
    rw [code, atPC, decode191]; rfl
  rw [decoded]
  exact step_JUMPDEST fuel 1 pre

theorem transition2 (fuel cost : Nat) (pre : EVM.State) (word a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 191)
    (stack : pre.stack = word :: a :: base :: tail) :
    EVM.step (fuel + 1) 3 (some (decodeAt (s1 pre))) (s1 pre) = .ok (s2 pre word a base tail) := by
  have atPC : (s1 pre).pc = UInt256.ofNat 192 := by
    simp only [s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s1 pre) = ((.Push .PUSH1), some (UInt256.ofNat 32, 1)) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s1 pre).pc).getD _ = _
    rw [code, atPC, decode192]; rfl
  rw [decoded]
  change Except.ok ((stepPre 3 (s1 pre)).replaceStackAndIncrPC (UInt256.ofNat 32 :: pre.stack) 2) = _
  rw [stack]
  rfl

theorem transition3 (fuel cost : Nat) (pre : EVM.State) (word a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 191)
    (stack : pre.stack = word :: a :: base :: tail) :
    EVM.step (fuel + 1) 3 (some (decodeAt (s2 pre word a base tail))) (s2 pre word a base tail) = .ok (s3 pre word a base tail) := by
  have atPC : (s2 pre word a base tail).pc = UInt256.ofNat 194 := by
    simp only [s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s2 pre word a base tail) = (.DUP4, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s2 pre word a base tail).pc).getD _ = _
    rw [code, atPC, decode194]; rfl
  rw [decoded]
  change EvmYul.dup 4 (stepPre 3 (s2 pre word a base tail)) = _
  unfold EvmYul.dup
  simp only [s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack]
  rfl

theorem transition4 (fuel cost : Nat) (pre : EVM.State) (word a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 191)
    (stack : pre.stack = word :: a :: base :: tail) :
    EVM.step (fuel + 1) 3 (some (decodeAt (s3 pre word a base tail))) (s3 pre word a base tail) = .ok (s4 pre word a base tail) := by
  have atPC : (s3 pre word a base tail).pc = UInt256.ofNat 195 := by
    simp only [s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s3 pre word a base tail) = (.ADD, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s3 pre word a base tail).pc).getD _ = _
    rw [code, atPC, decode195]; rfl
  rw [decoded]
  change EvmYul.step (τ := .EVM) .ADD none (stepPre 3 (s3 pre word a base tail)) = _
  unfold EvmYul.step
  simp only [s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack]
  rfl

theorem transition5 (fuel cost : Nat) (pre : EVM.State) (word a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 191)
    (stack : pre.stack = word :: a :: base :: tail) :
    EVM.step (fuel + 1) 3 (some (decodeAt (s4 pre word a base tail))) (s4 pre word a base tail) = .ok (s5 pre word a base tail) := by
  have atPC : (s4 pre word a base tail).pc = UInt256.ofNat 196 := by
    simp only [s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s4 pre word a base tail) = (.SWAP1, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s4 pre word a base tail).pc).getD _ = _
    rw [code, atPC, decode196]; rfl
  rw [decoded]
  change EvmYul.swap 1 (stepPre 3 (s4 pre word a base tail)) = _
  unfold EvmYul.swap
  simp only [s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack]
  rfl

theorem transition6 (fuel cost : Nat) (pre : EVM.State) (word a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 191)
    (stack : pre.stack = word :: a :: base :: tail) :
    EVM.step (fuel + 1) 3 (some (decodeAt (s5 pre word a base tail))) (s5 pre word a base tail) = .ok (s6 pre word a base tail) := by
  have atPC : (s5 pre word a base tail).pc = UInt256.ofNat 197 := by
    simp only [s5, s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s5 pre word a base tail) = (.DUP2, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s5 pre word a base tail).pc).getD _ = _
    rw [code, atPC, decode197]; rfl
  rw [decoded]
  change EvmYul.dup 2 (stepPre 3 (s5 pre word a base tail)) = _
  unfold EvmYul.dup
  simp only [s5, s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC, stack]
  rfl

theorem transition7 (fuel cost : Nat) (pre : EVM.State) (word a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 191)
    (stack : pre.stack = word :: a :: base :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s6 pre word a base tail))) (s6 pre word a base tail) = .ok (stored cost pre word a base tail) := by
  have atPC : (s6 pre word a base tail).pc = UInt256.ofNat 198 := by
    simp only [s6, s5, s4, s3, s2, s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  have decoded : decodeAt (s6 pre word a base tail) = (.MSTORE, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s6 pre word a base tail).pc).getD _ = _
    rw [code, atPC, decode198]; rfl
  rw [decoded]
  exact step_MSTORE fuel cost (s6 pre word a base tail) _ (base + UInt256.ofNat 32) word (by rfl)

theorem stored_stack (cost : Nat) (pre : EVM.State) (word a base : UInt256) (tail : Stack UInt256) :
    (stored cost pre word a base tail).stack = (base + UInt256.ofNat 32) :: a :: base :: tail := by rfl

theorem stored_memory (cost : Nat) (pre : EVM.State) (word a base : UInt256) (tail : Stack UInt256) :
    (stored cost pre word a base tail).memory =
      (pre.toMachineState.mstore (base + UInt256.ofNat 32) word).memory := by rfl

theorem stored_world (cost : Nat) (pre : EVM.State) (word a base : UInt256) (tail : Stack UInt256) :
    (stored cost pre word a base tail).toState = pre.toState := by rfl

end Compiler.Proofs.IRGeneration.NativeSourceMidnightFieldStore

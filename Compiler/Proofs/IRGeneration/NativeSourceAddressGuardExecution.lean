import Compiler.Proofs.IRGeneration.NativeSourceAddressCanonicality
import Compiler.Proofs.IRGeneration.NativeSourcePreludeDecoded

namespace Compiler.Proofs.IRGeneration.NativeSourceAddressGuardExecution
open EvmYul EVM.Proof NativeSourcePreludeDecoded

theorem immediate947 : NativeSourceAbiWrite.code.extract' 948 949 = ⟨#[1]⟩ := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[948]? = some 1 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  apply ByteArray.ext
  simp only [ByteArray.extract', show (948 < 2^64 && 949 < 2^64) = true by decide, if_true, ByteArray.data_extract]
  apply Array.ext
  · simp only [Array.size_extract, size, ByteArray.size_data]; decide
  · intro index left right
    have bound : index < 1 := by simpa using right
    have zero : index = 0 := by omega
    subst index
    simp only [Array.getElem_extract, Nat.add_zero]
    exact Option.some.inj ((Array.getElem?_eq_getElem (by change 948 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte)

theorem immediate949 : NativeSourceAbiWrite.code.extract' 950 951 = ⟨#[1]⟩ := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[950]? = some 1 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  apply ByteArray.ext
  simp only [ByteArray.extract', show (950 < 2^64 && 951 < 2^64) = true by decide, if_true, ByteArray.data_extract]
  apply Array.ext
  · simp only [Array.size_extract, size, ByteArray.size_data]; decide
  · intro index left right
    have bound : index < 1 := by simpa using right
    have zero : index = 0 := by omega
    subst index
    simp only [Array.getElem_extract, Nat.add_zero]
    exact Option.some.inj ((Array.getElem?_eq_getElem (by change 950 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte)

theorem immediate951 : NativeSourceAbiWrite.code.extract' 952 953 = ⟨#[160]⟩ := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[952]? = some 160 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  apply ByteArray.ext
  simp only [ByteArray.extract', show (952 < 2^64 && 953 < 2^64) = true by decide, if_true, ByteArray.data_extract]
  apply Array.ext
  · simp only [Array.size_extract, size, ByteArray.size_data]; decide
  · intro index left right
    have bound : index < 1 := by simpa using right
    have zero : index = 0 := by omega
    subst index
    simp only [Array.getElem_extract, Nat.add_zero]
    exact Option.some.inj ((Array.getElem?_eq_getElem (by change 952 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte)

theorem decode946 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 946) = some (.SWAP1, none) := by
  have byte : NativeSourceAbiWrite.code.get? 946 = some 144 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 946).toNat = 946 by decide, byte]
  decide

theorem decode947 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 947) = some (.Push .PUSH1, some (UInt256.ofNat 1, 1)) := by
  have byte : NativeSourceAbiWrite.code.get? 947 = some 96 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 947).toNat = 947 by decide, byte]
  change some (Operation.Push Operation.POp.PUSH1, some (uInt256OfByteArray (NativeSourceAbiWrite.code.extract' 948 949), 1)) = _
  rw [immediate947]
  decide

theorem decode949 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 949) = some (.Push .PUSH1, some (UInt256.ofNat 1, 1)) := by
  have byte : NativeSourceAbiWrite.code.get? 949 = some 96 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 949).toNat = 949 by decide, byte]
  change some (Operation.Push Operation.POp.PUSH1, some (uInt256OfByteArray (NativeSourceAbiWrite.code.extract' 950 951), 1)) = _
  rw [immediate949]
  decide

theorem decode951 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 951) = some (.Push .PUSH1, some (UInt256.ofNat 160, 1)) := by
  have byte : NativeSourceAbiWrite.code.get? 951 = some 96 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 951).toNat = 951 by decide, byte]
  change some (Operation.Push Operation.POp.PUSH1, some (uInt256OfByteArray (NativeSourceAbiWrite.code.extract' 952 953), 1)) = _
  rw [immediate951]
  decide

theorem decode953 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 953) = some (.SHL, none) := by
  have byte : NativeSourceAbiWrite.code.get? 953 = some 27 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 953).toNat = 953 by decide, byte]
  decide

theorem decode954 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 954) = some (.SUB, none) := by
  have byte : NativeSourceAbiWrite.code.get? 954 = some 3 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 954).toNat = 954 by decide, byte]
  decide

theorem decode955 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 955) = some (.DUP3, none) := by
  have byte : NativeSourceAbiWrite.code.get? 955 = some 130 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 955).toNat = 955 by decide, byte]
  decide

theorem decode956 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 956) = some (.AND, none) := by
  have byte : NativeSourceAbiWrite.code.get? 956 = some 22 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 956).toNat = 956 by decide, byte]
  decide

theorem decode957 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 957) = some (.DUP3, none) := by
  have byte : NativeSourceAbiWrite.code.get? 957 = some 130 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 957).toNat = 957 by decide, byte]
  decide

theorem decode958 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 958) = some (.SUB, none) := by
  have byte : NativeSourceAbiWrite.code.get? 958 = some 3 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 958).toNat = 958 by decide, byte]
  decide

def s1 (cost : Nat) (pre : EVM.State) (word ret : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost pre).replaceStackAndIncrPC (ret :: word :: tail) 1

def s2 (cost : Nat) (pre : EVM.State) (word ret : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost (s1 cost pre word ret tail)).replaceStackAndIncrPC (UInt256.ofNat 1 :: ret :: word :: tail) 2

def s3 (cost : Nat) (pre : EVM.State) (word ret : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost (s2 cost pre word ret tail)).replaceStackAndIncrPC (UInt256.ofNat 1 :: UInt256.ofNat 1 :: ret :: word :: tail) 2

def s4 (cost : Nat) (pre : EVM.State) (word ret : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost (s3 cost pre word ret tail)).replaceStackAndIncrPC (UInt256.ofNat 160 :: UInt256.ofNat 1 :: UInt256.ofNat 1 :: ret :: word :: tail) 2

def s5 (cost : Nat) (pre : EVM.State) (word ret : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost (s4 cost pre word ret tail)).replaceStackAndIncrPC (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160) :: UInt256.ofNat 1 :: ret :: word :: tail) 1

def s6 (cost : Nat) (pre : EVM.State) (word ret : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost (s5 cost pre word ret tail)).replaceStackAndIncrPC (NativeSourceAddressCanonicality.mask :: ret :: word :: tail) 1

def s7 (cost : Nat) (pre : EVM.State) (word ret : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost (s6 cost pre word ret tail)).replaceStackAndIncrPC (word :: NativeSourceAddressCanonicality.mask :: ret :: word :: tail) 1

def s8 (cost : Nat) (pre : EVM.State) (word ret : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost (s7 cost pre word ret tail)).replaceStackAndIncrPC (word.land NativeSourceAddressCanonicality.mask :: ret :: word :: tail) 1

def s9 (cost : Nat) (pre : EVM.State) (word ret : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost (s8 cost pre word ret tail)).replaceStackAndIncrPC (word :: word.land NativeSourceAddressCanonicality.mask :: ret :: word :: tail) 1

def s10 (cost : Nat) (pre : EVM.State) (word ret : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost (s9 cost pre word ret tail)).replaceStackAndIncrPC ((word - word.land NativeSourceAddressCanonicality.mask) :: ret :: word :: tail) 1

theorem transition1 (fuel : Nat) (cost : Nat) (pre : EVM.State) (word ret : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 946)
    (stack : pre.stack = word :: ret :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt pre)) pre = .ok (s1 cost pre word ret tail) := by
  have atPC : pre.pc = UInt256.ofNat 946 := by
    exact pc
  have decoded : decodeAt pre = (.SWAP1, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code pre.pc).getD _ = _
    rw [code, atPC, decode946]; rfl
  rw [decoded]
  change EvmYul.swap 1 (stepPre cost pre) = _
  unfold EvmYul.swap
  simp only [stepPre, stack]
  rfl

theorem transition2 (fuel : Nat) (cost : Nat) (pre : EVM.State) (word ret : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 946)
    (stack : pre.stack = word :: ret :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s1 cost pre word ret tail))) (s1 cost pre word ret tail) = .ok (s2 cost pre word ret tail) := by
  have atPC : (s1 cost pre word ret tail).pc = UInt256.ofNat 947 := by
    change pre.pc + UInt256.ofNat 1 = _
    rw [pc]; decide
  have decoded : decodeAt (s1 cost pre word ret tail) = (.Push .PUSH1, some (UInt256.ofNat 1, 1)) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s1 cost pre word ret tail).pc).getD _ = _
    rw [code, atPC, decode947]; rfl
  rw [decoded]
  rfl

theorem transition3 (fuel : Nat) (cost : Nat) (pre : EVM.State) (word ret : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 946)
    (stack : pre.stack = word :: ret :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s2 cost pre word ret tail))) (s2 cost pre word ret tail) = .ok (s3 cost pre word ret tail) := by
  have atPC : (s2 cost pre word ret tail).pc = UInt256.ofNat 949 := by
    change pre.pc + UInt256.ofNat 1 + UInt256.ofNat 2 = _
    rw [pc]; decide
  have decoded : decodeAt (s2 cost pre word ret tail) = (.Push .PUSH1, some (UInt256.ofNat 1, 1)) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s2 cost pre word ret tail).pc).getD _ = _
    rw [code, atPC, decode949]; rfl
  rw [decoded]
  rfl

theorem transition4 (fuel : Nat) (cost : Nat) (pre : EVM.State) (word ret : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 946)
    (stack : pre.stack = word :: ret :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s3 cost pre word ret tail))) (s3 cost pre word ret tail) = .ok (s4 cost pre word ret tail) := by
  have atPC : (s3 cost pre word ret tail).pc = UInt256.ofNat 951 := by
    change pre.pc + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 2 = _
    rw [pc]; decide
  have decoded : decodeAt (s3 cost pre word ret tail) = (.Push .PUSH1, some (UInt256.ofNat 160, 1)) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s3 cost pre word ret tail).pc).getD _ = _
    rw [code, atPC, decode951]; rfl
  rw [decoded]
  rfl

theorem transition5 (fuel : Nat) (cost : Nat) (pre : EVM.State) (word ret : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 946)
    (stack : pre.stack = word :: ret :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s4 cost pre word ret tail))) (s4 cost pre word ret tail) = .ok (s5 cost pre word ret tail) := by
  have atPC : (s4 cost pre word ret tail).pc = UInt256.ofNat 953 := by
    change pre.pc + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 2 = _
    rw [pc]; decide
  have decoded : decodeAt (s4 cost pre word ret tail) = (.SHL, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s4 cost pre word ret tail).pc).getD _ = _
    rw [code, atPC, decode953]; rfl
  rw [decoded]
  rfl

theorem transition6 (fuel : Nat) (cost : Nat) (pre : EVM.State) (word ret : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 946)
    (stack : pre.stack = word :: ret :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s5 cost pre word ret tail))) (s5 cost pre word ret tail) = .ok (s6 cost pre word ret tail) := by
  have atPC : (s5 cost pre word ret tail).pc = UInt256.ofNat 954 := by
    change pre.pc + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 1 = _
    rw [pc]; decide
  have decoded : decodeAt (s5 cost pre word ret tail) = (.SUB, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s5 cost pre word ret tail).pc).getD _ = _
    rw [code, atPC, decode954]; rfl
  rw [decoded]
  rfl

theorem transition7 (fuel : Nat) (cost : Nat) (pre : EVM.State) (word ret : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 946)
    (stack : pre.stack = word :: ret :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s6 cost pre word ret tail))) (s6 cost pre word ret tail) = .ok (s7 cost pre word ret tail) := by
  have atPC : (s6 cost pre word ret tail).pc = UInt256.ofNat 955 := by
    change pre.pc + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 1 + UInt256.ofNat 1 = _
    rw [pc]; decide
  have decoded : decodeAt (s6 cost pre word ret tail) = (.DUP3, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s6 cost pre word ret tail).pc).getD _ = _
    rw [code, atPC, decode955]; rfl
  rw [decoded]
  rfl

theorem transition8 (fuel : Nat) (cost : Nat) (pre : EVM.State) (word ret : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 946)
    (stack : pre.stack = word :: ret :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s7 cost pre word ret tail))) (s7 cost pre word ret tail) = .ok (s8 cost pre word ret tail) := by
  have atPC : (s7 cost pre word ret tail).pc = UInt256.ofNat 956 := by
    change pre.pc + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 = _
    rw [pc]; decide
  have decoded : decodeAt (s7 cost pre word ret tail) = (.AND, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s7 cost pre word ret tail).pc).getD _ = _
    rw [code, atPC, decode956]; rfl
  rw [decoded]
  rfl

theorem transition9 (fuel : Nat) (cost : Nat) (pre : EVM.State) (word ret : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 946)
    (stack : pre.stack = word :: ret :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s8 cost pre word ret tail))) (s8 cost pre word ret tail) = .ok (s9 cost pre word ret tail) := by
  have atPC : (s8 cost pre word ret tail).pc = UInt256.ofNat 957 := by
    change pre.pc + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 = _
    rw [pc]; decide
  have decoded : decodeAt (s8 cost pre word ret tail) = (.DUP3, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s8 cost pre word ret tail).pc).getD _ = _
    rw [code, atPC, decode957]; rfl
  rw [decoded]
  rfl

theorem transition10 (fuel : Nat) (cost : Nat) (pre : EVM.State) (word ret : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 946)
    (stack : pre.stack = word :: ret :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s9 cost pre word ret tail))) (s9 cost pre word ret tail) = .ok (s10 cost pre word ret tail) := by
  have atPC : (s9 cost pre word ret tail).pc = UInt256.ofNat 958 := by
    change pre.pc + UInt256.ofNat 1 + UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 = _
    rw [pc]; decide
  have decoded : decodeAt (s9 cost pre word ret tail) = (.SUB, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s9 cost pre word ret tail).pc).getD _ = _
    rw [code, atPC, decode958]; rfl
  rw [decoded]
  rfl

theorem execute (fuel : Nat) (cost : Nat) (pre : EVM.State) (word ret : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 946)
    (stack : pre.stack = word :: ret :: tail) :
    run fuel cost 10 pre = .ok (s10 cost pre word ret tail) := by
  rw [run, transition1 fuel cost pre word ret tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition2 fuel cost pre word ret tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition3 fuel cost pre word ret tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition4 fuel cost pre word ret tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition5 fuel cost pre word ret tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition6 fuel cost pre word ret tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition7 fuel cost pre word ret tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition8 fuel cost pre word ret tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition9 fuel cost pre word ret tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition10 fuel cost pre word ret tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rfl

theorem output_stack (cost : Nat) (pre : EVM.State) (word ret : UInt256) (tail : Stack UInt256) :
    (s10 cost pre word ret tail).stack = (word - word.land NativeSourceAddressCanonicality.mask) :: ret :: word :: tail := by rfl

theorem memory (cost : Nat) (pre : EVM.State) (word ret : UInt256) (tail : Stack UInt256) : (s10 cost pre word ret tail).memory = pre.memory := by rfl

theorem guard_zero_iff (cost : Nat) (pre : EVM.State) (word ret : UInt256) (tail : Stack UInt256) :
    (s10 cost pre word ret tail).stack.head! = UInt256.ofNat 0 ↔ word.toNat < 2 ^ 160 := by
  rw [output_stack]
  exact NativeSourceAddressCanonicality.difference_zero_iff word

end Compiler.Proofs.IRGeneration.NativeSourceAddressGuardExecution

import Compiler.Proofs.IRGeneration.NativeSourcePreludeCopy

namespace Compiler.Proofs.IRGeneration.NativeSourcePreludeDecoded
open EvmYul EVM.Proof NativeSourcePreludeShuffles

def run (fuel cost : Nat) : Nat → EVM.State → Except EVM.ExecutionException EVM.State
  | 0, pre => .ok pre
  | count + 1, pre => do
    let next ← EVM.step (fuel + 1) cost (some (decodeAt pre)) pre
    run fuel cost count next

def s1 (cost : Nat) (pre : EVM.State) (free a b c d e f g h : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost pre).replaceStackAndIncrPC (e :: a :: b :: c :: d :: free :: f :: g :: h :: tail)

def s2 (cost : Nat) (pre : EVM.State) (free a b c d e f g h : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost (s1 cost pre free a b c d e f g h tail)).replaceStackAndIncrPC (free :: e :: a :: b :: c :: d :: free :: f :: g :: h :: tail)

def s3 (cost : Nat) (pre : EVM.State) (free a b c d e f g h : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost (s2 cost pre free a b c d e f g h tail)).replaceStackAndIncrPC (c :: e :: a :: b :: free :: d :: free :: f :: g :: h :: tail)

def s4 (cost : Nat) (pre : EVM.State) (free a b c d e f g h : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost (s3 cost pre free a b c d e f g h tail)).replaceStackAndIncrPC (b :: c :: e :: a :: b :: free :: d :: free :: f :: g :: h :: tail)

def s5 (cost : Nat) (pre : EVM.State) (free a b c d e f g h : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost (s4 cost pre free a b c d e f g h tail)).replaceStackAndIncrPC (free :: b :: c :: e :: a :: b :: free :: d :: free :: f :: g :: h :: tail)

def s6 (cost : Nat) (pre : EVM.State) (free a b c d e f g h : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost (s5 cost pre free a b c d e f g h tail)).replaceStackAndIncrPC ((free + b) :: c :: e :: a :: b :: free :: d :: free :: f :: g :: h :: tail)

def s7 (cost : Nat) (pre : EVM.State) (free a b c d e f g h : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost (s6 cost pre free a b c d e f g h tail)).replaceStackAndIncrPC (f :: c :: e :: a :: b :: free :: d :: free :: (free + b) :: g :: h :: tail)

theorem transition1 (fuel : Nat) (cost : Nat) (pre : EVM.State) (free a b c d e f g h : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 636)
    (stack : pre.stack = free :: a :: b :: c :: d :: e :: f :: g :: h :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt pre)) pre = .ok (s1 cost pre free a b c d e f g h tail) := by
  have atPC : pre.pc = UInt256.ofNat 636 := by
    rw [pc]
  have decoded : decodeAt pre = (.SWAP5, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code pre.pc).getD _ = _
    rw [code, atPC, NativeSourcePreludeLength.decode636]
    rfl
  rw [decoded]
  exact operation1 fuel cost pre free a b c d e f g h tail stack

theorem transition2 (fuel : Nat) (cost : Nat) (pre : EVM.State) (free a b c d e f g h : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 636)
    (_stack : pre.stack = free :: a :: b :: c :: d :: e :: f :: g :: h :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s1 cost pre free a b c d e f g h tail))) (s1 cost pre free a b c d e f g h tail) = .ok (s2 cost pre free a b c d e f g h tail) := by
  have atPC : (s1 cost pre free a b c d e f g h tail).pc = UInt256.ofNat 637 := by
    change pre.pc + UInt256.ofNat 1 = _
    rw [pc]
    decide
  have decoded : decodeAt (s1 cost pre free a b c d e f g h tail) = (.DUP6, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s1 cost pre free a b c d e f g h tail).pc).getD _ = _
    rw [code, atPC, NativeSourcePreludeLength.decode637]
    rfl
  rw [decoded]
  exact operation2 fuel cost (s1 cost pre free a b c d e f g h tail) free a b c d e f g h tail (by rfl)

theorem transition3 (fuel : Nat) (cost : Nat) (pre : EVM.State) (free a b c d e f g h : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 636)
    (_stack : pre.stack = free :: a :: b :: c :: d :: e :: f :: g :: h :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s2 cost pre free a b c d e f g h tail))) (s2 cost pre free a b c d e f g h tail) = .ok (s3 cost pre free a b c d e f g h tail) := by
  have atPC : (s2 cost pre free a b c d e f g h tail).pc = UInt256.ofNat 638 := by
    change (pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1 = _
    rw [pc]
    decide
  have decoded : decodeAt (s2 cost pre free a b c d e f g h tail) = (.SWAP4, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s2 cost pre free a b c d e f g h tail).pc).getD _ = _
    rw [code, atPC, NativeSourcePreludeLength.decode638]
    rfl
  rw [decoded]
  exact operation3 fuel cost (s2 cost pre free a b c d e f g h tail) free a b c d e f g h tail (by rfl)

theorem transition4 (fuel : Nat) (cost : Nat) (pre : EVM.State) (free a b c d e f g h : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 636)
    (_stack : pre.stack = free :: a :: b :: c :: d :: e :: f :: g :: h :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s3 cost pre free a b c d e f g h tail))) (s3 cost pre free a b c d e f g h tail) = .ok (s4 cost pre free a b c d e f g h tail) := by
  have atPC : (s3 cost pre free a b c d e f g h tail).pc = UInt256.ofNat 639 := by
    change ((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1 = _
    rw [pc]
    decide
  have decoded : decodeAt (s3 cost pre free a b c d e f g h tail) = (.DUP4, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s3 cost pre free a b c d e f g h tail).pc).getD _ = _
    rw [code, atPC, NativeSourcePreludeLength.decode639]
    rfl
  rw [decoded]
  exact operation4 fuel cost (s3 cost pre free a b c d e f g h tail) free a b c d e f g h tail (by rfl)

theorem transition5 (fuel : Nat) (cost : Nat) (pre : EVM.State) (free a b c d e f g h : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 636)
    (_stack : pre.stack = free :: a :: b :: c :: d :: e :: f :: g :: h :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s4 cost pre free a b c d e f g h tail))) (s4 cost pre free a b c d e f g h tail) = .ok (s5 cost pre free a b c d e f g h tail) := by
  have atPC : (s4 cost pre free a b c d e f g h tail).pc = UInt256.ofNat 640 := by
    change (((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1 = _
    rw [pc]
    decide
  have decoded : decodeAt (s4 cost pre free a b c d e f g h tail) = (.DUP6, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s4 cost pre free a b c d e f g h tail).pc).getD _ = _
    rw [code, atPC, NativeSourcePreludeLength.decode640]
    rfl
  rw [decoded]
  exact operation5 fuel cost (s4 cost pre free a b c d e f g h tail) free a b c d e f g h tail (by rfl)

theorem transition6 (fuel : Nat) (cost : Nat) (pre : EVM.State) (free a b c d e f g h : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 636)
    (_stack : pre.stack = free :: a :: b :: c :: d :: e :: f :: g :: h :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s5 cost pre free a b c d e f g h tail))) (s5 cost pre free a b c d e f g h tail) = .ok (s6 cost pre free a b c d e f g h tail) := by
  have atPC : (s5 cost pre free a b c d e f g h tail).pc = UInt256.ofNat 641 := by
    change ((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1 = _
    rw [pc]
    decide
  have decoded : decodeAt (s5 cost pre free a b c d e f g h tail) = (.ADD, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s5 cost pre free a b c d e f g h tail).pc).getD _ = _
    rw [code, atPC, NativeSourcePreludeLength.decode641]
    rfl
  rw [decoded]
  exact operation6 fuel cost (s5 cost pre free a b c d e f g h tail) free a b c d e f g h tail (by rfl)

theorem transition7 (fuel : Nat) (cost : Nat) (pre : EVM.State) (free a b c d e f g h : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 636)
    (_stack : pre.stack = free :: a :: b :: c :: d :: e :: f :: g :: h :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt (s6 cost pre free a b c d e f g h tail))) (s6 cost pre free a b c d e f g h tail) = .ok (s7 cost pre free a b c d e f g h tail) := by
  have atPC : (s6 cost pre free a b c d e f g h tail).pc = UInt256.ofNat 642 := by
    change (((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1 = _
    rw [pc]
    decide
  have decoded : decodeAt (s6 cost pre free a b c d e f g h tail) = (.SWAP8, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s6 cost pre free a b c d e f g h tail).pc).getD _ = _
    rw [code, atPC, NativeSourcePreludeLength.decode642]
    rfl
  rw [decoded]
  exact operation7 fuel cost (s6 cost pre free a b c d e f g h tail) free a b c d e f g h tail (by rfl)

theorem execute (fuel : Nat) (cost : Nat) (pre : EVM.State) (free a b c d e f g h : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 636)
    (stack : pre.stack = free :: a :: b :: c :: d :: e :: f :: g :: h :: tail) :
    run fuel cost 7 pre = .ok (s7 cost pre free a b c d e f g h tail) := by
  rw [run, transition1 fuel cost pre free a b c d e f g h tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition2 fuel cost pre free a b c d e f g h tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition3 fuel cost pre free a b c d e f g h tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition4 fuel cost pre free a b c d e f g h tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition5 fuel cost pre free a b c d e f g h tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition6 fuel cost pre free a b c d e f g h tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition7 fuel cost pre free a b c d e f g h tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rfl

theorem run_add (fuel cost left right : Nat) (pre : EVM.State) :
    run fuel cost (left + right) pre = (run fuel cost left pre >>= run fuel cost right) := by
  induction left generalizing pre with
  | zero => simp only [Nat.zero_add, run, Bind.bind, Except.bind]
  | succ left ih =>
    simp only [Nat.succ_add, run]
    cases step : EVM.step (fuel + 1) cost (some (decodeAt pre)) pre with
    | error reason => rfl
    | ok next => exact ih next

theorem transition8 (fuel cost loadCost : Nat) (pre : EVM.State) (free a b c d e f g h : UInt256)
    (tail : Stack UInt256) (code : pre.executionEnv.code = NativeSourceAbiWrite.code)
    (pc : pre.pc = UInt256.ofNat 636) :
    EVM.step (fuel + 1) loadCost (some (decodeAt (s7 cost pre free a b c d e f g h tail)))
      (s7 cost pre free a b c d e f g h tail) =
      .ok (NativeSourcePreludeLength.loaded cost loadCost pre free a b c d e f g h tail) := by
  have atPC : (s7 cost pre free a b c d e f g h tail).pc = UInt256.ofNat 643 := by
    change ((((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) +
      UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1 = _
    rw [pc]; decide
  have decoded : decodeAt (s7 cost pre free a b c d e f g h tail) = (.MLOAD, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (s7 cost pre free a b c d e f g h tail).pc).getD _ = _
    rw [code, atPC, NativeSourcePreludeLength.decode643]
    rfl
  rw [decoded]
  exact NativeSourceLoadStep.step fuel loadCost _ f _ (by rfl)

theorem execute8 (fuel cost : Nat) (pre : EVM.State) (free a b c d e f g h : UInt256)
    (tail : Stack UInt256) (code : pre.executionEnv.code = NativeSourceAbiWrite.code)
    (pc : pre.pc = UInt256.ofNat 636)
    (stack : pre.stack = free :: a :: b :: c :: d :: e :: f :: g :: h :: tail) :
    run fuel cost 8 pre = .ok (NativeSourcePreludeLength.loaded cost cost pre free a b c d e f g h tail) := by
  rw [show 8 = 7 + 1 by decide, run_add, execute fuel cost pre free a b c d e f g h tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, transition8 fuel cost cost pre free a b c d e f g h tail code pc]
  rfl

end Compiler.Proofs.IRGeneration.NativeSourcePreludeDecoded

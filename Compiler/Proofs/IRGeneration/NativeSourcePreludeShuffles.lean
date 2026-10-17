import Compiler.Proofs.IRGeneration.NativeSourceLoadStep

namespace Compiler.Proofs.IRGeneration.NativeSourcePreludeShuffles
open EvmYul EVM.Proof

def run (fuel cost : Nat) : List (Operation .EVM) → EVM.State → Except EVM.ExecutionException EVM.State
  | [], pre => .ok pre
  | op :: ops, pre => do
    let next ← EVM.step (fuel + 1) cost (some (op, none)) pre
    run fuel cost ops next

def result (cost : Nat) (pre : EVM.State) (free a b c d e f g h : UInt256)
    (tail : Stack UInt256) : EVM.State :=
  let s1 := (stepPre cost pre).replaceStackAndIncrPC (e :: a :: b :: c :: d :: free :: f :: g :: h :: tail)
  let s2 := (stepPre cost s1).replaceStackAndIncrPC (free :: e :: a :: b :: c :: d :: free :: f :: g :: h :: tail)
  let s3 := (stepPre cost s2).replaceStackAndIncrPC (c :: e :: a :: b :: free :: d :: free :: f :: g :: h :: tail)
  let s4 := (stepPre cost s3).replaceStackAndIncrPC (b :: c :: e :: a :: b :: free :: d :: free :: f :: g :: h :: tail)
  let s5 := (stepPre cost s4).replaceStackAndIncrPC (free :: b :: c :: e :: a :: b :: free :: d :: free :: f :: g :: h :: tail)
  let s6 := (stepPre cost s5).replaceStackAndIncrPC ((free + b) :: c :: e :: a :: b :: free :: d :: free :: f :: g :: h :: tail)
  (stepPre cost s6).replaceStackAndIncrPC (f :: c :: e :: a :: b :: free :: d :: free :: (free + b) :: g :: h :: tail)

theorem operation1 (fuel cost : Nat) (pre : EVM.State) (free a b c d e f g h : UInt256) (tail : Stack UInt256)
    (stack : pre.stack = free :: a :: b :: c :: d :: e :: f :: g :: h :: tail) :
    EVM.step (fuel + 1) cost (some (.SWAP5, none)) pre =
      .ok ((stepPre cost pre).replaceStackAndIncrPC (e :: a :: b :: c :: d :: free :: f :: g :: h :: tail)) := by
  change EvmYul.swap 5 (stepPre cost pre) = _
  simp only [EvmYul.swap, stepPre, stack]
  rfl

theorem operation2 (fuel cost : Nat) (pre : EVM.State) (free a b c d e f g h : UInt256) (tail : Stack UInt256)
    (stack : pre.stack = e :: a :: b :: c :: d :: free :: f :: g :: h :: tail) :
    EVM.step (fuel + 1) cost (some (.DUP6, none)) pre =
      .ok ((stepPre cost pre).replaceStackAndIncrPC (free :: e :: a :: b :: c :: d :: free :: f :: g :: h :: tail)) := by
  change EvmYul.dup 6 (stepPre cost pre) = _
  simp only [EvmYul.dup, stepPre, stack]
  rfl

theorem operation3 (fuel cost : Nat) (pre : EVM.State) (free a b c d e f g h : UInt256) (tail : Stack UInt256)
    (stack : pre.stack = free :: e :: a :: b :: c :: d :: free :: f :: g :: h :: tail) :
    EVM.step (fuel + 1) cost (some (.SWAP4, none)) pre =
      .ok ((stepPre cost pre).replaceStackAndIncrPC (c :: e :: a :: b :: free :: d :: free :: f :: g :: h :: tail)) := by
  change EvmYul.swap 4 (stepPre cost pre) = _
  simp only [EvmYul.swap, stepPre, stack]
  rfl

theorem operation4 (fuel cost : Nat) (pre : EVM.State) (free a b c d e f g h : UInt256) (tail : Stack UInt256)
    (stack : pre.stack = c :: e :: a :: b :: free :: d :: free :: f :: g :: h :: tail) :
    EVM.step (fuel + 1) cost (some (.DUP4, none)) pre =
      .ok ((stepPre cost pre).replaceStackAndIncrPC (b :: c :: e :: a :: b :: free :: d :: free :: f :: g :: h :: tail)) := by
  change EvmYul.dup 4 (stepPre cost pre) = _
  simp only [EvmYul.dup, stepPre, stack]
  rfl

theorem operation5 (fuel cost : Nat) (pre : EVM.State) (free a b c d e f g h : UInt256) (tail : Stack UInt256)
    (stack : pre.stack = b :: c :: e :: a :: b :: free :: d :: free :: f :: g :: h :: tail) :
    EVM.step (fuel + 1) cost (some (.DUP6, none)) pre =
      .ok ((stepPre cost pre).replaceStackAndIncrPC (free :: b :: c :: e :: a :: b :: free :: d :: free :: f :: g :: h :: tail)) := by
  change EvmYul.dup 6 (stepPre cost pre) = _
  simp only [EvmYul.dup, stepPre, stack]
  rfl

theorem operation6 (fuel cost : Nat) (pre : EVM.State) (free a b c d e f g h : UInt256) (tail : Stack UInt256)
    (stack : pre.stack = free :: b :: c :: e :: a :: b :: free :: d :: free :: f :: g :: h :: tail) :
    EVM.step (fuel + 1) cost (some (.ADD, none)) pre =
      .ok ((stepPre cost pre).replaceStackAndIncrPC ((free + b) :: c :: e :: a :: b :: free :: d :: free :: f :: g :: h :: tail)) := by
  change EVM.execBinOp UInt256.add (stepPre cost pre) = _
  simp only [EVM.execBinOp, stepPre, stack]
  rfl

theorem operation7 (fuel cost : Nat) (pre : EVM.State) (free a b c d e f g h : UInt256) (tail : Stack UInt256)
    (stack : pre.stack = (free + b) :: c :: e :: a :: b :: free :: d :: free :: f :: g :: h :: tail) :
    EVM.step (fuel + 1) cost (some (.SWAP8, none)) pre =
      .ok ((stepPre cost pre).replaceStackAndIncrPC (f :: c :: e :: a :: b :: free :: d :: free :: (free + b) :: g :: h :: tail)) := by
  change EvmYul.swap 8 (stepPre cost pre) = _
  simp only [EvmYul.swap, stepPre, stack]
  rfl


theorem execute (fuel cost : Nat) (pre : EVM.State) (free a b c d e f g h : UInt256)
    (tail : Stack UInt256) (stack : pre.stack = free :: a :: b :: c :: d :: e :: f :: g :: h :: tail) :
    run fuel cost [.SWAP5, .DUP6, .SWAP4, .DUP4, .DUP6, .ADD, .SWAP8] pre =
      .ok (result cost pre free a b c d e f g h tail) := by
  rw [run, operation1 fuel cost _ free a b c d e f g h tail stack]
  simp only [Bind.bind, Except.bind]
  rw [run, operation2 fuel cost _ free a b c d e f g h tail (by rfl)]
  simp only [Bind.bind, Except.bind]
  rw [run, operation3 fuel cost _ free a b c d e f g h tail (by rfl)]
  simp only [Bind.bind, Except.bind]
  rw [run, operation4 fuel cost _ free a b c d e f g h tail (by rfl)]
  simp only [Bind.bind, Except.bind]
  rw [run, operation5 fuel cost _ free a b c d e f g h tail (by rfl)]
  simp only [Bind.bind, Except.bind]
  rw [run, operation6 fuel cost _ free a b c d e f g h tail (by rfl)]
  simp only [Bind.bind, Except.bind]
  rw [run, operation7 fuel cost _ free a b c d e f g h tail (by rfl)]
  simp only [Bind.bind, Except.bind]
  rfl

theorem stack (cost : Nat) (pre : EVM.State) (free a b c d e f g h : UInt256) (tail : Stack UInt256) :
    (result cost pre free a b c d e f g h tail).stack =
      f :: c :: e :: a :: b :: free :: d :: free :: (free + b) :: g :: h :: tail := by rfl

theorem memory (cost : Nat) (pre : EVM.State) (free a b c d e f g h : UInt256) (tail : Stack UInt256) :
    (result cost pre free a b c d e f g h tail).memory = pre.memory := by rfl

end Compiler.Proofs.IRGeneration.NativeSourcePreludeShuffles

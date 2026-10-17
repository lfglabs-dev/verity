import Verity.Core.Model.MidnightInitcode

/-! Post-Shanghai/Petersburg value-zero CREATE2 caller preparation. Context
is an actual opcode-entry observation; no defaults or supplied gas certificate.
Account nonce/collision/address/callee and warm-access effects are separate. -/
namespace Verity.Core.Model.Create2Entry
open Compiler.CompilationModel.DenoteMemory MidnightInitcode

structure Context where
  gas : Nat
  /-- Active caller frame depth, root=0, as in pinned Revm EthFrame.depth. -/
  depth : Nat
  isStatic : Bool

def maxGas : Nat := 2^64 - 1

def entryCost (memory : Memory) (offset size : Nat) : Nat :=
  32000 + 8 * words size + expansionCost memory offset size

structure Forwarded where
  memory : Memory
  retainedGas : Nat
  childGas : Nat

inductive Preparation where
  | exceptional
  | depthFailure (memory : Memory) (gasLeft : Nat)
  | forwarded (frame : Forwarded)

/-- Exceptional caller halts consume its gas; depth failure returns ZERO with
expanded caller memory and all child gas refunded. Root depth is zero. -/
def prepare (memory : Memory) (context : Context) (offset size : Nat) :
    Except String Preparation :=
  if maxGas < context.gas then .error "CREATE2 opcode gas exceeds uint64 projection" else
  if context.isStatic || decide (49152 < size) then .ok .exceptional else
  let charge := entryCost memory offset size
  if context.gas < charge then .ok .exceptional else
  let remaining := context.gas - charge
  let expanded := returnMemory memory offset size
  if 1024 ≤ context.depth then .ok (.depthFailure expanded remaining) else
  .ok (.forwarded { memory := expanded, retainedGas := remaining / 64, childGas := remaining - remaining / 64 })

def completeGas (frame : Forwarded) (childGasLeft : Nat) : Nat :=
  frame.retainedGas + childGasLeft

theorem entryCost_zero (memory : Memory) (offset : Nat) :
    entryCost memory offset 0 = 32000 := by
  simp [entryCost, expansionCost, words]

theorem entryCost_covered (memory : Memory) (offset size : Nat)
    (covered : offset + size ≤ memory.size) :
    entryCost memory offset size = 32000 + 8 * words size := by
  simp only [entryCost, expansionCost_covered memory offset size covered, Nat.add_zero]

theorem prepare_invalid_gas (memory : Memory) (context : Context) (offset size : Nat)
    (invalid : maxGas < context.gas) :
    prepare memory context offset size = .error "CREATE2 opcode gas exceeds uint64 projection" := by
  simp only [prepare, invalid, if_true]

theorem prepare_static (memory : Memory) (context : Context) (offset size : Nat)
    (valid : context.gas ≤ maxGas) (staticMode : context.isStatic = true) :
    prepare memory context offset size = .ok .exceptional := by
  simp only [prepare, Nat.not_lt.mpr valid, if_false, staticMode, Bool.true_or, if_true]

theorem prepare_oversize (memory : Memory) (context : Context) (offset size : Nat)
    (valid : context.gas ≤ maxGas) (oversize : 49152 < size) :
    prepare memory context offset size = .ok .exceptional := by
  simp only [prepare, Nat.not_lt.mpr valid, if_false, oversize, decide_true, Bool.or_true, if_true]

theorem prepare_out_of_gas (memory : Memory) (context : Context) (offset size : Nat)
    (valid : context.gas ≤ maxGas) (exhausted : context.gas < entryCost memory offset size) :
    prepare memory context offset size = .ok .exceptional := by
  simp only [prepare, Nat.not_lt.mpr valid, if_false, exhausted, if_true]
  split <;> rfl

theorem prepare_depth_failure (memory : Memory) (context : Context) (offset size : Nat)
    (valid : context.gas ≤ maxGas) (mutable : context.isStatic = false)
    (cap : size ≤ 49152) (enough : entryCost memory offset size ≤ context.gas)
    (blocked : 1024 ≤ context.depth) :
    prepare memory context offset size = .ok
      (.depthFailure (returnMemory memory offset size) (context.gas - entryCost memory offset size)) := by
  simp only [prepare, Nat.not_lt.mpr valid, mutable, Nat.not_lt.mpr cap,
    decide_false, Bool.or_self, Bool.false_eq_true, if_false, Nat.not_lt.mpr enough, blocked, if_true]

theorem prepare_forwarded (memory : Memory) (context : Context) (offset size : Nat)
    (valid : context.gas ≤ maxGas) (mutable : context.isStatic = false)
    (cap : size ≤ 49152) (enough : entryCost memory offset size ≤ context.gas)
    (depth : context.depth < 1024) :
    prepare memory context offset size = .ok (.forwarded
      { memory := returnMemory memory offset size,
        retainedGas := (context.gas - entryCost memory offset size) / 64,
        childGas := (context.gas - entryCost memory offset size) -
          (context.gas - entryCost memory offset size) / 64 }) := by
  simp only [prepare, Nat.not_lt.mpr valid, mutable, Nat.not_lt.mpr cap,
    decide_false, Bool.or_self, Bool.false_eq_true, if_false, Nat.not_lt.mpr enough, Nat.not_le.mpr depth]

theorem forwarded_gas_split (memory : Memory) (context : Context) (offset size : Nat)
    (frame : Forwarded) (prepared : prepare memory context offset size = .ok (.forwarded frame)) :
    frame.retainedGas + frame.childGas = context.gas - entryCost memory offset size := by
  dsimp only [prepare] at prepared
  split at prepared
  · simp only [reduceCtorEq] at prepared
  · split at prepared
    · simp only [Except.ok.injEq, reduceCtorEq] at prepared
    · split at prepared
      · simp only [Except.ok.injEq, reduceCtorEq] at prepared
      · split at prepared
        · simp only [Except.ok.injEq, reduceCtorEq] at prepared
        · cases prepared
          have bounded := Nat.div_le_self (context.gas - entryCost memory offset size) 64
          simp only
          omega

theorem full_child_refund (memory : Memory) (context : Context) (offset size : Nat)
    (frame : Forwarded) (prepared : prepare memory context offset size = .ok (.forwarded frame)) :
    completeGas frame frame.childGas = context.gas - entryCost memory offset size :=
  forwarded_gas_split memory context offset size frame prepared

theorem child_spent (memory : Memory) (context : Context) (offset size : Nat)
    (frame : Forwarded) (prepared : prepare memory context offset size = .ok (.forwarded frame))
    (spent : Nat) (enough : spent ≤ frame.childGas) :
    completeGas frame (frame.childGas - spent) = context.gas - entryCost memory offset size - spent := by
  have split := forwarded_gas_split memory context offset size frame prepared
  unfold completeGas
  omega

end Verity.Core.Model.Create2Entry

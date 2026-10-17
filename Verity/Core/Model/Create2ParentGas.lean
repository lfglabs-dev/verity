import Verity.Core.Model.DenoteCreate2

/-!
CREATE2 parent-opcode charging for the pinned Osaka fork. This component
computes a child allowance from the parent's pre-opcode gas and memory size;
it does not accept an adversary-supplied child allowance. Whole-frame source
gas tracking and canonical Stmt integration remain required before admission.
Static/size/depth/account checks remain in their respective control layers.
-/
namespace Compiler.CompilationModel.Create2ParentGas

/-- EVM memory expansion is charged by words, with the quadratic term. -/
def memoryCost (words : Nat) : Nat := 3 * words + words * words / 512

/-- A zero-length memory range never expands memory, regardless of offset. -/
def resultingWords (oldWords offset size : Nat) : Nat :=
  if size = 0 then oldWords else max oldWords ((offset + size + 31) / 32)

/-- CREATE2 base + Keccak initcode charge + EIP-3860 charge + expansion. -/
def opcodeCost (oldWords offset size : Nat) : Nat :=
  32000 + 8 * ((size + 31) / 32) +
    (memoryCost (resultingWords oldWords offset size) - memoryCost oldWords)

structure Charged where
  memoryWords : Nat
  opcodeGas : Nat
  childGas : Nat
  reservedGas : Nat
  deriving DecidableEq, Repr

inductive Result where
  | outOfGas
  | charged (state : Charged)
  deriving DecidableEq, Repr

def charge (gas oldWords offset size : Nat) : Result :=
  let cost := opcodeCost oldWords offset size
  if cost ≤ gas then
    let remaining := gas - cost
    .charged { memoryWords := resultingWords oldWords offset size,
               opcodeGas := cost, childGas := remaining - remaining / 64,
               reservedGas := remaining / 64 }
  else .outOfGas

/-- Only gas actually returned by the child may be refunded to its parent. -/
def finish (state : Charged) (childGasLeft : Nat) : Except String Nat :=
  if childGasLeft ≤ state.childGas then .ok (state.reservedGas + childGasLeft)
  else .error "CREATE2 child returned more gas than its allowance"

theorem memoryCost_monotone {oldWords newWords : Nat} (grows : oldWords ≤ newWords) :
    memoryCost oldWords ≤ memoryCost newWords := by
  have square : oldWords * oldWords ≤ newWords * newWords := Nat.mul_le_mul grows grows
  have quadratic : oldWords * oldWords / 512 ≤ newWords * newWords / 512 :=
    Nat.div_le_div_right square
  unfold memoryCost
  omega

theorem resultingWords_ge (oldWords offset size : Nat) :
    oldWords ≤ resultingWords oldWords offset size := by
  unfold resultingWords
  split
  · exact Nat.le_refl _
  · exact Nat.le_max_left _ _

theorem opcodeCost_zero_size (oldWords offset : Nat) :
    opcodeCost oldWords offset 0 = 32000 := by
  simp [opcodeCost, resultingWords]

theorem charge_of_enough (gas oldWords offset size : Nat)
    (enough : opcodeCost oldWords offset size ≤ gas) :
    charge gas oldWords offset size = .charged
      { memoryWords := resultingWords oldWords offset size,
        opcodeGas := opcodeCost oldWords offset size,
        childGas := (gas - opcodeCost oldWords offset size) -
          (gas - opcodeCost oldWords offset size) / 64,
        reservedGas := (gas - opcodeCost oldWords offset size) / 64 } := by
  simp [charge, enough]

theorem charge_of_insufficient (gas oldWords offset size : Nat)
    (insufficient : gas < opcodeCost oldWords offset size) :
    charge gas oldWords offset size = .outOfGas := by
  simp [charge, Nat.not_le.mpr insufficient]

theorem charge_conserves_gas (gas oldWords offset size : Nat) (state : Charged)
    (charged : charge gas oldWords offset size = .charged state) :
    state.opcodeGas + state.childGas + state.reservedGas = gas := by
  dsimp [charge] at charged
  split at charged
  · rename_i enough
    have reservedBound : (gas - opcodeCost oldWords offset size) / 64 ≤
        gas - opcodeCost oldWords offset size := Nat.div_le_self _ _
    cases charged
    dsimp
    omega
  · cases charged

theorem finish_of_within (state : Charged) (childGasLeft : Nat)
    (within : childGasLeft ≤ state.childGas) :
    finish state childGasLeft = .ok (state.reservedGas + childGasLeft) := by
  simp [finish, within]

theorem finish_of_excess (state : Charged) (childGasLeft : Nat)
    (excess : state.childGas < childGasLeft) :
    finish state childGasLeft = .error "CREATE2 child returned more gas than its allowance" := by
  simp [finish, Nat.not_le.mpr excess]

theorem finished_gas_bound (gas oldWords offset size : Nat) (state : Charged)
    (charged : charge gas oldWords offset size = .charged state)
    (childGasLeft : Nat) (within : childGasLeft ≤ state.childGas) :
    state.reservedGas + childGasLeft ≤ gas - state.opcodeGas := by
  have conservation := charge_conserves_gas gas oldWords offset size state charged
  omega

end Compiler.CompilationModel.Create2ParentGas

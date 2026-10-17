import Compiler.Proofs.IRGeneration.NativeConstructorDataRun

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul EVM.Proof
open Verity.Core.Model.MidnightInitcode

/-- Memory extent reached by the actual constructor at each boundary. -/
def stageWords (size : Nat) (stage : Fin 9) : Nat :=
  if stage.val < 7 then 0 else words size

/-- Actual instruction gas, without the separately charged expansion. -/
def stageCost (size : Nat) : Fin 9 → Nat
  | ⟨0, _⟩ => 3
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 3
  | ⟨3, _⟩ => 3
  | ⟨4, _⟩ => 3
  | ⟨5, _⟩ => 2
  | ⟨6, _⟩ => 3 + 3 * words size
  | ⟨7, _⟩ => 2
  | ⟨8, _⟩ => 0

theorem stage_instruction_cost (payload : ByteArray) (stage : Fin 9) (pre : EVM.State)
    (holds : DataAt payload stage pre) (bounded : payload.size < UInt256.size) :
    EVM.C' pre (stageInstruction stage).1 = stageCost payload.size stage := by
  obtain ⟨stage, small⟩ := stage
  have positions : stage = 0 ∨ stage = 1 ∨ stage = 2 ∨ stage = 3 ∨ stage = 4 ∨
      stage = 5 ∨ stage = 6 ∨ stage = 7 ∨ stage = 8 := by omega
  rcases positions with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | rfl | skip
  have actual := copy_instruction_cost pre (UInt256.ofNat 0) (.ofNat 11)
    (.ofNat payload.size) [.ofNat payload.size] holds.2.2.1
  change EVM.C' pre .CODECOPY = 3 + 3 * words payload.size
  rw [actual]
  have value : (UInt256.ofNat payload.size).toNat = payload.size := Nat.mod_eq_of_lt bounded
  rw [value]

theorem copy_memory_cost (payload : ByteArray) (pre : EVM.State)
    (holds : DataAt payload ⟨6, by decide⟩ pre)
    (fresh : pre.activeWords = UInt256.ofNat 0)
    (bounded : payload.size ≤ 49152) :
    EVM.memoryExpansionCost pre .CODECOPY = memoryCost (words payload.size) := by
  have huge : 49152 < UInt256.size := by decide
  have value : (UInt256.ofNat payload.size).toNat = payload.size :=
    Nat.mod_eq_of_lt (by omega)
  simp only [EVM.memoryExpansionCost, EVM.memoryExpansionCost.μᵢ', holds.2.2.1, fresh]
  change EVM.Cₘ (UInt256.ofNat (MachineState.M 0 0 (UInt256.ofNat payload.size).toNat)) -
    EVM.Cₘ (UInt256.ofNat 0) = _
  rw [value, fresh_extent, native_memory_cost _ (constructor_words_bound _ bounded)]
  rfl

theorem return_memory_cost (payload : ByteArray) (pre : EVM.State)
    (holds : DataAt payload ⟨8, by decide⟩ pre)
    (copied : pre.activeWords = UInt256.ofNat (words payload.size))
    (bounded : payload.size ≤ 49152) :
    EVM.memoryExpansionCost pre .RETURN = 0 := by
  have huge : 49152 < UInt256.size := by decide
  have value : (UInt256.ofNat payload.size).toNat = payload.size :=
    Nat.mod_eq_of_lt (by omega)
  have counter : (UInt256.ofNat (words payload.size)).toNat = words payload.size :=
    Nat.mod_eq_of_lt (constructor_words_bound _ bounded)
  simp only [EVM.memoryExpansionCost, EVM.memoryExpansionCost.μᵢ', holds.2.2.1, copied]
  change EVM.Cₘ (UInt256.ofNat (MachineState.M
    (UInt256.ofNat (words payload.size)).toNat 0 (UInt256.ofNat payload.size).toNat)) -
      EVM.Cₘ (UInt256.ofNat (words payload.size)) = 0
  rw [value, counter, repeated_extent, Nat.sub_self]

/-- Every reachable stage has its real memory charge; only CODECOPY expands. -/
theorem stage_memory_cost (payload : ByteArray) (stage : Fin 9) (pre : EVM.State)
    (holds : DataAt payload stage pre)
    (extent : pre.activeWords = UInt256.ofNat (stageWords payload.size stage))
    (bounded : payload.size ≤ 49152) :
    EVM.memoryExpansionCost pre (stageInstruction stage).1 =
      if stage.val = 6 then memoryCost (words payload.size) else 0 := by
  obtain ⟨stage, small⟩ := stage
  have positions : stage = 0 ∨ stage = 1 ∨ stage = 2 ∨ stage = 3 ∨ stage = 4 ∨
      stage = 5 ∨ stage = 6 ∨ stage = 7 ∨ stage = 8 := by omega
  rcases positions with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact copy_memory_cost payload pre holds extent bounded
    | exact return_memory_cost payload pre holds extent bounded
    | (change EVM.Cₘ pre.activeWords - EVM.Cₘ pre.activeWords = 0; exact Nat.sub_self _)

/-- Cumulative debits before each reachable constructor boundary. -/
def stageSpent (size : Nat) : Fin 9 → Nat
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 3
  | ⟨2, _⟩ => 5
  | ⟨3, _⟩ => 8
  | ⟨4, _⟩ => 11
  | ⟨5, _⟩ => 14
  | ⟨6, _⟩ => 16
  | ⟨7, _⟩ => 19 + 3 * words size + memoryCost (words size)
  | ⟨8, _⟩ => prefixCost size

/-- The local native debits add to the canonical prefix cost. -/
theorem stage_spent_next (size : Nat) (stage : Fin 8) :
    stageSpent size ⟨stage.val + 1, by omega⟩ =
      stageSpent size ⟨stage.val, by omega⟩ + stageCost size ⟨stage.val, by omega⟩ +
        (if stage.val = 6 then memoryCost (words size) else 0) := by
  obtain ⟨stage, small⟩ := stage
  have positions : stage = 0 ∨ stage = 1 ∨ stage = 2 ∨ stage = 3 ∨ stage = 4 ∨
      stage = 5 ∨ stage = 6 ∨ stage = 7 := by omega
  rcases positions with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [stageSpent, stageCost, prefixCost]
  all_goals omega

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor

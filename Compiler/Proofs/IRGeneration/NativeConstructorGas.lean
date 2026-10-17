import Compiler.Proofs.IRGeneration.NativeMidnightConstructor

/-! Native/canonical gas arithmetic for the actual Midnight header.
These are local cost facts, not a whole-X gas correspondence theorem. -/
namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul
open Verity.Core.Model.MidnightInitcode

/-- The actual native fresh-memory extent uses the same word rounding. -/
theorem fresh_extent (size : Nat) :
    MachineState.M 0 0 size = words size := by
  cases size with
  | zero => rfl
  | succ size => simp only [MachineState.M, words, Nat.zero_add, Nat.zero_max]

/-- RETURN over precisely the copied window does not expand active memory. -/
theorem repeated_extent (size : Nat) :
    MachineState.M (words size) 0 size = words size := by
  cases size with
  | zero => rfl
  | succ size => simp only [MachineState.M, words, Nat.zero_add, Nat.max_self]

/-- The native C_m polynomial agrees with canonical memoryCost when its word
counter is represented without wrapping. -/
theorem native_memory_cost (count : Nat) (bounded : count < UInt256.size) :
    EVM.Cₘ (UInt256.ofNat count) = memoryCost count := by
  have value : (UInt256.ofNat count).toNat = count := by
    exact Nat.mod_eq_of_lt bounded
  simp only [EVM.Cₘ, value, GasConstants.Gmemory, EVM.Cₘ.QuadraticCeofficient, memoryCost]

/-- The EIP-3860 constructor limit is well below the native word modulus. -/
theorem constructor_words_bound (size : Nat) (bounded : size ≤ 49152) :
    words size < UInt256.size := by
  have rounded := Nat.div_le_self (size + 31) 32
  have huge : 49183 < UInt256.size := by decide
  unfold words
  omega

/-- This is the native CODECOPY instruction charge before its separate memory
expansion charge. The actual stack word supplies the copied size. -/
theorem copy_instruction_cost (pre : EVM.State) (dest source length : UInt256)
    (rest : Stack UInt256) (stack : pre.stack = dest :: source :: length :: rest) :
    EVM.C' pre .CODECOPY = 3 + 3 * words length.toNat := by
  simp [EVM.C', EVM.InstructionGasGroups.Wcopy, stack, GasConstants.Gverylow,
    GasConstants.Gcopy, words]

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor

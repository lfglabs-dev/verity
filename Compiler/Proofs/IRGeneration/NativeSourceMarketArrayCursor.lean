import Compiler.Proofs.IRGeneration.NativeSourceArrayIterationBounds

namespace Compiler.Proofs.IRGeneration.NativeSourceMarketArrayCursor
open EvmYul EVM EVM.Proof NativeSourceMarketArrayBounds

def cursor (index : Nat) := UInt256.ofNat (388 + 128 * index)

theorem cursor_value (index count : Nat) (within : index ≤ count)
    (bound : 388 + 128 * count < UInt256.size) :
    (cursor index).toNat = 388 + 128 * index := by
  change (388 + 128 * index) % UInt256.size = _
  exact Nat.mod_eq_of_lt (by omega)

theorem iterate (n : UInt256) (index : Nat) (inside : index < n.toNat)
    (bound : 388 + 128 * n.toNat < UInt256.size) :
    NativeSourceArrayIterationGuard.flag (arrayEnd n) (cursor index) = UInt256.ofNat 1 := by
  have position := cursor_value index n.toNat (by omega) bound
  have endValue := end_value n bound
  exact NativeSourceArrayIterationBounds.flag_one _ _ (by omega)

theorem finished (n : UInt256) (bound : 388 + 128 * n.toNat < UInt256.size) :
    NativeSourceArrayIterationGuard.flag (arrayEnd n) (cursor n.toNat) = UInt256.ofNat 0 := by
  have position := cursor_value n.toNat n.toNat (by omega) bound
  have endValue := end_value n bound
  exact NativeSourceArrayIterationBounds.flag_zero _ _ (by omega)

theorem advance (index count : Nat) (inside : index < count)
    (bound : 388 + 128 * count < UInt256.size) :
    (cursor index + UInt256.ofNat 128).toNat = (cursor (index + 1)).toNat := by
  have current := cursor_value index count (by omega) bound
  have next := cursor_value (index + 1) count (by omega) bound
  have step128 : (UInt256.ofNat 128).toNat = 128 := by decide
  have addition := NativeSourceCheckedAllocatorBounds.addition (cursor index) (UInt256.ofNat 128) (by omega)
  omega

theorem execute (fuel : Nat) (pre : EVM.State) (pointer n : UInt256) (index : Nat) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 324)
    (stack : pre.stack = pointer :: arrayEnd n :: cursor index :: tail)
    (gas : 22 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1019)
    (within : index ≤ n.toNat) (bound : 388 + 128 * n.toNat < UInt256.size) :
    EVM.X (fuel + 6) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      EVM.X (fuel + 1) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0))
        (NativeSourceArrayIterationGuard.decided pre pointer (arrayEnd n) (cursor index) tail) ∧
    (NativeSourceArrayIterationGuard.decided pre pointer (arrayEnd n) (cursor index) tail).pc =
      (if index < n.toNat then UInt256.ofNat 806 else UInt256.ofNat 331) ∧
    (NativeSourceArrayIterationGuard.decided pre pointer (arrayEnd n) (cursor index) tail).gasAvailable.toNat =
      pre.gasAvailable.toNat - 22 := by
  refine ⟨NativeSourceArrayIterationGuard.execute fuel pre pointer (arrayEnd n) (cursor index) tail code pc stack gas depth,
    ?_, NativeSourceArrayIterationGuard.gas_exact pre pointer (arrayEnd n) (cursor index) tail gas⟩
  rw [NativeSourceArrayIterationBounds.destinations pre pointer (arrayEnd n) (cursor index) tail pc]
  by_cases inside : index < n.toNat
  · rw [iterate n index inside bound, if_pos inside]
    rfl
  · have equal : index = n.toNat := by omega
    rw [equal, finished n bound, if_neg (show ¬n.toNat < n.toNat by omega)]
    rfl

end Compiler.Proofs.IRGeneration.NativeSourceMarketArrayCursor

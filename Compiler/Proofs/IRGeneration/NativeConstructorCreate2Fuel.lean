import Compiler.Proofs.IRGeneration.NativeConstructorLambdaAdequacy

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul
open Verity.Core.Model.MidnightInitcode

theorem lambda_all_targets_fuel_stable (payload : ByteArray) (bounded : payload.size ≤ 49152)
    (blobs : List ByteArray) (created : Std.TreeSet AccountAddress compare)
    (genesis : BlockHeader) (blocks : ProcessedBlocks)
    (accounts original : AccountMap .EVM) (substate : Substate)
    (sender origin : AccountAddress) (gas price value depth : UInt256)
    (salt : ByteArray) (header : BlockHeader) (permission : Bool)
    (fuelA fuelB : Nat) (enoughA : 10 ≤ fuelA) (enoughB : 10 ≤ fuelB) :
    EVM.Lambda (fuelA + 2) blobs created genesis blocks accounts original substate
      sender origin gas price value (initcode payload) depth (some salt) header permission =
    EVM.Lambda (fuelB + 2) blobs created genesis blocks accounts original substate
      sender origin gas price value (initcode payload) depth (some salt) header permission := by
  let target := nativeCreate2Target sender salt (initcode payload)
  by_cases vacant : (accounts.getD target default).nonce = UInt256.ofNat 0 ∧
      (accounts.getD target default).code.size = 0
  · rw [lambda_constructor payload bounded blobs created genesis blocks accounts original substate
      sender origin gas price value depth salt header permission vacant fuelA enoughA,
      lambda_constructor payload bounded blobs created genesis blocks accounts original substate
      sender origin gas price value depth salt header permission vacant fuelB enoughB]
  · have collision : (decide ((accounts.getD target default).nonce ≠ (⟨0⟩ : UInt256)) ||
        decide ((accounts.getD target default).code.size ≠ 0)) = true := by
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      have zeroEq : UInt256.ofNat 0 = (⟨0⟩ : UInt256) := rfl
      rw [zeroEq] at vacant
      by_cases nonce : (accounts.getD target default).nonce = (⟨0⟩ : UInt256)
      · exact Or.inr (fun code => vacant ⟨nonce, code⟩)
      · exact Or.inl nonce
    rw [show fuelA + 2 = (fuelA - 1) + 3 by omega,
      show fuelB + 2 = (fuelB - 1) + 3 by omega,
      lambda_collision (initcode payload) blobs created genesis blocks accounts original substate
        sender origin gas price value depth salt header permission collision (fuelA - 1),
      lambda_collision (initcode payload) blobs created genesis blocks accounts original substate
        sender origin gas price value depth salt header permission collision (fuelB - 1)]

/-- Actual native CREATE2 step becomes fuel-independent once the memory
slice is exactly the supported constructor and its child fuel is adequate. -/
theorem create2_step_fuel_stable (payload : ByteArray) (bounded : payload.size ≤ 49152)
    (pre : EVM.State) (cost : Nat) (rest : Stack UInt256)
    (value offset size salt : UInt256)
    (popped : pre.stack.pop4 = some (rest, value, offset, size, salt))
    (code : pre.memory.readWithPadding offset.toNat size.toNat = initcode payload)
    (fuelA fuelB : Nat) (enoughA : 10 ≤ fuelA) (enoughB : 10 ≤ fuelB) :
    EVM.step (fuelA + 3) cost (some (.CREATE2, none)) pre =
      EVM.step (fuelB + 3) cost (some (.CREATE2, none)) pre := by
  simp only [EVM.step]
  dsimp only [Pure.pure, Except.pure, Bind.bind, Except.bind]
  simp only [popped, code]
  rw [lambda_all_targets_fuel_stable payload bounded _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    fuelA fuelB enoughA enoughB]

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor

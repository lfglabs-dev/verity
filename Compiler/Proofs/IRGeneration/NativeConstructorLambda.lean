import Compiler.Proofs.IRGeneration.NativeConstructorXi

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul
open Verity.Core.Model.MidnightInitcode

/-- Native CREATE2 address expression, using the actual FFI hash boundary. -/
def nativeCreate2Target (sender : AccountAddress) (salt init : ByteArray) : AccountAddress :=
  Fin.ofNat _ (fromByteArrayBigEndian
    ((ffi.KEC (BE 255 ++ sender.toByteArray ++ salt ++ ffi.KEC init)).extract 12 32))

/-- For a collision-free target Lambda consumes one unit before Ξ.
The premise refers to the exact native address, not a guessed account. -/
theorem lambda_fuel_stable (payload : ByteArray)
    (blobs : List ByteArray) (created : Std.TreeSet AccountAddress compare)
    (genesis : BlockHeader) (blocks : ProcessedBlocks)
    (accounts original : AccountMap .EVM) (substate : Substate)
    (sender origin : AccountAddress) (gas price value depth : UInt256)
    (salt : ByteArray) (header : BlockHeader) (permission : Bool)
    (vacant : let account := accounts.getD (nativeCreate2Target sender salt (initcode payload)) default
      account.nonce = UInt256.ofNat 0 ∧ account.code.size = 0)
    (fuelA fuelB : Nat) (enoughA : 14 ≤ fuelA) (enoughB : 14 ≤ fuelB) :
    EVM.Lambda (fuelA + 1) blobs created genesis blocks accounts original substate
      sender origin gas price value (initcode payload) depth (some salt) header permission =
    EVM.Lambda (fuelB + 1) blobs created genesis blocks accounts original substate
      sender origin gas price value (initcode payload) depth (some salt) header permission := by
  simp only [EVM.Lambda, EVM.Lambda.L_A]
  dsimp only [liftM, monadLift, MonadLift.monadLift, Option.option, Bind.bind, Except.bind]
  rw [xi_fuel_stable payload _ _ _ _ _ _ _ _ ?_ fuelA fuelB enoughA enoughB]
  simp only [nativeCreate2Target] at vacant
  simp only [vacant.1, vacant.2]
  rfl

theorem lambda_fuel_adequate (payload : ByteArray)
    (blobs : List ByteArray) (created : Std.TreeSet AccountAddress compare)
    (genesis : BlockHeader) (blocks : ProcessedBlocks)
    (accounts original : AccountMap .EVM) (substate : Substate)
    (sender origin : AccountAddress) (gas price value depth : UInt256)
    (salt : ByteArray) (header : BlockHeader) (permission : Bool)
    (vacant : let account := accounts.getD (nativeCreate2Target sender salt (initcode payload)) default
      account.nonce = UInt256.ofNat 0 ∧ account.code.size = 0)
    (fuel : Nat) (enough : 14 ≤ fuel) :
    EVM.Lambda (fuel + 1) blobs created genesis blocks accounts original substate
      sender origin gas price value (initcode payload) depth (some salt) header permission ≠
      .error .OutOfFuel := by
  simp only [EVM.Lambda, EVM.Lambda.L_A]
  dsimp only [liftM, monadLift, MonadLift.monadLift, Option.option, Bind.bind, Except.bind]
  split
  · rename_i reason failed
    by_cases exhausted : reason = .OutOfFuel
    · subst reason
      exfalso
      refine (xi_fuel_adequate payload _ _ _ _ _ _ _ _ ?_ fuel enough) failed
      · simp only [nativeCreate2Target] at vacant
        simp only [vacant.1, vacant.2]
        rfl
    · have guard : (reason == EVM.ExecutionException.OutOfFuel) = false := by
        cases reason
        · exact False.elim (exhausted rfl)
        all_goals rfl
      rw [guard]
      intro impossible
      cases impossible
  · intro impossible
    cases impossible
  · intro impossible
    cases impossible

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor

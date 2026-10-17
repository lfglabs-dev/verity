import Compiler.Proofs.IRGeneration.NativeConstructorXiResult
import Compiler.Proofs.IRGeneration.NativeConstructorLambda

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul
open Verity.Core.Model.MidnightInitcode

/-- Actual native creation rolls back the account map on constructor gas
exhaustion, retaining the native accessed/created-account bookkeeping. -/
theorem lambda_low_gas (payload : ByteArray) (bounded : payload.size ≤ 49152)
    (blobs : List ByteArray) (created : Std.TreeSet AccountAddress compare)
    (genesis : BlockHeader) (blocks : ProcessedBlocks)
    (accounts original : AccountMap .EVM) (substate : Substate)
    (sender origin : AccountAddress) (gas price value depth : UInt256)
    (salt : ByteArray) (header : BlockHeader) (permission : Bool)
    (vacant : let account := accounts.getD (nativeCreate2Target sender salt (initcode payload)) default
      account.nonce = UInt256.ofNat 0 ∧ account.code.size = 0)
    (low : gas.toNat < prefixCost payload.size) (fuel : Nat) (enough : 10 ≤ fuel) :
    let target := nativeCreate2Target sender salt (initcode payload)
    EVM.Lambda (fuel + 2) blobs created genesis blocks accounts original substate
      sender origin gas price value (initcode payload) depth (some salt) header permission =
      .ok (target, created.insert target, accounts, UInt256.ofNat 0,
        substate.addAccessedAccount target, false, ByteArray.empty) := by
  simp only [EVM.Lambda, EVM.Lambda.L_A]
  dsimp only [liftM, monadLift, MonadLift.monadLift, Option.option, Bind.bind, Except.bind]
  rw [xi_constructor payload bounded _ _ _ _ _ _ _ _ ?_ fuel enough]
  · rw [if_pos low]
    simp only [nativeCreate2Target] at vacant
    simp only [vacant.1, vacant.2]
    rfl
  · simp only [nativeCreate2Target] at vacant
    simp only [vacant.1, vacant.2]
    rfl

/-- Exact native post-constructor account/gas formula. The following theorem
identifies this explicit result with execution of the pinned native Lambda. -/
def lambdaConstructorResult (payload : ByteArray)
    (created : Std.TreeSet AccountAddress compare) (accounts : AccountMap .EVM)
    (substate : Substate) (sender : AccountAddress) (gas value : UInt256) (salt : ByteArray) :
    Except EVM.ExecutionException (AccountAddress × Std.TreeSet AccountAddress compare ×
      AccountMap .EVM × UInt256 × Substate × Bool × ByteArray) :=
    let target := nativeCreate2Target sender salt (initcode payload)
    let old := accounts.getD target default
    let reserved : Account .EVM := { old with
      nonce := old.nonce + UInt256.ofNat 1
      balance := value + old.balance
      storage := default }
    let entered := match accounts.get? sender with
      | none => accounts
      | some account => (accounts.insert sender { account with balance := account.balance - value }).insert target reserved
    let marked := created.insert target
    let accessed := substate.addAccessedAccount target
    let remaining := UInt256.ofNat (gas.toNat - prefixCost payload.size)
    let rejected : Bool := Id.run do
      let collision : Bool := match accounts.get? target with
        | some account => account.code ≠ ByteArray.empty ∨ account.nonce ≠ UInt256.ofNat 0
        | none => false
      let deposit : Bool := remaining.toNat < GasConstants.Gcodedeposit * payload.size
      let large : Bool := payload.size > 24576
      let forbidden : Bool := ¬large && payload[0]? = some 0xef
      pure (collision ∨ deposit ∨ large ∨ forbidden)
    if gas.toNat < prefixCost payload.size then
      .ok (target, marked, accounts, UInt256.ofNat 0, accessed, false, ByteArray.empty)
    else .ok (target, marked,
      (if rejected then accounts else entered.insert target { (entered.getD target default) with code := payload }),
      UInt256.ofNat (if rejected then 0 else remaining.toNat - GasConstants.Gcodedeposit * payload.size),
      accessed, !rejected, ByteArray.empty)

theorem lambda_constructor (payload : ByteArray) (bounded : payload.size ≤ 49152)
    (blobs : List ByteArray) (created : Std.TreeSet AccountAddress compare)
    (genesis : BlockHeader) (blocks : ProcessedBlocks)
    (accounts original : AccountMap .EVM) (substate : Substate)
    (sender origin : AccountAddress) (gas price value depth : UInt256)
    (salt : ByteArray) (header : BlockHeader) (permission : Bool)
    (vacant : let account := accounts.getD (nativeCreate2Target sender salt (initcode payload)) default
      account.nonce = UInt256.ofNat 0 ∧ account.code.size = 0)
    (fuel : Nat) (enough : 10 ≤ fuel) :
    EVM.Lambda (fuel + 2) blobs created genesis blocks accounts original substate
      sender origin gas price value (initcode payload) depth (some salt) header permission =
      lambdaConstructorResult payload created accounts substate sender gas value salt := by
  unfold lambdaConstructorResult
  simp only [EVM.Lambda, EVM.Lambda.L_A]
  dsimp only [liftM, monadLift, MonadLift.monadLift, Option.option, Bind.bind, Except.bind]
  rw [xi_constructor payload bounded _ _ _ _ _ _ _ _ ?_ fuel enough]
  · simp only [nativeCreate2Target] at vacant
    simp only [vacant.1, vacant.2]
    simp only [nativeCreate2Target]
    have zeroEq : UInt256.ofNat 0 = (⟨0⟩ : UInt256) := rfl
    simp only [zeroEq, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, if_false, Bool.or_false]
    by_cases low : gas.toNat < prefixCost payload.size
    · simp only [if_pos low]
      rfl
    · simp only [if_neg low]
      simp only [vacant.1, ite_self]
      rfl
  · simp only [nativeCreate2Target] at vacant
    simp only [vacant.1, vacant.2]
    rfl

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor

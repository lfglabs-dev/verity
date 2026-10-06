import Contracts.Common
import Compiler.CheckContract

set_option linter.unusedVariables false

/-!
# ERC-20 balance read and transfer through a linked hop (G14)

A strategy-shaped contract reads `IERC20(token).balanceOf(this)` and calls
`transfer` on a generated ERC-20 bound by `linked_contracts`. Both run the
token's generated body at the runtime target (`hopCallView` / `hopCall`), so:

* the balance read equals the token's own `balances` entry for the strategy,
  parked at `.scoped token (.map 0 strategy)` (general theorem
  `held_eq_token_entry`, for every state);
* a transfer through the hop moves the token's balances, and the next balance
  read sees the new value (kernel witnesses);
* the strategy's own storage is untouched by the hop.

This is the shape of `strategyUnderlyingBalance >= remainingReserve`
(Pareto CLAIM-1): the left-hand side is a token-world word, not a value
stored by the strategy.
-/

namespace Contracts.Smoke.Erc20BalanceHop

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256

verity_contract HopToken where
  storage
    balances : Address → Uint256 := slot 0

  function view balanceOf (account : Address) : Uint256 := do
    let b ← getMapping balances account
    return b

  function transfer (recipient : Address, amount : Uint256) : Bool := do
    let sender ← msgSender
    let fromBalance ← getMapping balances sender
    require (fromBalance >= amount) "ERC20: transfer amount exceeds balance"
    setMapping balances sender (sub fromBalance amount)
    let toBalance ← getMapping balances recipient
    setMapping balances recipient (add toBalance amount)
    return true

#check_contract HopToken

verity_contract HopStrategy where
  storage
    reserve : Uint256 := slot 0

  interfaces
    interface IHopERC20 where
      function balanceOf(Address) view returns (Uint256)
      function transfer(Address, Uint256) returns (Bool)
    end

  linked_contracts
    underlying : IHopERC20 := HopToken

  function view held (_t : IHopERC20, _account : Address) : Uint256 := do
    let v ← _t.balanceOf _account
    return v

  function reentrancy_trusted pay (_t : IHopERC20, _to : Address, _amount : Uint256) : Unit := do
    let ok ← _t.transfer _to _amount
    require ok "SafeERC20: ERC20 operation did not succeed"

#check_contract HopStrategy

/-- The typed view call elaborates to the token's generated body in a view hop. -/
theorem held_is_hopCallView (t a : Address) :
    HopStrategy.held t a = (do
      let v ← Contract.hopCallView t (HopToken.balanceOf a)
      return v) := rfl

/-- For every state: reading `balanceOf(a)` on a distinct token returns the
token's own parked `balances[a]` and leaves the caller's storage unchanged. -/
theorem held_eq_token_entry (t a : Address) (s : ContractState) (h : s.thisAddress ≠ t) :
    HopStrategy.held t a s =
      ContractResult.success (s.storageWords (.scoped t.toNat (.map 0 a)))
        { s with returndata := [] } := by
  rw [held_is_hopCallView]
  show (Contract.hopCallView t (HopToken.balanceOf a) >>= fun v => pure v) s = _
  have hb : HopToken.balanceOf a = (do
      let b ← getMapping HopToken.balances a
      return b) := rfl
  rw [hb]
  show Verity.bind _ _ s = _
  unfold Verity.bind
  rw [Contract.hopCallView_of_ne t _ s h]
  rfl

def stratAddr : Address := (70 : Address)
def tokenAddr : Address := (71 : Address)
def userAddr : Address := (72 : Address)

/-- Strategy at `stratAddr` with its own reserve 40; the token holds 100 for the
strategy and 5 for the user in the token's namespace. -/
def s0 : ContractState :=
  ({ defaultState with thisAddress := stratAddr, sender := (1 : Address) }.withStorageWords fun k =>
      if k == StorageKey.scoped tokenAddr.toNat (.map 0 stratAddr) then 100
      else if k == StorageKey.scoped tokenAddr.toNat (.map 0 userAddr) then 5
      else 0).writeSlot 0 40

theorem held_strategy_is_100 :
    (HopStrategy.held tokenAddr stratAddr s0).getValue? = some (100 : Uint256) := by
  decide +kernel

/-- `pay` runs the token's `transfer` with `msg.sender = strategy`. -/
def s1 : ContractState :=
  (HopStrategy.pay ExecutableCallContext.stub tokenAddr userAddr 30 s0).getState

theorem pay_moves_token_balances :
    s1.storageWords (.scoped tokenAddr.toNat (.map 0 stratAddr)) = 70 ∧
    s1.storageWords (.scoped tokenAddr.toNat (.map 0 userAddr)) = 35 ∧
    s1.readSlot 0 = 40 := by
  decide +kernel

theorem held_after_pay :
    (HopStrategy.held tokenAddr stratAddr s1).getValue? = some (70 : Uint256) := by
  decide +kernel

/-- Over-transfer reverts inside the hop and the whole state is rolled back. -/
theorem pay_overdraw_reverts :
    (match HopStrategy.pay ExecutableCallContext.stub tokenAddr userAddr 101 s0 with
      | .success _ _ => false
      | .revert _ _ => true) = true := by
  decide +kernel

end Contracts.Smoke.Erc20BalanceHop

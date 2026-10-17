import Verity.Core.Uint256

/-! Account projection needed by CREATE2, isolated from opcode/gas execution.
This records nonce/code/balance effects at a creation boundary; it does not
execute initcode or justify Solidity admission. The caller must supply the
actual creation-entry decision and the actual runtime result. -/
namespace Verity.Core.Model.Create2Accounts

structure Account where
  nonce : Nat := 0
  code : ByteArray := ByteArray.empty
  balance : Uint256 := Uint256.ofNat 0

abbrev Accounts := Nat → Account

def occupied (account : Account) : Bool := account.nonce != 0 || account.code.size != 0

def bumpCreator (accounts : Accounts) (creator : Nat) : Accounts :=
  fun query => if query = creator then { accounts query with nonce := (accounts query).nonce + 1 }
    else accounts query

inductive Reservation where
  | collision (accounts : Accounts)
  | reserved (accounts : Accounts)

def Reservation.accounts : Reservation → Accounts
  | .collision accounts | .reserved accounts => accounts

/-- Once creation has entered, increment the creator before checking collision.
Checking the bumped map also handles target=creator without overwriting it.
On reservation, EIP-161 sets the created nonce to one; existing balance stays. -/
def reserve (accounts : Accounts) (creator target : Nat) : Reservation :=
  let bumped := bumpCreator accounts creator
  if occupied (bumped target) then .collision bumped
  else .reserved fun query => if query = target then { bumped query with nonce := 1 }
    else bumped query

theorem reserve_self_collision (accounts : Accounts) (creator : Nat) :
    reserve accounts creator creator = .collision (bumpCreator accounts creator) := by
  simp [reserve, occupied, bumpCreator]

/-- Every account outside the two affected addresses is preserved in either
outcome, including its code, nonce and balance. -/
theorem reserve_frame (accounts : Accounts) (creator target query : Nat)
    (notCreator : query ≠ creator) (notTarget : query ≠ target) :
    (reserve accounts creator target).accounts query = accounts query := by
  dsimp only [reserve]
  split <;> simp [Reservation.accounts, bumpCreator, notCreator, notTarget]

/-- Value-zero deployment never changes any account balance at reservation. -/
theorem reserve_balance (accounts : Accounts) (creator target query : Nat) :
    ((reserve accounts creator target).accounts query).balance = (accounts query).balance := by
  dsimp only [reserve]
  split <;> simp only [Reservation.accounts]
  · unfold bumpCreator; split <;> rfl
  · split
    · unfold bumpCreator; split <;> rfl
    · unfold bumpCreator; split <;> rfl

/-- Reservation itself cannot install runtime code or pretend that the
constructor ran. Exact runtime installation is a separate required step. -/
theorem reserve_code (accounts : Accounts) (creator target query : Nat) :
    ((reserve accounts creator target).accounts query).code = (accounts query).code := by
  dsimp only [reserve]
  split <;> simp only [Reservation.accounts]
  · unfold bumpCreator; split <;> rfl
  · split
    · unfold bumpCreator; split <;> rfl
    · unfold bumpCreator; split <;> rfl

/-- The successful reservation initializes exactly the target nonce. -/
theorem reserved_nonce (accounts : Accounts) (creator target : Nat) (after : Accounts)
    (success : reserve accounts creator target = .reserved after) :
    (after target).nonce = 1 := by
  dsimp only [reserve] at success
  split at success
  · contradiction
  · cases success
    simp

end Verity.Core.Model.Create2Accounts

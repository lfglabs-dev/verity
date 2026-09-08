/-
  Tests for P-ACCOUNT-1 specification.
  Concrete examples and property checks via #eval / #guard.
-/

import PAccount1
open PAccount1 PAddress1

private theorem small_lt_u256 {n : Nat} (h : n < 2 ^ 20) : n < U256_BOUND := by
  unfold U256_BOUND
  have : (2 : Nat) ^ 20 ≤ 2 ^ 256 := Nat.pow_le_pow_right (by omega) (by omega)
  omega

private def mkU256 (n : Nat) (h : n < 2 ^ 20 := by omega) : U256 :=
  ⟨n, small_lt_u256 h⟩

private theorem u256_bound_pos : 0 < U256_BOUND := by
  unfold U256_BOUND
  have : ∀ n : Nat, 0 < 2 ^ n := by
    intro n; induction n with
    | zero => decide
    | succ k ih => simp [Nat.pow_succ]; omega
  exact this 256

private def maxU256 : U256 :=
  ⟨U256_BOUND - 1, Nat.sub_lt u256_bound_pos (by omega)⟩

-- § Fee deduction — success path

#eval do
  let acct : Account := { nonce := u256_zero, balance := mkU256 1000 }
  let fee := mkU256 400
  let result ← deductFee acct fee
  guard (result.balance.val = 600)
  guard (result.nonce = acct.nonce)
  return "deductFee success OK"

-- § Fee deduction — insufficient balance

#guard deductFee { nonce := u256_zero, balance := mkU256 100 } (mkU256 200) = none

-- § Fee deduction — exact balance

#eval do
  let acct : Account := { nonce := u256_zero, balance := mkU256 500 }
  let fee := mkU256 500
  let result ← deductFee acct fee
  guard (result.balance.val = 0)
  return "deductFee exact OK"

-- § Credit — success path

#eval do
  let acct : Account := { nonce := u256_zero, balance := mkU256 1000 }
  let amt := mkU256 500
  let result ← creditAccount acct amt
  guard (result.balance.val = 1500)
  return "credit success OK"

-- § Credit — overflow rejection

#guard creditAccount { nonce := u256_zero, balance := maxU256 } (mkU256 1) = none

-- § Fee-then-claim roundtrip

#eval do
  let acct : Account := { nonce := u256_zero, balance := mkU256 1000 }
  let fee := mkU256 300
  let mid ← deductFee acct fee
  let final_ ← creditAccount mid fee
  guard (final_.balance = acct.balance)
  return "fee-claim roundtrip OK"

-- § Panic precedence

#guard ExecOutcome.beats .outOfGas .revert = true
#guard ExecOutcome.beats .outOfGas .success = true
#guard ExecOutcome.beats .revert .success = true
#guard ExecOutcome.beats .success .revert = false
#guard ExecOutcome.beats .revert .outOfGas = false

#guard resolveOutcome .outOfGas .revert = .outOfGas
#guard resolveOutcome .revert .success = .revert
#guard resolveOutcome .success .outOfGas = .outOfGas

-- § Packed storage roundtrip

#guard (Account.mk (mkU256 42) (mkU256 999)).pack.unpack
     = Account.mk (mkU256 42) (mkU256 999)

-- § Batch operations

#eval do
  let acct : Account := { nonce := u256_zero, balance := mkU256 1000 }
  let ops : List AccountOp := [
    .credit (mkU256 500),
    .deduct (mkU256 200),
    .deduct (mkU256 100)
  ]
  let result ← applyBatch acct ops
  guard (result.balance.val = 1200)
  return "batch ops OK"

-- § Batch — failure propagation

#guard applyBatch { nonce := u256_zero, balance := mkU256 100 }
  [.credit (mkU256 50), .deduct (mkU256 200), .credit (mkU256 999)] = none

-- § Auth — verified apply

#eval do
  let addr ← Address.ofNat? 42
  let ctx : AuthContext := ⟨fun _ _ => some addr⟩
  let acct : Account := { nonce := u256_zero, balance := mkU256 1000 }
  let authOp : AuthenticatedOp := {
    sender := addr, op := .deduct (mkU256 100), msgHash := 0, sig := 0
  }
  let result ← verifyAndApply ctx acct authOp
  guard (result.balance.val = 900)
  return "auth verify-and-apply OK"

-- § Auth — wrong sender rejected

#eval do
  let goodAddr ← Address.ofNat? 42
  let badAddr ← Address.ofNat? 99
  let ctx : AuthContext := ⟨fun _ _ => some goodAddr⟩
  let acct : Account := { nonce := u256_zero, balance := mkU256 1000 }
  let authOp : AuthenticatedOp := {
    sender := badAddr, op := .deduct (mkU256 100), msgHash := 0, sig := 0
  }
  guard (verifyAndApply ctx acct authOp = none)
  return "auth wrong sender rejected OK"

-- § Mutation canaries

#guard U256_BOUND = 2 ^ 256
#guard U256_BOUND > 0

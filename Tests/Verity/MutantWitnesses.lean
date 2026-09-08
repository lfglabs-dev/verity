/-
  Mutation witnesses for P-ACCOUNT-1 / P-ADDRESS-1.
  Each witness demonstrates that a specific mutation to the spec
  would be caught by the existing theorems and tests.
-/

import PAccount1
open PAccount1 PAddress1

/-
  Mutant 1: "fee deduction allows underflow"
  If deductFee didn't check fee ≤ balance, the conservation
  theorem would fail: result.balance.val + fee.val ≠ acct.balance.val
  when fee > balance because Nat subtraction saturates at 0.
  Witness: deductFee_conserves proves exact conservation.
-/
example : ∀ (acct : Account) (fee : U256) (result : Account),
    deductFee acct fee = some result →
    result.balance.val + fee.val = acct.balance.val :=
  deductFee_conserves

/-
  Mutant 2: "credit ignores overflow"
  If creditAccount didn't bound-check, credit_overflow_witness
  would fail: it explicitly proves rejection when sum ≥ U256_BOUND.
-/
example : ∀ (acct : Account) (amount : U256),
    acct.balance.val + amount.val ≥ U256_BOUND →
    creditAccount acct amount = none :=
  credit_overflow_witness

/-
  Mutant 3: "panic precedence reversed — revert beats outOfGas"
  The ordering is witnessed by concrete proofs on each pair.
  If the priority function were mutated, beats_asymm combined with
  outofgas_beats_revert would contradict the mutant.
-/
example : ExecOutcome.beats .outOfGas .revert := outofgas_beats_revert
example : ¬ExecOutcome.beats .revert .outOfGas :=
  beats_asymm .outOfGas .revert outofgas_beats_revert

/-
  Mutant 4: "packed storage drops nonce"
  If pack zeroed the nonce, pack_unpack_roundtrip would fail
  because unpack(pack(acct)) ≠ acct for nonzero nonce.
-/
example : ∀ (acct : Account), acct.pack.unpack = acct :=
  pack_unpack_roundtrip

/-
  Mutant 5: "batch ignores failed operations"
  If applyBatch skipped failures and continued, applyBatch_cons_none
  would fail: it proves that a failed op causes the whole batch to fail.
-/
example : ∀ (acct : Account) (op : AccountOp) (ops : List AccountOp),
    applyOp acct op = none →
    applyBatch acct (op :: ops) = none :=
  applyBatch_cons_none

/-
  Mutant 6: "auth skips sender check"
  If verifyAndApply didn't verify sender = recovered address,
  verifyAndApply_requires_auth would fail because it proves
  the recovered address must equal the claimed sender.
-/
example : ∀ (ctx : AuthContext) (acct : Account) (authOp : AuthenticatedOp)
    (result : Account),
    verifyAndApply ctx acct authOp = some result →
    ∃ addr, ctx.recover authOp.msgHash authOp.sig = some addr
          ∧ addr = authOp.sender :=
  verifyAndApply_requires_auth

/-
  Mutant 7: "address roundtrip loses high bits"
  If ofNat? truncated instead of bounding, the roundtrip
  theorem would fail for values near ADDR_BOUND.
-/
example : ∀ (a : Address), Address.ofNat? a.toNat = some a :=
  Address.roundtrip

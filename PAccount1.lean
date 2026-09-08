/-
  P-ACCOUNT-1: Formal specification of Ethereum account state operations.

  Solidity pin: 17005714f151e5502c559932319a3f2f74ac2436
  Checkpoint: 38895d80
  Branch base (main): caad1ef5e297202636e6fe643afa88fe8a62d618

  Transport-independent: no network-layer or serialisation-format assumptions.
  This is a specification that may advance; it is NOT claimed as a certified
  compile.  Prod archive-forward (HEAD 4622ddd8) is uncertified.

  Covers: fee/claim, overflow witnesses, panic-precedence ordering, auth
  verification, packed storage roundtrip, batch operations.
-/

import PAddress1

namespace PAccount1
open PAddress1

-- ────────────────────────────────────────────────────────
-- § 1  Uint256 — EVM word
-- ────────────────────────────────────────────────────────

def U256_BOUND : Nat := 2 ^ 256

private theorem u256_bound_pos_aux : 0 < U256_BOUND := by
  unfold U256_BOUND
  have : ∀ n : Nat, 0 < 2 ^ n := by
    intro n; induction n with
    | zero => decide
    | succ k ih => simp [Nat.pow_succ]; omega
  exact this 256

abbrev U256 := Fin U256_BOUND

def u256_zero : U256 := ⟨0, u256_bound_pos_aux⟩

-- ────────────────────────────────────────────────────────
-- § 2  Account state
-- ────────────────────────────────────────────────────────

structure Account where
  nonce   : U256
  balance : U256
  deriving DecidableEq, Repr

def Account.empty : Account :=
  { nonce := u256_zero, balance := u256_zero }

-- ────────────────────────────────────────────────────────
-- § 3  Fee deduction — underflow protection
-- ────────────────────────────────────────────────────────

def deductFee (acct : Account) (fee : U256) : Option Account :=
  if h : fee.val ≤ acct.balance.val then
    some { acct with balance := ⟨acct.balance.val - fee.val, by omega⟩ }
  else
    none

theorem deductFee_conserves (acct : Account) (fee : U256) (result : Account)
    (h : deductFee acct fee = some result) :
    result.balance.val + fee.val = acct.balance.val := by
  unfold deductFee at h
  split at h
  · next h_le =>
    injection h with h
    have : result.balance.val = acct.balance.val - fee.val := by
      rw [← h]
    omega
  · contradiction

theorem deductFee_nonce_preserved (acct : Account) (fee : U256) (result : Account)
    (h : deductFee acct fee = some result) :
    result.nonce = acct.nonce := by
  unfold deductFee at h
  split at h
  · injection h with h; rw [← h]
  · contradiction

theorem deductFee_insufficient (acct : Account) (fee : U256)
    (h : acct.balance.val < fee.val) :
    deductFee acct fee = none := by
  unfold deductFee
  simp [Nat.not_le.mpr h]

-- ────────────────────────────────────────────────────────
-- § 4  Claim / credit — overflow protection witness
-- ────────────────────────────────────────────────────────

def creditAccount (acct : Account) (amount : U256) : Option Account :=
  if h : acct.balance.val + amount.val < U256_BOUND then
    some { acct with balance := ⟨acct.balance.val + amount.val, h⟩ }
  else
    none

theorem credit_sum (acct : Account) (amount : U256) (result : Account)
    (h : creditAccount acct amount = some result) :
    result.balance.val = acct.balance.val + amount.val := by
  unfold creditAccount at h
  split at h
  · injection h with h
    rw [← h]
  · contradiction

theorem credit_overflow_witness (acct : Account) (amount : U256)
    (h : acct.balance.val + amount.val ≥ U256_BOUND) :
    creditAccount acct amount = none := by
  unfold creditAccount
  simp [Nat.not_lt.mpr h]

theorem credit_nonce_preserved (acct : Account) (amount : U256) (result : Account)
    (h : creditAccount acct amount = some result) :
    result.nonce = acct.nonce := by
  unfold creditAccount at h
  split at h
  · injection h with h; rw [← h]
  · contradiction

-- ────────────────────────────────────────────────────────
-- § 5  Fee-then-claim roundtrip (conservation law)
-- ────────────────────────────────────────────────────────

theorem fee_claim_roundtrip (acct : Account) (fee : U256) (mid final_ : Account)
    (h1 : deductFee acct fee = some mid)
    (h2 : creditAccount mid fee = some final_) :
    final_.balance = acct.balance := by
  have hcons := deductFee_conserves acct fee mid h1
  have hsum  := credit_sum mid fee final_ h2
  apply Fin.ext
  omega

-- ────────────────────────────────────────────────────────
-- § 6  Panic-precedence ordering
--      OutOfGas > Revert > Success, total order.
--      "Panic precedence" means: when multiple outcomes
--      could apply, the highest-priority one wins.
-- ────────────────────────────────────────────────────────

inductive ExecOutcome where
  | outOfGas
  | revert
  | success
  deriving DecidableEq, Repr

def ExecOutcome.priority : ExecOutcome → Nat
  | .outOfGas => 2
  | .revert   => 1
  | .success  => 0

def ExecOutcome.beats (a b : ExecOutcome) : Prop :=
  a.priority > b.priority

instance : DecidableRel ExecOutcome.beats := fun a b =>
  inferInstanceAs (Decidable (a.priority > b.priority))

theorem outofgas_beats_revert : ExecOutcome.beats .outOfGas .revert := by decide

theorem outofgas_beats_success : ExecOutcome.beats .outOfGas .success := by decide

theorem revert_beats_success : ExecOutcome.beats .revert .success := by decide

theorem beats_irrefl (o : ExecOutcome) : ¬ExecOutcome.beats o o := by
  cases o <;> decide

theorem beats_asymm (a b : ExecOutcome) (h : ExecOutcome.beats a b) :
    ¬ExecOutcome.beats b a := by
  cases a <;> cases b <;> simp [ExecOutcome.beats, ExecOutcome.priority] at * <;> omega

theorem beats_trans (a b c : ExecOutcome)
    (h1 : ExecOutcome.beats a b) (h2 : ExecOutcome.beats b c) :
    ExecOutcome.beats a c := by
  cases a <;> cases b <;> cases c <;>
    simp [ExecOutcome.beats, ExecOutcome.priority] at * <;> omega

def resolveOutcome (a b : ExecOutcome) : ExecOutcome :=
  if ExecOutcome.beats a b then a else b

theorem resolve_picks_higher (a b : ExecOutcome)
    (h : ExecOutcome.beats a b) :
    resolveOutcome a b = a := by
  unfold resolveOutcome; simp [h]

-- ────────────────────────────────────────────────────────
-- § 7  Packed storage — account to/from word pair
-- ────────────────────────────────────────────────────────

structure PackedAccount where
  word0 : U256  -- nonce
  word1 : U256  -- balance

def Account.pack (acct : Account) : PackedAccount :=
  { word0 := acct.nonce, word1 := acct.balance }

def PackedAccount.unpack (p : PackedAccount) : Account :=
  { nonce := p.word0, balance := p.word1 }

theorem pack_unpack_roundtrip (acct : Account) :
    acct.pack.unpack = acct := by
  simp [Account.pack, PackedAccount.unpack]

theorem unpack_pack_roundtrip (p : PackedAccount) :
    p.unpack.pack = p := by
  simp [Account.pack, PackedAccount.unpack]

-- ────────────────────────────────────────────────────────
-- § 8  Batch operations
-- ────────────────────────────────────────────────────────

inductive AccountOp where
  | deduct (fee : U256)
  | credit (amount : U256)

def applyOp (acct : Account) (op : AccountOp) : Option Account :=
  match op with
  | .deduct fee    => deductFee acct fee
  | .credit amount => creditAccount acct amount

def applyBatch (acct : Account) : List AccountOp → Option Account
  | []        => some acct
  | op :: ops => match applyOp acct op with
    | some acct' => applyBatch acct' ops
    | none       => none

theorem applyBatch_nil (acct : Account) :
    applyBatch acct [] = some acct := rfl

theorem applyBatch_cons_some (acct mid : Account) (op : AccountOp)
    (ops : List AccountOp)
    (h : applyOp acct op = some mid) :
    applyBatch acct (op :: ops) = applyBatch mid ops := by
  simp [applyBatch, h]

theorem applyBatch_cons_none (acct : Account) (op : AccountOp)
    (ops : List AccountOp)
    (h : applyOp acct op = none) :
    applyBatch acct (op :: ops) = none := by
  simp [applyBatch, h]

theorem applyBatch_append (acct : Account) (ops1 ops2 : List AccountOp)
    (mid : Account)
    (h1 : applyBatch acct ops1 = some mid) :
    applyBatch acct (ops1 ++ ops2) = applyBatch mid ops2 := by
  induction ops1 generalizing acct with
  | nil =>
    simp [applyBatch] at h1
    subst h1
    simp
  | cons op rest ih =>
    simp only [List.cons_append, applyBatch]
    simp only [applyBatch] at h1
    generalize h_op : applyOp acct op = r at *
    cases r with
    | none => simp at h1
    | some acct' => exact ih acct' h1

-- ────────────────────────────────────────────────────────
-- § 9  Auth — address-guarded operations
--      Uses PAddress1.AuthContext for recovery.
-- ────────────────────────────────────────────────────────

structure AuthenticatedOp where
  sender  : Address
  op      : AccountOp
  msgHash : Nat
  sig     : Nat

def verifyAndApply (ctx : AuthContext) (acct : Account)
    (authOp : AuthenticatedOp) : Option Account :=
  match ctx.recover authOp.msgHash authOp.sig with
  | some addr =>
    if addr = authOp.sender then applyOp acct authOp.op else none
  | none => none

theorem verifyAndApply_requires_auth (ctx : AuthContext) (acct : Account)
    (authOp : AuthenticatedOp) (result : Account)
    (h : verifyAndApply ctx acct authOp = some result) :
    ∃ addr, ctx.recover authOp.msgHash authOp.sig = some addr
          ∧ addr = authOp.sender := by
  unfold verifyAndApply at h
  split at h
  · next addr h_rec =>
    split at h
    · next h_eq => exact ⟨addr, h_rec, h_eq⟩
    · contradiction
  · contradiction

end PAccount1

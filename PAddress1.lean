/-
  P-ADDRESS-1: Formal specification of Ethereum address representation and operations.

  Solidity pin: 17005714f151e5502c559932319a3f2f74ac2436
  Checkpoint: 38895d80
  Branch base (main): caad1ef5e297202636e6fe643afa88fe8a62d618

  Transport-independent: no network-layer or serialisation-format assumptions.
  This is a specification that may advance; it is NOT claimed as a certified
  compile.  Prod archive-forward (HEAD 4622ddd8) is uncertified.
-/

namespace PAddress1

-- ────────────────────────────────────────────────────────
-- § 1  Address type — 160-bit bounded natural
-- ────────────────────────────────────────────────────────

def ADDR_BOUND : Nat := 2 ^ 160

private theorem two_pow_pos (n : Nat) : 0 < 2 ^ n := by
  induction n with
  | zero => decide
  | succ k ih => simp [Nat.pow_succ]; omega

structure Address where
  val : Fin ADDR_BOUND
  deriving DecidableEq, Repr

instance : Inhabited Address where
  default := ⟨⟨0, two_pow_pos 160⟩⟩

def Address.zero : Address := default

def Address.ofNat? (n : Nat) : Option Address :=
  if h : n < ADDR_BOUND then some ⟨⟨n, h⟩⟩ else none

def Address.toNat (a : Address) : Nat := a.val.val

-- ────────────────────────────────────────────────────────
-- § 2  Bounds and representation
-- ────────────────────────────────────────────────────────

theorem Address.bounded (a : Address) : a.toNat < ADDR_BOUND :=
  a.val.isLt

theorem addr_bound_pos : 0 < ADDR_BOUND := two_pow_pos 160

-- ────────────────────────────────────────────────────────
-- § 3  Packed storage — lossless roundtrip
-- ────────────────────────────────────────────────────────

theorem Address.roundtrip (a : Address) :
    Address.ofNat? a.toNat = some a := by
  unfold ofNat? toNat
  have h := a.val.isLt
  simp [h]

theorem Address.ofNat?_rejects (n : Nat) (h : n ≥ ADDR_BOUND) :
    Address.ofNat? n = none := by
  unfold ofNat?
  simp [Nat.not_lt.mpr h]

-- ────────────────────────────────────────────────────────
-- § 4  Injectivity — distinct values ↔ distinct addresses
-- ────────────────────────────────────────────────────────

theorem Address.toNat_injective (a b : Address) (h : a.toNat = b.toNat) :
    a = b := by
  cases a with | mk va =>
  cases b with | mk vb =>
  simp [toNat] at h
  congr 1
  exact Fin.ext h

theorem Address.ofNat?_val (n : Nat) (a : Address)
    (h : Address.ofNat? n = some a) : a.toNat = n := by
  unfold ofNat? at h
  split at h
  · simp at h; simp [toNat]; exact congrArg Fin.val (congrArg Address.val h.symm)
  · contradiction

-- ────────────────────────────────────────────────────────
-- § 5  Auth stub — abstract signature-to-address recovery
--      Transport-independent: does not prescribe secp256k1
--      or any specific curve.  The contract is: recovery is
--      a partial function that, when it succeeds, yields
--      exactly one address deterministically.
-- ────────────────────────────────────────────────────────

structure AuthContext where
  recover : (msgHash : Nat) → (sig : Nat) → Option Address

theorem auth_deterministic (ctx : AuthContext) (msg sig : Nat)
    (a b : Address)
    (ha : ctx.recover msg sig = some a)
    (hb : ctx.recover msg sig = some b) :
    a = b := by
  rw [ha] at hb; injection hb

-- ────────────────────────────────────────────────────────
-- § 6  Batch address validation
-- ────────────────────────────────────────────────────────

def validateBatch (ns : List Nat) : List Address :=
  ns.filterMap Address.ofNat?

theorem validateBatch_subset (ns : List Nat) (a : Address)
    (h : a ∈ validateBatch ns) : a.toNat ∈ ns := by
  simp [validateBatch, List.mem_filterMap] at h
  obtain ⟨n, hn_mem, hn_eq⟩ := h
  have := Address.ofNat?_val n a hn_eq
  rw [this]
  exact hn_mem

theorem validateBatch_bounded (ns : List Nat) (a : Address)
    (_ : a ∈ validateBatch ns) : a.toNat < ADDR_BOUND :=
  a.bounded

end PAddress1

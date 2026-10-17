import EvmYul.UInt256

/-! Shared, kernel-proved ordering facts for the pinned native word type.
No native backend state bridge or model-storage conversion is imported. -/
namespace Compiler.Proofs.EvmYulUInt256Order
open EvmYul

/-- The derived `Ord` for `UInt256` generates
    `compare (mk a) (mk b) = Ordering.then (compare a b) .eq`
    rather than `compare a b` directly. This helper reduces the
    `Ordering.then` wrapper so we can delegate to `Fin`'s instances. -/
private theorem ordering_then_eq (o : Ordering) : o.then .eq = o := by
  cases o <;> rfl

/-- The derived `Ord` on `UInt256` (a single-field structure wrapping `Fin`)
    satisfies `compare (mk a) (mk b) = compare a b` on `Fin UInt256.size`.

    Lean 4's `deriving Ord` generates `Ordering.then (compare a b) .eq`,
    which we reduce via `ordering_then_eq`. -/
private theorem UInt256_compare_eq_fin (a b : Fin UInt256.size) :
    @compare UInt256 _ (UInt256.mk a) (UInt256.mk b) = @compare (Fin UInt256.size) _ a b := by
  -- The derived Ord generates: Ordering.then (compare a b) .eq
  -- We reduce this to compare a b by simplifying the Ordering.then wrapper.
  -- Use `change` to assert the definitional form, then apply ordering_then_eq.
  change (compare a b).then .eq = compare a b
  exact ordering_then_eq _

/-- `TransCmp` instance for `UInt256`'s derived `compare`.
    `UInt256` derives `Ord` which compares via the `Fin` field.
    `Fin n` has `TransOrd` and `LawfulEqOrd` in Lean 4's Std library.

    We bridge the derived Ord (which wraps in `Ordering.then ... .eq`)
    to `Fin`'s `TransCmp` instance. -/
instance instTransCmpUInt256 : Std.TransCmp (α := UInt256) compare where
  eq_swap {a b} := by
    cases a with | mk va => cases b with | mk vb =>
    simp only [UInt256_compare_eq_fin]
    exact Std.OrientedCmp.eq_swap
  isLE_trans {a b c} hab hbc := by
    cases a with | mk va => cases b with | mk vb => cases c with | mk vc =>
    simp only [UInt256_compare_eq_fin] at hab hbc ⊢
    exact Std.TransCmp.isLE_trans hab hbc

/-- `compare` on `UInt256` returning `.eq` implies equality.
    Proved by reducing to `Fin`'s compare and using `LawfulEqOrd`. -/
theorem UInt256_eq_of_compare_eq {u v : UInt256}
    (h : compare u v = Ordering.eq) : u = v := by
  cases u with | mk uv =>
  cases v with | mk vv =>
  rw [UInt256_compare_eq_fin] at h
  have heq : uv = vv := Std.LawfulEqCmp.eq_of_compare h
  subst heq
  rfl

end Compiler.Proofs.EvmYulUInt256Order

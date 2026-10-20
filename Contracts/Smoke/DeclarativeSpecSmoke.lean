import Contracts.Common

namespace Contracts.Smoke.DeclarativeSpecSmoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math
open Verity.Macro

/-!
# Declarative Contract Clauses & Auto-Frame (`by decide`) Smoke Test

Validates:
1. Declarative `preserves(...)`, `ensures(...)`, `requires_clause(...)`, and
   `ensures_clause(...)` syntax in `verity_contract`.
2. Automatic generation and 1-line proof of `<fn>_preserves_frame` and
   `<fn>_meets_ensures` without manual per-slot frame boilerplate.
3. Bitmask footprint disjointness (`slotsToBitmask`, `bitmaskDisjoint`,
   `slotBitDisjoint`) discharged in 1 line by `decide`.
4. Universal `StatementFootprintBound` composition and untouched-slot
   preservation (`eval_preserves_untouched_slot_of_bitmask_disjoint`,
   `eval_preserves_untouched_slot_snd_of_bitmask_disjoint`,
   `eval_preserves_preserved_mask_of_bitmask_disjoint`,
   `eval_preserves_preserved_mask_snd_of_bitmask_disjoint`).
5. Standalone `#gen_auto_frame_spec` macro and `verity_frame_auto` / `verity_auto`
   tactics.
-/

verity_contract DeclarativeVaultSmoke where
  storage
    totalAssets : Uint256 := slot 0
    owner : Address := slot 1
    feeBps : Uint256 := slot 2
    balances : Address → Uint256 := slot 3
    nonces : Uint256 → Uint256 := slot 4

  function setTotalAssets (newTotal : Uint256)
    modifies(totalAssets)
    preserves(owner, feeBps, balances, nonces)
    ensures(s'.storage 0 = newTotal ∧ s'.storage 2 = s.storage 2)
    : Unit := do
    setStorage totalAssets newTotal

  function rotateOwner (newOwner : Address)
    preserves(totalAssets, feeBps, balances, nonces)
    requires_clause(s.sender = s.storageAddr 1)
    ensures_clause(s'.storageAddr 1 = newOwner)
    ensures_clause(s'.storage 0 = s.storage 0)
    : Unit := do
    let sender ← msgSender
    let currentOwner ← getStorageAddr owner
    require (sender == currentOwner) "not owner"
    setStorageAddr owner newOwner

  function creditUser (user : Address, amount : Uint256)
    modifies(balances)
    preserves(totalAssets, owner, feeBps, nonces)
    ensures(s'.storageMap 3 user = amount ∧ s'.storage 0 = s.storage 0)
    : Unit := do
    setMapping balances user amount

  function setFeeBps (newFee : Uint256)
    modifies(feeBps)
    : Unit := do
    setStorage feeBps newFee

  function view getFeeBps ()
    preserves(totalAssets, owner, feeBps, balances, nonces)
    ensures(s' = s)
    : Uint256 := do
    let fee ← getStorage feeBps
    return fee

namespace DeclarativeVaultSmoke

-- 1. Verify auto-generated frame & postcondition theorems exist with expected types
example : bitmaskDisjoint setTotalAssets_writes_mask setTotalAssets_preserves_mask = true :=
  setTotalAssets_footprint_disjoint

example : ∀ (newTotal : Uint256) (s : ContractState),
    setTotalAssets_preserves_spec s ((setTotalAssets newTotal).run s).snd :=
  setTotalAssets_preserves_frame

example : ∀ (newTotal : Uint256) (s : ContractState),
    setTotalAssets_ensures_spec newTotal s ((setTotalAssets newTotal).run s).snd :=
  setTotalAssets_meets_ensures

example : bitmaskDisjoint rotateOwner_writes_mask rotateOwner_preserves_mask = true :=
  rotateOwner_footprint_disjoint

example : ∀ (newOwner : Address) (s : ContractState),
    rotateOwner_preserves_spec s ((rotateOwner newOwner).run s).snd :=
  rotateOwner_preserves_frame

example : ∀ (newOwner : Address) (s : ContractState),
    rotateOwner_ensures_spec newOwner s ((rotateOwner newOwner).run s).snd :=
  rotateOwner_meets_ensures

example : bitmaskDisjoint creditUser_writes_mask creditUser_preserves_mask = true :=
  creditUser_footprint_disjoint

example : ∀ (user : Address) (amount : Uint256) (s : ContractState),
    creditUser_preserves_spec s ((creditUser user amount).run s).snd :=
  creditUser_preserves_frame

example : ∀ (user : Address) (amount : Uint256) (s : ContractState),
    creditUser_ensures_spec user amount s ((creditUser user amount).run s).snd :=
  creditUser_meets_ensures

example : bitmaskDisjoint getFeeBps_writes_mask getFeeBps_preserves_mask = true :=
  getFeeBps_footprint_disjoint

example : ∀ (s : ContractState),
    getFeeBps_preserves_spec s (getFeeBps.run s).snd :=
  getFeeBps_preserves_frame

example : ∀ (s : ContractState),
    getFeeBps_ensures_spec s (getFeeBps.run s).snd :=
  getFeeBps_meets_ensures

-- 2. Verify 1-line `by decide` bitmask disjointness for multi-slot footprints
theorem vault_bitmask_disjoint_by_decide :
    bitmaskDisjoint (slotsToBitmask [0, 3]) (slotsToBitmask [1, 2, 4, 5]) = true := by
  decide

theorem vault_slot_disjoint_by_decide :
    slotBitDisjoint (slotsToBitmask [0, 3]) 2 = true := by
  decide

-- 3. Verify standalone `#gen_auto_frame_spec` on `setFeeBps` mixing typed `StorageSlot` and raw `Nat` slot indices
#gen_auto_frame_spec setFeeBps for (newFee : Uint256)
  modifies [feeBps] preserves [0, 1, 3, 4]

example : bitmaskDisjoint setFeeBps_writes_mask setFeeBps_preserves_mask = true :=
  setFeeBps_footprint_disjoint

example : ∀ (newFee : Uint256) (s : ContractState),
    setFeeBps_preserves_spec s ((setFeeBps newFee).run s).snd :=
  setFeeBps_preserves_frame

-- 4. Verify 1-line `verity_frame_auto` and `verity_auto` on custom obligations
theorem setTotalAssets_custom_frame (newTotal : Uint256) (s : ContractState) :
    let s' := ((setTotalAssets newTotal).run s).snd
    Verity.Specs.sameStorageSlot 2 s s' ∧
    Verity.Specs.sameStorageAddrSlot 1 s s' ∧
    Verity.Specs.sameContext s s' := by
  verity_frame_auto [setTotalAssets, totalAssets]

theorem creditUser_custom_auto (user : Address) (amount : Uint256) (s : ContractState) :
    let s' := ((creditUser user amount).run s).snd
    s'.storageMap 3 user = amount ∧
    s'.storage 0 = s.storage 0 ∧
    s'.storage 2 = s.storage 2 := by
  verity_auto [creditUser, balances]

-- 5. Verify universal `StatementFootprintBound` composition + 1-line `by decide` discharge
theorem setTotalAssets_statement_footprint_bound (newTotal : Uint256) :
    StatementFootprintBound (slotsToBitmask [0]) (setTotalAssets newTotal) := by
  simpa [setTotalAssets, totalAssets, slotsToBitmask] using
    (StatementFootprintBound_setStorage (slotsToBitmask [0]) totalAssets newTotal (by decide))

theorem setTotalAssets_untouched_slot_via_bitmask
    (newTotal : Uint256) (s : ContractState) :
    (((setTotalAssets newTotal).run s).snd).storage 2 = s.storage 2 := by
  exact eval_preserves_untouched_slot_snd_of_bitmask_disjoint
    (setTotalAssets_statement_footprint_bound newTotal) s 2

theorem setTotalAssets_preserved_mask_via_bitmask
    (newTotal : Uint256) (s : ContractState) :
    (((setTotalAssets newTotal).run s).snd).storage 4 = s.storage 4 := by
  exact eval_preserves_preserved_mask_snd_of_bitmask_disjoint
    (preservesMask := slotsToBitmask [1, 2, 3, 4])
    (setTotalAssets_statement_footprint_bound newTotal) s (by decide) 4 (by decide)

theorem setTotalAssets_and_fee_statement_footprint_bound
    (newTotal newFee : Uint256) :
    StatementFootprintBound (slotsToBitmask [0, 2])
      (Verity.bind (setTotalAssets newTotal) (fun _ => setFeeBps newFee)) := by
  refine StatementFootprintBound_bind ?_ (fun _ => ?_)
  · simpa [setTotalAssets, totalAssets, slotsToBitmask] using
      (StatementFootprintBound_setStorage (slotsToBitmask [0, 2]) totalAssets newTotal (by decide))
  · simpa [setFeeBps, feeBps, slotsToBitmask] using
      (StatementFootprintBound_setStorage (slotsToBitmask [0, 2]) feeBps newFee (by decide))

theorem setTotalAssets_and_fee_preserves_slot_1
    (newTotal newFee : Uint256) (s : ContractState) :
    (((Verity.bind (setTotalAssets newTotal) (fun _ => setFeeBps newFee)).run s).snd).storage 1 =
      s.storage 1 := by
  exact eval_preserves_untouched_slot_snd_of_bitmask_disjoint
    (setTotalAssets_and_fee_statement_footprint_bound newTotal newFee) s 1

end DeclarativeVaultSmoke

end Contracts.Smoke.DeclarativeSpecSmoke

/-
  Smoke & soundness checks for Verity 2.0 Safe-by-Construction primitives:
  - `Verity.Core.SafeArith`
  - `Verity.Core.BoundedLoops`
  - `Verity.Macro.Storage` (packed bitfield & ERC-7201 slot collision detection)
-/

import Verity.Core.SafeArith
import Verity.Core.BoundedLoops
import Verity.Macro.Storage

namespace Contracts.Smoke.SafeByConstructionSmoke

open Verity
open Verity.Core.SafeArith
open Verity.Core.BoundedLoops
open Verity.Macro

/-! ## 1. `SafeArith` Smoke Theorems -/

theorem checkedAdd_success_smoke :
    ((checkedAdd 40 2).run defaultState).getValue? = some 42 := by
  decide

theorem checkedAdd_overflow_reverts_smoke :
    ((checkedAdd (Core.Uint256.ofNat Core.MAX_UINT256) 1).run defaultState).isSuccess = false := by
  decide

theorem checkedSub_success_smoke :
    ((checkedSub 50 8).run defaultState).getValue? = some 42 := by
  decide

theorem checkedSub_underflow_reverts_smoke :
    ((checkedSub 3 5).run defaultState).isSuccess = false := by
  decide

theorem checkedMul_success_smoke :
    ((checkedMul 6 7).run defaultState).getValue? = some 42 := by
  decide

theorem checkedMul_overflow_reverts_smoke :
    ((checkedMul (Core.Uint256.ofNat Core.MAX_UINT256) 2).run defaultState).isSuccess = false := by
  decide

theorem checkedDiv_success_smoke :
    ((checkedDiv 84 2).run defaultState).getValue? = some 42 := by
  decide

theorem checkedDiv_zero_reverts_smoke :
    ((checkedDiv 84 0).run defaultState).isSuccess = false := by
  decide

theorem checkedMod_success_smoke :
    ((checkedMod 47 5).run defaultState).getValue? = some 2 := by
  decide

theorem checkedMod_zero_reverts_smoke :
    ((checkedMod 47 0).run defaultState).isSuccess = false := by
  decide

theorem wrapping_ops_smoke :
    ((Core.Uint256.ofNat Core.MAX_UINT256) +% 2 = 1) ∧
    ((0 : Uint256) -% 1 = Core.Uint256.ofNat Core.MAX_UINT256) ∧
    ((6 : Uint256) *% 7 = 42) := by
  decide

theorem narrowChecked_success_smoke :
    ((narrowChecked 8 255).run defaultState).getValue? = some 255 := by
  decide

theorem narrowChecked_overflow_reverts_smoke :
    ((narrowChecked 8 256).run defaultState).isSuccess = false := by
  decide

theorem truncateMask_canonical_smoke (x : Uint256) :
    CanonicalWord 160 (truncateMask 160 x) :=
  truncateMask_canonical (by decide) x

theorem truncateMask_concrete_smoke :
    truncateMask 8 (Core.Uint256.ofNat 0x12ab) = Core.Uint256.ofNat 0xab := by
  decide

/-! ## 2. `BoundedLoops` Smoke Theorems -/

def accumSlot : StorageSlot Uint256 := ⟨0⟩
def guardSlot : StorageSlot Uint256 := ⟨1⟩

def rangeAccumSpec : Contract Uint256 :=
  Verity.bind
    (forEachRange 1 4 (fun i =>
      Verity.bind (getStorage accumSlot) (fun cur =>
        setStorage accumSlot (cur +% Core.Uint256.ofNat i))))
    (fun _ => getStorage accumSlot)

theorem forEachRange_accum_smoke :
    (rangeAccumSpec.run defaultState).getValue? = some 10 := by
  decide

theorem forEachRange_preserves_other_slot_smoke (count : Nat) (s s' : ContractState)
    (hRun :
      (forEachRange 0 count (fun i => setStorage accumSlot (Core.Uint256.ofNat i))).run s =
        .success () s') :
    s'.storage guardSlot.slot = s.storage guardSlot.slot := by
  refine forEachRange_preserves_invariant
    (P := fun st => st.storage guardSlot.slot = s.storage guardSlot.slot) ?_ 0 s s' hRun rfl
  intro i st st' hStep hInv
  simp [setStorage, Contract.run] at hStep
  subst hStep
  simpa [accumSlot, guardSlot] using hInv

def setBitCountSpec (bitmap : Uint256) : Contract Uint256 :=
  Verity.bind
    (forEachSetBit bitmap 8 (fun _ =>
      Verity.bind (getStorage accumSlot) (fun cur =>
        setStorage accumSlot (cur +% 1))))
    (fun _ => getStorage accumSlot)

theorem forEachSetBit_popcount_smoke :
    ((setBitCountSpec (Core.Uint256.ofNat 0b101101)).run defaultState).getValue? = some 4 := by
  decide

theorem binarySearchInterval_smoke :
    ((binarySearchInterval 0 16 5 (fun mid => Verity.pure (decide (11 ≤ mid)))).run
      defaultState).getValue? = some 11 := by
  decide

def boundedWhileCountdownSpec : Contract Uint256 :=
  Verity.bind (setStorage accumSlot 3) (fun _ =>
    Verity.bind
      (boundedWhile 5
        (Verity.bind (getStorage accumSlot) (fun v => Verity.pure (decide (0 < v.val))))
        (Verity.bind (getStorage accumSlot) (fun v => setStorage accumSlot (v -% 1))))
      (fun _ => getStorage accumSlot))

theorem boundedWhile_countdown_smoke :
    (boundedWhileCountdownSpec.run defaultState).getValue? = some 0 := by
  decide

/-! ## 3. Collision-Free Storage Layout & ERC-7201 Smoke Theorems -/

def validPackedAndERC7201Layout : List (String × PackedRange) :=
  [ ("owner", { «slot» := 0, offset := 0, width := 160 })
  , ("paused", { «slot» := 0, offset := 160, width := 8 })
  , ("feeBps", { «slot» := 0, offset := 168, width := 16 })
  , ("erc7201_vault_totalAssets", erc7201SlotRange 0x1000 0)
  , ("erc7201_vault_totalShares", erc7201SlotRange 0x1000 1)
  , ("erc7201_roles_admin", erc7201SlotRange 0x2000 0)
  ]

theorem validPackedAndERC7201Layout_no_conflict :
    firstStorageLayoutConflict validPackedAndERC7201Layout = none := by
  decide

theorem validPackedAndERC7201Layout_pairwise_disjoint :
    validPackedAndERC7201Layout.Pairwise (fun a b => packedRangesOverlap a.2 b.2 = false) :=
  (firstStorageLayoutConflict_eq_none_iff validPackedAndERC7201Layout).mp
    validPackedAndERC7201Layout_no_conflict

def collidingPackedLayout : List (String × PackedRange) :=
  [ ("owner", { «slot» := 0, offset := 0, width := 160 })
  , ("overlappingFlags", { «slot» := 0, offset := 128, width := 64 })
  ]

theorem collidingPackedLayout_detected :
    firstStorageLayoutConflict collidingPackedLayout =
      some ("owner", "overlappingFlags", 0) := by
  decide

def collidingERC7201Layout : List (String × PackedRange) :=
  [ ("nsA_field0", erc7201SlotRange 0x5000 1)
  , ("nsB_alias", erc7201SlotRange 0x5001 0)
  ]

theorem collidingERC7201Layout_detected :
    firstStorageLayoutConflict collidingERC7201Layout =
      some ("nsA_field0", "nsB_alias", 0x5001) := by
  decide

end Contracts.Smoke.SafeByConstructionSmoke

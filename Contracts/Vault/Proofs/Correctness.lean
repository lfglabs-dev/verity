import Contracts.Vault.Proofs.Basic
import Verity.Proofs.Stdlib.Automation

/-!
  Correctness and read-only proofs for the Vault example's view functions.

  `totalAssets`, `totalSupply`, and `balanceOf` are pure view functions that
  read storage but never write it. These proofs establish their functional
  results (meeting the corresponding specs in `Contracts.Vault.Spec`) and that
  they leave the contract state untouched. They previously had no proofs.
-/

namespace Contracts.Vault.Proofs

open Verity
open Contracts.Vault
open Contracts.Vault.Spec

/-! ## totalAssets -/

theorem totalAssets_meets_spec (s : ContractState) :
    let result := ((totalAssets).run s).fst
    totalAssets_spec result s := by
  simp [totalAssets, totalAssets_spec, Contract.run, ContractResult.fst, getStorage,
    Verity.bind, Bind.bind, Verity.pure, Pure.pure, totalAssetsSlot, ContractState.readSlot]

theorem totalAssets_preserves_state (s : ContractState) :
    let s' := ((totalAssets).run s).snd
    s' = s := by
  verity_unfold totalAssets

/-! ## totalSupply -/

theorem totalSupply_meets_spec (s : ContractState) :
    let result := ((totalSupply).run s).fst
    totalSupply_spec result s := by
  simp [totalSupply, totalSupply_spec, Contract.run, ContractResult.fst, getStorage,
    Verity.bind, Bind.bind, Verity.pure, Pure.pure, totalSupplySlot, ContractState.readSlot]

theorem totalSupply_preserves_state (s : ContractState) :
    let s' := ((totalSupply).run s).snd
    s' = s := by
  verity_unfold totalSupply

/-! ## balanceOf -/

theorem balanceOf_meets_spec (s : ContractState) (addr : Address) :
    let result := ((balanceOf addr).run s).fst
    balanceOf_spec addr result s := by
  simp [balanceOf, balanceOf_spec, Contract.run, ContractResult.fst, getMapping,
    Verity.bind, Bind.bind, Verity.pure, Pure.pure, shareBalancesSlot, ContractState.readMap]

theorem balanceOf_preserves_state (s : ContractState) (addr : Address) :
    let s' := ((balanceOf addr).run s).snd
    s' = s := by
  verity_unfold balanceOf

end Contracts.Vault.Proofs

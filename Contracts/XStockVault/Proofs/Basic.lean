import Contracts.XStockVault.Spec

/-!
Baseline proof module for the XStockVault example.

The xStocks-specific proofs live in `Contracts.XStockVault.Proofs.XStocks`.
-/

namespace Contracts.XStockVault.Proofs.Basic

open Verity
open Contracts.XStockVault.Spec

theorem totalAssets_spec_reads_slot_one (result : Uint256) (s : ContractState)
    (h : totalAssets_spec result s) :
    result = s.storage 1 := h

theorem totalSupply_spec_reads_slot_two (result : Uint256) (s : ContractState)
    (h : totalSupply_spec result s) :
    result = s.storage 2 := h

theorem multiplierEpoch_spec_reads_slot_four (result : Uint256) (s : ContractState)
    (h : multiplierEpoch_spec result s) :
    result = s.storage 4 := h

end Contracts.XStockVault.Proofs.Basic

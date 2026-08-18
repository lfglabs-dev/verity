import Contracts.LocalObligationMacroSmoke.Spec
import Contracts.LocalObligationMacroSmoke.Invariants
import Verity.Proofs.Stdlib.Automation

namespace Contracts.LocalObligationMacroSmoke.Proofs

open Verity
open Contracts
open Contracts.LocalObligationMacroSmoke.Spec
open Contracts.LocalObligationMacroSmoke.Invariants

theorem unsafeEdge_preserves_state (s : ContractState) :
  let s' := ((LocalObligationMacroSmoke.unsafeEdge).run s).snd
  unsafeEdge_spec s s' := by
  rfl

theorem dischargedEdge_meets_spec (s : ContractState) (value : Uint256) :
  let output := (LocalObligationMacroSmoke.dischargedEdge value).run s
  dischargedEdge_spec value output.fst s output.snd := by
  unfold LocalObligationMacroSmoke.dischargedEdge
  simp [dischargedEdge_spec, LocalObligationMacroSmoke.lastValue, Verity.Contract.run, Verity.bind, Bind.bind, Verity.setStorage, Verity.pure, Pure.pure, ContractState.writeSlot, ContractState.storage]

theorem dischargedEdge_preserves_slot_zero (s : ContractState) (value : Uint256) :
  let s' := ((LocalObligationMacroSmoke.dischargedEdge value).run s).snd
  slotZeroUnchanged s s' := by
  unfold LocalObligationMacroSmoke.dischargedEdge
  simp [slotZeroUnchanged, LocalObligationMacroSmoke.lastValue, Verity.Contract.run, Verity.bind, Bind.bind, Verity.setStorage, Verity.pure, Pure.pure, ContractState.writeSlot, ContractState.storage]

end Contracts.LocalObligationMacroSmoke.Proofs

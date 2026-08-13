import Verity.Specs.Common
import Verity.Specs.Composition
import Contracts.Ownable.Ownable

namespace Contracts.Ownable.Invariants

open Verity
open Verity.Specs.Composition
open Contracts.Ownable

structure WellFormedState (s : ContractState) : Prop where
  sender_nonzero : s.sender ≠ 0
  contract_nonzero : s.thisAddress ≠ 0
  owner_nonzero : s.storageAddr owner.slot ≠ 0

def Inv (s : ContractState) : Prop :=
  s.storageAddr owner.slot ≠ 0

theorem inv_depends_only_on_footprint :
    InvDependsOnlyOn Inv { addrSlots := [owner.slot] } := by
  intro s s' h
  constructor
  · intro hinv
    have := h.2.1 owner.slot (by simp)
    simpa [Inv, this] using hinv
  · intro hinv
    have := h.2.1 owner.slot (by simp)
    simpa [Inv, this] using hinv

end Contracts.Ownable.Invariants

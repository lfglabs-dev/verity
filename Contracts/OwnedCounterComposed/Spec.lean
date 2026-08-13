import Verity.Specs.Common
import Verity.Specs.Composition
import Verity.Macro
import Contracts.OwnedCounterComposed.OwnedCounterComposed

namespace Contracts.OwnedCounterComposed.Spec

open Verity
open Verity.EVM.Uint256
open Verity.Specs
open Verity.Specs.Composition
open Contracts.OwnedCounterComposed

#gen_spec increment_spec (count.slot, (fun st => add (st.storage count.slot) 1), sameAddrMapContext)
#gen_spec decrement_spec (count.slot, (fun st => sub (st.storage count.slot) 1), sameAddrMapContext)

def getCount_spec (result : Uint256) (s : ContractState) : Prop :=
  result = s.storage count.slot

def countFootprint : Footprint := { uintSlots := [count.slot] }

end Contracts.OwnedCounterComposed.Spec

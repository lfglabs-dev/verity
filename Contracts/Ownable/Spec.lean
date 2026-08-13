import Verity.Specs.Common
import Verity.Specs.Composition
import Verity.Macro
import Contracts.Ownable.Ownable

namespace Contracts.Ownable.Spec

open Verity
open Verity.Specs
open Verity.Specs.Composition
open Contracts.Ownable

#gen_spec_addr constructor_spec for (initialOwner : Address)
  (owner.slot, (fun _ => initialOwner), sameStorageMapContext)

def getOwner_spec (result : Address) (s : ContractState) : Prop :=
  result = s.storageAddr owner.slot

#gen_spec_addr transferOwnership_spec for (newOwner : Address)
  (owner.slot, (fun _ => newOwner), sameStorageMapContext)

def footprint : Footprint := { addrSlots := [owner.slot] }

end Contracts.Ownable.Spec

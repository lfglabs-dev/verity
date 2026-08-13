/-
  Formal specifications for Owned operations.
-/

import Verity.Specs.Common
import Verity.Macro
import Contracts.Owned.Owned

namespace Contracts.Owned.Spec

open Verity
open Verity.Specs
open Contracts.Owned

/-! ## Operation Specifications -/

-- Constructor: sets the owner to the provided address.
#gen_spec_addr constructor_spec for (initialOwner : Address) (owner.slot, (fun _ => initialOwner), sameStorageMapContext)

/-- getOwner: returns the current owner address -/
def getOwner_spec (result : Address) (s : ContractState) : Prop :=
  result = s.storageAddr owner.slot

-- transferOwnership: updates owner to new address (owner only).
#gen_spec_addr transferOwnership_spec for (newOwner : Address) (owner.slot, (fun _ => newOwner), sameStorageMapContext)

/-- isOwner: returns true if sender equals current owner -/
def isOwner_spec (result : Bool) (s : ContractState) : Prop :=
  result = (s.sender == s.storageAddr owner.slot)

end Contracts.Owned.Spec

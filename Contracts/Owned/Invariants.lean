/-
  State invariants for Owned contract.

  Defines properties that should always hold, regardless of operations.
-/

import Verity.Specs.Common
import Contracts.Owned.Owned

namespace Contracts.Owned.Invariants

open Verity
open Contracts.Owned

/-! ## State Invariants

Properties that should be maintained by all operations.
-/

/-- Well-formed contract state:
    - Sender address is nonzero
    - Contract address is nonzero
    - Owner address is nonzero (after construction)
-/
structure WellFormedState (s : ContractState) : Prop where
  sender_nonzero : s.sender ≠ 0
  contract_nonzero : s.thisAddress ≠ 0
  owner_nonzero : s.storageAddr owner.slot ≠ 0

end Contracts.Owned.Invariants

import Contracts.Common

namespace Contracts.Smoke.InheritanceImport

open Contracts
open Verity hiding pure bind

verity_contract ImportedInheritanceBase where
  types
    ImportedAmount : Uint256
  storage
    inheritedValue : Uint256 := slot 0

end Contracts.Smoke.InheritanceImport

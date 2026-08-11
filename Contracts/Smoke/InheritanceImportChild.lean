import Contracts.Smoke.InheritanceImportBase
import Compiler.CheckContract

namespace Contracts.Smoke.InheritanceImport

open Contracts
open Verity hiding pure bind

-- The parent is loaded exclusively from InheritanceImportBase.olean. This
-- fails if inheritance metadata is held in process-local state.
verity_contract ImportedInheritanceChild is ImportedInheritanceBase where
  storage
    childValue : Uint256 := slot 1

  function setImported (next : ImportedAmount) : Unit := do
    setStorage inheritedValue next

#check_contract ImportedInheritanceChild

end Contracts.Smoke.InheritanceImport

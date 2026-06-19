import Contracts.Common

namespace Contracts

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256

verity_contract ProxyUpgradeabilityMacroSmoke where
  storage
    initializedVersion : Uint256 := slot 0
    admin : Address := slot 1
    implementation : Address := slot 2

  function initProxy (seedAdmin : Address, seedImplementation : Address) initializer(initializedVersion)
      local_obligations [implementation_slot_discipline := assumed "Proxy storage-slot discipline must be validated against the intended implementation layout."] : Unit := do
    setStorageAddr admin seedAdmin
    setStorageAddr implementation seedImplementation

  function upgradeTo (newImplementation : Address) reinitializer(initializedVersion, 2)
      local_obligations [upgrade_authorization := assumed "Caller must separately prove that only the intended admin can authorize upgrades.", storage_layout_compatibility := unchecked "Storage-layout compatibility across versions remains a manual proof obligation."] : Unit := do
    setStorageAddr implementation newImplementation

  function reentrancy_trusted forward (gas : Uint256, inOffset : Uint256, inSize : Uint256, outOffset : Uint256, outSize : Uint256)
      local_obligations [delegatecall_refinement := assumed "Delegatecall fallback behavior must be shown to refine the selected proxy semantics."] : Uint256 := do
    let target ← getStorageAddr implementation
    let ok := delegatecall gas (addressToWord target) inOffset inSize outOffset outSize
    return ok

end Contracts

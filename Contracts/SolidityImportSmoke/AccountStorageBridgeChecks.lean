import Verity.Core.Model.AccountStorageBridge

namespace SolidityImportSmoke.AccountStorageBridgeChecks
open Verity.Core

/-- A duplicated physical slot is transformed once from the original word. -/
theorem duplicate_modify_is_atomic :
    let initial := Verity.defaultState.writePhysicalSlot 7 9
    let final := initial.modifyPhysicalSlots [7, 7] (fun word => word + 1)
    (final.readSlot 7, (final.accountWorld final.thisAddress).storageAt 7) = (10, 10) := rfl

theorem batch_delete_updates_both_views :
    let initial := Verity.defaultState.writePhysicalSlot 7 9
    let final := initial.writePhysicalSlots [7, 7] 0
    (final.readSlot 7, (final.accountWorld final.thisAddress).storageAt 7) = (0, 0) := rfl

theorem another_slot_is_framed :
    let initial := (Verity.defaultState.writePhysicalSlot 7 9).writePhysicalSlot 8 42
    let final := initial.modifyPhysicalSlots [7, 7] (fun word => word + 1)
    (final.readSlot 8, (final.accountWorld final.thisAddress).storageAt 8) = (42, 42) := rfl

theorem transient_write_does_not_enter_account_storage :
    let initial := Verity.defaultState.writePhysicalSlot 7 9
    let final := initial.writeTransient 7 99
    (final.readSlot 7, (final.accountWorld final.thisAddress).storageAt 7) = (9, 9) := rfl

theorem inconsistent_code_balance_views_are_not_repaired_by_storage :
    let initial := { Verity.defaultState with selfBalance := 99, codeSize := fun _ => 42 }
    let final := initial.writePhysicalSlot 7 9
    (final.selfBalance, final.codeSize 0, (final.accountWorld final.thisAddress).storageAt 7) =
      (99, 42, 9) := rfl

end SolidityImportSmoke.AccountStorageBridgeChecks

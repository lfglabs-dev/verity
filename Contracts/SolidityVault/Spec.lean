import Contracts.SolidityVault.Contract

namespace Contracts.SolidityVault.Spec
open Verity

/-- Exact post-state, including Verity's ghost key-enumeration metadata. -/
def accountingState (s : ContractState) (shares assets supply : Uint256) : ContractState :=
  let mapped := { s.writeMap Imported.shareBalancesSlot.slot s.sender shares with
    knownAddresses := fun slot => if slot == Imported.shareBalancesSlot.slot then
      (s.knownAddresses slot).insert s.sender else s.knownAddresses slot }
  (mapped.writeSlot Imported.totalAssetsSlot.slot assets).writeSlot Imported.totalSupplySlot.slot supply

def deposit (s : ContractState) (amount : Uint256) : Prop :=
  (Imported.deposit amount).run s = ContractResult.success ()
    (accountingState s (s.readMap Imported.shareBalancesSlot.slot s.sender + amount)
      (s.readSlot Imported.totalAssetsSlot.slot + amount)
      (s.readSlot Imported.totalSupplySlot.slot + amount))

def withdraw (s : ContractState) (amount : Uint256) : Prop :=
  (Imported.withdraw amount).run s = ContractResult.success ()
    (accountingState s (s.readMap Imported.shareBalancesSlot.slot s.sender - amount)
      (s.readSlot Imported.totalAssetsSlot.slot - amount)
      (s.readSlot Imported.totalSupplySlot.slot - amount))

def balance (s : ContractState) (account : Address) : Prop :=
  (Imported.balanceOf account).run s =
    ContractResult.success (s.readMap Imported.shareBalancesSlot.slot account) s

end Contracts.SolidityVault.Spec

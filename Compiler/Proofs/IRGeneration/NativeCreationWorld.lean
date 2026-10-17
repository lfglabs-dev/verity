import Compiler.Proofs.IRGeneration.CreationCaller
import Verity.Core.Model.CreationWorld

/-! Native account views for authenticating a CREATE2 caller boundary.
These are views of the actual native machine, not a synthesized source world.
Account absence, original storage, access sets and raw event-time logs remain
in that machine. Source mapping/channel agreement and event decoding are
separate obligations; this module does not enable any caller opcode. -/
namespace Compiler.Proofs.IRGeneration.NativeCreationWorld
open EvmYul

/-- Preserve absence separately from the zero-valued account view. In
particular, this view must not justify EXTCODEHASH's existence distinction. -/
def account? (machine : EVM.State) (owner : AccountAddress) : Option (Account .EVM) :=
  machine.accountMap.get? owner

def account (machine : EVM.State) (owner : AccountAddress) : Account .EVM :=
  (account? machine owner).getD default

def creationAccount (machine : EVM.State) (owner : AccountAddress) :
    Verity.Core.Model.Create2Accounts.Account :=
  { nonce := (account machine owner).nonce.toNat
    balance := Verity.Core.Uint256.ofNat (account machine owner).balance.toNat
    code := (account machine owner).code }

def persistentWord (machine : EVM.State) (owner : AccountAddress) (slot : UInt256) :
    Verity.Core.Uint256 :=
  Verity.Core.Uint256.ofNat ((account machine owner).storage.getD slot (.ofNat 0)).toNat

def transientWord (machine : EVM.State) (owner : AccountAddress) (slot : UInt256) :
    Verity.Core.Uint256 :=
  Verity.Core.Uint256.ofNat ((account machine owner).tstorage.getD slot (.ofNat 0)).toNat

def accountWarm (machine : EVM.State) (owner : AccountAddress) : Bool :=
  machine.substate.accessedAccounts.contains owner

/-- The original transaction storage is distinct from the current map: SSTORE
metering must consult this even after earlier writes in the same transaction. -/
def originalPersistentWord (machine : EVM.State) (owner : AccountAddress) (slot : UInt256) :
    Verity.Core.Uint256 :=
  let original := (machine.σ₀.get? owner).getD default
  Verity.Core.Uint256.ofNat (original.storage.getD slot (.ofNat 0)).toNat

def storageWarm (machine : EVM.State) (owner : AccountAddress) (slot : UInt256) : Bool :=
  machine.substate.accessedStorageKeys.contains (owner, slot)

/-- Raw native logs retain their event-time payload, rather than being decoded
from the final mutable memory. No source event agreement is asserted here. -/
def rawLogs (machine : EVM.State) : LogSeries := machine.substate.logSeries

/-- Raw boundary agreement. It intentionally does not claim agreement of
source mapping/array channels, decoded events, or entire function execution.
Those must be established before this can authenticate an imported function. -/
structure Agreement (world : Verity.ContractState) (machine : EVM.State)
    (warm : Verity.Core.Model.Create2Access.WarmAccounts) : Prop where
  caller : world.thisAddress.val = machine.executionEnv.codeOwner.val
  source : world.sender.val = machine.executionEnv.source.val
  origin : world.txOrigin.val = machine.executionEnv.sender.val
  value : world.msgValue = Verity.Core.Uint256.ofNat machine.executionEnv.weiValue.toNat
  accounts : ∀ (owner : AccountAddress), world.creationAccounts owner.val = creationAccount machine owner
  selfBalance : world.selfBalance = (creationAccount machine machine.executionEnv.codeOwner).balance
  codeSizes : ∀ (owner : AccountAddress), world.codeSize owner.val =
    Verity.Core.Uint256.ofNat (account machine owner).code.size
  persistent : ∀ (slot : UInt256), world.readSlot slot.toNat =
    persistentWord machine machine.executionEnv.codeOwner slot
  transient : ∀ (slot : UInt256), world.transientStorage slot.toNat =
    transientWord machine machine.executionEnv.codeOwner slot
  parkedPersistent : ∀ (owner : AccountAddress), owner ≠ machine.executionEnv.codeOwner → ∀ (slot : UInt256),
    world.storageWords (.contractSlot owner.val slot.toNat) = persistentWord machine owner slot
  parkedTransient : ∀ (owner : AccountAddress), owner ≠ machine.executionEnv.codeOwner → ∀ (slot : UInt256),
    world.storageWords (.scoped owner.val (.transient slot.toNat)) = transientWord machine owner slot
  accountAccess : ∀ (owner : AccountAddress), warm owner.val = accountWarm machine owner

/-- Changing local gas/stack/PC/memory cannot establish or destroy account
agreement: account world, original map, substate and environment are retained. -/
theorem account?_local (machine : EVM.State) (owner : AccountAddress)
    (gas pc : UInt256) (stack : Stack UInt256) (memory : ByteArray) :
    account? { machine with gasAvailable := gas, pc := pc, stack := stack, memory := memory } owner =
      account? machine owner := rfl

theorem persistentWord_local (machine : EVM.State) (owner : AccountAddress) (slot : UInt256)
    (gas pc : UInt256) (stack : Stack UInt256) (memory : ByteArray) :
    persistentWord { machine with gasAvailable := gas, pc := pc, stack := stack, memory := memory } owner slot =
      persistentWord machine owner slot := rfl

theorem transientWord_local (machine : EVM.State) (owner : AccountAddress) (slot : UInt256)
    (gas pc : UInt256) (stack : Stack UInt256) (memory : ByteArray) :
    transientWord { machine with gasAvailable := gas, pc := pc, stack := stack, memory := memory } owner slot =
      transientWord machine owner slot := rfl

theorem originalPersistentWord_local (machine : EVM.State) (owner : AccountAddress) (slot : UInt256)
    (gas pc : UInt256) (stack : Stack UInt256) (memory : ByteArray) :
    originalPersistentWord { machine with gasAvailable := gas, pc := pc, stack := stack, memory := memory } owner slot =
      originalPersistentWord machine owner slot := rfl

theorem storageWarm_local (machine : EVM.State) (owner : AccountAddress) (slot : UInt256)
    (gas pc : UInt256) (stack : Stack UInt256) (memory : ByteArray) :
    storageWarm { machine with gasAvailable := gas, pc := pc, stack := stack, memory := memory } owner slot =
      storageWarm machine owner slot := rfl

theorem rawLogs_local (machine : EVM.State)
    (gas pc : UInt256) (stack : Stack UInt256) (memory : ByteArray) :
    rawLogs { machine with gasAvailable := gas, pc := pc, stack := stack, memory := memory } =
      rawLogs machine := rfl

theorem agreement_local (world : Verity.ContractState) (machine : EVM.State)
    (warm : Verity.Core.Model.Create2Access.WarmAccounts)
    (agrees : Agreement world machine warm)
    (gas pc : UInt256) (stack : Stack UInt256) (memory : ByteArray) :
    Agreement world { machine with gasAvailable := gas, pc := pc, stack := stack, memory := memory } warm :=
  { caller := agrees.caller
    source := agrees.source
    origin := agrees.origin
    value := agrees.value
    accounts := agrees.accounts
    selfBalance := agrees.selfBalance
    codeSizes := agrees.codeSizes
    persistent := agrees.persistent
    transient := agrees.transient
    parkedPersistent := agrees.parkedPersistent
    parkedTransient := agrees.parkedTransient
    accountAccess := agrees.accountAccess }

end Compiler.Proofs.IRGeneration.NativeCreationWorld

import Compiler.Proofs.IRGeneration.NativeCreationFlatStorage

/-! Preserve self-slot agreement through actual native storage primitives.
These are not checked-opcode/whole-function or source hashed-channel theorems. -/
namespace Compiler.Proofs.IRGeneration.NativeCreationStorageAgreement
open EvmYul NativeCreationWorld NativeCreationWorldWrites NativeCreationFlatStorage

/-- The EVM machine lift changes exactly the native State component. -/
theorem self_account_sstore (machine : EVM.State) (entry : Account .EVM)
    (present : machine.toState.lookupAccount machine.executionEnv.codeOwner = some entry)
    (slot value : UInt256) :
    account { machine with toState := machine.toState.sstore slot value }
      machine.executionEnv.codeOwner = entry.updateStorage slot value := by
  change ((machine.toState.sstore slot value).lookupAccount
    machine.executionEnv.codeOwner).getD Inhabited.default = _
  rw [sstore_self_account machine.toState slot value entry present]
  rfl

theorem self_account_tstore (machine : EVM.State) (entry : Account .EVM)
    (present : machine.toState.lookupAccount machine.executionEnv.codeOwner = some entry)
    (slot value : UInt256) :
    account { machine with toState := machine.toState.tstore slot value }
      machine.executionEnv.codeOwner = entry.updateTransientStorage slot value := by
  change ((machine.toState.tstore slot value).lookupAccount
    machine.executionEnv.codeOwner).getD Inhabited.default = _
  rw [tstore_self_account machine.toState slot value entry present]
  rfl

/-- Persistent Agreement field preserved by actual SSTORE state effects.
The opcode's gas/static/stack prechecks remain separate obligations. -/
theorem persistent_sstore_agreement (world : Verity.ContractState) (machine : EVM.State)
    (entry : Account .EVM)
    (present : machine.toState.lookupAccount machine.executionEnv.codeOwner = some entry)
    (agrees : ∀ key : UInt256, world.readSlot key.toNat =
      persistentWord machine machine.executionEnv.codeOwner key)
    (slot value : UInt256) :
    ∀ key : UInt256,
      (world.writeSlot slot.toNat (Verity.Core.Uint256.ofNat value.toNat)).readSlot key.toNat =
      persistentWord { machine with toState := machine.toState.sstore slot value }
        machine.executionEnv.codeOwner key := by
  have account_before : account machine machine.executionEnv.codeOwner = entry := by
    change (machine.toState.lookupAccount machine.executionEnv.codeOwner).getD Inhabited.default = _
    rw [present]
    rfl
  have before : ∀ key : UInt256, world.readSlot key.toNat =
      Verity.Core.Uint256.ofNat (entry.lookupStorage key).toNat := by
    intro key
    have h := agrees key
    unfold persistentWord at h
    rw [account_before] at h
    exact h
  intro key
  unfold persistentWord
  rw [self_account_sstore machine entry present slot value]
  exact persistent_write world entry before slot value key

/-- Transient Agreement field preserved by actual TSTORE state effects. -/
theorem transient_tstore_agreement (world : Verity.ContractState) (machine : EVM.State)
    (entry : Account .EVM)
    (present : machine.toState.lookupAccount machine.executionEnv.codeOwner = some entry)
    (agrees : ∀ key : UInt256, world.transientStorage key.toNat =
      transientWord machine machine.executionEnv.codeOwner key)
    (slot value : UInt256) :
    ∀ key : UInt256,
      (world.writeTransient slot.toNat (Verity.Core.Uint256.ofNat value.toNat)).transientStorage key.toNat =
      transientWord { machine with toState := machine.toState.tstore slot value }
        machine.executionEnv.codeOwner key := by
  have account_before : account machine machine.executionEnv.codeOwner = entry := by
    change (machine.toState.lookupAccount machine.executionEnv.codeOwner).getD Inhabited.default = _
    rw [present]
    rfl
  have before : ∀ key : UInt256, world.transientStorage key.toNat =
      Verity.Core.Uint256.ofNat (entry.lookupTransientStorage key).toNat := by
    intro key
    have h := agrees key
    unfold transientWord at h
    rw [account_before] at h
    exact h
  intro key
  unfold transientWord
  rw [self_account_tstore machine entry present slot value]
  exact transient_write world entry before slot value key

/-- Storage writes preserve the existence and complete state of foreign accounts. -/
theorem foreign_account_sstore (machine : EVM.State) (entry : Account .EVM)
    (present : machine.toState.lookupAccount machine.executionEnv.codeOwner = some entry)
    (owner : AccountAddress) (different : owner ≠ machine.executionEnv.codeOwner)
    (slot value : UInt256) :
    account? { machine with toState := machine.toState.sstore slot value } owner =
      account? machine owner := by
  unfold account?
  change (machine.toState.sstore slot value).accountMap[owner]? = machine.accountMap[owner]?
  rw [NativeCreationWorldSteps.sstore_account machine.toState slot value entry present,
    Std.TreeMap.getElem?_insert]
  have distinct : compare machine.executionEnv.codeOwner owner ≠ Ordering.eq := by
    intro equal
    exact different (Std.LawfulEqOrd.eq_of_compare equal).symm
  rw [if_neg distinct]

/-- Transient writes also leave foreign accounts entirely unchanged. -/
theorem foreign_account_tstore (machine : EVM.State) (entry : Account .EVM)
    (present : machine.toState.lookupAccount machine.executionEnv.codeOwner = some entry)
    (owner : AccountAddress) (different : owner ≠ machine.executionEnv.codeOwner)
    (slot value : UInt256) :
    account? { machine with toState := machine.toState.tstore slot value } owner =
      account? machine owner := by
  unfold account?
  change (machine.toState.tstore slot value).accountMap[owner]? = machine.accountMap[owner]?
  rw [NativeCreationWorldSteps.tstore_account machine.toState slot value entry present,
    Std.TreeMap.getElem?_insert]
  have distinct : compare machine.executionEnv.codeOwner owner ≠ Ordering.eq := by
    intro equal
    exact different (Std.LawfulEqOrd.eq_of_compare equal).symm
  rw [if_neg distinct]

private theorem self_account_before (machine : EVM.State) (entry : Account .EVM)
    (present : machine.toState.lookupAccount machine.executionEnv.codeOwner = some entry) :
    account machine machine.executionEnv.codeOwner = entry := by
  change (machine.toState.lookupAccount machine.executionEnv.codeOwner).getD Inhabited.default = _
  rw [present]
  rfl

/-- Native SSTORE leaves nonce, balance and code intact for every account. -/
theorem creationAccount_sstore (machine : EVM.State) (entry : Account .EVM)
    (present : machine.toState.lookupAccount machine.executionEnv.codeOwner = some entry)
    (slot value : UInt256) (owner : AccountAddress) :
    creationAccount { machine with toState := machine.toState.sstore slot value } owner =
      creationAccount machine owner := by
  by_cases same : owner = machine.executionEnv.codeOwner
  · subst owner
    unfold creationAccount
    rw [self_account_sstore machine entry present slot value,
      self_account_before machine entry present]
    unfold Account.updateStorage
    split <;> rfl
  · have unchanged : account { machine with toState := machine.toState.sstore slot value } owner =
        account machine owner := by
      unfold account
      rw [foreign_account_sstore machine entry present owner same slot value]
    simp only [creationAccount, unchanged]

/-- Native TSTORE leaves nonce, balance and code intact for every account. -/
theorem creationAccount_tstore (machine : EVM.State) (entry : Account .EVM)
    (present : machine.toState.lookupAccount machine.executionEnv.codeOwner = some entry)
    (slot value : UInt256) (owner : AccountAddress) :
    creationAccount { machine with toState := machine.toState.tstore slot value } owner =
      creationAccount machine owner := by
  by_cases same : owner = machine.executionEnv.codeOwner
  · subst owner
    unfold creationAccount
    rw [self_account_tstore machine entry present slot value,
      self_account_before machine entry present]
    unfold Account.updateTransientStorage
    split <;> rfl
  · have unchanged : account { machine with toState := machine.toState.tstore slot value } owner =
        account machine owner := by
      unfold account
      rw [foreign_account_tstore machine entry present owner same slot value]
    simp only [creationAccount, unchanged]

/-- Persistent writes leave the entire native transient channel intact. -/
theorem transientWord_sstore (machine : EVM.State) (entry : Account .EVM)
    (present : machine.toState.lookupAccount machine.executionEnv.codeOwner = some entry)
    (slot value key : UInt256) (owner : AccountAddress) :
    transientWord { machine with toState := machine.toState.sstore slot value } owner key =
      transientWord machine owner key := by
  by_cases same : owner = machine.executionEnv.codeOwner
  · subst owner
    unfold transientWord
    rw [self_account_sstore machine entry present slot value,
      self_account_before machine entry present]
    unfold Account.updateStorage
    split <;> rfl
  · have unchanged : account { machine with toState := machine.toState.sstore slot value } owner =
        account machine owner := by
      unfold account
      rw [foreign_account_sstore machine entry present owner same slot value]
    simp only [transientWord, unchanged]

/-- Transient writes leave the entire native persistent channel intact. -/
theorem persistentWord_tstore (machine : EVM.State) (entry : Account .EVM)
    (present : machine.toState.lookupAccount machine.executionEnv.codeOwner = some entry)
    (slot value key : UInt256) (owner : AccountAddress) :
    persistentWord { machine with toState := machine.toState.tstore slot value } owner key =
      persistentWord machine owner key := by
  by_cases same : owner = machine.executionEnv.codeOwner
  · subst owner
    unfold persistentWord
    rw [self_account_tstore machine entry present slot value,
      self_account_before machine entry present]
    unfold Account.updateTransientStorage
    split <;> rfl
  · have unchanged : account { machine with toState := machine.toState.tstore slot value } owner =
        account machine owner := by
      unfold account
      rw [foreign_account_tstore machine entry present owner same slot value]
    simp only [persistentWord, unchanged]

private theorem account_access_sstore (machine : EVM.State)
    (warm : Verity.Core.Model.Create2Access.WarmAccounts)
    (agrees : ∀ owner : AccountAddress, warm owner.val = accountWarm machine owner)
    (slot value : UInt256) :
    ∀ owner : AccountAddress, warm owner.val =
      accountWarm { machine with toState := machine.toState.sstore slot value } owner := by
  intro owner
  change warm owner.val = (machine.toState.sstore slot value).substate.accessedAccounts.contains owner
  rw [(NativeCreationWorldSteps.sstore_frame machine.toState slot value).2.2.2]
  exact agrees owner

/-- Preserve every field of the raw boundary relation through actual SSTORE
state effects. The relation still intentionally excludes source hashed channels,
refund adequacy, event decoding and whole checked-opcode execution. -/
private theorem codeSizes_sstore (world : Verity.ContractState) (machine : EVM.State)
    (warm : Verity.Core.Model.Create2Access.WarmAccounts) (entry : Account .EVM)
    (present : machine.toState.lookupAccount machine.executionEnv.codeOwner = some entry)
    (agrees : Agreement world machine warm) (slot value : UInt256) :
    ∀ owner : AccountAddress, world.codeSize owner.val =
      Verity.Core.Uint256.ofNat (account { machine with toState := machine.toState.sstore slot value } owner).code.size := by
  intro owner
  have code := congrArg (fun a : Verity.Core.Model.Create2Accounts.Account => a.code)
    (creationAccount_sstore machine entry present slot value owner)
  change (account { machine with toState := machine.toState.sstore slot value } owner).code =
    (account machine owner).code at code
  change world.codeSize owner.val = _
  rw [code]
  exact agrees.codeSizes owner

private theorem parked_persistent_sstore (world : Verity.ContractState) (machine : EVM.State)
    (warm : Verity.Core.Model.Create2Access.WarmAccounts) (entry : Account .EVM)
    (present : machine.toState.lookupAccount machine.executionEnv.codeOwner = some entry)
    (agrees : Agreement world machine warm) (slot value : UInt256) :
    ∀ (owner : AccountAddress), owner ≠ (machine.toState.sstore slot value).executionEnv.codeOwner →
      ∀ key : UInt256,
      (world.writeSlot slot.toNat (Verity.Core.Uint256.ofNat value.toNat)).storageWords
        (.contractSlot owner.val key.toNat) =
      persistentWord { machine with toState := machine.toState.sstore slot value } owner key := by
  have environment := (NativeCreationWorldSteps.sstore_frame machine.toState slot value).2.1
  intro owner different key
  change owner ≠ (machine.toState.sstore slot value).executionEnv.codeOwner at different
  rw [environment] at different
  have foreign := foreign_account_sstore machine entry present owner different slot value
  change _ = Verity.Core.Uint256.ofNat
    ((((account? { machine with toState := machine.toState.sstore slot value } owner).getD
      Inhabited.default).storage.getD key (.ofNat 0)).toNat)
  rw [foreign]
  simpa [Verity.ContractState.writeSlot, persistentWord, account] using
    agrees.parkedPersistent owner different key

private theorem transient_frame_sstore (world : Verity.ContractState) (machine : EVM.State)
    (warm : Verity.Core.Model.Create2Access.WarmAccounts) (entry : Account .EVM)
    (present : machine.toState.lookupAccount machine.executionEnv.codeOwner = some entry)
    (agrees : Agreement world machine warm) (slot value : UInt256) :
    ∀ key : UInt256,
      (world.writeSlot slot.toNat (Verity.Core.Uint256.ofNat value.toNat)).transientStorage key.toNat =
      transientWord { machine with toState := machine.toState.sstore slot value }
        (machine.toState.sstore slot value).executionEnv.codeOwner key := by
  have environment := (NativeCreationWorldSteps.sstore_frame machine.toState slot value).2.1
  intro key
  change _ = transientWord { machine with toState := machine.toState.sstore slot value }
    (machine.toState.sstore slot value).executionEnv.codeOwner key
  rw [environment, transientWord_sstore machine entry present slot value key]
  simpa [Verity.ContractState.transientStorage, Verity.ContractState.writeSlot] using agrees.transient key

theorem agreement_sstore (world : Verity.ContractState) (machine : EVM.State)
    (warm : Verity.Core.Model.Create2Access.WarmAccounts) (entry : Account .EVM)
    (present : machine.toState.lookupAccount machine.executionEnv.codeOwner = some entry)
    (agrees : Agreement world machine warm) (slot value : UInt256) :
    Agreement (world.writeSlot slot.toNat (Verity.Core.Uint256.ofNat value.toNat))
      { machine with toState := machine.toState.sstore slot value } warm := by
  have environment := (NativeCreationWorldSteps.sstore_frame machine.toState slot value).2.1
  constructor
  · change world.thisAddress.val = (machine.toState.sstore slot value).executionEnv.codeOwner.val
    rw [environment]
    exact agrees.caller
  · change world.sender.val = (machine.toState.sstore slot value).executionEnv.source.val
    rw [environment]
    exact agrees.source
  · change world.txOrigin.val = (machine.toState.sstore slot value).executionEnv.sender.val
    rw [environment]
    exact agrees.origin
  · change world.msgValue = Verity.Core.Uint256.ofNat
      (machine.toState.sstore slot value).executionEnv.weiValue.toNat
    rw [environment]
    exact agrees.value
  · intro owner
    rw [creationAccount_sstore machine entry present slot value owner]
    exact agrees.accounts owner
  · change world.selfBalance =
      (creationAccount { machine with toState := machine.toState.sstore slot value }
        (machine.toState.sstore slot value).executionEnv.codeOwner).balance
    rw [environment, creationAccount_sstore machine entry present slot value]
    exact agrees.selfBalance
  · exact codeSizes_sstore world machine warm entry present agrees slot value
  · intro key
    change _ = persistentWord { machine with toState := machine.toState.sstore slot value }
      (machine.toState.sstore slot value).executionEnv.codeOwner key
    rw [environment]
    exact persistent_sstore_agreement world machine entry present agrees.persistent slot value key
  · exact transient_frame_sstore world machine warm entry present agrees slot value
  · exact parked_persistent_sstore world machine warm entry present agrees slot value
  · intro owner different key
    change owner ≠ (machine.toState.sstore slot value).executionEnv.codeOwner at different
    rw [environment] at different
    rw [transientWord_sstore machine entry present slot value key owner]
    simpa [Verity.ContractState.writeSlot] using agrees.parkedTransient owner different key
  · exact account_access_sstore machine warm agrees.accountAccess slot value

/-- Preserve every field of the raw boundary relation through actual TSTORE
state effects. The relation still intentionally excludes source hashed channels,
refund adequacy, event decoding and whole checked-opcode execution. -/
private theorem codeSizes_tstore (world : Verity.ContractState) (machine : EVM.State)
    (warm : Verity.Core.Model.Create2Access.WarmAccounts) (entry : Account .EVM)
    (present : machine.toState.lookupAccount machine.executionEnv.codeOwner = some entry)
    (agrees : Agreement world machine warm) (slot value : UInt256) :
    ∀ owner : AccountAddress, world.codeSize owner.val =
      Verity.Core.Uint256.ofNat (account { machine with toState := machine.toState.tstore slot value } owner).code.size := by
  intro owner
  have code := congrArg (fun a : Verity.Core.Model.Create2Accounts.Account => a.code)
    (creationAccount_tstore machine entry present slot value owner)
  change (account { machine with toState := machine.toState.tstore slot value } owner).code =
    (account machine owner).code at code
  change world.codeSize owner.val = _
  rw [code]
  exact agrees.codeSizes owner

private theorem parked_persistent_tstore (world : Verity.ContractState) (machine : EVM.State)
    (warm : Verity.Core.Model.Create2Access.WarmAccounts) (entry : Account .EVM)
    (present : machine.toState.lookupAccount machine.executionEnv.codeOwner = some entry)
    (agrees : Agreement world machine warm) (slot value : UInt256) :
    ∀ (owner : AccountAddress), owner ≠ (machine.toState.tstore slot value).executionEnv.codeOwner →
      ∀ key : UInt256,
      (world.writeTransient slot.toNat (Verity.Core.Uint256.ofNat value.toNat)).storageWords
        (.contractSlot owner.val key.toNat) =
      persistentWord { machine with toState := machine.toState.tstore slot value } owner key := by
  have environment := (NativeCreationWorldSteps.tstore_frame machine.toState slot value).2.1
  intro owner different key
  change owner ≠ (machine.toState.tstore slot value).executionEnv.codeOwner at different
  rw [environment] at different
  have foreign := foreign_account_tstore machine entry present owner different slot value
  change _ = Verity.Core.Uint256.ofNat
    ((((account? { machine with toState := machine.toState.tstore slot value } owner).getD
      Inhabited.default).storage.getD key (.ofNat 0)).toNat)
  rw [foreign]
  simpa [Verity.ContractState.writeTransient, persistentWord, account] using
    agrees.parkedPersistent owner different key

private theorem parked_transient_tstore (world : Verity.ContractState) (machine : EVM.State)
    (warm : Verity.Core.Model.Create2Access.WarmAccounts) (entry : Account .EVM)
    (present : machine.toState.lookupAccount machine.executionEnv.codeOwner = some entry)
    (agrees : Agreement world machine warm) (slot value : UInt256) :
    ∀ (owner : AccountAddress), owner ≠ (machine.toState.tstore slot value).executionEnv.codeOwner →
      ∀ key : UInt256,
      (world.writeTransient slot.toNat (Verity.Core.Uint256.ofNat value.toNat)).storageWords
        (.scoped owner.val (.transient key.toNat)) =
      transientWord { machine with toState := machine.toState.tstore slot value } owner key := by
  have environment := (NativeCreationWorldSteps.tstore_frame machine.toState slot value).2.1
  intro owner different key
  change owner ≠ (machine.toState.tstore slot value).executionEnv.codeOwner at different
  rw [environment] at different
  have foreign := foreign_account_tstore machine entry present owner different slot value
  unfold transientWord account
  rw [foreign]
  simpa [Verity.ContractState.writeTransient, transientWord, account] using
    agrees.parkedTransient owner different key

theorem agreement_tstore (world : Verity.ContractState) (machine : EVM.State)
    (warm : Verity.Core.Model.Create2Access.WarmAccounts) (entry : Account .EVM)
    (present : machine.toState.lookupAccount machine.executionEnv.codeOwner = some entry)
    (agrees : Agreement world machine warm) (slot value : UInt256) :
    Agreement (world.writeTransient slot.toNat (Verity.Core.Uint256.ofNat value.toNat))
      { machine with toState := machine.toState.tstore slot value } warm := by
  have environment := (NativeCreationWorldSteps.tstore_frame machine.toState slot value).2.1
  have access := (NativeCreationWorldSteps.tstore_frame machine.toState slot value).2.2
  constructor
  · change world.thisAddress.val = (machine.toState.tstore slot value).executionEnv.codeOwner.val
    rw [environment]
    exact agrees.caller
  · change world.sender.val = (machine.toState.tstore slot value).executionEnv.source.val
    rw [environment]
    exact agrees.source
  · change world.txOrigin.val = (machine.toState.tstore slot value).executionEnv.sender.val
    rw [environment]
    exact agrees.origin
  · change world.msgValue = Verity.Core.Uint256.ofNat
      (machine.toState.tstore slot value).executionEnv.weiValue.toNat
    rw [environment]
    exact agrees.value
  · intro owner
    rw [creationAccount_tstore machine entry present slot value owner]
    exact agrees.accounts owner
  · change world.selfBalance =
      (creationAccount { machine with toState := machine.toState.tstore slot value }
        (machine.toState.tstore slot value).executionEnv.codeOwner).balance
    rw [environment, creationAccount_tstore machine entry present slot value]
    exact agrees.selfBalance
  · exact codeSizes_tstore world machine warm entry present agrees slot value
  · intro key
    change _ = persistentWord { machine with toState := machine.toState.tstore slot value }
      (machine.toState.tstore slot value).executionEnv.codeOwner key
    rw [environment]
    rw [persistentWord_tstore machine entry present slot value key]
    simpa [Verity.ContractState.readSlot, Verity.ContractState.storage,
      Verity.ContractState.writeTransient] using agrees.persistent key
  · intro key
    change _ = transientWord { machine with toState := machine.toState.tstore slot value }
      (machine.toState.tstore slot value).executionEnv.codeOwner key
    rw [environment]
    exact transient_tstore_agreement world machine entry present agrees.transient slot value key
  · exact parked_persistent_tstore world machine warm entry present agrees slot value
  · exact parked_transient_tstore world machine warm entry present agrees slot value
  · intro owner
    change warm owner.val = (machine.toState.tstore slot value).substate.accessedAccounts.contains owner
    rw [access]
    exact agrees.accountAccess owner

end Compiler.Proofs.IRGeneration.NativeCreationStorageAgreement

import Compiler.Proofs.IRGeneration.NativeCallerAllocationSteps

namespace Verity.Core.Model.Create2Operation
open Verity Create2Entry Create2Callee

/-- The actual complete supported constructor decodes to every payload byte. -/
theorem decode_initcode (payload : ByteArray) : decode (MidnightInitcode.initcode payload) = .ok payload := by
  have suffix : (MidnightInitcode.initcode payload).data.extract MidnightInitcode.header.size
      (MidnightInitcode.initcode payload).size = payload.data := by
    change (MidnightInitcode.header.data ++ payload.data).extract MidnightInitcode.header.data.size
      (MidnightInitcode.header.data ++ payload.data).size = payload.data
    rw [Array.size_append, Array.extract_append_right, Array.extract_size]
  unfold decode
  rw [suffix]
  dsimp only
  exact if_pos rfl

/-- Canonical entry really decodes the complete native supported initcode. -/
theorem enterCode_initcode (accounts : Create2Accounts.Accounts) (creator target : Nat)
    (payload : ByteArray) (gas : Nat) (reserved : Create2Accounts.Accounts)
    (legal : (accounts creator).nonce < Create2NonceEntry.maxCreatorNonce)
    (reservation : Create2Accounts.reserve accounts creator target = .reserved reserved) :
    enterCode accounts creator target (MidnightInitcode.initcode payload) gas =
      runEntered accounts creator target payload gas :=
  enterCode_reserved accounts creator target _ payload gas legal reserved reservation (decode_initcode payload)

/-- Compose actual canonical preparation, child execution and storage commit.
Every intermediate is the result of the existing operation, not an oracle. -/
theorem run_forwarded (before : Frame) (offset size salt : Uint256) (child : Forwarded)
    (result : EnteredResult) (committed : ContractState)
    (prepared : prepare before.world.byteMemory before.context offset.val size.val = .ok (.forwarded child))
    (legal : (before.world.creationAccounts before.world.thisAddress.val).nonce < Create2NonceEntry.maxCreatorNonce)
    (entered : let world := before.world.installPhysicalMemory child.memory
      enterCode world.creationAccounts world.thisAddress.val
        (Create2.create2AddressFromPhysicalMemory world offset size salt world.thisAddress).val
        (Create2.physicalInitcodeBytes world offset.val size.val) child.childGas = .ok result)
    (commit : CreationStorage.commit (before.world.installPhysicalMemory child.memory) result.outcome = .ok committed) :
    run before offset size salt = .ok (.continued (outcomeValue result.outcome)
      { world := committed, context := { before.context with gas := completeGas child result.gasLeft }
        warm := Create2Access.warm before.warm
          (Create2.create2AddressFromPhysicalMemory (before.world.installPhysicalMemory child.memory)
            offset size salt before.world.thisAddress).val }) := by
  have invalid : ¬ Create2NonceEntry.maxCreatorNonce <
      (before.world.creationAccounts before.world.thisAddress.val).nonce := by omega
  have notFull : (before.world.creationAccounts before.world.thisAddress.val).nonce ≠
      Create2NonceEntry.maxCreatorNonce := Nat.ne_of_lt legal
  simp only [run, prepared]
  change (if Create2NonceEntry.maxCreatorNonce <
    (before.world.creationAccounts before.world.thisAddress.val).nonce then _ else _) = _
  rw [if_neg invalid]
  have notFullInstalled : ((before.world.installPhysicalMemory child.memory).creationAccounts
      (before.world.installPhysicalMemory child.memory).thisAddress.val).nonce ≠
      Create2NonceEntry.maxCreatorNonce := notFull
  rw [if_neg notFullInstalled]
  rw [entered]
  dsimp only [Bind.bind, Except.bind]
  rw [commit]
  rfl

end Verity.Core.Model.Create2Operation

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul NativeCreationWorld
open Verity.Core.Model

private theorem native_executed_flag_accepted (payload : ByteArray) (bounded : payload.size ≤ 49152)
    (gas remaining : Nat) (flag : Bool)
    (executed : Create2Callee.execute payload gas = .ok
      { result := if flag then .returned payload true else .exceptional, gasLeft := remaining })
    (yes : flag = true) : Create2Runtime.runtimeAccepted payload = true := by
  have large : 49163 < MidnightInitcode.modulus := by decide
  have nowrap : 11 + payload.size < MidnightInitcode.modulus := by omega
  rw [yes, Create2Callee.execute_formula payload nowrap gas] at executed
  split at executed
  · next funded => exact (Bool.and_eq_true_iff.mp funded).1
  · cases executed

/-- The actual native CREATE2 child determines canonical execution status and
gas. The child result is fixed by its real invocation, not chosen independently. -/
theorem native_create2_child_execution (payload : ByteArray) (bounded : payload.size ≤ 49152)
    (pre : EVM.State) (cost : Nat) (offset size salt : UInt256)
    (code : pre.memory.readWithPadding offset.toNat size.toNat = MidnightInitcode.initcode payload)
    (vacant : let target := nativeCreate2Target pre.executionEnv.codeOwner salt.toByteArray (MidnightInitcode.initcode payload)
      ((create2ChildEntry pre cost).accountMap.getD target default).nonce = UInt256.ofNat 0 ∧
      ((create2ChildEntry pre cost).accountMap.getD target default).code.size = 0)
    (fuel : Nat) (enough : 10 ≤ fuel)
    (result : AccountAddress × Std.TreeSet AccountAddress compare × AccountMap .EVM ×
      UInt256 × Substate × Bool × ByteArray)
    (completed : nativeCreate2Child (fuel + 2) cost pre offset size salt = .ok result) :
    Create2Callee.execute payload (EVM.L (pre.gasAvailable - UInt256.ofNat cost).toNat) = .ok
      { result := if result.2.2.2.2.2.1 then .returned payload true else .exceptional
        gasLeft := result.2.2.2.1.toNat } := by
  let machine := create2ChildEntry pre cost
  let gas := UInt256.ofNat (EVM.L (pre.gasAvailable - UInt256.ofNat cost).toNat)
  obtain ⟨child, native, executed, _⟩ := lambda_canonical_callee payload bounded
    machine.executionEnv.blobVersionedHashes machine.createdAccounts machine.genesisBlockHeader machine.blocks
    machine.accountMap machine.σ₀ machine.substate pre.executionEnv.codeOwner pre.executionEnv.sender
    gas (UInt256.ofNat pre.executionEnv.gasPrice) (UInt256.ofNat 0)
    (UInt256.ofNat (pre.executionEnv.depth + 1)) salt.toByteArray pre.executionEnv.header pre.executionEnv.perm vacant fuel enough
  have sameInvocation : nativeCreate2Child (fuel + 2) cost pre offset size salt = .ok child := by
    simpa only [nativeCreate2Child, machine, create2ChildEntry, creatorBumpedMachine, code, gas] using native
  have identical : child = result := Except.ok.inj (sameInvocation.symm.trans completed)
  subst child
  have gasValue : gas.toNat = EVM.L (pre.gasAvailable - UInt256.ofNat cost).toNat := by
    apply Nat.mod_eq_of_lt
    exact lt_of_le_of_lt (native_forwarded_gas_le _) (pre.gasAvailable - UInt256.ofNat cost).val.isLt
  rw [gasValue] at executed
  exact executed

/-- Canonical reservation is derived from the actual nonce-bumped native entry. -/
theorem native_create2_reservation (world : Verity.ContractState) (pre : EVM.State)
    (warm : Create2Access.WarmAccounts) (agrees : Agreement world pre warm)
    (payload : ByteArray) (cost : Nat) (salt : UInt256)
    (nonce : ¬ ((pre.accountMap.get? pre.executionEnv.codeOwner).getD default).nonce.toNat ≥ 2^64 - 1)
    (vacant : let target := nativeCreate2Target pre.executionEnv.codeOwner salt.toByteArray (MidnightInitcode.initcode payload)
      ((create2ChildEntry pre cost).accountMap.getD target default).nonce = UInt256.ofNat 0 ∧
      ((create2ChildEntry pre cost).accountMap.getD target default).code.size = 0) :
    ∃ reserved, Create2Accounts.reserve world.creationAccounts pre.executionEnv.codeOwner.val
      (nativeCreate2Target pre.executionEnv.codeOwner salt.toByteArray (MidnightInitcode.initcode payload)).val =
        .reserved reserved := by
  let charged := { pre with gasAvailable := pre.gasAvailable - UInt256.ofNat cost }
  have bound : (charged.accountMap.getD pre.executionEnv.codeOwner default).nonce.toNat + 1 < UInt256.size := by
    apply creator_bump_nonce_bound
    simpa only [Std.TreeMap.getD_eq_getD_getElem?, Std.TreeMap.get?_eq_getElem?] using nonce
  obtain ⟨reserved, reservation, _⟩ := constructor_canonical_reservation (create2ChildEntry pre cost)
    world.creationAccounts pre.executionEnv.codeOwner _ _ (creator_bump_present charged pre.executionEnv.codeOwner)
    vacant.1 vacant.2
    (constructor_creator_bump charged world.creationAccounts pre.executionEnv.codeOwner · bound agrees.accounts)
  exact ⟨reserved, reservation⟩

/-- Actual native child completion, canonical reservation and the canonical
runEntered outcome are derived together from the same actual invocation. -/
theorem native_create2_child_entered (world : Verity.ContractState) (pre : EVM.State)
    (warm : Create2Access.WarmAccounts) (agrees : Agreement world pre warm)
    (payload : ByteArray) (bounded : payload.size ≤ 49152) (cost : Nat) (offset size salt : UInt256)
    (code : pre.memory.readWithPadding offset.toNat size.toNat = MidnightInitcode.initcode payload)
    (nonce : ¬ ((pre.accountMap.get? pre.executionEnv.codeOwner).getD default).nonce.toNat ≥ 2^64 - 1)
    (vacant : let target := nativeCreate2Target pre.executionEnv.codeOwner salt.toByteArray (MidnightInitcode.initcode payload)
      ((create2ChildEntry pre cost).accountMap.getD target default).nonce = UInt256.ofNat 0 ∧
      ((create2ChildEntry pre cost).accountMap.getD target default).code.size = 0)
    (fuel : Nat) (enough : 10 ≤ fuel) :
    let target := nativeCreate2Target pre.executionEnv.codeOwner salt.toByteArray (MidnightInitcode.initcode payload)
    ∃ result reserved, nativeCreate2Child (fuel + 2) cost pre offset size salt = .ok result ∧
      Create2Accounts.reserve world.creationAccounts pre.executionEnv.codeOwner.val target.val = .reserved reserved ∧
      Create2Callee.runEntered world.creationAccounts pre.executionEnv.codeOwner.val target.val payload
        (EVM.L (pre.gasAvailable - UInt256.ofNat cost).toNat) = .ok
          { outcome := constructorOutcome world.creationAccounts reserved pre.executionEnv.codeOwner target payload result.2.2.2.2.2.1
            gasLeft := result.2.2.2.1.toNat } := by
  obtain ⟨reserved, reservation⟩ := native_create2_reservation world pre warm agrees payload cost salt nonce vacant
  obtain ⟨result, completed⟩ := native_create2_child_completed payload bounded pre cost offset size salt code fuel enough
  have executed := native_create2_child_execution payload bounded pre cost offset size salt code vacant fuel enough result completed
  have accepted := native_executed_flag_accepted payload bounded _ _ _ executed
  exact ⟨result, reserved, completed, reservation,
    constructor_canonical_entered world.creationAccounts reserved pre.executionEnv.codeOwner.val _ payload _ _ _ reservation executed accepted⟩

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor

import Compiler.Proofs.IRGeneration.NativeMappingKeccak

namespace Compiler.Proofs.IRGeneration.NativeMappingStorageExecution
open EvmYul NativeCreationWorld NativeMappingKeccak

/-- Actual checked MSTORE determines its stack, PC and complete account-world frame. -/
theorem checked_mstore_shape (machine after : EVM.State) (offset value : UInt256) (tail : Stack UInt256)
    (stack : machine.stack = offset :: value :: tail)
    (success : CreationCaller.checkedStep machine .MSTORE none = .ok after) :
    after.stack = tail ∧ after.toState = machine.toState ∧ after.pc = machine.pc + UInt256.ofNat 1 := by
  let expanded := { machine with
    gasAvailable := machine.gasAvailable - UInt256.ofNat (EVM.memoryExpansionCost machine .MSTORE) }
  let cost := EVM.C' expanded .MSTORE
  have stepped := NativeCreationStorageOpcodes.checkedStep_delegates machine after .MSTORE none success
  change EVM.step 1 cost (some (.MSTORE, none)) expanded = .ok after at stepped
  have expandedStack : expanded.stack = offset :: value :: tail := stack
  have actual := EVM.Proof.step_MSTORE 0 cost expanded tail offset value (by rw [expandedStack]; rfl)
  have same : after = EVM.Proof.mstorePost cost expanded tail offset value :=
    Except.ok.inj (stepped.symm.trans actual)
  rw [same]
  exact ⟨rfl, rfl, rfl⟩

/-- All intermediate operands follow from the initial stack and actual checked steps. -/
theorem stores_hash_stack (initial middle prepared hashed : EVM.State) (base key : Nat)
    (value : UInt256) (tail : Stack UInt256)
    (stack : initial.stack = UInt256.ofNat 0 :: UInt256.ofNat key :: UInt256.ofNat 32 ::
      UInt256.ofNat base :: UInt256.ofNat 0 :: UInt256.ofNat 64 :: value :: tail)
    (first : CreationCaller.checkedStep initial .MSTORE none = .ok middle)
    (second : CreationCaller.checkedStep middle .MSTORE none = .ok prepared)
    (hashStep : CreationCaller.checkedStep prepared .KECCAK256 none = .ok hashed)
    (hash : ffi.KEC (Compiler.Proofs.abiEncodeMappingSlot base key) =
      KeccakEngine.keccak256 (Compiler.Proofs.abiEncodeMappingSlot base key)) :
    hashed.stack = UInt256.ofNat (Compiler.Proofs.solidityMappingSlot base key) :: value :: tail ∧
      hashed.toState = initial.toState ∧
      hashed.memory.readWithPadding 0 64 = Compiler.Proofs.abiEncodeMappingSlot base key := by
  obtain ⟨middleStack, middleWorld, _⟩ := checked_mstore_shape initial middle _ _ _ stack first
  obtain ⟨preparedStack, preparedWorld, _⟩ := checked_mstore_shape middle prepared _ _ _ middleStack second
  have result := checked_mapping_hash initial middle prepared hashed base key _ _ (value :: tail)
    stack middleStack preparedStack first second hashStep hash
  have preimage := checked_mapping_preimage initial middle prepared _ _ _ _ stack middleStack first second
  exact ⟨result.1, result.2.1.trans (preparedWorld.trans middleWorld),
    by rw [result.2.2.1]; exact preimage⟩

/-- The singleton source mapping location is exactly the slot computed by native hashing. -/
theorem singleton_location (base key : Nat) :
    Compiler.Proofs.Storage.HashedMappingLayout.Entry.location (base, [key], 0) =
      Compiler.Proofs.solidityMappingSlot base key := by
  exact Compiler.Proofs.mappingChainSlotLocation_zero base key []

/-- A real hash-and-store fragment agrees with the actual source mapping helper.
No intermediate stack or poststate Agreement is supplied by the caller. -/
theorem stores_hash_sstore (world : Verity.ContractState)
    (initial middle prepared hashed final : EVM.State) (base key : Nat)
    (value : UInt256) (tail : Stack UInt256)
    (warm : Verity.Core.Model.Create2Access.WarmAccounts) (account : Account .EVM)
    (present : initial.toState.lookupAccount initial.executionEnv.codeOwner = some account)
    (agrees : Agreement world initial warm)
    (stack : initial.stack = UInt256.ofNat 0 :: UInt256.ofNat key :: UInt256.ofNat 32 ::
      UInt256.ofNat base :: UInt256.ofNat 0 :: UInt256.ofNat 64 :: value :: tail)
    (first : CreationCaller.checkedStep initial .MSTORE none = .ok middle)
    (second : CreationCaller.checkedStep middle .MSTORE none = .ok prepared)
    (hashStep : CreationCaller.checkedStep prepared .KECCAK256 none = .ok hashed)
    (store : CreationCaller.checkedStep hashed .SSTORE none = .ok final)
    (hash : ffi.KEC (Compiler.Proofs.abiEncodeMappingSlot base key) =
      KeccakEngine.keccak256 (Compiler.Proofs.abiEncodeMappingSlot base key)) :
    Agreement (SourceSemantics.writeAddressKeyedMappingChainSlots world [base] [key] value.toNat) final warm := by
  obtain ⟨actualStack, frame, _⟩ := stores_hash_stack initial middle prepared hashed base key value tail
    stack first second hashStep hash
  have current : Agreement world hashed warm :=
    NativeCreationLocalFrames.agreement_of_state_eq world initial hashed warm agrees frame
  have currentAccount : hashed.toState.lookupAccount hashed.executionEnv.codeOwner = some account := by
    rw [frame]; exact present
  have restored : { hashed with
      stack := UInt256.ofNat (Compiler.Proofs.Storage.HashedMappingLayout.Entry.location (base, [key], 0)) :: value :: tail } = hashed := by
    rw [singleton_location, ← actualStack]
  exact NativeSourceMappingWrites.checked_source_chain_write world hashed final warm account currentAccount
    current base [key] value tail (by simpa only [restored] using store)

/-- Source key normalization preserves the exact ABI mapping preimage. -/
theorem mapping_key_normalize (base key : Nat) :
    Compiler.Proofs.solidityMappingSlot base (SourceSemantics.wordNormalize key) =
      Compiler.Proofs.solidityMappingSlot base key := by
  unfold Compiler.Proofs.solidityMappingSlot Compiler.Proofs.abiEncodeMappingSlot
  rw [SourceSemantics.wordNormalize_eq_mod, Compiler.Proofs.evmYul_uint256_ofNat_mod]

/-- The complete actual Source statement and four checked native instructions agree. -/
theorem stores_hash_source_statement (fields : List Compiler.CompilationModel.Field)
    (events : List Compiler.CompilationModel.EventDef) (state : SourceSemantics.RuntimeState)
    (name : String) (base key : Nat) (value : UInt256) (tail : Stack UInt256)
    (slots : Compiler.CompilationModel.findFieldWriteSlots fields name = some [base])
    (initial middle prepared hashed final : EVM.State)
    (warm : Verity.Core.Model.Create2Access.WarmAccounts) (account : Account .EVM)
    (present : initial.toState.lookupAccount initial.executionEnv.codeOwner = some account)
    (agrees : Agreement state.world initial warm)
    (stack : initial.stack = UInt256.ofNat 0 :: UInt256.ofNat key :: UInt256.ofNat 32 ::
      UInt256.ofNat base :: UInt256.ofNat 0 :: UInt256.ofNat 64 :: value :: tail)
    (first : CreationCaller.checkedStep initial .MSTORE none = .ok middle)
    (second : CreationCaller.checkedStep middle .MSTORE none = .ok prepared)
    (hashStep : CreationCaller.checkedStep prepared .KECCAK256 none = .ok hashed)
    (store : CreationCaller.checkedStep hashed
      (if SourceSemantics.fieldIsTransient fields name then .TSTORE else .SSTORE) none = .ok final)
    (hash : ffi.KEC (Compiler.Proofs.abiEncodeMappingSlot base key) =
      KeccakEngine.keccak256 (Compiler.Proofs.abiEncodeMappingSlot base key)) :
    ∃ result, SourceSemantics.execStmtWithEvents fields events state
      (.setMappingChain name [.literal key] (.literal value.toNat)) = .continue result ∧
      Agreement result.world final warm := by
  obtain ⟨actualStack, frame, _⟩ := stores_hash_stack initial middle prepared hashed base key value tail
    stack first second hashStep hash
  have current : Agreement state.world hashed warm :=
    NativeCreationLocalFrames.agreement_of_state_eq state.world initial hashed warm agrees frame
  have currentAccount : hashed.toState.lookupAccount hashed.executionEnv.codeOwner = some account := by
    rw [frame]; exact present
  have word : UInt256.ofNat value.toNat = value := by
    apply congrArg UInt256.mk
    apply Fin.ext
    exact Nat.mod_eq_of_lt value.val.isLt
  apply NativeSourceMappingExecution.resolved_chain_native fields events state name [key] value.toNat base slots
    hashed final warm account currentAccount current tail
  · simpa only [List.map_cons, List.map_nil, singleton_location, mapping_key_normalize,
      word] using actualStack
  · exact store

/-- A successful checked hash preserves the whole native account world without a supplied stack. -/
theorem checked_keccak_state (machine after : EVM.State)
    (success : CreationCaller.checkedStep machine .KECCAK256 none = .ok after) :
    after.toState = machine.toState := by
  have enough := (NativePairedCallerChecks.checked_guards machine after .KECCAK256 none success).stack
  simp only [EVM.δ, Option.getD] at enough
  cases stack : machine.stack with
  | nil => simp only [stack, List.length_nil] at enough; omega
  | cons offset rest =>
    cases rest with
    | nil => simp only [stack, List.length_cons, List.length_nil] at enough; omega
    | cons size tail => exact (checked_keccak machine after offset size tail stack success).2.1

/-- A byte-authenticated MSTORE continues the actual iterator with all checks retained. -/
theorem checked_mstore_x (fuel : Nat) (machine after : EVM.State)
    (bounded : machine.executionEnv.code.size < UInt256.size)
    (fetched : machine.executionEnv.code.get? machine.pc.toNat = some 0x52)
    (success : CreationCaller.checkedStep machine .MSTORE none = .ok after) :
    EVM.X (fuel + 2) (EVM.D_J machine.executionEnv.code (UInt256.ofNat 0)) machine =
      EVM.X (fuel + 1) (EVM.D_J machine.executionEnv.code (UInt256.ofNat 0)) after := by
  have decoded : EVM.Proof.decodeAt machine = (.MSTORE, none) := by
    simp only [EVM.Proof.decodeAt, EVM.decode, fetched, Bind.bind, Option.bind]
    rfl
  exact NativePairedCallerChecks.checked_native_x fuel machine after _ _ bounded
    (by decide) decoded success

/-- Four byte-authenticated checked instructions compose in the real EVM iterator.
The preimage/source correspondence is proved separately, with the same states. -/
theorem stores_hash_native_x (fuel : Nat) (transient : Bool) (initial middle prepared hashed final : EVM.State)
    (bounded : initial.executionEnv.code.size < UInt256.size)
    (firstByte : initial.executionEnv.code.get? initial.pc.toNat = some 0x52)
    (secondByte : middle.executionEnv.code.get? middle.pc.toNat = some 0x52)
    (hashByte : prepared.executionEnv.code.get? prepared.pc.toNat = some 0x20)
    (storeByte : hashed.executionEnv.code.get? hashed.pc.toNat = some (if transient then 0x5d else 0x55))
    (first : CreationCaller.checkedStep initial .MSTORE none = .ok middle)
    (second : CreationCaller.checkedStep middle .MSTORE none = .ok prepared)
    (hashStep : CreationCaller.checkedStep prepared .KECCAK256 none = .ok hashed)
    (store : CreationCaller.checkedStep hashed (if transient then .TSTORE else .SSTORE) none = .ok final) :
    EVM.X (fuel + 5) (EVM.D_J initial.executionEnv.code (UInt256.ofNat 0)) initial =
      EVM.X (fuel + 1) (EVM.D_J initial.executionEnv.code (UInt256.ofNat 0)) final := by
  have firstWorld := NativeCreationLocalFrames.supported_checked_state .MSTORE initial middle none (by decide) first
  have secondWorld := NativeCreationLocalFrames.supported_checked_state .MSTORE middle prepared none (by decide) second
  have hashWorld := checked_keccak_state prepared hashed hashStep
  have middleCode : middle.executionEnv.code = initial.executionEnv.code :=
    congrArg (fun state : State .EVM => state.executionEnv.code) firstWorld
  have preparedCode : prepared.executionEnv.code = initial.executionEnv.code :=
    congrArg (fun state : State .EVM => state.executionEnv.code) (secondWorld.trans firstWorld)
  have hashedCode : hashed.executionEnv.code = initial.executionEnv.code :=
    congrArg (fun state : State .EVM => state.executionEnv.code) (hashWorld.trans (secondWorld.trans firstWorld))
  have secondBound : middle.executionEnv.code.size < UInt256.size := by rw [middleCode]; exact bounded
  have storeBound : hashed.executionEnv.code.size < UInt256.size := by rw [hashedCode]; exact bounded
  have firstX := checked_mstore_x (fuel + 3) initial middle bounded firstByte first
  have secondX := checked_mstore_x (fuel + 2) middle prepared secondBound secondByte second
  have hashX := checked_keccak_x (fuel + 1) prepared hashed hashByte hashStep
  have storeX := NativePairedCallerChecks.checked_native_x fuel hashed final (if transient then .TSTORE else .SSTORE) none storeBound
    (by cases transient <;> decide) (NativeSourceStorageBytecode.storage_decode hashed transient storeByte) store
  rw [middleCode] at secondX
  rw [preparedCode] at hashX
  rw [hashedCode] at storeX
  exact firstX.trans (secondX.trans (hashX.trans storeX))

end Compiler.Proofs.IRGeneration.NativeMappingStorageExecution

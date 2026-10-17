import Compiler.Proofs.IRGeneration.NativeCreate2CallerNonce

namespace Verity.Core.Model.Create2Operation
open Verity Create2Entry Create2Callee

/-- Real canonical collision does not decode constructor bytes and burns child gas. -/
theorem run_collision (before : Frame) (offset size salt : Uint256) (child : Forwarded)
    (prepared : prepare before.world.byteMemory before.context offset.val size.val = .ok (.forwarded child))
    (legal : (before.world.creationAccounts before.world.thisAddress.val).nonce < Create2NonceEntry.maxCreatorNonce)
    (collision : let world := before.world.installPhysicalMemory child.memory
      Create2Accounts.reserve world.creationAccounts world.thisAddress.val
        (Create2.create2AddressFromPhysicalMemory world offset size salt world.thisAddress).val =
        .collision (Create2Accounts.bumpCreator world.creationAccounts world.thisAddress.val)) :
    let world := before.world.installPhysicalMemory child.memory
    let after := Create2Accounts.bumpCreator world.creationAccounts world.thisAddress.val
    run before offset size salt = .ok (.continued 0
      { world := { world with creationAccounts := after, returndata := [] }
        context := { before.context with gas := child.retainedGas }
        warm := Create2Access.warm before.warm
          (Create2.create2AddressFromPhysicalMemory world offset size salt world.thisAddress).val }) := by
  have entered := enterCode_collision (before.world.installPhysicalMemory child.memory).creationAccounts
    (before.world.installPhysicalMemory child.memory).thisAddress.val
    (Create2.create2AddressFromPhysicalMemory (before.world.installPhysicalMemory child.memory)
      offset size salt (before.world.installPhysicalMemory child.memory).thisAddress).val
    (Create2.physicalInitcodeBytes (before.world.installPhysicalMemory child.memory) offset.val size.val)
    child.childGas legal _ collision
  have committed := CreationStorage.commit_failed_empty (before.world.installPhysicalMemory child.memory)
    (Create2Accounts.bumpCreator (before.world.installPhysicalMemory child.memory).creationAccounts
      (before.world.installPhysicalMemory child.memory).thisAddress.val)
  have result := run_forwarded before offset size salt child _ _ prepared legal entered committed
  have owner : (before.world.installPhysicalMemory child.memory).thisAddress = before.world.thisAddress := rfl
  simpa only [outcomeValue, Create2Entry.completeGas, Nat.add_zero, owner] using result

end Verity.Core.Model.Create2Operation

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul EVM.Proof NativeCreationWorld
open Verity.Core.Model

/-- Collision uses the real child result to derive zero value and every caller observation. -/
theorem caller_collision_observations (pre next : EVM.State) (fuel cost : Nat)
    (rest : Stack UInt256) (offset size salt : UInt256)
    (popped : pre.stack.pop4 = some (rest, UInt256.ofNat 0, offset, size, salt))
    (nonce : ¬ ((pre.accountMap.get? pre.executionEnv.codeOwner).getD default).nonce.toNat ≥ 2^64 - 1)
    (entry : UInt256.ofNat 0 ≤ (pre.accountMap.get? pre.executionEnv.codeOwner |>.option (UInt256.ofNat 0) (·.balance)) ∧
      pre.executionEnv.depth < 1024 ∧ (pre.memory.readWithPadding offset.toNat size.toNat).size ≤ 49152)
    (collision : let machine := create2ChildEntry pre cost
      let target := nativeCreate2Target pre.executionEnv.codeOwner salt.toByteArray
        (pre.memory.readWithPadding offset.toNat size.toNat)
      let account := machine.accountMap.getD target default
      (decide (account.nonce ≠ (⟨0⟩ : UInt256)) || decide (account.code.size ≠ 0)) = true)
    (stepped : EVM.step (fuel + 4) cost (some (.CREATE2, none)) pre = .ok next) :
    CallerResultObservations pre next rest offset size 0 := by
  have child := native_create2_child_collision fuel cost pre offset size salt collision
  have observed := native_create2_caller_frame (fuel + 3) cost pre next rest offset size salt _ popped nonce entry child stepped
  have frame := native_create2_child_frame (fuel + 3) cost pre next rest offset size salt _ popped nonce entry child stepped
  refine ⟨?_, ?_, observed.2.2.2.1, observed.2.2.2.2.1, observed.2.2.2.2.2,
    frame.2.2.2.2.1, frame.2.2.2.2.2, frame.2.2.2.1⟩
  · simpa only [Bool.false_eq_true, not_false_eq_true, true_or, if_true, Verity.Core.Uint256.val_zero] using observed.1
  · exact observed.2.2.1

/-- Collision consumes forwarded gas and retains the exact native target warming. -/
theorem caller_collision_gas_substate (pre next : EVM.State) (fuel cost : Nat)
    (rest : Stack UInt256) (offset size salt : UInt256)
    (popped : pre.stack.pop4 = some (rest, UInt256.ofNat 0, offset, size, salt))
    (nonce : ¬ ((pre.accountMap.get? pre.executionEnv.codeOwner).getD default).nonce.toNat ≥ 2^64 - 1)
    (entry : UInt256.ofNat 0 ≤ (pre.accountMap.get? pre.executionEnv.codeOwner |>.option (UInt256.ofNat 0) (·.balance)) ∧
      pre.executionEnv.depth < 1024 ∧ (pre.memory.readWithPadding offset.toNat size.toNat).size ≤ 49152)
    (collision : let machine := create2ChildEntry pre cost
      let target := nativeCreate2Target pre.executionEnv.codeOwner salt.toByteArray
        (pre.memory.readWithPadding offset.toNat size.toNat)
      let account := machine.accountMap.getD target default
      (decide (account.nonce ≠ (⟨0⟩ : UInt256)) || decide (account.code.size ≠ 0)) = true)
    (stepped : EVM.step (fuel + 4) cost (some (.CREATE2, none)) pre = .ok next) :
    next.gasAvailable.toNat = (pre.gasAvailable - UInt256.ofNat cost).toNat / 64 ∧
      next.substate = pre.substate.addAccessedAccount
        (nativeCreate2Target pre.executionEnv.codeOwner salt.toByteArray
          (pre.memory.readWithPadding offset.toNat size.toNat)) := by
  have child := native_create2_child_collision fuel cost pre offset size salt collision
  have observed := native_create2_caller_frame (fuel + 3) cost pre next rest offset size salt _ popped nonce entry child stepped
  have frame := native_create2_child_frame (fuel + 3) cost pre next rest offset size salt _ popped nonce entry child stepped
  have returned : (UInt256.ofNat 0).toNat ≤ EVM.L (pre.gasAvailable - UInt256.ofNat cost).toNat := Nat.zero_le _
  have gas := native_create2_caller_gas pre next cost rest offset size _ observed returned
  have zero : (UInt256.ofNat 0).toNat = 0 := rfl
  exact ⟨by simpa only [zero, Nat.add_zero] using gas, frame.2.1⟩

/-- Initial collision inputs, with explicit pointwise primitive hash agreements. -/
structure CallerCollisionGuards (pre : EVM.State) (rest : Stack UInt256)
    (offset size salt : UInt256) : Prop where
  stack : pre.stack = UInt256.ofNat 0 :: offset :: size :: salt :: rest
  cap : size.toNat ≤ 49152
  nonce : ¬ ((pre.accountMap.get? pre.executionEnv.codeOwner).getD default).nonce.toNat ≥ 2^64 - 1
  depth : pre.executionEnv.depth < 1024
  valid : pre.gasAvailable.toNat ≤ Create2Entry.maxGas
  mutable : pre.executionEnv.perm = true
  funded : EVM.memoryExpansionCost pre .CREATE2 + EVM.C' pre .CREATE2 ≤ pre.gasAvailable.toNat
  collision : let machine := create2ChildEntry (create2MemoryDebited pre) (EVM.C' (create2MemoryDebited pre) .CREATE2)
    let target := nativeCreate2Target pre.executionEnv.codeOwner salt.toByteArray
      (pre.memory.readWithPadding offset.toNat size.toNat)
    let account := machine.accountMap.getD target default
    (decide (account.nonce ≠ (⟨0⟩ : UInt256)) || decide (account.code.size ≠ 0)) = true
  inner : ffi.KEC (pre.memory.readWithPadding offset.toNat size.toNat) =
    KeccakEngine.keccak256 (pre.memory.readWithPadding offset.toNat size.toNat)
  outer : ffi.KEC (BE 255 ++ pre.executionEnv.codeOwner.toByteArray ++ salt.toByteArray ++
      ffi.KEC (pre.memory.readWithPadding offset.toNat size.toNat)) =
    KeccakEngine.keccak256 (BE 255 ++ pre.executionEnv.codeOwner.toByteArray ++ salt.toByteArray ++
      ffi.KEC (pre.memory.readWithPadding offset.toNat size.toNat))

/-- Actual bumped collision and two-hash address derive canonical reservation failure. -/
theorem caller_collision_reservation (world : Verity.ContractState) (pre : EVM.State)
    (warm : Create2Access.WarmAccounts) (agrees : Agreement world pre warm) (allocated : CallerAllocated pre)
    (rest : Stack UInt256) (offset size salt : UInt256)
    (guards : CallerCollisionGuards pre rest offset size salt) :
    let prepared := callerPreparedWorld world pre offset size
    Create2Accounts.reserve prepared.creationAccounts prepared.thisAddress.val
      (Create2.create2AddressFromPhysicalMemory prepared
        (Verity.Core.Uint256.ofNat offset.toNat) (Verity.Core.Uint256.ofNat size.toNat)
        (Verity.Core.Uint256.ofNat salt.toNat) prepared.thisAddress).val =
      .collision (Create2Accounts.bumpCreator prepared.creationAccounts prepared.thisAddress.val) := by
  have prepared := caller_prepared_agreement world (create2MemoryDebited pre) warm
    (caller_debited_agreement world pre warm agrees) offset size
  have canonical := native_create2_collision_canonical _ (create2MemoryDebited pre) warm prepared
    (EVM.C' (create2MemoryDebited pre) .CREATE2) offset size salt guards.nonce guards.collision
  have target := native_create2_prepared_address world pre warm agrees allocated offset size salt
    guards.cap guards.inner guards.outer
  have reserved := canonical.1
  change Create2Accounts.reserve (callerPreparedWorld world pre offset size).creationAccounts
    pre.executionEnv.codeOwner.val
    (nativeCreate2Target pre.executionEnv.codeOwner salt.toByteArray
      (pre.memory.readWithPadding offset.toNat size.toNat)).val = _ at reserved
  rw [target] at reserved
  change Create2Accounts.reserve (callerPreparedWorld world pre offset size).creationAccounts world.thisAddress.val _ =
    .collision (Create2Accounts.bumpCreator world.creationAccounts world.thisAddress.val)
  rw [agrees.caller]
  exact reserved

/-- Actual prepared collision commit and retained-gas caller frame. -/
def callerCollisionFinal (world : Verity.ContractState) (pre : EVM.State)
    (warm : Create2Access.WarmAccounts) (offset size salt : UInt256) : Create2Operation.Frame :=
  let prepared := callerPreparedWorld world pre offset size
  { world := { prepared with creationAccounts := Create2Accounts.bumpCreator prepared.creationAccounts prepared.thisAddress.val, returndata := [] }
    context := { gas := (callerForwarded pre offset size).retainedGas, depth := pre.executionEnv.depth, isStatic := !pre.executionEnv.perm }
    warm := Create2Access.warm warm (Create2.create2AddressFromPhysicalMemory prepared
      (Verity.Core.Uint256.ofNat offset.toNat) (Verity.Core.Uint256.ofNat size.toNat)
      (Verity.Core.Uint256.ofNat salt.toNat) prepared.thisAddress).val }

/-- The full canonical operation follows from the actual initial collision guards. -/
theorem caller_collision_run (world : Verity.ContractState) (pre : EVM.State)
    (warm : Create2Access.WarmAccounts) (agrees : Agreement world pre warm) (allocated : CallerAllocated pre)
    (rest : Stack UInt256) (offset size salt : UInt256)
    (guards : CallerCollisionGuards pre rest offset size salt) :
    Create2Operation.run (CreationBytecode.atBoundary ⟨world, pre, warm⟩)
      (Verity.Core.Uint256.ofNat offset.toNat) (Verity.Core.Uint256.ofNat size.toNat)
      (Verity.Core.Uint256.ofNat salt.toNat) = .ok (.continued 0 (callerCollisionFinal world pre warm offset size salt)) := by
  have offsetValue : (Verity.Core.Uint256.ofNat offset.toNat).val = offset.toNat := Nat.mod_eq_of_lt offset.val.isLt
  have sizeValue : (Verity.Core.Uint256.ofNat size.toNat).val = size.toNat := Nat.mod_eq_of_lt size.val.isLt
  have actual : Create2Entry.prepare (CreationBytecode.atBoundary ⟨world, pre, warm⟩).world.byteMemory
      (CreationBytecode.atBoundary ⟨world, pre, warm⟩).context
      (Verity.Core.Uint256.ofNat offset.toNat).val (Verity.Core.Uint256.ofNat size.toNat).val =
        .ok (.forwarded (callerForwarded pre offset size)) := by
    rw [offsetValue, sizeValue]
    exact caller_prepare_funded pre (UInt256.ofNat 0) offset size salt rest guards.stack
      guards.valid guards.mutable guards.cap guards.funded guards.depth
  have legal := caller_world_legal_nonce world pre warm agrees guards.nonce
  have reserved := caller_collision_reservation world pre warm agrees allocated rest offset size salt guards
  exact Create2Operation.run_collision (CreationBytecode.atBoundary ⟨world, pre, warm⟩)
    (Verity.Core.Uint256.ofNat offset.toNat) (Verity.Core.Uint256.ofNat size.toNat)
    (Verity.Core.Uint256.ofNat salt.toNat) (callerForwarded pre offset size) actual legal reserved

/-- Transport actual collision agreement to the same canonical world and warmed target. -/
theorem caller_collision_world_transport (world : Verity.ContractState) (pre next : EVM.State)
    (warm : Create2Access.WarmAccounts) (agrees : Agreement world pre warm) (allocated : CallerAllocated pre)
    (rest : Stack UInt256) (offset size salt : UInt256) (guards : CallerCollisionGuards pre rest offset size salt)
    (native : Agreement ((callerPreparedWorld world pre offset size).withCreationAccounts
        (Create2Accounts.bumpCreator world.creationAccounts pre.executionEnv.codeOwner.val)) next
      (Create2Access.warm warm (nativeCreate2Target pre.executionEnv.codeOwner salt.toByteArray
        (pre.memory.readWithPadding offset.toNat size.toNat)).val)) :
    Agreement (callerCollisionFinal world pre warm offset size salt).world next
      (callerCollisionFinal world pre warm offset size salt).warm := by
  have raw : Agreement (callerCollisionFinal world pre warm offset size salt).world next
      (Create2Access.warm warm (nativeCreate2Target pre.executionEnv.codeOwner salt.toByteArray
        (pre.memory.readWithPadding offset.toNat size.toNat)).val) := by
    change Agreement { callerPreparedWorld world pre offset size with
      creationAccounts := Create2Accounts.bumpCreator world.creationAccounts world.thisAddress.val, returndata := [] } next _
    rw [agrees.caller]
    exact { native with }
  have target := native_create2_prepared_address world pre warm agrees allocated offset size salt
    guards.cap guards.inner guards.outer
  exact (congrArg (fun address => Agreement (callerCollisionFinal world pre warm offset size salt).world
    next (Create2Access.warm warm address)) target).mp raw

/-- Derive the actual collision parent and its complete canonical world agreement. -/
theorem caller_collision_native (world : Verity.ContractState) (pre : EVM.State)
    (warm : Create2Access.WarmAccounts) (agrees : Agreement world pre warm) (allocated : CallerAllocated pre)
    (fuel : Nat) (rest : Stack UInt256) (offset size salt : UInt256)
    (guards : CallerCollisionGuards pre rest offset size salt) :
    ∃ next,
      EVM.step (fuel + 4) (EVM.C' (create2MemoryDebited pre) .CREATE2)
        (some (.CREATE2, none)) (create2MemoryDebited pre) = .ok next ∧
      Agreement (callerCollisionFinal world pre warm offset size salt).world next
        (callerCollisionFinal world pre warm offset size salt).warm ∧
      CallerResultObservations pre next rest offset size 0 ∧
      next.gasAvailable.toNat = (callerCollisionFinal world pre warm offset size salt).context.gas ∧
      next.substate = pre.substate.addAccessedAccount (nativeCreate2Target pre.executionEnv.codeOwner salt.toByteArray
        (pre.memory.readWithPadding offset.toNat size.toNat)) := by
  let machine := create2MemoryDebited pre
  let cost := EVM.C' machine .CREATE2
  have prepared := caller_prepared_agreement world machine warm (caller_debited_agreement world pre warm agrees) offset size
  have popped : machine.stack.pop4 = some (rest, UInt256.ofNat 0, offset, size, salt) := by
    change pre.stack.pop4 = _
    rw [guards.stack]
    rfl
  have entry := caller_zero_entry machine offset size guards.cap guards.depth
  obtain ⟨next, stepped, native, _, _⟩ := native_create2_collision_world _ machine warm prepared
    fuel cost rest offset size salt popped guards.nonce entry guards.collision
  have observation := caller_collision_observations machine next fuel cost rest offset size salt
    popped guards.nonce entry guards.collision stepped
  have gas := caller_collision_gas_substate machine next fuel cost rest offset size salt
    popped guards.nonce entry guards.collision stepped
  exact ⟨next, stepped, caller_collision_world_transport world pre next warm agrees allocated rest offset size salt guards native,
    caller_observations_debited pre next rest offset size 0 observation, gas.1, gas.2⟩

/-- The failed collision commit changes no storage word or remaining caller field. -/
theorem caller_collision_final_frame (world : Verity.ContractState) (pre : EVM.State)
    (warm : Create2Access.WarmAccounts) (offset size salt : UInt256) :
    callerWorldFrame (callerCollisionFinal world pre warm offset size salt).world = callerWorldFrame world ∧
      (callerCollisionFinal world pre warm offset size salt).world.storageWords = world.storageWords := by
  constructor
  · change callerWorldFrame { callerPreparedWorld world pre offset size with
      creationAccounts := Create2Accounts.bumpCreator world.creationAccounts world.thisAddress.val, returndata := [] } = _
    exact caller_prepared_world_frame world pre offset size
  · rfl

/-- Complete final physical memory follows from the same native observations. -/
theorem caller_collision_physical_memory (world : Verity.ContractState) (pre next : EVM.State)
    (warm : Create2Access.WarmAccounts) (allocated : CallerAllocated pre) (rest : Stack UInt256)
    (offset size salt : UInt256) (observed : CallerResultObservations pre next rest offset size 0) :
    CallerPhysicalMemoryAgreement (callerCollisionFinal world pre warm offset size salt).world next := by
  have physical := caller_prepared_physical_memory world pre next rest offset size 0 allocated observed
  exact ⟨physical.size, physical.byte⟩

/-- Complete checked/native/canonical collision result for one computed child and target. -/
theorem caller_collision_operation_completed (world : Verity.ContractState) (pre : EVM.State)
    (warm : Create2Access.WarmAccounts) (agrees : Agreement world pre warm) (allocated : CallerAllocated pre)
    (jumps : Array UInt256) (fuel : Nat) (rest : Stack UInt256) (offset size salt : UInt256)
    (guards : CallerCollisionGuards pre rest offset size salt)
    (decoded : decodeAt pre = (.CREATE2, none)) (limit : pre.stack.length ≤ 1024) :
    ∃ next final,
      EVM.step (fuel + 4) (EVM.C' (create2MemoryDebited pre) .CREATE2)
        (some (.CREATE2, none)) (create2MemoryDebited pre) = .ok next ∧
      EVM.X (fuel + 5) jumps pre = EVM.X (fuel + 4) jumps next ∧
      Create2Operation.run (CreationBytecode.atBoundary ⟨world, pre, warm⟩)
        (Verity.Core.Uint256.ofNat offset.toNat) (Verity.Core.Uint256.ofNat size.toNat)
        (Verity.Core.Uint256.ofNat salt.toNat) = .ok (.continued 0 final) ∧
      Agreement final.world next final.warm ∧ next.gasAvailable.toNat = final.context.gas ∧
      CallerResultObservations pre next rest offset size 0 ∧
      CallerPhysicalMemoryAgreement final.world next ∧
      CallerFrameAgreement world final.world pre.substate next.substate
        (nativeCreate2Target pre.executionEnv.codeOwner salt.toByteArray
          (pre.memory.readWithPadding offset.toNat size.toNat)) ∧
      final.world.storageWords = world.storageWords ∧
      next.substate = pre.substate.addAccessedAccount (nativeCreate2Target pre.executionEnv.codeOwner salt.toByteArray
        (pre.memory.readWithPadding offset.toNat size.toNat)) := by
  obtain ⟨next, stepped, agreement, observed, gas, substate⟩ :=
    caller_collision_native world pre warm agrees allocated fuel rest offset size salt guards
  have continued := caller_create2_X_continue pre next jumps (fuel + 1) rest offset size salt decoded
    guards.stack limit guards.mutable guards.cap guards.funded stepped
  have framed := caller_collision_final_frame world pre warm offset size salt
  have frames : CallerFrameAgreement world (callerCollisionFinal world pre warm offset size salt).world
      pre.substate next.substate (nativeCreate2Target pre.executionEnv.codeOwner salt.toByteArray
        (pre.memory.readWithPadding offset.toNat size.toNat)) := by
    refine ⟨framed.1, ?_, fun key _ => congrFun framed.2 key⟩
    rw [substate]
    exact constructor_substate_frame _ _
  exact ⟨next, _, stepped, continued, caller_collision_run world pre warm agrees allocated rest offset size salt guards,
    agreement, gas, observed, caller_collision_physical_memory world pre next warm allocated rest offset size salt observed,
    frames, framed.2, substate⟩

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor

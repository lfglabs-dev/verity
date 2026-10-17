import Compiler.Proofs.IRGeneration.NativeCreate2OperationRun

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul NativeCreationWorld
open Verity.Core.Model

/-- Canonical preparation expands memory but never changes any hashed byte.
This equation is about both actual complete initcode slices. -/
theorem caller_prepared_address (world : Verity.ContractState) (pre : EVM.State)
    (allocated : CallerAllocated pre) (offset size salt : UInt256)
    (bounded : size.toNat ≤ 49152) (sender : Verity.Core.Address) :
    Create2.create2AddressFromPhysicalMemory (world.installPhysicalMemory
      (MidnightInitcode.returnMemory (CreationBytecode.callerMemory pre) offset.toNat size.toNat))
      (Verity.Core.Uint256.ofNat offset.toNat) (Verity.Core.Uint256.ofNat size.toNat)
      (Verity.Core.Uint256.ofNat salt.toNat) sender =
    Create2.create2AddressFromPhysicalMemory (world.installPhysicalMemory (CreationBytecode.callerMemory pre))
      (Verity.Core.Uint256.ofNat offset.toNat) (Verity.Core.Uint256.ofNat size.toNat)
      (Verity.Core.Uint256.ofNat salt.toNat) sender := by
  have offsetValue : (Verity.Core.Uint256.ofNat offset.toNat).val = offset.toNat := Nat.mod_eq_of_lt offset.val.isLt
  have sizeValue : (Verity.Core.Uint256.ofNat size.toNat).val = size.toNat := Nat.mod_eq_of_lt size.val.isLt
  have slices := (prepared_physical_slice world pre allocated offset.toNat size.toNat bounded).trans
    (caller_physical_slice world pre allocated offset.toNat size.toNat bounded).symm
  unfold Create2.create2AddressFromPhysicalMemory
  rw [offsetValue, sizeValue]
  exact congrArg (fun bytes => Create2.create2Address (Verity.Core.Uint256.ofNat salt.toNat)
    (Verity.Core.Uint256.ofNat (KeccakEngine.byteArrayToNatBE (KeccakEngine.keccak256 bytes))) sender) slices

/-- The canonical caller address is the actual native code owner at a raw
agreement boundary, retained by physical-memory installation. -/
theorem caller_prepared_owner (world : Verity.ContractState) (pre : EVM.State)
    (warm : Create2Access.WarmAccounts) (agrees : Agreement world pre warm)
    (memory : Compiler.CompilationModel.DenoteMemory.Memory) :
    (world.installPhysicalMemory memory).thisAddress = Verity.Core.Address.ofNat pre.executionEnv.codeOwner.val := by
  apply Verity.Core.Address.ext
  exact agrees.caller.trans (Nat.mod_eq_of_lt pre.executionEnv.codeOwner.isLt).symm

/-- Exact canonical caller world after the actual memory preparation. -/
def callerPreparedWorld (world : Verity.ContractState) (pre : EVM.State) (offset size : UInt256) : Verity.ContractState :=
  world.installPhysicalMemory (MidnightInitcode.returnMemory (CreationBytecode.callerMemory pre) offset.toNat size.toNat)

/-- Installing actual prepared caller memory retains every raw account/storage
agreement field; memory equality is established by separate physical lemmas. -/
theorem caller_prepared_agreement (world : Verity.ContractState) (pre : EVM.State)
    (warm : Create2Access.WarmAccounts) (agrees : Agreement world pre warm) (offset size : UInt256) :
    Agreement (callerPreparedWorld world pre offset size) pre warm := by
  exact { agrees with }

/-- The actual native target is the canonical prepared-world target. Both
pointwise opaque Keccak agreements remain explicit primitive boundaries. -/
theorem native_create2_prepared_address (world : Verity.ContractState) (pre : EVM.State)
    (warm : Create2Access.WarmAccounts) (agrees : Agreement world pre warm) (allocated : CallerAllocated pre)
    (offset size salt : UInt256) (bounded : size.toNat ≤ 49152)
    (inner : ffi.KEC (pre.memory.readWithPadding offset.toNat size.toNat) =
      KeccakEngine.keccak256 (pre.memory.readWithPadding offset.toNat size.toNat))
    (outer : ffi.KEC (BE 255 ++ pre.executionEnv.codeOwner.toByteArray ++ salt.toByteArray ++
        ffi.KEC (pre.memory.readWithPadding offset.toNat size.toNat)) =
      KeccakEngine.keccak256 (BE 255 ++ pre.executionEnv.codeOwner.toByteArray ++ salt.toByteArray ++
        ffi.KEC (pre.memory.readWithPadding offset.toNat size.toNat))) :
    (nativeCreate2Target pre.executionEnv.codeOwner salt.toByteArray
      (pre.memory.readWithPadding offset.toNat size.toNat)).val =
      (Create2.create2AddressFromPhysicalMemory (callerPreparedWorld world pre offset size)
        (Verity.Core.Uint256.ofNat offset.toNat) (Verity.Core.Uint256.ofNat size.toNat)
        (Verity.Core.Uint256.ofNat salt.toNat) (callerPreparedWorld world pre offset size).thisAddress).val := by
  have prepared := caller_prepared_address world pre allocated offset size salt bounded
    (Verity.Core.Address.ofNat pre.executionEnv.codeOwner.val)
  have physical := native_create2_physical_address world pre allocated offset size salt bounded inner outer
  have combined := physical.trans (congrArg Verity.Core.Address.val prepared).symm
  have owner := caller_prepared_owner world pre warm agrees
    (MidnightInitcode.returnMemory (CreationBytecode.callerMemory pre) offset.toNat size.toNat)
  exact combined.trans (congrArg (fun sender =>
    (Create2.create2AddressFromPhysicalMemory (callerPreparedWorld world pre offset size)
      (Verity.Core.Uint256.ofNat offset.toNat) (Verity.Core.Uint256.ofNat size.toNat)
      (Verity.Core.Uint256.ofNat salt.toNat) sender).val) owner.symm)

/-- Raw account agreement derives the canonical legal nonce from the actual
native CREATE2 nonce guard; no separate canonical nonce certificate is supplied. -/
theorem caller_legal_nonce (world : Verity.ContractState) (pre : EVM.State)
    (warm : Create2Access.WarmAccounts) (agrees : Agreement world pre warm)
    (nonce : ¬ ((pre.accountMap.get? pre.executionEnv.codeOwner).getD default).nonce.toNat ≥ 2^64 - 1) :
    (world.creationAccounts pre.executionEnv.codeOwner.val).nonce < Create2NonceEntry.maxCreatorNonce := by
  have projected := congrArg Create2Accounts.Account.nonce (agrees.accounts pre.executionEnv.codeOwner)
  change (world.creationAccounts pre.executionEnv.codeOwner.val).nonce =
    ((pre.accountMap.get? pre.executionEnv.codeOwner).getD default).nonce.toNat at projected
  rw [projected]
  exact Nat.lt_of_not_ge nonce

/-- The canonical prepared operation reads the complete actual native window. -/
theorem caller_prepared_slice (world : Verity.ContractState) (pre : EVM.State)
    (allocated : CallerAllocated pre) (offset size : UInt256) (bounded : size.toNat ≤ 49152) :
    Create2.physicalInitcodeBytes (callerPreparedWorld world pre offset size)
      (Verity.Core.Uint256.ofNat offset.toNat).val (Verity.Core.Uint256.ofNat size.toNat).val =
      pre.memory.readWithPadding offset.toNat size.toNat := by
  have offsetValue : (Verity.Core.Uint256.ofNat offset.toNat).val = offset.toNat := Nat.mod_eq_of_lt offset.val.isLt
  have sizeValue : (Verity.Core.Uint256.ofNat size.toNat).val = size.toNat := Nat.mod_eq_of_lt size.val.isLt
  rw [offsetValue, sizeValue]
  exact prepared_physical_slice world pre allocated offset.toNat size.toNat bounded

/-- The same real child and reserved map determine canonical runEntered,
storage commit and complete raw world agreement of the actual parent step. -/
theorem native_create2_entered_world (world : Verity.ContractState) (pre next : EVM.State)
    (warm : Create2Access.WarmAccounts) (agrees : Agreement world pre warm)
    (payload : ByteArray) (bounded : payload.size ≤ 49152) (fuel cost : Nat)
    (rest : Stack UInt256) (offset size salt : UInt256) (enough : 10 ≤ fuel)
    (code : pre.memory.readWithPadding offset.toNat size.toNat = MidnightInitcode.initcode payload)
    (popped : pre.stack.pop4 = some (rest, UInt256.ofNat 0, offset, size, salt))
    (nonce : ¬ ((pre.accountMap.get? pre.executionEnv.codeOwner).getD default).nonce.toNat ≥ 2^64 - 1)
    (entry : UInt256.ofNat 0 ≤ (pre.accountMap.get? pre.executionEnv.codeOwner |>.option (UInt256.ofNat 0) (·.balance)) ∧
      pre.executionEnv.depth < 1024 ∧ (pre.memory.readWithPadding offset.toNat size.toNat).size ≤ 49152)
    (vacant : let target := nativeCreate2Target pre.executionEnv.codeOwner salt.toByteArray (MidnightInitcode.initcode payload)
      ((create2ChildEntry pre cost).accountMap.getD target default).nonce = UInt256.ofNat 0 ∧
      ((create2ChildEntry pre cost).accountMap.getD target default).code.size = 0)
    (stepped : EVM.step (fuel + 3) cost (some (.CREATE2, none)) pre = .ok next) :
    let target := nativeCreate2Target pre.executionEnv.codeOwner salt.toByteArray (MidnightInitcode.initcode payload)
    ∃ result reserved committed, nativeCreate2Child (fuel + 2) cost pre offset size salt = .ok result ∧
      Create2Callee.runEntered world.creationAccounts pre.executionEnv.codeOwner.val target.val payload
        (EVM.L (pre.gasAvailable - UInt256.ofNat cost).toNat) = .ok
          { outcome := constructorOutcome world.creationAccounts reserved pre.executionEnv.codeOwner target payload result.2.2.2.2.2.1
            gasLeft := result.2.2.2.1.toNat } ∧
      CreationStorage.commit world (constructorOutcome world.creationAccounts reserved pre.executionEnv.codeOwner
        target payload result.2.2.2.2.2.1) = .ok committed ∧
      Agreement committed next (Create2Access.warm warm target.val) ∧
      next.σ₀ = pre.σ₀ ∧ next.memory = pre.memory := by
  obtain ⟨result, reserved, completed, reservation, transport⟩ := native_create2_child_world
    world pre warm agrees payload bounded cost offset size salt code nonce vacant fuel enough
  obtain ⟨child, canonicalReserved, childCompleted, childReservation, entered⟩ := native_create2_child_entered
    world pre warm agrees payload bounded cost offset size salt code nonce vacant fuel enough
  have sameChild : child = result := Except.ok.inj (childCompleted.symm.trans completed)
  subst child
  have sameReserved : canonicalReserved = reserved := by injection childReservation.symm.trans reservation
  subst canonicalReserved
  have frames := native_create2_child_frame (fuel + 2) cost pre next rest offset size salt result
    popped nonce entry completed stepped
  let target := nativeCreate2Target pre.executionEnv.codeOwner salt.toByteArray (MidnightInitcode.initcode payload)
  exact ⟨result, reserved, _, completed, entered,
    constructor_outcome_commit world world.creationAccounts reserved pre.executionEnv.codeOwner target payload result.2.2.2.2.2.1,
    transport next frames.1 frames.2.2.2.1 frames.2.1, frames.2.2.2.2.1, frames.2.2.2.2.2⟩

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor

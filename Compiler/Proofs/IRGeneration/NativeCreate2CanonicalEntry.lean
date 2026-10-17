import Compiler.Proofs.IRGeneration.NativeCreate2CallerPreparation

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul NativeCreationWorld
open Verity.Core.Model

/-- Canonical entry consumes the actual complete constructor and actual target.
The reservation gate is derived from native nonce/vacancy guards. -/
theorem caller_enterCode_eq_runEntered (world : Verity.ContractState) (pre : EVM.State)
    (warm : Create2Access.WarmAccounts) (agrees : Agreement world pre warm) (allocated : CallerAllocated pre)
    (payload : ByteArray) (cost : Nat) (offset size salt : UInt256) (gas : Nat) (cap : size.toNat ≤ 49152)
    (code : pre.memory.readWithPadding offset.toNat size.toNat = MidnightInitcode.initcode payload)
    (nonce : ¬ ((pre.accountMap.get? pre.executionEnv.codeOwner).getD default).nonce.toNat ≥ 2^64 - 1)
    (vacant : let target := nativeCreate2Target pre.executionEnv.codeOwner salt.toByteArray (MidnightInitcode.initcode payload)
      ((create2ChildEntry pre cost).accountMap.getD target default).nonce = UInt256.ofNat 0 ∧
      ((create2ChildEntry pre cost).accountMap.getD target default).code.size = 0)
    (inner : ffi.KEC (pre.memory.readWithPadding offset.toNat size.toNat) =
      KeccakEngine.keccak256 (pre.memory.readWithPadding offset.toNat size.toNat))
    (outer : ffi.KEC (BE 255 ++ pre.executionEnv.codeOwner.toByteArray ++ salt.toByteArray ++
        ffi.KEC (pre.memory.readWithPadding offset.toNat size.toNat)) =
      KeccakEngine.keccak256 (BE 255 ++ pre.executionEnv.codeOwner.toByteArray ++ salt.toByteArray ++
        ffi.KEC (pre.memory.readWithPadding offset.toNat size.toNat))) :
    let prepared := callerPreparedWorld world pre offset size
    let target := nativeCreate2Target pre.executionEnv.codeOwner salt.toByteArray (MidnightInitcode.initcode payload)
    Create2Operation.enterCode prepared.creationAccounts prepared.thisAddress.val
      (Create2.create2AddressFromPhysicalMemory prepared (Verity.Core.Uint256.ofNat offset.toNat)
        (Verity.Core.Uint256.ofNat size.toNat) (Verity.Core.Uint256.ofNat salt.toNat) prepared.thisAddress).val
      (Create2.physicalInitcodeBytes prepared (Verity.Core.Uint256.ofNat offset.toNat).val
        (Verity.Core.Uint256.ofNat size.toNat).val) gas =
      Create2Callee.runEntered prepared.creationAccounts pre.executionEnv.codeOwner.val target.val payload gas := by
  dsimp only
  let prepared := callerPreparedWorld world pre offset size
  have agreement := caller_prepared_agreement world pre warm agrees offset size
  obtain ⟨reserved, reservation⟩ := native_create2_reservation prepared pre warm agreement payload cost salt nonce vacant
  have target := native_create2_prepared_address world pre warm agrees allocated offset size salt cap inner outer
  rw [code] at target
  have owner := caller_prepared_owner world pre warm agrees
    (MidnightInitcode.returnMemory (CreationBytecode.callerMemory pre) offset.toNat size.toNat)
  have ownerValue : prepared.thisAddress.val = pre.executionEnv.codeOwner.val := by
    rw [show prepared.thisAddress = Verity.Core.Address.ofNat pre.executionEnv.codeOwner.val from owner]
    exact Nat.mod_eq_of_lt pre.executionEnv.codeOwner.isLt
  rw [← target, caller_prepared_slice world pre allocated offset size cap, code, ownerValue]
  exact Create2Operation.enterCode_initcode _ _ _ payload gas reserved
    (caller_legal_nonce prepared pre warm agreement nonce) reservation

/-- Actual child execution determines canonical enterCode on the complete
prepared physical window. No chosen child outcome is supplied as a premise. -/
theorem native_create2_prepared_entered (world : Verity.ContractState) (pre : EVM.State)
    (warm : Create2Access.WarmAccounts) (agrees : Agreement world pre warm) (allocated : CallerAllocated pre)
    (payload : ByteArray) (bounded : payload.size ≤ 49152) (cost : Nat) (offset size salt : UInt256)
    (cap : size.toNat ≤ 49152)
    (code : pre.memory.readWithPadding offset.toNat size.toNat = MidnightInitcode.initcode payload)
    (nonce : ¬ ((pre.accountMap.get? pre.executionEnv.codeOwner).getD default).nonce.toNat ≥ 2^64 - 1)
    (vacant : let target := nativeCreate2Target pre.executionEnv.codeOwner salt.toByteArray (MidnightInitcode.initcode payload)
      ((create2ChildEntry pre cost).accountMap.getD target default).nonce = UInt256.ofNat 0 ∧
      ((create2ChildEntry pre cost).accountMap.getD target default).code.size = 0)
    (inner : ffi.KEC (pre.memory.readWithPadding offset.toNat size.toNat) =
      KeccakEngine.keccak256 (pre.memory.readWithPadding offset.toNat size.toNat))
    (outer : ffi.KEC (BE 255 ++ pre.executionEnv.codeOwner.toByteArray ++ salt.toByteArray ++
        ffi.KEC (pre.memory.readWithPadding offset.toNat size.toNat)) =
      KeccakEngine.keccak256 (BE 255 ++ pre.executionEnv.codeOwner.toByteArray ++ salt.toByteArray ++
        ffi.KEC (pre.memory.readWithPadding offset.toNat size.toNat))) (fuel : Nat) (enough : 10 ≤ fuel) :
    let prepared := callerPreparedWorld world pre offset size
    let target := nativeCreate2Target pre.executionEnv.codeOwner salt.toByteArray (MidnightInitcode.initcode payload)
    ∃ result reserved, nativeCreate2Child (fuel + 2) cost pre offset size salt = .ok result ∧
      Create2Operation.enterCode prepared.creationAccounts prepared.thisAddress.val
        (Create2.create2AddressFromPhysicalMemory prepared (Verity.Core.Uint256.ofNat offset.toNat)
          (Verity.Core.Uint256.ofNat size.toNat) (Verity.Core.Uint256.ofNat salt.toNat) prepared.thisAddress).val
        (Create2.physicalInitcodeBytes prepared (Verity.Core.Uint256.ofNat offset.toNat).val
          (Verity.Core.Uint256.ofNat size.toNat).val)
        (EVM.L (pre.gasAvailable - UInt256.ofNat cost).toNat) = .ok
          { outcome := constructorOutcome prepared.creationAccounts reserved pre.executionEnv.codeOwner target payload
              result.2.2.2.2.2.1, gasLeft := result.2.2.2.1.toNat } := by
  let prepared := callerPreparedWorld world pre offset size
  have agreement := caller_prepared_agreement world pre warm agrees offset size
  obtain ⟨result, reserved, child, reservation, entered⟩ := native_create2_child_entered
    prepared pre warm agreement payload bounded cost offset size salt code nonce vacant fuel enough
  have target := native_create2_prepared_address world pre warm agrees allocated offset size salt cap inner outer
  rw [code] at target
  have owner := caller_prepared_owner world pre warm agrees
    (MidnightInitcode.returnMemory (CreationBytecode.callerMemory pre) offset.toNat size.toNat)
  have ownerValue : prepared.thisAddress.val = pre.executionEnv.codeOwner.val := by
    rw [show prepared.thisAddress = Verity.Core.Address.ofNat pre.executionEnv.codeOwner.val from owner]
    exact Nat.mod_eq_of_lt pre.executionEnv.codeOwner.isLt
  refine ⟨result, reserved, child, ?_⟩
  rw [← target, caller_prepared_slice world pre allocated offset size cap, code, ownerValue]
  rw [Create2Operation.enterCode_initcode _ _ _ payload _ reserved
    (caller_legal_nonce prepared pre warm agreement nonce) reservation]
  exact entered

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor

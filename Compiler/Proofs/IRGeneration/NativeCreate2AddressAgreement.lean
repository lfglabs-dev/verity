import Compiler.Proofs.IRGeneration.NativeCreate2BigEndian
import Compiler.Keccak.SpongeProperties

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul
open Verity.Core.Model

private theorem native_hash_word (digest : ByteArray) :
    Verity.Core.Uint256.ofNat (UInt256.ofNat (fromByteArrayBigEndian digest)).toNat =
      Verity.Core.Uint256.ofNat (KeccakEngine.byteArrayToNatBE digest) := by
  apply Verity.Core.Uint256.ext
  rw [native_big_endian_decoder]
  change (fromByteArrayBigEndian digest % UInt256.size) % UInt256.size = _
  exact Nat.mod_mod _ _

/-- Actual native inner digest enters the canonical hashed-initcode preimage.
Only agreement at this particular primitive invocation is assumed. -/
theorem native_create2_preimage_hashed (sender : AccountAddress) (salt : UInt256)
    (init : ByteArray) (inner : ffi.KEC init = KeccakEngine.keccak256 init) :
    BE 255 ++ sender.toByteArray ++ salt.toByteArray ++ ffi.KEC init =
      ({ deployer := Verity.Core.Address.ofNat sender.val
         salt := Verity.Core.Uint256.ofNat salt.toNat
         initcodeHash := Verity.Core.Uint256.ofNat
           (KeccakEngine.byteArrayToNatBE (KeccakEngine.keccak256 init)) } : Create2.Preimage).bytes := by
  have sized : (ffi.KEC init).size = 32 := by rw [inner]; exact KeccakEngine.keccak256_size init
  have encoded := native_digest_preimage sender salt (ffi.KEC init) sized
  have canonicalWord := (native_hash_word (ffi.KEC init)).trans
    (congrArg (fun digest => Verity.Core.Uint256.ofNat (KeccakEngine.byteArrayToNatBE digest)) inner)
  exact encoded.trans (congrArg (fun word =>
    ({ deployer := Verity.Core.Address.ofNat sender.val
       salt := Verity.Core.Uint256.ofNat salt.toNat
       initcodeHash := word } : Create2.Preimage).bytes) canonicalWord)

/-- Complete native/canonical CREATE2 address agreement, conditional only on
pointwise agreement at the two real opaque Keccak calls. No primitive axiom. -/
theorem native_create2_address_agreement (sender : AccountAddress) (salt : UInt256)
    (init : ByteArray) (inner : ffi.KEC init = KeccakEngine.keccak256 init)
    (outer : ffi.KEC (BE 255 ++ sender.toByteArray ++ salt.toByteArray ++ ffi.KEC init) =
      KeccakEngine.keccak256 (BE 255 ++ sender.toByteArray ++ salt.toByteArray ++ ffi.KEC init)) :
    (nativeCreate2Target sender salt.toByteArray init).val =
      (Create2.create2Address (Verity.Core.Uint256.ofNat salt.toNat)
        (Verity.Core.Uint256.ofNat (KeccakEngine.byteArrayToNatBE (KeccakEngine.keccak256 init)))
        (Verity.Core.Address.ofNat sender.val)).val := by
  have sized : (ffi.KEC (BE 255 ++ sender.toByteArray ++ salt.toByteArray ++ ffi.KEC init)).size = 32 := by
    rw [outer]
    exact KeccakEngine.keccak256_size _
  have preimage := native_create2_preimage_hashed sender salt init inner
  have canonicalHash := outer.trans (congrArg KeccakEngine.keccak256 preimage)
  have decoded := (congrArg fromByteArrayBigEndian canonicalHash).trans
    (native_big_endian_decoder _).symm
  exact (native_create2_target_mod sender salt.toByteArray init sized).trans
    (congrArg (fun number => number % AccountAddress.size) decoded)

/-- Complete address agreement for the actual physical caller-memory slice.
The allocation invariant and both pointwise hash boundaries remain explicit. -/
theorem native_create2_physical_address (world : Verity.ContractState) (pre : EVM.State)
    (allocated : pre.memory.size ≤ pre.activeWords.toNat * 32)
    (offset size salt : UInt256) (bounded : size.toNat ≤ 49152)
    (inner : ffi.KEC (pre.memory.readWithPadding offset.toNat size.toNat) =
      KeccakEngine.keccak256 (pre.memory.readWithPadding offset.toNat size.toNat))
    (outer : ffi.KEC (BE 255 ++ pre.executionEnv.codeOwner.toByteArray ++ salt.toByteArray ++
        ffi.KEC (pre.memory.readWithPadding offset.toNat size.toNat)) =
      KeccakEngine.keccak256 (BE 255 ++ pre.executionEnv.codeOwner.toByteArray ++ salt.toByteArray ++
        ffi.KEC (pre.memory.readWithPadding offset.toNat size.toNat))) :
    (nativeCreate2Target pre.executionEnv.codeOwner salt.toByteArray
      (pre.memory.readWithPadding offset.toNat size.toNat)).val =
    (Create2.create2AddressFromPhysicalMemory
      (world.installPhysicalMemory (CreationBytecode.callerMemory pre))
      (Verity.Core.Uint256.ofNat offset.toNat) (Verity.Core.Uint256.ofNat size.toNat)
      (Verity.Core.Uint256.ofNat salt.toNat) (Verity.Core.Address.ofNat pre.executionEnv.codeOwner.val)).val := by
  have offsetValue : (Verity.Core.Uint256.ofNat offset.toNat).val = offset.toNat :=
    Nat.mod_eq_of_lt offset.val.isLt
  have sizeValue : (Verity.Core.Uint256.ofNat size.toNat).val = size.toNat :=
    Nat.mod_eq_of_lt size.val.isLt
  have slice := caller_physical_slice world pre allocated offset.toNat size.toNat bounded
  have address := native_create2_address_agreement pre.executionEnv.codeOwner salt
    (pre.memory.readWithPadding offset.toNat size.toNat) inner outer
  unfold Create2.create2AddressFromPhysicalMemory
  rw [offsetValue, sizeValue]
  exact address.trans (congrArg (fun bytes =>
    (Create2.create2Address (Verity.Core.Uint256.ofNat salt.toNat)
      (Verity.Core.Uint256.ofNat (KeccakEngine.byteArrayToNatBE (KeccakEngine.keccak256 bytes)))
      (Verity.Core.Address.ofNat pre.executionEnv.codeOwner.val)).val) slice.symm)

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor

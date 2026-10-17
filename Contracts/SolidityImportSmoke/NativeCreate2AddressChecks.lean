import Contracts.SolidityImportSmoke.NativeMidnightSourceChecks
import Contracts.SolidityImportSmoke.NativeHashedDenoteChecks
import Contracts.SolidityImportSmoke.NativeHashedCallerChecks
import Contracts.SolidityImportSmoke.NativeMappingHelperChecks
import Compiler.Proofs.IRGeneration.NativeSourceMappingExecution
import Compiler.Proofs.IRGeneration.NativeSourceStorageBytecode
import Compiler.Proofs.IRGeneration.NativeMappingKeccak
import Compiler.Proofs.IRGeneration.NativeMappingStorageExecution

namespace SolidityImportSmoke.NativeCreate2AddressChecks
open EvmYul
open Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open Verity.Core.Model

/-- Compare the actual opaque native hash boundary with the independent pure
kernel engine, all preimage bytes, and the complete resulting CREATE2 address. -/
def runChecks : IO Unit := do
  let payloads : List ByteArray := [ByteArray.empty, ⟨#[0x00]⟩, ⟨#[0xef]⟩,
    ⟨Array.replicate 33 0x42⟩, ⟨Array.replicate 49141 0x00⟩, ⟨#[0x01, 0x80, 0xff]⟩]
  let senders := [0, 8193, 2^160 - 1]
  let salts := [0, 23, 2^256 - 1]
  for sender in senders do
    let nativeSender : AccountAddress := Fin.ofNat _ sender
    let canonicalSender := Verity.Core.Address.ofNat sender
    unless nativeSender.toByteArray == Create2.addressBytes canonicalSender do
      throw (IO.userError s!"CREATE2 sender encoding differs: {sender}")
    for salt in salts do
      let nativeSalt : UInt256 := .ofNat salt
      let canonicalSalt := Verity.Core.Uint256.ofNat salt
      unless nativeSalt.toByteArray == Create2.wordBytes canonicalSalt do
        throw (IO.userError s!"CREATE2 salt encoding differs: {salt}")
      for payload in payloads do
        let init := MidnightInitcode.initcode payload
        let nativeInner := ffi.KEC init
        let kernelInner := KeccakEngine.keccak256 init
        unless nativeInner.size == 32 && nativeInner == kernelInner do
          throw (IO.userError s!"CREATE2 inner hash differs: size={payload.size}")
        let hashWord := Verity.Core.Uint256.ofNat (KeccakEngine.byteArrayToNatBE kernelInner)
        let canonicalPreimage := ({
          deployer := canonicalSender
          salt := canonicalSalt
          initcodeHash := hashWord } : Create2.Preimage).bytes
        let nativePreimage := BE 255 ++ nativeSender.toByteArray ++ nativeSalt.toByteArray ++ nativeInner
        unless nativePreimage.size == 85 && nativePreimage == canonicalPreimage do
          throw (IO.userError s!"CREATE2 preimage differs: sender={sender} salt={salt} size={payload.size}")
        let nativeOuter := ffi.KEC nativePreimage
        let kernelOuter := KeccakEngine.keccak256 canonicalPreimage
        unless nativeOuter.size == 32 && nativeOuter == kernelOuter do
          throw (IO.userError "CREATE2 outer hash differs")
        let target := nativeCreate2Target nativeSender nativeSalt.toByteArray init
        let expected := Create2.create2Address canonicalSalt hashWord canonicalSender
        unless target.val == expected.val do
          throw (IO.userError "CREATE2 address truncation differs")
        let wrong := ffi.KEC (BE 255 ++ nativeSender.toByteArray ++ nativeSalt.toByteArray ++ init)
        unless wrong != nativeOuter do
          throw (IO.userError "CREATE2 raw-initcode mutation not distinguished")
  IO.println "native create2 address:54 cases,two hashes,exact preimage,full address,raw-initcode sentinel"

end SolidityImportSmoke.NativeCreate2AddressChecks

def main : IO Unit := do
  MidnightSourceCaller.runChecks false
  SolidityImportSmoke.NativeHashedDenoteChecks.runChecks
  SolidityImportSmoke.NativeHashedCallerChecks.runChecks
  SolidityImportSmoke.NativeMappingHelperChecks.runChecks
  SolidityImportSmoke.NativeCreate2AddressChecks.runChecks

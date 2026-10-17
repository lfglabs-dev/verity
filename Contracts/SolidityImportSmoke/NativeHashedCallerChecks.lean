import Compiler.Proofs.IRGeneration.NativeHashedWorldCaller

namespace SolidityImportSmoke.NativeHashedCallerChecks
open EvmYul Compiler.Proofs.IRGeneration.NativeCreationWorld
open Compiler.Proofs.IRGeneration.NativeCreationWorldCaller
open Compiler.Proofs.IRGeneration.NativeMidnightConstructor
private def owner : AccountAddress := AccountAddress.ofUInt256 (.ofNat 8193)
private def initial (code : ByteArray) (gas : Nat) (stack : Stack UInt256) : Frame :=
  let entry := ({ (Inhabited.default : Account .EVM) with code := code }).updateStorage (.ofNat 7) (.ofNat 23)
  let accounts := (Inhabited.default : AccountMap .EVM).insert owner entry
  { world := ({ Verity.defaultState with
      thisAddress := Verity.Core.Address.ofNat 8193
      creationAccounts := fun address => if address == 8193 then { code := code } else {}
      codeSize := fun address => if address == 8193 then Verity.Core.Uint256.ofNat code.size else 0
    }).writeSlot 7 (Verity.Core.Uint256.ofNat 23)
    warm := fun address => address == 8193
    machine := { (Inhabited.default : EVM.State) with
      accountMap := accounts
      σ₀ := accounts
      gasAvailable := .ofNat gas
      stack := stack
      executionEnv := { (Inhabited.default : ExecutionEnv .EVM) with codeOwner := owner, code := code, perm := true }
      substate := { (Inhabited.default : Substate) with
        accessedAccounts := (Inhabited.default : Substate).accessedAccounts.insert owner } } }

private def persistentReference : ByteArray := ⟨#[0x60, 0x63, 0x60, 0x07, 0x55, 0x7f, 0x60, 0x0b, 0x38, 0x03, 0x80, 0x60, 0x0b, 0x5f, 0x39, 0x5f, 0xf3, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x5f, 0x52, 0x60, 0x07, 0x60, 0x0b, 0x5f, 0x5f, 0xf5, 0x5f, 0x52, 0x60, 0x20, 0x5f, 0xf3]⟩

def runChecks : IO Unit := do
  let mut count := 0
  for key in [0, 1, 255, 65537] do
    for base in [0, 7] do
      for transient in [false, true] do
        let hashPrefix : ByteArray := ⟨#[0x7f]⟩ ++ (UInt256.ofNat key).toByteArray ++ ⟨#[0x5f, 0x52,
          0x60, UInt8.ofNat base, 0x60, 0x20, 0x52, 0x60, 0x40, 0x5f, 0x20,
          0x60, 0x63, 0x90, if transient then 0x5d else 0x55]⟩
        let code := hashPrefix ++ persistentReference.extract 5 persistentReference.size
        let before := initial code 1000000 []
        let boundary ← match Compiler.Proofs.IRGeneration.NativeHashedWorldCaller.run 80 before with
          | .ok (.ready frame) => pure frame
          | _ => throw (IO.userError "hash prefix failed")
        let slot := uInt256OfByteArray
          (KeccakEngine.keccak256 (Compiler.Proofs.abiEncodeMappingSlot
            base key))
        let stored := if transient then transientWord boundary.machine owner slot
          else persistentWord boundary.machine owner slot
        let modeled := if transient then boundary.world.transientStorage slot.toNat
          else boundary.world.readSlot slot.toNat
        unless stored.val == 99 && modeled.val == 99 && boundary.machine.pc.toNat == code.size - 7 do
          throw (IO.userError "hash prefix storage/PC mismatch")
        let computed ← match Compiler.Proofs.IRGeneration.CreationBytecode.execReady boundary with
          | .ok (.continued frame) => pure frame
          | _ => throw (IO.userError "hash prefix canonical creation failed")
        let native ← match EVM.step 30 (EVM.C' (create2MemoryDebited boundary.machine) .CREATE2)
            (some (.CREATE2, none)) (create2MemoryDebited boundary.machine) with
          | .ok machine => pure machine
          | _ => throw (IO.userError "hash prefix native creation failed")
        let result ← match native.stack with
          | address :: _ => pure address
          | _ => throw (IO.userError "creation omitted address")
        unless native.stack == computed.machine.stack && native.pc == computed.machine.pc &&
            native.gasAvailable == computed.machine.gasAvailable && native.memory == computed.machine.memory &&
            (computed.world.creationAccounts result.toNat).nonce == 1 &&
            (creationAccount native (AccountAddress.ofUInt256 result)).nonce == 1 &&
            (rawLogs native).isEmpty && native.returnData.isEmpty &&
            (if transient then transientWord native owner slot else persistentWord native owner slot).val == 99 do
          throw (IO.userError "hash prefix native/canonical creation mismatch")
        match EVM.X 120 (EVM.D_J code (UInt256.ofNat 0)) before.machine with
        | .ok (.success final output) =>
          unless output == result.toByteArray &&
              (if transient then transientWord final owner slot else persistentWord final owner slot).val == 99 do
            throw (IO.userError "whole native iterator mismatch")
        | _ => throw (IO.userError "whole native iterator failed")
        count := count + 1
  for opcode in [0x3b, 0x3c, 0xf1, 0xa1] do
    match Compiler.Proofs.IRGeneration.NativeHashedWorldCaller.run 2 (initial ⟨#[opcode,0xf5]⟩ 1000000 []) with
    | .error _ => pure ()
    | _ => throw (IO.userError "unsupported neighbor admitted")
  match Compiler.Proofs.IRGeneration.NativeHashedWorldCaller.run 2 (initial ⟨#[0x20,0xf5]⟩ 1000000 []) with
  | .ok (.exceptional .StackUnderflow frame) =>
    unless frame.machine.gasAvailable.toNat == 0 do throw (IO.userError "hash underflow gas retained")
  | _ => throw (IO.userError "hash underflow status changed")
  IO.println s!"HASHED_CREATION_SUCCESS: {count} storage/creation/native-iterator comparisons; 5 refusals"
end SolidityImportSmoke.NativeHashedCallerChecks

import Contracts.SolidityImportSmoke.ImportedCreationPrefixFrames
import Compiler.Proofs.IRGeneration.NativeSourceEntryWrite
import Compiler.Proofs.IRGeneration.NativeSourceAbiInputs

namespace Contracts.SolidityImportSmoke.ImportedCreationPrefixRelation
open EvmYul Compiler.CompilationModel
open Compiler.Proofs.IRGeneration
open CreationMemoryFrames NativeSourceEntryWrite

/-- The actual imported prefix's whole nonmemory effect, using the pure mapping
oracle and original ABI words; no interpreter result is evaluated in the kernel. -/
theorem imported_world (oracle : Denote.DenoteOracle)
    (mapping : oracle.mappingSlot = Compiler.Proofs.solidityMappingSlot)
    (fn : FunctionSpec) (shape : ImportedCreationPrefixFrames.imported.model.functions = [fn])
    (initial final : Denote.DenoteState) (offset key value : Nat) (rest : List Nat)
    (args : initial.world.calldata = offset :: key :: value :: rest)
    (executed : Denote.execStmtList oracle
      (Denote.effectiveFields ImportedCreationPrefixFrames.imported.model) initial fn.body.dropLast = .continue final) :
    eraseMemory final.world = (eraseMemory initial.world).writeSlot
      (Compiler.Proofs.solidityMappingSlot 0 (key % Compiler.Constants.evmModulus))
      (Verity.Core.Uint256.ofNat (value % Compiler.Constants.evmModulus)) := by
  have actual := ImportedCreationPrefixFrames.actual_prefix_abi_effect oracle fn shape initial final executed
  rw [mapping, args] at actual
  have slot := Compiler.Proofs.solidityMappingSlot_lt_evmModulus 0 (key % Compiler.Constants.evmModulus)
  simpa only [List.getD_cons_succ, List.getD_cons_zero, Denote.wordNormalize, Verity.Core.Uint256.ofNat, Verity.Core.Uint256.modulus,
    Verity.Core.UINT256_MODULUS,
    Nat.mod_eq_of_lt slot] using actual

/-- Independently executed original source entry and imported prefix perform the
same complete nonmemory write. All native intermediates come from entryWrite. -/
theorem entry_imported_world (oracle : Denote.DenoteOracle)
    (mapping : oracle.mappingSlot = Compiler.Proofs.solidityMappingSlot)
    (fn : FunctionSpec) (shape : ImportedCreationPrefixFrames.imported.model.functions = [fn])
    (initial final : Denote.DenoteState) (offset key value : Nat) (rest : List Nat)
    (args : initial.world.calldata = offset :: key :: value :: rest)
    (executed : Denote.execStmtList oracle
      (Denote.effectiveFields ImportedCreationPrefixFrames.imported.model) initial fn.body.dropLast = .continue final)
    (fuel : Nat) (native after : EVM.State)
    (warm : Verity.Core.Model.Create2Access.WarmAccounts) (account : Account .EVM)
    (code : native.executionEnv.code = NativeSourceAbiWrite.code)
    (present : native.toState.lookupAccount native.executionEnv.codeOwner = some account)
    (encoded : native.executionEnv.calldata = Compiler.Proofs.YulGeneration.Backends.StateBridge.calldataToByteArray
      initial.selector initial.world.calldata)
    (success : entryWrite fuel native = .ok after)
    (hash : ffi.KEC (Compiler.Proofs.abiEncodeMappingSlot 0 (key % Compiler.Constants.evmModulus)) =
      KeccakEngine.keccak256 (Compiler.Proofs.abiEncodeMappingSlot 0 (key % Compiler.Constants.evmModulus))) :
    ∃ ready middle written, runTo (UInt256.ofNat 404) fuel native = .ok ready ∧
      CapturedMappingHelper.checkedSteps 12 ready = .ok middle ∧
      CreationCaller.checkedStep middle .SSTORE none = .ok after ∧
      NativeCreationWorldCaller.worldAfter ⟨initial.world, middle, warm⟩ .SSTORE = .ok written ∧
      Related final.world written := by
  have inputs := NativeSourceAbiInputs.encoded_mapping_arguments native initial.selector offset key value rest
    (by simpa only [args] using encoded)
  have hashNative : ffi.KEC (Compiler.Proofs.abiEncodeMappingSlot 0
      (native.toState.calldataload (UInt256.ofNat 36)).toNat) =
        KeccakEngine.keccak256 (Compiler.Proofs.abiEncodeMappingSlot 0
          (native.toState.calldataload (UInt256.ofNat 36)).toNat) := by rw [inputs.1]; exact hash
  obtain ⟨ready, middle, entry, steps, stored, effect⟩ :=
    entryWrite_paired initial.world fuel native after warm account code present success hashNative
  rw [inputs.1, inputs.2] at effect
  refine ⟨ready, middle, _, entry, steps, stored, effect, ?_⟩
  change eraseMemory final.world = eraseMemory (initial.world.writeSlot _ _)
  rw [ImportedMappingEffect.erase_write]
  exact imported_world oracle mapping fn shape initial final offset key value rest args executed

end Contracts.SolidityImportSmoke.ImportedCreationPrefixRelation

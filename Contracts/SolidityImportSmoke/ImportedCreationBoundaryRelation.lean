import Contracts.SolidityImportSmoke.ImportedCreationPrefixRelation
import Compiler.Proofs.IRGeneration.NativePrefixWorld

namespace Contracts.SolidityImportSmoke.ImportedCreationBoundaryRelation
open EvmYul Compiler.CompilationModel
open Compiler.Proofs.IRGeneration
open CreationMemoryFrames NativeCreationWorldCaller

/-- Independent imported execution and the actual existing source-prefix runner
reach CREATE2 with equal ENTIRE nonmemory worlds, retaining their own memories.
Both worlds start from the same original transaction world, not a native result. -/
theorem boundary_world (oracle : Denote.DenoteOracle)
    (mapping : oracle.mappingSlot = Compiler.Proofs.solidityMappingSlot)
    (fn : FunctionSpec) (shape : ImportedCreationPrefixFrames.imported.model.functions = [fn])
    (initial final : Denote.DenoteState) (offset key value : Nat) (rest : List Nat)
    (args : initial.world.calldata = offset :: key :: value :: rest)
    (executed : Denote.execStmtList oracle
      (Denote.effectiveFields ImportedCreationPrefixFrames.imported.model) initial fn.body.dropLast = .continue final)
    (entryFuel suffixFuel : Nat) (native : EVM.State) (boundary : Frame)
    (warm : Verity.Core.Model.Create2Access.WarmAccounts) (account : Account .EVM)
    (code : native.executionEnv.code = NativeSourceAbiWrite.code)
    (present : native.toState.lookupAccount native.executionEnv.codeOwner = some account)
    (encoded : native.executionEnv.calldata = Compiler.Proofs.YulGeneration.Backends.StateBridge.calldataToByteArray
      initial.selector initial.world.calldata)
    (success : NativePrefixComposition.execute entryFuel suffixFuel ⟨initial.world, native, warm⟩ = .ok (.ready boundary))
    (hash : ffi.KEC (Compiler.Proofs.abiEncodeMappingSlot 0 (key % Compiler.Constants.evmModulus)) =
      KeccakEngine.keccak256 (Compiler.Proofs.abiEncodeMappingSlot 0 (key % Compiler.Constants.evmModulus))) :
    ∃ steps, steps < entryFuel ∧
      NativeHashedWorldCaller.run (steps + 13 + suffixFuel) ⟨initial.world, native, warm⟩ = .ok (.ready boundary) ∧
      Related final.world boundary.world := by
  have inputs := NativeSourceAbiInputs.encoded_mapping_arguments native initial.selector offset key value rest
    (by simpa only [args] using encoded)
  have hashNative : ffi.KEC (Compiler.Proofs.abiEncodeMappingSlot 0
      (native.toState.calldataload (UInt256.ofNat 36)).toNat) =
        KeccakEngine.keccak256 (Compiler.Proofs.abiEncodeMappingSlot 0
          (native.toState.calldataload (UInt256.ofNat 36)).toNat) := by rw [inputs.1]; exact hash
  have effect := NativePrefixWorld.execute_world entryFuel suffixFuel ⟨initial.world, native, warm⟩ boundary
    account code present success hashNative
  obtain ⟨steps, bound, sameRun⟩ := NativePrefixComposition.execute_run entryFuel suffixFuel _ boundary success
  refine ⟨steps, bound, sameRun, ?_⟩
  change eraseMemory final.world = eraseMemory boundary.world
  rw [effect, ImportedMappingEffect.erase_write]
  simp only [inputs.1, inputs.2]
  exact ImportedCreationPrefixRelation.imported_world oracle mapping fn shape initial final offset key value rest args executed

end Contracts.SolidityImportSmoke.ImportedCreationBoundaryRelation

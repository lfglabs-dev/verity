import Contracts.Smoke.EcmFailurePayloadSmoke
import Compiler.Modules.Hashing

namespace Contracts.Smoke.EcmFidelitySmoke

open Verity Contracts Contracts.Smoke

-- The EDSL ECM call sees the callee the compiled Yul calls.

/-- Every call succeeds, answering its own `CallSite.target`. -/
def targetEchoAdversary : Compiler.CompilationModel.DenoteExternalCalls.AdversaryModel where
  stateTransition := fun _ s => s
  result := fun site _ => .success [site.target]
  gasUsed := fun _ _ => 0

def ctx : ExecutableCallContext := .ofAdversary targetEchoAdversary

/-- The ecrecover module calls the precompile at `address(1)` (`fixedTarget`), as its
compiled `staticcall(gas(), 1, …)` does; without it the call site recorded target 0. -/
example :
    (match EcmFailurePayloadSmoke.recover ctx 1 27 2 3 Verity.defaultState with
      | .success signer _ => some signer
      | .revert _ _ => none) = some 1 := by
  rfl

/-- The callee of each precompile module is its precompile address. -/
example :
    (Compiler.Modules.Precompiles.ecrecoverModule "r").callTarget [] = 1 ∧
      (Compiler.Modules.Precompiles.sha256MemoryModule "r").callTarget [] = 2 ∧
      (Compiler.Modules.Precompiles.bn256AddModule "x" "y").callTarget [] = 6 ∧
      (Compiler.Modules.Precompiles.bn256ScalarMulModule "x" "y").callTarget [] = 7 ∧
      (Compiler.Modules.Precompiles.bn256PairingModule "r").callTarget [] = 8 ∧
      (Compiler.Modules.Hashing.sha256PackedWordsModule "r" 1).callTarget [] = 2 ∧
      (Compiler.Modules.Hashing.sha256PackedStaticSegmentsModule "r" [32]).callTarget [] = 2 ∧
      (Compiler.ECM.eip712EcrecoverModule "r").callTarget [] = 1 := by
  decide

end Contracts.Smoke.EcmFidelitySmoke

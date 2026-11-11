import Compiler.Proofs.EndToEnd.SimpleStorage
import Compiler.Proofs.EndToEnd.ObsBridge
import Compiler.Proofs.YulGeneration.BytecodeTranslationValidation

/-!
End-to-end proof facade.

Bridge coverage audit: replacement coverage: universal bridge lemmas for all
pure bridged builtins.
-/

namespace Compiler.Proofs.EndToEnd

open Compiler.Proofs.YulGeneration.BytecodeTranslationValidation

/-- End-to-end TCB reduction: a `Codegen`-emitted `YulObject` together with a
    post-`solc` `BytecodeTranslationCertificate` whose frozen helper table and
    bytecode blocks are validated by `checkCodegenBytecodeBridge`. -/
abbrev EndToEndBytecodeClosure := CodegenBytecodeBridge

/-- **Theorem E2E.1 (`checkCodegenBytecodeBridge` Soundness at the End-to-End Facade)**:
    Re-exports `checkCodegenBytecodeBridge_sound` so Layer 3 consumers can close the
    Yul-to-EVM translation obligation without importing the validator module directly. -/
theorem endToEndBytecodeClosure_sound
    (bridge : EndToEndBytecodeClosure)
    (hok : checkCodegenBytecodeBridge bridge = true)
    (blk : BytecodeBlockCert)
    (hmem : blk ∈ bridge.translation.blocks) :
    bridge.yulFunctionTable = extractYulFunctionTable bridge.yulObject ∧
    blk.entryPc < blk.exitPc ∧
    blk.evmSlicePostDigest = blk.yulBlockPostDigest ∧
    (blk.requiresJumpdestEntry = true →
      isValidJumpdestList bridge.translation.bytecode blk.entryPc = true) :=
  checkCodegenBytecodeBridge_sound bridge hok blk hmem

end Compiler.Proofs.EndToEnd

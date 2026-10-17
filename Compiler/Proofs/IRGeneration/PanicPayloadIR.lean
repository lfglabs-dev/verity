import Compiler.Proofs.IRGeneration.IRInterpreter
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanBridgeLemmas

/-!
# Abstract IR memory/revert result for Panic(uint256) (#1999)

The compiler owns panic emission (`solidityPanicPayload` in
`Compiler/CompilationModel/DynamicData.lean`); this module supplies the
matching abstract IR result: the emitted statements deterministically revert
after storing selector `0x4e487b71 << 224` at offset 0 and the panic code
at offset 4, retaining the complete physical poststate. This interpreter does not retain revert offsets, lengths, or returned
bytes. `PanicPayloadBytes` separately proves the actual 36-byte payload using
EVMYulLean's byte-addressed memory operations and the emitted Yul AST.
-/
namespace Compiler.Proofs.IRGeneration

open Compiler.Yul
open Compiler.CompilationModel

/-- The 32-byte word holding the left-aligned `Panic(uint256)` selector. -/
def panicSelectorWord : Nat := 0x4e487b71 * 2 ^ 224

/-- Exact physical world after the two overlapping panic stores. Revert
bytes remain the separate native observation in `PanicPayloadBytes`. -/
def panicPayloadState (state : IRState) (code : Nat) : IRState :=
  (state.writePhysicalMemoryValue 0 panicSelectorWord).writePhysicalMemoryValue 4 code

/-- The emitted panic sequence updates actual bytes and every overlapping word
window before reverting; it does not leave unrelated word-map entries frozen. -/
theorem execIRStmts_solidityPanicPayload (fuel : Nat) (state : IRState)
    (code : Nat) (hcode : code < Compiler.Constants.evmModulus) :
    execIRStmts (fuel + 4) state (solidityPanicPayload code) =
      .revert (panicPayloadState state code) := by
  have offset : 4 % Compiler.Constants.evmModulus = 4 := by decide
  have offsetWord : 4 % Verity.Core.Uint256.modulus = 4 := by decide
  have selector :
      (if 224 % Compiler.Constants.evmModulus < 256 then
        0x4e487b71 * 2 ^ (224 % Compiler.Constants.evmModulus) % Compiler.Constants.evmModulus
       else 0) = panicSelectorWord := by decide
  simp [solidityPanicPayload, solidityPanicPayloadExpr, execIRStmts, execIRStmt,
    evalIRExpr, evalIRCall, evalIRExprs,
    YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
    panicPayloadState, offset, offsetWord, selector]

/-- The arithmetic-overflow panic retains its complete physical poststate. -/
theorem execIRStmts_arithmeticOverflowPanicPayload (fuel : Nat) (state : IRState) :
    execIRStmts (fuel + 4) state
        (solidityPanicPayload Verity.Core.PanicCode.arithmeticOverflow.toNat) =
      .revert (panicPayloadState state 0x11) := by
  simpa using execIRStmts_solidityPanicPayload fuel state 0x11 (by decide)

/-- The division-by-zero panic retains its complete physical poststate. -/
theorem execIRStmts_divisionByZeroPanicPayload (fuel : Nat) (state : IRState) :
    execIRStmts (fuel + 4) state
        (solidityPanicPayload Verity.Core.PanicCode.divisionByZero.toNat) =
      .revert (panicPayloadState state 0x12) := by
  simpa using execIRStmts_solidityPanicPayload fuel state 0x12 (by decide)

end Compiler.Proofs.IRGeneration

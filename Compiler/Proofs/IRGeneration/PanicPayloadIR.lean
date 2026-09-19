import Compiler.Proofs.IRGeneration.IRInterpreter
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanBridgeLemmas

/-!
# Abstract IR memory/revert result for Panic(uint256) (#1999)

The compiler owns panic emission (`solidityPanicPayload` in
`Compiler/CompilationModel/DynamicData.lean`); this module supplies the
matching abstract IR result: the emitted statements deterministically revert
with selector word `0x4e487b71 << 224` at memory offset 0 and the panic code at
offset 4. This interpreter does not retain revert offsets, lengths, or returned
bytes. `PanicPayloadBytes` separately proves the actual 36-byte payload using
EVMYulLean's byte-addressed memory operations and the emitted Yul AST.
-/
namespace Compiler.Proofs.IRGeneration

open Compiler.Yul
open Compiler.CompilationModel

/-- The 32-byte word holding the left-aligned `Panic(uint256)` selector. -/
def panicSelectorWord : Nat := 0x4e487b71 * 2 ^ 224

/-- The emitted panic sequence reverts with the selector word at abstract
memory entry 0 and the code at entry 4; other entries are unchanged.
This result does not describe the returned byte array. -/
theorem execIRStmts_solidityPanicPayload (fuel : Nat) (state : IRState)
    (code : Nat) (hcode : code < Compiler.Constants.evmModulus) :
    execIRStmts (fuel + 4) state (solidityPanicPayload code) =
      .revert { state with
        memory := fun o =>
          if o = 4 then code
          else if o = 0 then panicSelectorWord
          else state.memory o } := by
  simp [solidityPanicPayload, solidityPanicPayloadExpr, execIRStmts, execIRStmt,
    evalIRExpr, evalIRCall, evalIRExprs,
    YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
    panicSelectorWord, Nat.mod_eq_of_lt hcode]
  funext o
  by_cases h4 : o = 4
  · simp [h4]
  · by_cases h0 : o = 0
    · have h224 : (224 : Nat) % Compiler.Constants.evmModulus = 224 := by decide
      simp [h4, h0, h224]
    · simp [h4, h0]

/-- A typed arithmetic-overflow panic reverts with code `0x11` in abstract
memory; all entries other than 0 and 4 are preserved. -/
theorem execIRStmts_arithmeticOverflowPanicPayload (fuel : Nat) (state : IRState) :
    execIRStmts (fuel + 4) state
        (solidityPanicPayload Verity.Core.PanicCode.arithmeticOverflow.toNat) =
      .revert { state with
        memory := fun o =>
          if o = 4 then 0x11
          else if o = 0 then panicSelectorWord
          else state.memory o } := by
  simpa using execIRStmts_solidityPanicPayload fuel state 0x11 (by decide)

/-- A typed division-by-zero panic reverts with code `0x12` (`18`) in abstract
memory; all entries other than 0 and 4 are preserved. -/
theorem execIRStmts_divisionByZeroPanicPayload (fuel : Nat) (state : IRState) :
    execIRStmts (fuel + 4) state
        (solidityPanicPayload Verity.Core.PanicCode.divisionByZero.toNat) =
      .revert { state with
        memory := fun o =>
          if o = 4 then 0x12
          else if o = 0 then panicSelectorWord
          else state.memory o } := by
  simpa using execIRStmts_solidityPanicPayload fuel state 0x12 (by decide)

end Compiler.Proofs.IRGeneration

import Compiler.Proofs.IRGeneration.IRInterpreter
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanBridgeLemmas

/-!
# Proof-side observable for the built-in Panic(uint256) payload (#1999)

The compiler owns panic emission (`solidityPanicPayload` in
`Compiler/CompilationModel/DynamicData.lean`); this module supplies the
matching proof-side revert observable: under the IR interpreter, the emitted
statements deterministically revert with the exact Solidity ABI panic payload
laid out in memory — selector word `0x4e487b71 << 224` at offset 0 and the
panic code at offset 4 — for every code and every starting state.
-/
namespace Compiler.Proofs.IRGeneration

open Compiler.Yul
open Compiler.CompilationModel

/-- The 32-byte word holding the left-aligned `Panic(uint256)` selector. -/
def panicSelectorWord : Nat := 0x4e487b71 * 2 ^ 224

/-- The emitted panic sequence reverts with the canonical payload in memory:
selector word at offset 0, code at offset 4, nothing else changed. -/
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

end Compiler.Proofs.IRGeneration

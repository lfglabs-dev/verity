import Compiler.Proofs.IRGeneration.ErrorStringPayloadIR

/-!
# Memory-insensitive expression evaluation (event lane)

Event payload emission interleaves memory writes with value expressions
(`normalizeEventWord ty argExpr` — masks and sign-extensions over variables).
To move those evaluations across the payload's `mstore`s, this module proves
that expressions avoiding the two memory-reading builtins (`mload`,
`keccak256`) evaluate identically under any memory: every other evaluation
path reads variables, storage, transient storage, calldata, or the
environment — never `state.memory`.
-/
namespace Compiler.Proofs.IRGeneration

open Compiler.Yul

mutual

/-- Expressions whose evaluation never reads memory. -/
def MemInsensitiveExpr : YulExpr → Prop
  | .lit _ => True
  | .hex _ => True
  | .str _ => True
  | .ident _ => True
  | .call f args =>
      f ≠ "mload" ∧ f ≠ "keccak256" ∧ MemInsensitiveExprs args

def MemInsensitiveExprs : List YulExpr → Prop
  | [] => True
  | e :: rest => MemInsensitiveExpr e ∧ MemInsensitiveExprs rest

end

mutual

/-- Memory-insensitive expressions evaluate identically under any memory. -/
theorem evalIRExpr_mem_insensitive :
    ∀ (e : YulExpr), MemInsensitiveExpr e → ∀ (state : IRState) (m : Nat → Nat),
      evalIRExpr { state with memory := m } e = evalIRExpr state e
  | .lit _, _, _, _ => by simp [evalIRExpr]
  | .hex _, _, _, _ => by simp [evalIRExpr]
  | .str _, _, _, _ => by simp [evalIRExpr]
  | .ident _, _, _, _ => by simp [evalIRExpr, IRState.getVar]
  | .call f args, h, state, m => by
      obtain ⟨hml, hkec, hargs⟩ := h
      simp only [evalIRExpr]
      rw [evalIRCall, evalIRCall,
        evalIRExprs_mem_insensitive args hargs state m]
      cases hv : evalIRExprs state args with
      | none => simp
      | some argVals => simp [hml, hkec]

theorem evalIRExprs_mem_insensitive :
    ∀ (es : List YulExpr), MemInsensitiveExprs es →
      ∀ (state : IRState) (m : Nat → Nat),
        evalIRExprs { state with memory := m } es = evalIRExprs state es
  | [], _, _, _ => by simp [evalIRExprs]
  | e :: rest, h, state, m => by
      obtain ⟨he, hrest⟩ := h
      simp only [evalIRExprs]
      rw [evalIRExpr_mem_insensitive e he state m,
        evalIRExprs_mem_insensitive rest hrest state m]

end

end Compiler.Proofs.IRGeneration

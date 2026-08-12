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

/-- Pointer-offset stores with memory-insensitive expression values: the block
executes to its evaluated writes applied at the pointer, evaluations taken in
the initial state (the values commute with the block's own writes). -/
theorem execIRStmts_mstore_ptr_expr_block (ptrName : String) (p : Nat) :
    ∀ (stores : List (Nat × YulExpr)) (vals : List Nat) (fuel : Nat)
      (state : IRState),
      state.getVar ptrName = some p →
      MemInsensitiveExprs (stores.map (·.2)) →
      evalIRExprs state (stores.map (·.2)) = some vals →
      execIRStmts (stores.length + fuel + 1) state
          (stores.map fun ov =>
            YulStmt.exprStmt (.call "mstore"
              [.call "add" [.ident ptrName, .lit ov.1], ov.2])) =
        .continue { state with
          memory := applyWrites state.memory
            ((stores.map (fun ov => (p + ov.1) % Compiler.Constants.evmModulus)).zip vals) }
  | [], vals, fuel, state, _, _, hvals => by
      have hnil : vals = [] := by
        simpa [evalIRExprs] using hvals.symm
      subst hnil
      simp [execIRStmts, applyWrites]
  | (o, v) :: rest, vals, fuel, state, hptr, hmi, hvals => by
      obtain ⟨hv, hrest⟩ : MemInsensitiveExpr v ∧
          MemInsensitiveExprs (rest.map (fun (x : Nat × YulExpr) => x.2)) := hmi
      simp only [List.map, evalIRExprs] at hvals
      cases hev : evalIRExpr state v with
      | none => rw [hev] at hvals; cases hvals
      | some w =>
          rw [hev] at hvals
          cases hevs : evalIRExprs state (rest.map (·.2)) with
          | none => rw [hevs] at hvals; cases hvals
          | some ws =>
              rw [hevs] at hvals
              obtain rfl : w :: ws = vals := by simpa using hvals
              rw [show ((o, v) :: rest).length + fuel + 1 =
                (rest.length + fuel + 1) + 1 from by simp [List.length]; omega]
              show (match execIRStmt (rest.length + fuel + 1) state
                  (.exprStmt (.call "mstore"
                    [.call "add" [.ident ptrName, .lit o], v])) with
                | .continue s₁ => execIRStmts (rest.length + fuel + 1) s₁
                    (rest.map fun (ov : Nat × YulExpr) =>
                      YulStmt.exprStmt (.call "mstore"
                        [.call "add" [.ident ptrName, .lit ov.1], ov.2]))
                | .return v' s => .return v' s
                | .stop s => .stop s
                | .revert s => .revert s) = _
              rw [show execIRStmt (rest.length + fuel + 1) state
                  (.exprStmt (.call "mstore"
                    [.call "add" [.ident ptrName, .lit o], v])) =
                .continue { state with
                  memory := fun x =>
                    if x = (p + o) % Compiler.Constants.evmModulus then w
                    else state.memory x } from by
                simp [execIRStmt, evalIRExpr, evalIRCall, evalIRExprs, hptr, hev,
                  YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext]]
              have hptr' : ({ state with
                  memory := fun x =>
                    if x = (p + o) % Compiler.Constants.evmModulus then w
                    else state.memory x } : IRState).getVar ptrName = some p := hptr
              have hevs' : evalIRExprs { state with
                  memory := fun x =>
                    if x = (p + o) % Compiler.Constants.evmModulus then w
                    else state.memory x } (rest.map (·.2)) = some ws := by
                rw [evalIRExprs_mem_insensitive (rest.map (·.2)) hrest state _]
                exact hevs
              exact execIRStmts_mstore_ptr_expr_block ptrName p rest ws fuel _
                hptr' hrest hevs'

end Compiler.Proofs.IRGeneration

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
open Compiler.CompilationModel

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

/-- Memory-insensitive expressions evaluate identically under any word view and
physical carrier. -/
theorem evalIRExpr_memory_insensitive :
    ∀ (e : YulExpr), MemInsensitiveExpr e →
      ∀ (state : IRState) (m : Nat → Nat) (bytes : DenoteMemory.Memory),
        evalIRExpr { state with memory := m, byteMemory := bytes } e = evalIRExpr state e
  | .lit _, _, _, _, _ => by simp [evalIRExpr]
  | .hex _, _, _, _, _ => by simp [evalIRExpr]
  | .str _, _, _, _, _ => by simp [evalIRExpr]
  | .ident _, _, _, _, _ => by simp [evalIRExpr, IRState.getVar]
  | .call f args, h, state, m, bytes => by
      obtain ⟨hml, hkec, hargs⟩ := h
      simp only [evalIRExpr]
      rw [evalIRCall, evalIRCall,
        evalIRExprs_memory_insensitive args hargs state m bytes]
      cases hv : evalIRExprs state args with
      | none => simp
      | some argVals => simp [hml, hkec]

theorem evalIRExprs_memory_insensitive :
    ∀ (es : List YulExpr), MemInsensitiveExprs es →
      ∀ (state : IRState) (m : Nat → Nat) (bytes : DenoteMemory.Memory),
        evalIRExprs { state with memory := m, byteMemory := bytes } es = evalIRExprs state es
  | [], _, _, _, _ => by simp [evalIRExprs]
  | e :: rest, h, state, m, bytes => by
      obtain ⟨he, hrest⟩ := h
      simp only [evalIRExprs]
      rw [evalIRExpr_memory_insensitive e he state m bytes,
        evalIRExprs_memory_insensitive rest hrest state m bytes]

end

theorem evalIRExpr_mem_insensitive (e : YulExpr) (h : MemInsensitiveExpr e)
    (state : IRState) (m : Nat → Nat) :
    evalIRExpr { state with memory := m } e = evalIRExpr state e :=
  evalIRExpr_memory_insensitive e h state m state.byteMemory

theorem evalIRExprs_mem_insensitive (es : List YulExpr) (h : MemInsensitiveExprs es)
    (state : IRState) (m : Nat → Nat) :
    evalIRExprs { state with memory := m } es = evalIRExprs state es :=
  evalIRExprs_memory_insensitive es h state m state.byteMemory

/-- A physical `mstore` cannot change a memory-insensitive evaluation. -/
theorem evalIRExprs_writePhysicalMemoryValue (es : List YulExpr) (h : MemInsensitiveExprs es)
    (state : IRState) (offset value : Nat) :
    evalIRExprs (state.writePhysicalMemoryValue offset value) es = evalIRExprs state es :=
  evalIRExprs_memory_insensitive es h state _ _

/-- A physical store sequence only replaces the word view and the byte carrier. -/
theorem applyStores_eq_memory_update :
    ∀ (state : IRState) (writes : List (Nat × Nat)),
      PhysicalPayloadStores.applyStores state writes =
        { state with
            memory := (PhysicalPayloadStores.applyStores state writes).memory
            byteMemory := (PhysicalPayloadStores.applyStores state writes).byteMemory }
  | _, [] => rfl
  | state, (offset, value) :: rest => by
      simp only [PhysicalPayloadStores.applyStores]
      rw [applyStores_eq_memory_update _ rest]
      rfl

theorem applyStores_getVar (state : IRState) (writes : List (Nat × Nat)) (name : String) :
    (PhysicalPayloadStores.applyStores state writes).getVar name = state.getVar name := by
  rw [applyStores_eq_memory_update]
  rfl

theorem evalIRExprs_applyStores (es : List YulExpr) (h : MemInsensitiveExprs es)
    (state : IRState) (writes : List (Nat × Nat)) :
    evalIRExprs (PhysicalPayloadStores.applyStores state writes) es = evalIRExprs state es := by
  rw [applyStores_eq_memory_update]
  exact evalIRExprs_memory_insensitive es h state _ _

/-- Pointer-offset stores with memory-insensitive expression values: the block
executes to its evaluated physical writes applied at the pointer, evaluations
taken in the initial state (the values commute with the block's own writes). -/
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
        .continue (PhysicalPayloadStores.applyStores state
            ((stores.map (fun ov => (p + ov.1) % Compiler.Constants.evmModulus)).zip vals))
  | [], vals, fuel, state, _, _, hvals => by
      have hnil : vals = [] := by
        simpa [evalIRExprs] using hvals.symm
      subst hnil
      simp [execIRStmts, PhysicalPayloadStores.applyStores]
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
              let next := state.writePhysicalMemoryValue
                (Verity.Core.Uint256.ofNat ((p + o) % Compiler.Constants.evmModulus)).val w
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
                    [.call "add" [.ident ptrName, .lit o], v])) = .continue next from by
                simp [next, execIRStmt, evalIRExpr, evalIRCall, evalIRExprs, hptr, hev,
                  YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext]]
              have hptr' : next.getVar ptrName = some p := hptr
              have hevs' : evalIRExprs next (rest.map (·.2)) = some ws := by
                rw [evalIRExprs_writePhysicalMemoryValue (rest.map (·.2)) hrest state _ _]
                exact hevs
              exact execIRStmts_mstore_ptr_expr_block ptrName p rest ws fuel _
                hptr' hrest hevs'

/-- `normalizeEventWord` preserves memory insensitivity: every wrapper it
emits (`and`/`signextend`/`iszero∘iszero`) is a non-memory builtin over the
argument. -/
theorem normalizeEventWord_memInsensitive :
    ∀ (ty : ParamType) (e : YulExpr), MemInsensitiveExpr e →
      MemInsensitiveExpr (normalizeEventWord ty e)
  | .uint8, e, he => ⟨by decide, by decide, he, trivial, trivial⟩
  | .uint16, e, he => ⟨by decide, by decide, he, trivial, trivial⟩
  | .uintN _, e, he => ⟨by decide, by decide, he, trivial, trivial⟩
  | .intN _, e, he => ⟨by decide, by decide, trivial, he, trivial⟩
  | .bytesN _, e, he => ⟨by decide, by decide, he, trivial, trivial⟩
  | .address, e, he => ⟨by decide, by decide, he, trivial, trivial⟩
  | .bool, e, he =>
      ⟨by decide, by decide, ⟨by decide, by decide, he, trivial⟩, trivial⟩
  | .newtypeOf _ baseType, e, he =>
      normalizeEventWord_memInsensitive baseType e he
  | .uint256, e, he => he
  | .int256, e, he => he
  | .bytes32, e, he => he
  | .string, e, he => he
  | .tuple _, e, he => he
  | .array _, e, he => he
  | .fixedArray _ _, e, he => he
  | .bytes, e, he => he
  | .adt _ _, e, he => he

/-- The write list of the scalar unindexed-store block: offsets accumulate by
head word size, values are the normalized argument expressions. -/
def scalarEventWrites :
    List (EventParam × Expr × YulExpr) → Nat → List (Nat × YulExpr)
  | [], _ => []
  | (p, _, argExpr) :: rest, headOffset =>
      (headOffset, normalizeEventWord p.ty argExpr) ::
        scalarEventWrites rest (headOffset + eventHeadWordSize p.ty)

/-- The emitted store block is exactly the pointer-store map of its write
list — so `execIRStmts_mstore_ptr_expr_block` applies directly. -/
theorem scalarEventUnindexedStoresFrom_shape :
    ∀ (unindexed : List (EventParam × Expr × YulExpr)) (headOffset : Nat),
      scalarEventUnindexedStoresFrom unindexed headOffset =
        (scalarEventWrites unindexed headOffset).map fun ov =>
          YulStmt.exprStmt (.call "mstore"
            [.call "add" [.ident "__evt_ptr", .lit ov.1], ov.2])
  | [], _ => rfl
  | (p, e, argExpr) :: rest, headOffset => by
      rw [show scalarEventUnindexedStoresFrom ((p, e, argExpr) :: rest) headOffset =
        YulStmt.exprStmt (YulExpr.call "mstore" [
          YulExpr.call "add" [YulExpr.ident "__evt_ptr", YulExpr.lit headOffset],
          normalizeEventWord p.ty argExpr
        ]) :: scalarEventUnindexedStoresFrom rest
          (headOffset + eventHeadWordSize p.ty) from rfl,
        scalarEventUnindexedStoresFrom_shape rest
          (headOffset + eventHeadWordSize p.ty)]
      rfl

end Compiler.Proofs.IRGeneration

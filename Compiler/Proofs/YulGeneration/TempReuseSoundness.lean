import Compiler.Yul.TempReuse

namespace Compiler.Proofs.YulGeneration.TempReuseSoundness

open Compiler.Yul
open Compiler.Yul.TempReuse

/-- Fast-path identity theorem: any lexical block with `≤ maxStackLocals` `let` bindings
    is returned definitionally unchanged by `reuseBlockTemps`. -/
theorem reuseBlockTemps_eq_self_of_le
    (maxStackLocals : Nat)
    (protectedNames : List String)
    (stmts : List YulStmt)
    (hLe : countLetBindings stmts ≤ maxStackLocals) :
    reuseBlockTemps maxStackLocals protectedNames stmts = stmts := by
  unfold reuseBlockTemps
  exact if_pos hLe

/-- Default-threshold specialization of `reuseBlockTemps_eq_self_of_le`. -/
theorem reuseBlockTemps_default_eq_self_of_le
    (protectedNames : List String)
    (stmts : List YulStmt)
    (hLe : countLetBindings stmts ≤ defaultMaxStackLocals) :
    reuseBlockTemps defaultMaxStackLocals protectedNames stmts = stmts :=
  reuseBlockTemps_eq_self_of_le defaultMaxStackLocals protectedNames stmts hLe

/-- Local variable and linear memory state for straight-line Yul block evaluation. -/
structure YulBlockState where
  vars : String → Nat
  mem : Nat → Nat

/-- Update a single local variable binding in `YulBlockState`. -/
def YulBlockState.setVar (s : YulBlockState) (name : String) (val : Nat) : YulBlockState :=
  { s with vars := fun k => if k == name then val else s.vars k }

/-- Update a single 32-byte word slot in `YulBlockState.mem`. -/
def YulBlockState.mstoreWord (s : YulBlockState) (slot val : Nat) : YulBlockState :=
  { s with mem := fun addr => if addr == slot then val else s.mem addr }

mutual
/-- Evaluate a pure/memory-reading `YulExpr` against `YulBlockState` and primitive `callEval`. -/
def evalYulExpr (s : YulBlockState) (callEval : String → List Nat → Nat) :
    YulExpr → Nat
  | .lit n => n
  | .hex n => n
  | .str _ => 0
  | .ident name => s.vars name
  | .call func args =>
      let argVals := evalYulExprs s callEval args
      if func == "mload" then
        match argVals with
        | [slot] => s.mem slot
        | _ => callEval func argVals
      else
        callEval func argVals

/-- Evaluate a list of `YulExpr` against `YulBlockState`. -/
def evalYulExprs (s : YulBlockState) (callEval : String → List Nat → Nat) :
    List YulExpr → List Nat
  | [] => []
  | e :: es => evalYulExpr s callEval e :: evalYulExprs s callEval es
end

/-- Execute one straight-line Yul statement (`let_`, `assign`, or `mstore` `exprStmt`). -/
def execStraightStmt (callEval : String → List Nat → Nat)
    (s : YulBlockState) : YulStmt → YulBlockState
  | .let_ name rhs => s.setVar name (evalYulExpr s callEval rhs)
  | .assign name rhs => s.setVar name (evalYulExpr s callEval rhs)
  | .exprStmt (.call "mstore" [slotExpr, valExpr]) =>
      s.mstoreWord (evalYulExpr s callEval slotExpr) (evalYulExpr s callEval valExpr)
  | _ => s

mutual
/-- Check whether an expression contains a call to `targetFunc`. -/
def exprUsesFunc (targetFunc : String) : YulExpr → Bool
  | .lit _ | .hex _ | .str _ | .ident _ => false
  | .call func args => (func == targetFunc) || exprsUseFunc targetFunc args

/-- Check whether any expression in a list contains a call to `targetFunc`. -/
def exprsUseFunc (targetFunc : String) : List YulExpr → Bool
  | [] => false
  | e :: es => exprUsesFunc targetFunc e || exprsUseFunc targetFunc es
end

mutual
/-- Renaming `oldName → newName` in an expression that does not mention `newName`
    evaluates under `s.setVar newName val` to the same word as under `s.setVar oldName val`. -/
theorem evalYulExpr_renameIdent
    (s : YulBlockState)
    (callEval : String → List Nat → Nat)
    (oldName newName : String)
    (val : Nat) :
    ∀ (e : YulExpr),
      exprUsesIdent newName e = false →
      evalYulExpr (s.setVar newName val) callEval (replaceIdentInExpr oldName (.ident newName) e) =
        evalYulExpr (s.setVar oldName val) callEval e
  | .lit _, _ => rfl
  | .hex _, _ => rfl
  | .str _, _ => rfl
  | .ident name, hNoNew => by
      simp only [exprUsesIdent] at hNoNew
      simp only [replaceIdentInExpr]
      cases hOld : name == oldName <;>
        simp only [evalYulExpr, YulBlockState.setVar, hOld, hNoNew, BEq.rfl, Bool.false_eq_true, ↓reduceIte]
  | .call func args, hNoNew => by
      simp only [exprUsesIdent] at hNoNew
      have hArgs := evalYulExprs_renameIdent s callEval oldName newName val args hNoNew
      simp only [replaceIdentInExpr, evalYulExpr, hArgs]
      rfl

/-- List counterpart of `evalYulExpr_renameIdent`. -/
theorem evalYulExprs_renameIdent
    (s : YulBlockState)
    (callEval : String → List Nat → Nat)
    (oldName newName : String)
    (val : Nat) :
    ∀ (es : List YulExpr),
      exprsUseIdent newName es = false →
      evalYulExprs (s.setVar newName val) callEval (replaceIdentInExprs oldName (.ident newName) es) =
        evalYulExprs (s.setVar oldName val) callEval es
  | [], _ => rfl
  | e :: es, hNoNew => by
      simp only [exprsUseIdent, Bool.or_eq_false_iff] at hNoNew
      simp only [replaceIdentInExprs, evalYulExprs]
      rw [evalYulExpr_renameIdent s callEval oldName newName val e hNoNew.1,
          evalYulExprs_renameIdent s callEval oldName newName val es hNoNew.2]
end

/-- Step preservation for dead-temporary reuse: executing `newName := rhs` followed by
    evaluating any renamed expression `e` (free of `newName`) produces the exact same result
    as executing `let oldName := rhs` followed by evaluating `e`. -/
theorem reuseDeadLetStep_eval_eq
    (s : YulBlockState)
    (callEval : String → List Nat → Nat)
    (oldName newName : String)
    (rhs e : YulExpr)
    (hNoNew : exprUsesIdent newName e = false) :
    evalYulExpr (execStraightStmt callEval s (.assign newName rhs)) callEval
        (replaceIdentInExpr oldName (.ident newName) e) =
      evalYulExpr (execStraightStmt callEval s (.let_ oldName rhs)) callEval e := by
  simp only [execStraightStmt]
  exact evalYulExpr_renameIdent s callEval oldName newName (evalYulExpr s callEval rhs) e hNoNew

mutual
/-- Replacing `oldName` with `mload(slot)` in a pure expression `e` (free of `"mload"`)
    evaluates under `s.mstoreWord slot val` to the same word as under `s.setVar oldName val`. -/
theorem evalYulExpr_spillIdent
    (s : YulBlockState)
    (callEval : String → List Nat → Nat)
    (oldName : String)
    (slot val : Nat) :
    ∀ (e : YulExpr),
      exprUsesFunc "mload" e = false →
      evalYulExpr (s.mstoreWord slot val) callEval
          (replaceIdentInExpr oldName (.call "mload" [.lit slot]) e) =
        evalYulExpr (s.setVar oldName val) callEval e
  | .lit _, _ => rfl
  | .hex _, _ => rfl
  | .str _, _ => rfl
  | .ident name, _ => by
      simp only [replaceIdentInExpr]
      cases hOld : name == oldName <;>
        simp only [evalYulExpr, evalYulExprs, YulBlockState.mstoreWord, YulBlockState.setVar,
          hOld, BEq.rfl, Bool.false_eq_true, ↓reduceIte]
  | .call func args, hNoMload => by
      simp only [exprUsesFunc, Bool.or_eq_false_iff] at hNoMload
      have hArgs := evalYulExprs_spillIdent s callEval oldName slot val args hNoMload.2
      simp only [replaceIdentInExpr, evalYulExpr, hArgs, hNoMload.1, Bool.false_eq_true, ↓reduceIte]

/-- List counterpart of `evalYulExpr_spillIdent`. -/
theorem evalYulExprs_spillIdent
    (s : YulBlockState)
    (callEval : String → List Nat → Nat)
    (oldName : String)
    (slot val : Nat) :
    ∀ (es : List YulExpr),
      exprsUseFunc "mload" es = false →
      evalYulExprs (s.mstoreWord slot val) callEval
          (replaceIdentInExprs oldName (.call "mload" [.lit slot]) es) =
        evalYulExprs (s.setVar oldName val) callEval es
  | [], _ => rfl
  | e :: es, hNoMload => by
      simp only [exprsUseFunc, Bool.or_eq_false_iff] at hNoMload
      simp only [replaceIdentInExprs, evalYulExprs]
      rw [evalYulExpr_spillIdent s callEval oldName slot val e hNoMload.1,
          evalYulExprs_spillIdent s callEval oldName slot val es hNoMload.2]
end

/-- Step preservation for scratch-memory spilling: executing `mstore(slot, rhs)` followed by
    evaluating `e[oldName := mload(slot)]` produces the exact same word as executing
    `let oldName := rhs` followed by evaluating `e`. -/
theorem spillLetStep_eval_eq
    (s : YulBlockState)
    (callEval : String → List Nat → Nat)
    (oldName : String)
    (slot : Nat)
    (rhs e : YulExpr)
    (hNoMload : exprUsesFunc "mload" e = false) :
    evalYulExpr
        (execStraightStmt callEval s (.exprStmt (.call "mstore" [.lit slot, rhs])))
        callEval
        (replaceIdentInExpr oldName (.call "mload" [.lit slot]) e) =
      evalYulExpr (execStraightStmt callEval s (.let_ oldName rhs)) callEval e := by
  simp only [execStraightStmt, evalYulExpr]
  exact evalYulExpr_spillIdent s callEval oldName slot (evalYulExpr s callEval rhs) e hNoMload

end Compiler.Proofs.YulGeneration.TempReuseSoundness

import Mathlib.Data.Nat.Basic
import Compiler.SolidityImport.Access

/-!
Lemmas for proofs about an imported model's `Denote` execution: 256-bit word
arithmetic, environment bindings, and splitting a body into straight-line parts.
-/

open Compiler.CompilationModel Compiler.CompilationModel.Denote
open Verity.Core
namespace Compiler.CompilationModel.SolidityImport

/-- Split a body just after its top-level `let name := ...`. Since imported
Solidity locals keep their name, this cuts a body at a Solidity statement. -/
def splitAfter (name : String) : List Stmt → List Stmt × List Stmt
  | [] => ([], [])
  | stmt :: rest =>
      match stmt with
      | .letVar n _ => if n = name then ([stmt], rest) else
          (stmt :: (splitAfter name rest).1, (splitAfter name rest).2)
      | _ => (stmt :: (splitAfter name rest).1, (splitAfter name rest).2)

/-! ## Words -/

def max128 : Nat := 2^128 - 1

theorem max128_lt : max128 < Uint256.modulus := by decide

theorem word_of_small {a : Nat} (h : a ≤ max128) : (Uint256.ofNat a).val = a :=
  Nat.mod_eq_of_lt (lt_of_le_of_lt h max128_lt)

@[simp] theorem normalize_normalize (n : Nat) : wordNormalize (wordNormalize n) = wordNormalize n :=
  Nat.mod_mod _ _

@[simp] theorem normalize_max : wordNormalize max128 = max128 := word_of_small (Nat.le_refl _)

theorem sub_word {a b : Nat} (ha : a < Uint256.modulus) (hb : b ≤ a) :
    (Uint256.ofNat a - Uint256.ofNat b).val = a - b := by
  change (Uint256.sub _ _).val = _
  simp [Uint256.sub, Uint256.ofNat, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt (lt_of_le_of_lt hb ha), hb,
    Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.sub_le a b) ha)]

theorem mul_word128 {a b : Nat} (ha : a ≤ max128) (hb : b ≤ max128) :
    (Uint256.ofNat a * Uint256.ofNat b).val = a * b := by
  have hp : a * b < Uint256.modulus := lt_of_le_of_lt (Nat.mul_le_mul ha hb) (by decide)
  change (Uint256.mul _ _).val = _
  simp [Uint256.mul, Uint256.ofNat, Nat.mod_eq_of_lt hp,
    Nat.mod_eq_of_lt (lt_of_le_of_lt ha max128_lt),
    Nat.mod_eq_of_lt (lt_of_le_of_lt hb max128_lt)]

theorem div_word {a b : Nat} (ha : a < Uint256.modulus) (hb : b < Uint256.modulus) :
    (Uint256.ofNat a / Uint256.ofNat b).val = a / b := by
  change (Uint256.div _ _).val = _
  by_cases h : b = 0
  · subst b; simp [Uint256.div, Uint256.ofNat]
  · simp [Uint256.div, Uint256.ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, h,
      Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self a b) ha)]

theorem mask_le (a : Nat) : (Uint256.and (Uint256.ofNat a) (Uint256.ofNat max128)).val ≤ a := by
  exact le_trans (Nat.mod_le _ _) (le_trans Nat.and_le_left (Nat.mod_le _ _))

theorem mask_bounded (a : Nat) : (Uint256.and (Uint256.ofNat a) (Uint256.ofNat max128)).val ≤ max128 := by
  exact le_trans (Nat.mod_le _ _) (le_trans Nat.and_le_right (Nat.mod_le _ _))

theorem mask_eq {a : Nat} (ha : a ≤ max128) :
    (Uint256.and (Uint256.ofNat a) (Uint256.ofNat max128)).val = a := by
  have h : a < 2^128 := by unfold max128 at ha; omega
  simp only [Uint256.and, Uint256.ofNat, Nat.mod_eq_of_lt (lt_of_le_of_lt ha max128_lt),
    Nat.mod_eq_of_lt max128_lt]
  rw [Nat.land_eq, max128, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt h,
    Nat.mod_eq_of_lt (lt_of_le_of_lt ha max128_lt)]

theorem ofNat_val (u : Uint256) : Uint256.ofNat u.val = u := by
  apply Uint256.ext
  exact Nat.mod_eq_of_lt u.isLt

/-! ## Execution -/

@[simp] theorem lookup_bind_same (env : Env) (name : String) (v : Nat) :
    lookupValue (bindValue env name v) name = v := by
  simp [lookupValue, bindValue]

@[simp] theorem lookup_bind_other (env : Env) (name key : String) (v : Nat)
    (h : name ≠ key) : lookupValue (bindValue env name v) key = lookupValue env key := by
  induction env with
  | nil => simp [lookupValue, bindValue, h]
  | cons e es ih =>
    rcases e with ⟨n, x⟩
    by_cases hn : n = name
    · subst n
      simpa [lookupValue, bindValue, h] using ih
    · by_cases hk : n = key
      · subst n; simp [lookupValue, bindValue, h, Ne.symm h]
      · simpa [lookupValue, bindValue, h, hn, hk] using ih

mutual
/-- A prefix can only continue or revert, and cannot assign a protected name. -/
 def prefixStmt (keys : List String) : Stmt → Bool
  | .letVar name _ | .assignVar name _ => !keys.contains name
  | .ite _ yes no => prefixList keys yes && prefixList keys no
  | .panic _ => true
  | _ => false
 def prefixList (keys : List String) : List Stmt → Bool
  | [] => true
  | s :: ss => prefixStmt keys s && prefixList keys ss
end

def Frame (keys : List String) (s : DenoteState) : StmtOutcome → Prop
 | .continue t => t.world = s.world ∧ ∀ k ∈ keys, lookupValue t.bindings k = lookupValue s.bindings k
 | .revert | .revertWithData _ => True
 | _ => False

mutual
 theorem stmt_frame (o : DenoteOracle) (fs : List Field) (s : DenoteState)
     (stmt : Stmt) (keys : List String) (h : prefixStmt keys stmt = true) :
     Frame keys s (execStmt o fs s stmt) := by
   unfold prefixStmt at h
   split at h
   · rename_i n e
     cases hv : evalExpr o fs s e <;> simp [execStmt, hv, Frame]
     intro k hk
     exact lookup_bind_other _ _ _ _ (by
       intro heq; subst n
       simp [hk] at h)
   · rename_i n e
     cases hv : evalExpr o fs s e <;> simp [execStmt, hv, Frame]
     intro k hk
     exact lookup_bind_other _ _ _ _ (by
       intro heq; subst n
       simp [hk] at h)
   · rename_i cond yes no
     have hh := Bool.and_eq_true_iff.mp h
     cases hv : evalExpr o fs s cond
     · simp [execStmt, hv, Frame]
     · simp only [execStmt, hv]
       split
       · exact list_frame o fs s yes keys hh.1
       · exact list_frame o fs s no keys hh.2
   · simp [execStmt, Frame]
   · cases h
 theorem list_frame (o : DenoteOracle) (fs : List Field) (s : DenoteState)
     (ss : List Stmt) (keys : List String) (h : prefixList keys ss = true) :
     Frame keys s (execStmtList o fs s ss) := by
   cases ss with
   | nil => simp [execStmtList, Frame]
   | cons stmt rest =>
     have hh := Bool.and_eq_true_iff.mp h
     have hs := stmt_frame o fs s stmt keys hh.1
     simp only [execStmtList]
     cases he : execStmt o fs s stmt
     · rename_i t
       have hf : t.world = s.world ∧ ∀ k ∈ keys, lookupValue t.bindings k = lookupValue s.bindings k := by
         simpa [Frame, he] using hs
       have hr := list_frame o fs t rest keys hh.2
       cases execStmtList o fs t rest <;> simp_all [Frame]
     · simp_all [Frame]
     · simp_all [Frame]
     · trivial
     · trivial
end

theorem exec_append (o : DenoteOracle) (fs : List Field) (s : DenoteState)
    (a b : List Stmt) : execStmtList o fs s (a ++ b) =
    match execStmtList o fs s a with
    | .continue t => execStmtList o fs t b
    | out => out := by
  induction a generalizing s with
  | nil => rfl
  | cons stmt rest ih =>
    simp only [List.cons_append, execStmtList]
    cases execStmt o fs s stmt <;> simp_all

/-- A successful execution after a prefix must have continued through that prefix. -/
theorem split_prefix (o : DenoteOracle) (fs : List Field) (s final : DenoteState)
    (a b : List Stmt) (ha : prefixList [] a = true)
    (h : execStmtList o fs s (a ++ b) = .stop final) :
    ∃ t, execStmtList o fs s a = .continue t ∧ execStmtList o fs t b = .stop final := by
  rw [exec_append] at h
  have hf := list_frame o fs s a [] ha
  cases he : execStmtList o fs s a <;> simp_all [Frame]

theorem split_prefix_continue (o : DenoteOracle) (fs : List Field) (s final : DenoteState)
    (a b : List Stmt)
    (h : execStmtList o fs s (a ++ b) = .continue final) :
    ∃ t, execStmtList o fs s a = .continue t ∧ execStmtList o fs t b = .continue final := by
  rw [exec_append] at h
  cases he : execStmtList o fs s a <;> simp_all

theorem exec_let_cons (o : DenoteOracle) (fs : List Field) (s : DenoteState)
    (n : String) (e : Expr) (ss : List Stmt) :
    execStmtList o fs s (.letVar n e :: ss) =
      match evalExpr o fs s e with
      | some v => execStmtList o fs {s with bindings := bindValue s.bindings n v} ss
      | none => .revert := by
  simp only [execStmtList, execStmt]
  cases evalExpr o fs s e <;> rfl

@[simp] theorem exec_singleton (o : DenoteOracle) (fs : List Field) (s : DenoteState)
    (stmt : Stmt) : execStmtList o fs s [stmt] = execStmt o fs s stmt := by
  simp only [execStmtList]
  cases execStmt o fs s stmt <;> rfl

/-- A fall-through prefix followed by an explicit return can only stop or revert. -/
theorem ends_return (o : DenoteOracle) (fs : List Field) (s : DenoteState)
    (pre : List Stmt) (args : List Expr) (hp : prefixList [] pre = true) :
    execStmtList o fs s (pre ++ [.returnValues args]) = .revert ∨
      (∃ data, execStmtList o fs s (pre ++ [.returnValues args]) = .revertWithData data) ∨
      ∃ t, execStmtList o fs s (pre ++ [.returnValues args]) = .stop t := by
  rw [exec_append]
  have hf := list_frame o fs s pre [] hp
  cases he : execStmtList o fs s pre
  · rename_i t
    simp only [exec_singleton, execStmt]
    cases evalExprList o fs t args <;> simp
  · simp_all [Frame]
  · simp_all [Frame]
  · simp
  · simp

end Compiler.CompilationModel.SolidityImport

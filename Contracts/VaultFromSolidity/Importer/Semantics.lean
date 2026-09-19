/-
  What each accepted Solidity construct means, in Verity terms.

  This is the single definition of the translation: `Importer.lean` parses solc's
  typed AST into the closed inductive in `Syntax.lean` and registers each entry
  point as `Fn.meaning body slots fns env`. Nothing here inspects JSON, and nothing
  here is generated source -- the registered value is a kernel-checked Lean term.

  Statement order matches the Solidity source order exactly, because the proofs
  pin the write order the contract produces. Internal calls evaluate arguments
  left to right, then run the callee body under the caller's `msg.sender` /
  `msg.value`. `Expr.call` is `view`/`pure` only; effectful internals are
  `Stmt.callStmt`. Pinned solc 0.8.x legacy codegen (`viaIR=false`) evaluates
  an effectful call before the other operand / `+=` old-read, so modelling
  those calls as left-to-right `Expr.call` would disagree with bytecode.
-/

import Contracts.VaultFromSolidity.Importer.Syntax
import Verity.Stdlib.Math
import Verity.Core.SolidityImportAttr

namespace SolidityImporter.Sol

open Lean

/-- `uint256` denotes Verity's `Uint256`, `address` its `Address`. -/
@[reducible] def Ty.denote : Ty → Type
  | .uint => Verity.Core.Uint256
  | .addr => Verity.Core.Address

/-- A function body returns nothing, one value, or (later) a tuple. -/
@[reducible] def Ret.denote : Ret → Type
  | [] => Unit
  | t :: [] => t.denote
  | t :: ts => t.denote × Ret.denote ts

/-- A state variable is a named `StorageSlot`, scalar, address, or `address`-keyed. -/
@[reducible] def StorageTy.denote : StorageTy → Type
  | .scalar => Verity.StorageSlot Verity.Core.Uint256
  | .mapping => Verity.StorageSlot (Verity.Core.Address → Verity.Core.Uint256)
  | .addr => Verity.StorageSlot Verity.Core.Address

/-- Parameter/local values, in the same de Bruijn order as `Ctx`. -/
inductive Env : Ctx → Type where
  | nil : Env []
  | cons : (x : t.denote) → (rest : Env Γ) → Env (t :: Γ)

/-- The imported state-variable handles, in the same order as `Layout`. -/
inductive Slots : Layout → Type where
  | nil : Slots []
  | cons : (s : st.denote) → (rest : Slots L) → Slots (st :: L)

/-- Declaration-order values of a call's arguments, before they are packed
into a de Bruijn `Env`. -/
inductive Vals : List Ty → Type where
  | nil : Vals []
  | cons : t.denote → Vals ts → Vals (t :: ts)

/-- Already-registered function meanings: each takes a de Bruijn environment
of its parameters and returns a `Contract` of its result type. Slots are
baked into the registered Lean constants. -/
inductive FnEnv : Fns → Type where
  | nil : FnEnv []
  | cons : (Env σ.params → Verity.Contract (Ret.denote σ.rets)) →
      FnEnv F → FnEnv (σ :: F)

/-- The value bound at a variable. -/
def Env.get : (env : Env Γ) → (v : Var Γ t) → t.denote
  | .cons x _, .here => x
  | .cons _ rest, .there v => Env.get rest v

/-- The storage slot a state-variable handle refers to. -/
def Slots.get : (slots : Slots L) → (s : SVar L st) → st.denote
  | .cons s _, .here => s
  | .cons _ rest, .there s => Slots.get rest s

/-- The meaning of an already-registered function. -/
def FnEnv.get : (fns : FnEnv F) → (f : FVar F σ) →
    Env σ.params → Verity.Contract (Ret.denote σ.rets)
  | .cons m _, .here => m
  | .cons _ rest, .there f => FnEnv.get rest f

/-- Pack declaration-order values into a de Bruijn environment by the same
`reverseAux` walk `List.reverse` uses, so the type is definitionally
`Env ts.reverse`. Last declared parameter is innermost. -/
def reverseAuxEnv : {acc : Ctx} → (ts : List Ty) → Vals ts → Env acc →
    Env (List.reverseAux ts acc)
  | _, [], .nil, env => env
  | acc, _ :: ts, .cons x vs, env => reverseAuxEnv (acc := _ :: acc) ts vs (.cons x env)

/-- Pack declaration-order values into a de Bruijn environment. -/
def envOfVals {ts : List Ty} (vs : Vals ts) : Env ts.reverse :=
  reverseAuxEnv ts vs .nil

/-- Solidity 0.8 checked `+`/`-` on `uint256`: overflow/underflow reverts with
`Panic(0x11)` instead of wrapping. -/
def checked (op : ArithOp) (a b : Verity.Core.Uint256) : Verity.Contract Verity.Core.Uint256 :=
  match op with
  | .add => Verity.Stdlib.Math.requireSomeUint (Verity.Stdlib.Math.safeAdd a b) "Panic(0x11)"
  | .sub => Verity.Stdlib.Math.requireSomeUint (Verity.Stdlib.Math.safeSub a b) "Panic(0x11)"

mutual
/-- The meaning of an expression: a `Contract` producing its value. -/
def Expr.meaning {L : Layout} {F : Fns} {Γ : Ctx} {t : Ty}
    (e : Expr L F Γ t) (slots : Slots L) (fns : FnEnv F) (env : Env Γ) :
    Verity.Contract t.denote :=
  match e with
  | .var v => Verity.pure (Env.get env v)
  | .sender => Verity.msgSender
  | .lit n => Verity.pure (Verity.Core.Uint256.ofNat n)
  | .load s => Verity.getStorage (Slots.get slots s)
  | .loadAddr s => Verity.getStorageAddr (Slots.get slots s)
  | .index m key =>
      Verity.bind (Expr.meaning key slots fns env) (fun a =>
        Verity.getMapping (Slots.get slots m) a)
  | .arith op a b =>
      Verity.bind (Expr.meaning a slots fns env) (fun x =>
        Verity.bind (Expr.meaning b slots fns env) (fun y => checked op x y))
  | .call fvar args =>
      Verity.bind (Args.eval args slots fns env) (fun vals =>
        FnEnv.get fns fvar (envOfVals vals))

/-- Evaluate call arguments left to right in declaration order. -/
def Args.eval {L : Layout} {F : Fns} {Γ : Ctx} {ts : List Ty}
    (args : Args L F Γ ts) (slots : Slots L) (fns : FnEnv F) (env : Env Γ) :
    Verity.Contract (Vals ts) :=
  match args with
  | .nil => Verity.pure Vals.nil
  | .cons e rest =>
      Verity.bind (Expr.meaning e slots fns env) (fun x =>
        Verity.bind (Args.eval rest slots fns env) (fun vs =>
          Verity.pure (Vals.cons x vs)))

/-- `lhs op= rhs` followed by `k`, in source evaluation order: for `+=`/`-=` the
mapping key (if any) is read first, then the old value, then the right-hand side,
then the checked arithmetic, then the write, then the rest of the body. -/
def assignWith {α : Type} (read : Verity.Contract Verity.Core.Uint256)
    (write : Verity.Core.Uint256 → Verity.Contract Unit) :
    AssignOp → Verity.Contract Verity.Core.Uint256 → Verity.Contract α → Verity.Contract α
  | .set, rhs, k => Verity.bind rhs (fun v => Verity.bind (write v) (fun _ => k))
  | .add, rhs, k =>
      Verity.bind read (fun old =>
        Verity.bind rhs (fun v =>
          Verity.bind (checked .add old v) (fun w => Verity.bind (write w) (fun _ => k))))
  | .sub, rhs, k =>
      Verity.bind read (fun old =>
        Verity.bind rhs (fun v =>
          Verity.bind (checked .sub old v) (fun w => Verity.bind (write w) (fun _ => k))))

/-- The meaning of a statement: the rest of the body is its continuation. -/
def Stmt.meaning {L : Layout} {F : Fns} {Γ : Ctx} {r : Ret}
    (s : Stmt L F Γ r) (slots : Slots L) (fns : FnEnv F) (env : Env Γ) :
    Verity.Contract (Ret.denote r) :=
  match s with
  | .done => Verity.pure ()
  | .ret e => Expr.meaning e slots fns env
  | .assign lv op rhs rest =>
      match lv with
      | .scalar sv =>
          assignWith (Verity.getStorage (Slots.get slots sv))
            (fun v => Verity.setStorage (Slots.get slots sv) v) op
            (Expr.meaning rhs slots fns env) (Stmt.meaning rest slots fns env)
      | .mapping sv key =>
          Verity.bind (Expr.meaning key slots fns env) (fun a =>
            assignWith (Verity.getMapping (Slots.get slots sv) a)
              (fun v => Verity.setMapping (Slots.get slots sv) a v) op
              (Expr.meaning rhs slots fns env) (Stmt.meaning rest slots fns env))
  | .assignAddr sv rhs rest =>
      Verity.bind (Expr.meaning rhs slots fns env) (fun a =>
        Verity.bind (Verity.setStorageAddr (Slots.get slots sv) a) (fun _ =>
          Stmt.meaning rest slots fns env))
  | .local_ e rest =>
      Verity.bind (Expr.meaning e slots fns env)
        (fun x => Stmt.meaning rest slots fns (Env.cons x env))
  | .guard a b msg rest =>
      Verity.bind (Expr.meaning a slots fns env) (fun x =>
        Verity.bind (Expr.meaning b slots fns env) (fun y =>
          Verity.bind (Verity.require (Nat.ble y.val x.val) msg)
            (fun _ => Stmt.meaning rest slots fns env)))
  | .callStmt fvar args rest =>
      Verity.bind (Args.eval args slots fns env) (fun vals =>
        Verity.bind (FnEnv.get fns fvar (envOfVals vals)) (fun _ =>
          Stmt.meaning rest slots fns env))
end

/-- Every imported entry point is non-payable. Internal calls do not re-apply
this guard; they run the callee body under the caller's `msg.value`. -/
def nonpayable {α : Type} (m : Verity.Contract α) : Verity.Contract α :=
  Verity.bind Verity.msgValue (fun value =>
    Verity.bind (Verity.require (Nat.beq value.val 0) "Nonpayable") (fun _ => m))

/-- The meaning of a whole function: its body, under the non-payable guard. -/
def Fn.meaning {L : Layout} {F : Fns} {Γ : Ctx} {r : Ret}
    (body : Stmt L F Γ r) (slots : Slots L) (fns : FnEnv F) (env : Env Γ) :
    Verity.Contract (Ret.denote r) :=
  nonpayable (Stmt.meaning body slots fns env)

/-- Body meaning without the non-payable guard, used for internal functions. -/
def Fn.bodyMeaning {L : Layout} {F : Fns} {Γ : Ctx} {r : Ret}
    (body : Stmt L F Γ r) (slots : Slots L) (fns : FnEnv F) (env : Env Γ) :
    Verity.Contract (Ret.denote r) :=
  Stmt.meaning body slots fns env

-- Every imported entry point is registered as `Fn.meaning` applied to the parsed
-- term, so the proofs need these definitions to unfold with the rest of the
-- `solidity_import` simp set.
attribute [solidity_import] Fn.meaning Fn.bodyMeaning nonpayable Stmt.meaning assignWith
  Expr.meaning Args.eval checked Env.get Slots.get FnEnv.get envOfVals
  Ty.denote Ret.denote StorageTy.denote

end SolidityImporter.Sol

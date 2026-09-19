/-
  The Solidity subset the Vault importer accepts, as an intrinsically typed
  inductive family.

  Ill-typed programs are unrepresentable: reading a `uint256` state variable
  yields a `uint`, a mapping index must be an `addr`, a `uint256` local can only
  be bound to a `uint`, and `Stmt L F Γ r` only ever produces a value of type `r`.
  The parser in `Importer.lean` is the only producer of these terms and
  `Semantics.lean` is the only place that gives them meaning.

  `Ctx` is a de Bruijn context: index 0 is the innermost binder. `Layout` is the
  imported state-variable order, which the importer keeps in lockstep with the
  `<var>Slot` handles it registers. `Fns` is the callee-first function table:
  a body may only mention functions already registered, so recursion is
  unrepresentable.
-/

import Lean

open Lean

namespace SolidityImporter.Sol

/-- Types of the accepted subset: `uint256` and `address`. -/
inductive Ty where
  | uint : Ty
  | addr : Ty
  deriving DecidableEq, Repr, Inhabited, ToExpr

/-- What an imported function returns. Empty is `void`; a singleton is the
POC's one named or unnamed return. Multi-value returns wait for a later slice. -/
abbrev Ret := List Ty

/-- Shape of an imported state variable. -/
inductive StorageTy where
  | scalar : StorageTy
  | mapping : StorageTy
  | addr : StorageTy
  deriving DecidableEq, Repr, Inhabited, ToExpr

/-- Parameter/local context, de Bruijn order. -/
abbrev Ctx := List Ty

/-- Imported state variables, in importer field order. -/
abbrev Layout := List StorageTy

/-- A function signature: parameters in de Bruijn order (last declared
innermost) and the return list. -/
structure Sig where
  params : Ctx
  rets : Ret
  deriving DecidableEq, Repr, Inhabited, ToExpr

/-- Already-registered function signatures, callee-first. -/
abbrev Fns := List Sig

/-- A parameter or local at a given type in a context. -/
inductive Var : Ctx → Ty → Type where
  | here : Var (t :: Γ) t
  | there : Var Γ t → Var (t' :: Γ) t
  deriving ToExpr

/-- A state variable handle of a given storage shape. -/
inductive SVar : Layout → StorageTy → Type where
  | here : SVar (st :: L) st
  | there : SVar L st → SVar (st' :: L) st
  deriving ToExpr

/-- A handle of an already-registered function. -/
inductive FVar : Fns → Sig → Type where
  | here : FVar (σ :: F) σ
  | there : FVar F σ → FVar (σ' :: F) σ
  deriving ToExpr

/-- Checked arithmetic operators: Solidity's `+` and `-` on `uint256`. -/
inductive ArithOp where
  | add : ArithOp
  | sub : ArithOp
  deriving DecidableEq, Repr, Inhabited, ToExpr

/-- Assignment operators: `=`, `+=` and `-=`. -/
inductive AssignOp where
  | set : AssignOp
  | add : AssignOp
  | sub : AssignOp
  deriving DecidableEq, Repr, Inhabited, ToExpr

/-- The `n`-th variable of a context, if the context is that deep. -/
def Var.ofIndex : (Γ : Ctx) → (n : Nat) → Option (Σ t, Var Γ t)
  | [], _ => none
  | _ :: _, 0 => some ⟨_, .here⟩
  | _ :: Γ, n + 1 => (Var.ofIndex Γ n).map fun v => ⟨v.1, .there v.2⟩

/-- The `n`-th state variable of a layout, if the layout is that deep. -/
def SVar.ofIndex : (L : Layout) → (n : Nat) → Option (Σ st, SVar L st)
  | [], _ => none
  | _ :: _, 0 => some ⟨_, .here⟩
  | _ :: L, n + 1 => (SVar.ofIndex L n).map fun s => ⟨s.1, .there s.2⟩

/-- The `n`-th already-registered function, if the table is that long. -/
def FVar.ofIndex : (F : Fns) → (n : Nat) → Option (Σ σ, FVar F σ)
  | [], _ => none
  | _ :: _, 0 => some ⟨_, .here⟩
  | _ :: F, n + 1 => (FVar.ofIndex F n).map fun f => ⟨f.1, .there f.2⟩

/-- Declaration-order argument list (leftmost first). `Sig.params` is the
de Bruijn reverse of this list. -/
abbrev DeclParams := List Ty

mutual
/-- `uint256`/`address` expressions: locals, `msg.sender`, literals, state
reads, checked `+`/`-`, and internal calls that return one value. -/
inductive Expr (L : Layout) (F : Fns) (Γ : Ctx) : Ty → Type where
  /-- A parameter or local. -/
  | var : Var Γ t → Expr L F Γ t
  /-- `msg.sender`. -/
  | sender : Expr L F Γ .addr
  /-- A numeric literal; the parser enforces `n < 2^256`. -/
  | lit : Nat → Expr L F Γ .uint
  /-- `uint256` state variable read. -/
  | load : SVar L .scalar → Expr L F Γ .uint
  /-- `address` state variable read. -/
  | loadAddr : SVar L .addr → Expr L F Γ .addr
  /-- `mapping(address => uint256)` read. -/
  | index : SVar L .mapping → Expr L F Γ .addr → Expr L F Γ .uint
  /-- Checked `+`/`-` on `uint256`, reverting with `Panic(0x11)`. -/
  | arith : ArithOp → Expr L F Γ .uint → Expr L F Γ .uint → Expr L F Γ .uint
  /-- Internal call of an already-registered `view`/`pure` function that
  returns one value. Arguments are in declaration order and evaluate left
  to right. Effectful internals are `Stmt.callStmt` only: pinned solc 0.8.x
  legacy codegen evaluates those calls before the other operand / old-read. -/
  | call : {ts : List Ty} →
      FVar F ⟨ts.reverse, [t]⟩ → Args L F Γ ts → Expr L F Γ t
  deriving ToExpr

/-- Declaration-order arguments of an internal call. -/
inductive Args (L : Layout) (F : Fns) (Γ : Ctx) : List Ty → Type where
  | nil : Args L F Γ []
  | cons : Expr L F Γ t → Args L F Γ ts → Args L F Γ (t :: ts)
  deriving ToExpr
end

/-- Assignment targets: a `uint256` state variable or one mapping entry.
Address writes use `Stmt.assignAddr`. -/
inductive LVal (L : Layout) (F : Fns) (Γ : Ctx) : Type where
  | scalar : SVar L .scalar → LVal L F Γ
  | mapping : SVar L .mapping → Expr L F Γ .addr → LVal L F Γ
  deriving ToExpr

/-- Statements of the accepted subset, in source order, ending in either
`done` (no return value) or `ret` of a single value. -/
inductive Stmt (L : Layout) (F : Fns) : Ctx → Ret → Type where
  /-- The end of a body that returns nothing. -/
  | done : Stmt L F Γ []
  /-- A terminal `return e;`. -/
  | ret : Expr L F Γ t → Stmt L F Γ [t]
  /-- `lval op= rhs;` followed by the rest of the body. `+=`/`-=` are uint-only. -/
  | assign : LVal L F Γ → AssignOp → Expr L F Γ .uint → Stmt L F Γ r → Stmt L F Γ r
  /-- `addr = rhs;` followed by the rest of the body. -/
  | assignAddr : SVar L .addr → Expr L F Γ .addr → Stmt L F Γ r → Stmt L F Γ r
  /-- `uint256 x = e;` (or a parameter), followed by the rest of the body. -/
  | local_ : Expr L F Γ .uint → Stmt L F (.uint :: Γ) r → Stmt L F Γ r
  /-- `if (a < b) revert E();` with `E()` stored verbatim, followed by the rest
  of the body. -/
  | guard : Expr L F Γ .uint → Expr L F Γ .uint → String → Stmt L F Γ r → Stmt L F Γ r
  /-- Internal call of an already-registered void function, then the rest. -/
  | callStmt : {ts : List Ty} →
      FVar F ⟨ts.reverse, []⟩ → Args L F Γ ts → Stmt L F Γ r → Stmt L F Γ r
  deriving ToExpr

end SolidityImporter.Sol

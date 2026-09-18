/-
  The Solidity subset the Vault importer accepts, as an intrinsically typed
  inductive family.

  Ill-typed programs are unrepresentable: reading a `uint256` state variable
  yields a `uint`, a mapping index must be an `addr`, a `uint256` local can only
  be bound to a `uint`, and `Stmt L Γ r` only ever produces a value of type `r`.
  The parser in `Importer.lean` is the only producer of these terms and
  `Semantics.lean` is the only place that gives them meaning.

  `Ctx` is a de Bruijn context: index 0 is the innermost binder. `Layout` is the
  imported state-variable order, which the importer keeps in lockstep with the
  `<var>Slot` handles it registers.
-/

import Lean

open Lean

namespace SolidityImporter.Sol

/-- Types of the accepted subset: `uint256` and `address`. -/
inductive Ty where
  | uint : Ty
  | addr : Ty
  deriving DecidableEq, Repr, Inhabited, ToExpr

/-- What an imported function returns. -/
inductive Ret where
  | unit : Ret
  | uint : Ret
  deriving DecidableEq, Repr, Inhabited, ToExpr

/-- Shape of an imported state variable. -/
inductive StorageTy where
  | scalar : StorageTy
  | mapping : StorageTy
  deriving DecidableEq, Repr, Inhabited, ToExpr

/-- Parameter/local context, de Bruijn order. -/
abbrev Ctx := List Ty

/-- Imported state variables, in importer field order. -/
abbrev Layout := List StorageTy

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

/-- `uint256`-valued expressions: locals, `msg.sender`, literals, state reads and
checked `+`/`-`. -/
inductive Expr (L : Layout) (Γ : Ctx) : Ty → Type where
  /-- A parameter or local. -/
  | var : Var Γ t → Expr L Γ t
  /-- `msg.sender`. -/
  | sender : Expr L Γ .addr
  /-- A numeric literal; the parser enforces `n < 2^256`. -/
  | lit : Nat → Expr L Γ .uint
  /-- `uint256` state variable read. -/
  | load : SVar L .scalar → Expr L Γ .uint
  /-- `mapping(address => uint256)` read. -/
  | index : SVar L .mapping → Expr L Γ .addr → Expr L Γ .uint
  /-- Checked `+`/`-` on `uint256`, reverting with `Panic(0x11)`. -/
  | arith : ArithOp → Expr L Γ .uint → Expr L Γ .uint → Expr L Γ .uint
  deriving ToExpr

/-- Assignment targets: a `uint256` state variable, or one mapping entry. -/
inductive LVal (L : Layout) (Γ : Ctx) : Type where
  | scalar : SVar L .scalar → LVal L Γ
  | mapping : SVar L .mapping → Expr L Γ .addr → LVal L Γ
  deriving ToExpr

/-- Statements of the accepted subset, in source order, ending in either
`done` (no return value) or `ret` of a `uint256`. -/
inductive Stmt (L : Layout) : Ctx → Ret → Type where
  /-- The end of a body that returns nothing. -/
  | done : Stmt L Γ .unit
  /-- A terminal `return e;`. -/
  | ret : Expr L Γ .uint → Stmt L Γ .uint
  /-- `lval op= rhs;` followed by the rest of the body. -/
  | assign : LVal L Γ → AssignOp → Expr L Γ .uint → Stmt L Γ r → Stmt L Γ r
  /-- `uint256 x = e;` (or a parameter), followed by the rest of the body. -/
  | local_ : Expr L Γ .uint → Stmt L (.uint :: Γ) r → Stmt L Γ r
  /-- `if (a < b) revert E();` with `E()` stored verbatim, followed by the rest
  of the body. -/
  | guard : Expr L Γ .uint → Expr L Γ .uint → String → Stmt L Γ r → Stmt L Γ r
  deriving ToExpr

end SolidityImporter.Sol

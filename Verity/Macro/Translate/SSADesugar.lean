import Lean
import Verity.Macro.Functions
import Verity.Macro.Storage
import Verity.Macro.Types
import Verity.Macro.Syntax

namespace Verity.Macro.SSADesugar

open Lean
open Lean.Elab
open Lean.Elab.Command

set_option hygiene false

/-!
# SSA & Syntax Desugaring Pass (`verity_contract` v2)

Closes the Pareto macro ergonomics issues across the `verity_contract`
translation and executable lowering pipeline:
- `#2427`: `let mut`, `:=` / `←` reassignments interleaved with monadic `←`
  binds, one-armed `if cond then body`, and `Int256` / `Bool` ternary
  conditionals (`if cond then a else b` / `ite cond a b`).
- `#2421`: Hygienic discard bindings (`let _ ← f ...`, `let _ := ...`,
  including typed and `let mut _` variants).
- `#2434`: Boolean negation (`!b`) in expressions and contract constants.
- `#2431`: 0-argument internal helpers (`helper()`, `helper ()`, and bare
  `helper`) in bind, expression, and statement positions.
- `#2423`: Root-qualified identifier helpers (`_root_.`) preventing namespace
  shadowing inside `Contracts.<ContractName>`.
-/

/-- Tracks the current SSA version of a local variable in a `do` block. -/
structure SSAVarVersion where
  baseName : String
  version : Nat
  isMutable : Bool
  deriving DecidableEq, Repr

/-- Pure SSA version environment for imperative-to-SSA local variable tracking. -/
structure SSAEnv where
  versions : List SSAVarVersion := []
  deriving DecidableEq, Repr

namespace SSAEnv

def empty : SSAEnv := ⟨[]⟩

def lookupEntry? (env : SSAEnv) (name : String) : Option SSAVarVersion :=
  env.versions.find? (fun entry => entry.baseName == name)

def lookupVersion? (env : SSAEnv) (name : String) : Option Nat :=
  (env.lookupEntry? name).map (·.version)

def ssaVersionedName (baseName : String) (version : Nat) : String :=
  if version == 0 then baseName else s!"{baseName}__ssa_{version}"

def currentSSAName? (env : SSAEnv) (name : String) : Option String :=
  (env.lookupEntry? name).map (fun entry => ssaVersionedName entry.baseName entry.version)

def bindVar (env : SSAEnv) (name : String) (isMutable : Bool) : SSAEnv × String :=
  let nextVer := match env.lookupVersion? name with
    | some v => v + 1
    | none => 0
  let entry : SSAVarVersion := { baseName := name, version := nextVer, isMutable := isMutable }
  let filtered := env.versions.filter (fun e => e.baseName != name)
  (⟨entry :: filtered⟩, ssaVersionedName name nextVer)

def rebindVar (env : SSAEnv) (name : String) : Option (SSAEnv × String) :=
  match env.lookupEntry? name with
  | some entry =>
      if entry.isMutable then
        let nextVer := entry.version + 1
        let updated : SSAVarVersion := { entry with version := nextVer }
        let filtered := env.versions.filter (fun e => e.baseName != name)
        some (⟨updated :: filtered⟩, ssaVersionedName name nextVer)
      else
        none
  | none => none

end SSAEnv

/-- Desugar a one-armed `if cond then thenBranch` into
    `if cond then thenBranch else pure ()` (#2427). -/
def desugarOneArmedIfDoElem?
    (elem : TSyntax `doElem) : CommandElabM (Option (TSyntax `doElem)) := do
  match elem with
  | `(doElem| if $cond:term then $thenBranch:doSeq) =>
      some <$> `(doElem| if $cond:term then $thenBranch:doSeq else pure ())
  | _ => pure none

/-- Desugar type-annotated `let` / `let mut` `doElem` forms so they flow
    uniformly through type validation, CompilationModel translation, and
    executable lowering (#2427). -/
def desugarTypedDoElem?
    (elem : TSyntax `doElem) : CommandElabM (Option (TSyntax `doElem)) := do
  match elem with
  | `(doElem| let $name:ident : $_ty:term := $rhs:term) =>
      some <$> `(doElem| let $name:ident := $rhs:term)
  | `(doElem| let $name:ident : $_ty:term ← $rhs:term) =>
      some <$> `(doElem| let $name:ident ← $rhs:term)
  | `(doElem| let mut $name:ident : $_ty:term := $rhs:term) =>
      some <$> `(doElem| let mut $name:ident := $rhs:term)
  | `(doElem| let mut $name:ident : $_ty:term ← $rhs:term) =>
      some <$> `(doElem| let mut $name:ident ← $rhs:term)
  | _ => pure none

/-- Generate a collision-free discard local name while preserving the expected
    base prefix (`"discard"` or `"__discard"`) for CompilationModel parity (#2421). -/
def freshHygienicDiscardName
    (base : String)
    (params : Array ParamDecl)
    (localNames : Array String)
    (mutableLocals : Array String := #[]) : String :=
  let used :=
    (params.map (·.name)) ++
    localNames ++
    mutableLocals
  Compiler.CompilationModel.pickFreshName base used.toList

/-- Desugar discard bindings (`let _ := ...`, `let _ ← ...`, `let mut _ := ...`,
    `let mut _ ← ...`, and typed variants) into fresh synthetic local bindings
    (#2421). -/
def desugarDiscardDoElem?
    (pureBase : String)
    (bindBase : String)
    (params : Array ParamDecl)
    (localNames : Array String)
    (mutableLocals : Array String)
    (elem : TSyntax `doElem) : CommandElabM (Option (TSyntax `doElem)) := do
  match elem with
  | `(doElem| let _ := ($rhs:term : $_ty:term))
  | `(doElem| let _ : $_ty:term := $rhs:term)
  | `(doElem| let mut _ : $_ty:term := $rhs:term)
  | `(doElem| let mut _ := $rhs:term)
  | `(doElem| let _ := $rhs:term) =>
      let discardName := freshHygienicDiscardName pureBase params localNames mutableLocals
      let discardIdent := mkIdent (Name.mkSimple discardName)
      some <$> `(doElem| let $discardIdent:ident := $rhs:term)
  | `(doElem| let _ : $_ty:term ← $rhs:term)
  | `(doElem| let mut _ : $_ty:term ← $rhs:term)
  | `(doElem| let mut _ ← $rhs:term)
  | `(doElem| let _ ← $rhs:term) =>
      let discardName := freshHygienicDiscardName bindBase params localNames mutableLocals
      let discardIdent := mkIdent (Name.mkSimple discardName)
      some <$> `(doElem| let $discardIdent:ident ← $rhs:term)
  | _ => pure none

/-- Flatten nested `(doElem| do $[$inner:doElem]*)` blocks produced when
    `wrapBinds` hoists monadic calls before a `let` / `let mut` / `:=` / `←`
    statement. Keeping hoisted binds in the enclosing `doSeq` scope ensures
    `let mut` and `let` bindings remain visible to subsequent statements across
    monadic binds (#2427). -/
partial def flattenHoistedDoElem (elem : TSyntax `doElem) : Array (TSyntax `doElem) :=
  match elem with
  | `(doElem| do $[$inner:doElem]*) =>
      inner.foldl (fun acc child => acc ++ flattenHoistedDoElem child) #[]
  | _ => #[elem]

/-- Convert a rewritten `let x ← rhs` / `let x := rhs` element back to its
    `let mut` counterpart after executable storage/call rewriting (#2427). -/
def rewriteBindElemToMut (elem : TSyntax `doElem) : CommandElabM (TSyntax `doElem) := do
  match elem with
  | `(doElem| let $name:ident ← $rhs:term) =>
      `(doElem| let mut $name:ident ← $rhs:term)
  | `(doElem| let $name:ident := $rhs:term) =>
      `(doElem| let mut $name:ident := $rhs:term)
  | `(doElem| let ($name:ident, _) ← $rhs:term) =>
      `(doElem| let mut $name:ident ← do
          let (__verity_mut_res, _) ← $rhs:term
          pure __verity_mut_res)
  | _ => pure elem

/-- Convert a rewritten `let x ← rhs` / `let x := rhs` element into a mutable
    reassignment `x ← rhs` / `x := rhs` (#2427). -/
def rewriteBindElemToReassign (elem : TSyntax `doElem) : CommandElabM (TSyntax `doElem) := do
  match elem with
  | `(doElem| let $name:ident ← $rhs:term) =>
      `(doElem| $name:ident ← $rhs:term)
  | `(doElem| let $name:ident := $rhs:term) =>
      `(doElem| $name:ident := $rhs:term)
  | `(doElem| let ($name:ident, _) ← $rhs:term) =>
      `(doElem| $name:ident ← do
          let (__verity_reassign_res, _) ← $rhs:term
          pure __verity_reassign_res)
  | _ => pure elem

/-- Extract the negated operand from `!a` (#2434). -/
def desugarBoolNotTerm? (stx : Term) : Option Term :=
  match stripParens stx with
  | `(term| ! $a:term) => some a
  | _ => none

/-- Extract `(cond, thenVal, elseVal)` from either `ite cond thenVal elseVal`
    or native `if cond then thenVal else elseVal` (#2427). -/
def desugarTernaryTerm? (stx : Term) : Option (Term × Term × Term) :=
  match stripParens stx with
  | `(term| ite $cond:term $thenVal:term $elseVal:term) =>
      some (cond, thenVal, elseVal)
  | `(term| if $cond:term then $thenVal:term else $elseVal:term) =>
      some (cond, thenVal, elseVal)
  | _ => none

/-- True when `stx` is the unit literal `()` (`Unit.unit`). -/
def isUnitLiteralTerm (stx : Term) : Bool :=
  match stripParens stx with
  | `(term| ()) | `(term| Unit.unit) => true
  | _ => false

/-- Normalize argument syntax for 0-parameter internal helpers (#2431).
    When a user writes `helper ()` (with whitespace before `()`), Lean parses
    it as an application of `helper` to one `()` argument. If `functions`
    declares a 0-parameter helper with that name (and no 1-parameter overload),
    strip the unit argument so `helper ()`, `helper()`, and `helper` behave
    identically. -/
def normalizeZeroArgHelperArgs
    (functions : Array FunctionDecl)
    (fnName : String)
    (args : Array Term) : Array Term :=
  if args.size == 1 && isUnitLiteralTerm args[0]! then
    let matchesName (fn : FunctionDecl) : Bool :=
      fn.name == fnName || toString fn.ident.getId == fnName ||
        fnName.endsWith ("." ++ fn.name)
    let hasZeroArg := functions.any (fun fn => matchesName fn && fn.params.isEmpty)
    let hasOneArg := functions.any (fun fn => matchesName fn && fn.params.size == 1)
    if hasZeroArg && !hasOneArg then #[] else args
  else
    args

/-- Extract `(fnIdent, argTerms)` from a helper call syntax in paren form
    `fn(a, b)`, juxtaposition form `fn a b`, or bare 0-arg form `fn` (#2431). -/
def helperAppSyntaxParts? (stx : Term) : Option (Ident × Array Term) :=
  match stripParens stx with
  | `(term| $fn:ident($[$args:term],*)) =>
      some (fn, args.map fun a => (⟨a.raw⟩ : Term))
  | `(term| $fn:ident $args:term*) =>
      some (fn, args.map fun a => (⟨a.raw⟩ : Term))
  | `(term| $fn:ident) =>
      some (fn, #[])
  | _ => none

/-- True when `n` already begins with `_root_.`. -/
def isRootQualifiedName (n : Name) : Bool :=
  match nameComponents n with
  | "_root_" :: _ => true
  | _ => false

/-- Prefix a `Name` with `_root_.` unless it is already root-qualified (#2423). -/
def qualifyRootName (n : Name) : Name :=
  if isRootQualifiedName n then n else `_root_ ++ n

/-- Prefix an `Ident` with `_root_.` while preserving source information (#2423). -/
def qualifyRootIdent (id : Ident) : Ident :=
  mkIdentFrom id (qualifyRootName id.getId)

end Verity.Macro.SSADesugar

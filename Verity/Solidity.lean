import Lean
import Verity.Stdlib.Math

/-! Proof-only, closed typed-AST importer. No source renderer or parse-back. -/
open Lean Meta Elab Command

namespace SolidityImporter

private def field (j : Json) (key : String) : MetaM Json :=
  match j.getObjVal? key with
  | .ok v => pure v
  | .error e => throwError "{e}"
private def str (j : Json) : MetaM String :=
  match j.getStr? with
  | .ok v => pure v
  | .error e => throwError "{e}"
private def num (j : Json) : MetaM Nat :=
  match j.getNat? with
  | .ok v => pure v
  | .error e => throwError "{e}"
private def arr (j : Json) : MetaM (Array Json) :=
  match j.getArr? with
  | .ok v => pure v
  | .error e => throwError "{e}"
private def item (j : Json) (i : Nat) : MetaM Json := do
  let a ← arr j
  if h : i < a.size then pure a[i] else throwError "missing AST operand"
private def tag (j : Json) : MetaM String := item j 0 >>= str
private def uint := mkConst ``Verity.Core.Uint256
private def address := mkConst ``Verity.Core.Address
private def unit := mkConst ``Unit
private def valueType (s : String) : MetaM Expr :=
  match s with
  | "uint256" => pure uint
  | "address" => pure address
  | "unit" => pure unit
  | _ => throwError "unsupported type {s}"
private def ret (x : Expr) : MetaM Expr := mkAppM ``Verity.pure #[x]
private def seq (m t : Expr) (k : Expr → MetaM Expr) : MetaM Expr :=
  withLocalDeclD `value t fun x => do
    let body ← k x
    mkAppM ``Verity.bind #[m, ← mkLambdaFVars #[x] body]

private def register (name : Name) (value : Expr) : MetaM Unit := do
  if (← getEnv).contains name then throwError "declaration collision: {name}"
  let value ← instantiateMVars value
  let type ← instantiateMVars (← inferType value)
  if value.hasMVar || value.hasFVar || type.hasMVar || type.hasFVar then
    throwError "unclosed imported declaration {name}"
  addDecl (.defnDecl {
    name := name
    levelParams := []
    type := type
    value := value
    hints := .regular 0
    safety := .safe }) (forceExpose := true)
  compileDecls #[name] (logErrors := false)

private abbrev Locals := List (Nat × Expr)
private abbrev Slots := List (Nat × Expr)
private def lookup (xs : List (Nat × Expr)) (id : Nat) : MetaM Expr :=
  match xs.lookup id with
  | some e => pure e
  | none => throwError "unresolved declaration id {id}"

private def checked (op : String) (a b : Expr) : MetaM Expr := do
  let fn ← match op with
    | "+" | "+=" => pure ``Verity.Stdlib.Math.safeAdd
    | "-" | "-=" => pure ``Verity.Stdlib.Math.safeSub
    | _ => throwError "unsupported arithmetic {op}"
  mkAppM ``Verity.Stdlib.Math.requireSomeUint #[← mkAppM fn #[a, b], mkStrLit "Panic(0x11)"]

private partial def eval (slots : Slots) (locals : Locals) (j : Json)
    (k : Expr → MetaM Expr) : MetaM Expr := do
  match ← tag j with
  | "local" => k (← lookup locals (← num (← item j 1)))
  | "number" => k (← mkAppM ``Verity.Core.Uint256.ofNat #[mkNatLit (← num (← item j 1))])
  | "sender" => seq (mkConst ``Verity.msgSender) address k
  | "read" =>
    seq (← mkAppM ``Verity.getStorage #[← lookup slots (← num (← item j 1))]) uint k
  | "map" =>
    let slot ← lookup slots (← num (← item j 1))
    eval slots locals (← item j 2) fun key => do
      seq (← mkAppM ``Verity.getMapping #[slot, key]) uint k
  | "+" | "-" =>
    let op ← tag j
    eval slots locals (← item j 1) fun a => do
      eval slots locals (← item j 2) fun b => do
        seq (← checked op a b) uint k
  | t => throwError "unsupported expression tag {t}"

private partial def body (slots : Slots) (locals : Locals) (nodes : List Json) : MetaM Expr := do
  match nodes with
  | [] => ret (mkConst ``Unit.unit)
  | j :: rest =>
    match ← tag j with
    | "return" =>
      unless rest.isEmpty do throwError "nonterminal return"
      eval slots locals (← item j 1) ret
    | "let" =>
      let id ← num (← item j 1)
      eval slots locals (← item j 2) fun v => body slots ((id, v) :: locals) rest
    | "guard" =>
      let cond ← item j 1
      unless (← tag cond) == "<" do throwError "unsupported guard"
      eval slots locals (← item cond 1) fun a => do
        eval slots locals (← item cond 2) fun b => do
          let av ← mkAppM ``Verity.Core.Uint256.val #[a]
          let bv ← mkAppM ``Verity.Core.Uint256.val #[b]
          let allowed ← mkAppM ``Nat.ble #[bv, av]
          let guard ← mkAppM ``Verity.require #[allowed, mkStrLit (← str (← item j 2))]
          seq guard unit fun _ => body slots locals rest
    | "write" =>
      let lhs ← item j 1
      let op ← str (← item j 2)
      let rhs ← item j 3
      let slot ← lookup slots (← num (← item lhs 1))
      let finish (key : Option Expr) : MetaM Expr := do
        let write (v : Expr) : MetaM Expr := do
          let m ← match key with
            | none => mkAppM ``Verity.setStorage #[slot, v]
            | some key => mkAppM ``Verity.setMapping #[slot, key, v]
          seq m unit fun _ => body slots locals rest
        if op == "=" then eval slots locals rhs write
        else
          let read ← match key with
            | none => mkAppM ``Verity.getStorage #[slot]
            | some key => mkAppM ``Verity.getMapping #[slot, key]
          seq read uint fun old => eval slots locals rhs fun rhs => do
            seq (← checked op old rhs) uint write
      match ← tag lhs with
      | "read" => finish none
      | "map" => eval slots locals (← item lhs 2) fun key => finish (some key)
      | _ => throwError "unsupported lvalue"
    | t => throwError "unsupported statement tag {t}"

private def nonpayable (m : Expr) : MetaM Expr :=
  seq (mkConst ``Verity.msgValue) uint fun value => do
    let n ← mkAppM ``Verity.Core.Uint256.val #[value]
    let zero ← mkAppM ``Nat.beq #[n, mkNatLit 0]
    let guard ← mkAppM ``Verity.require #[zero, mkStrLit "Nonpayable"]
    seq guard unit fun _ => pure m

private partial def params (ps : List Json) (locals : Locals)
    (k : Locals → MetaM Expr) : MetaM Expr := do
  match ps with
  | [] => k locals
  | p :: ps =>
    let id ← num (← field p "id")
    let name ← str (← field p "name")
    withLocalDeclD (Name.mkSimple name) (← valueType (← str (← field p "type"))) fun x => do
      mkLambdaFVars #[x] (← params ps ((id, x) :: locals) k)

private def importModel (ns : Name) (model : Json) : MetaM Unit := do
  if debug.skipKernelTC.get (← getOptions) then throwError "kernel checking must be enabled"
  let fs ← arr (← field model "fields")
  let functions ← arr (← field model "functions")
  -- Preflight every name before registering any declaration.
  let mut names := #[ns ++ `sourceDigest]
  for f in fs do
    names := names.push (ns ++ Name.mkSimple (← str (← field f "name")))
    if let .str s ← field f "getter" then names := names.push (ns ++ Name.mkSimple s)
  for f in functions do names := names.push (ns ++ Name.mkSimple (← str (← field f "name")))
  for i in [:names.size] do
    if (← getEnv).contains names[i]! || (names.extract 0 i).contains names[i]! then
      throwError "declaration collision: {names[i]!}"
  let mut slots := []
  for f in fs do
    let mapping := (← field f "mapping") == Json.bool true
    let ty ← if mapping then mkArrow address uint else pure uint
    let slot ← mkAppOptM ``Verity.StorageSlot.mk #[some ty, some (mkNatLit (← num (← field f "slot")))]
    let name := ns ++ Name.mkSimple (← str (← field f "name"))
    register name slot
    slots := (← num (← field f "id"), mkConst name) :: slots
  for f in fs do
    if let .str getter ← field f "getter" then
      let slot ← lookup slots (← num (← field f "id"))
      let value ← if (← field f "mapping") == Json.bool true then
          withLocalDeclD `account address fun x => do
            mkLambdaFVars #[x] (← nonpayable (← mkAppM ``Verity.getMapping #[slot, x]))
        else nonpayable (← mkAppM ``Verity.getStorage #[slot])
      register (ns ++ Name.mkSimple getter) value
  for f in functions do
    let value ← params (← arr (← field f "params")).toList [] fun locals => do
      let code ← body slots locals (← arr (← field f "body")).toList
      let expected ← mkAppM ``Verity.Contract #[← valueType (← str (← field f "returns"))]
      unless ← isDefEq (← inferType code) expected do
        throwError "imported body does not match typed AST return signature"
      nonpayable code
    register (ns ++ Name.mkSimple (← str (← field f "name"))) value
  register (ns ++ `sourceDigest) (mkStrLit (← str (← field model "digest")))

syntax (name := solidityContract) "solidity_contract " ident " from " str : command

@[command_elab solidityContract] def elabSolidityContract : CommandElab := fun stx => do
  let saved ← getEnv
  try
    let file ← getFileName
    let authored ← IO.FS.realPath file
    let source := authored.parent.getD "." / stx[3].isStrLit?.get!
    let mut root := authored.parent.getD "."
    while !(← (root / "lakefile.lean").pathExists) do
      let some p := root.parent | throwError "package root not found"
      if p == root then throwError "package root not found"
      root := p
    let output ← IO.Process.output {cmd := "python3", args := #[(root / "scripts/solidity_contract.py").toString, source.toString]}
    unless output.exitCode == 0 do throwError "Solidity import failed:\n{output.stderr}"
    let model ← match Json.parse output.stdout with
      | .ok j => pure j
      | .error e => throwError "invalid frontend JSON: {e}"
    let ns := (← getCurrNamespace) ++ stx[1].getId
    -- A checking error must be raised inside this transaction, not in a later
    -- async task after partial declarations have escaped the rollback handler.
    liftTermElabM <| withOptions (Elab.async.set · false) (importModel ns model)
  catch e =>
    setEnv saved
    throw e

end SolidityImporter

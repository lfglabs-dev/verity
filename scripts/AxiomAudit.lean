import Lean

/-!
Copyright (c) 2025 skbaek
Copyright (c) 2025 Thomas Marchand

Released under the MIT License. This file is derived from Jaune's
`scripts/AxiomAudit.lean` (Copyright (c) 2025 skbaek); the multi-prefix union is
a Verity extension (Copyright (c) 2025 Thomas Marchand). See `LICENSE.md`.

# The from-scratch axiom walker every Verity axiom audit uses

This module is the single definition of how an axiom audit learns which axioms
a declaration depends on. It imports only `Lean` and is a root of the
`Assurance` library, so a downstream package can import it and state its own
audits with the same walk.

Why not Lean's own report. Since Lean v4.30.0 `#print axioms` on an imported
constant reads a per-module result that was precomputed when that module's
`.olean` was written. The precomputation shares one cache across the module
and breaks the inductive/constructor cycle with an empty sentinel entry that it
cannot tell apart from a finished result, so an inductive reached first through
its own constructor can be exported as axiom-free, and every declaration that
reaches the axiom only through that inductive inherits the under-report
(https://github.com/leanprover/lean4/issues/15226). Which names are hit depends
on hash iteration order, so an unrelated edit can turn such an audit green or
red. By the user's decision of 2026-09-24, no audit takes its verdict from that
report, or from `Lean.collectAxioms`, until the issue is fixed.

What this walk does instead. For each audited name (or, for the union
audit below, for the whole set of roots together) it starts with an empty
visited set and follows, through `Environment.find?` alone, every constant used
by a declaration's type, by the value of a definition, theorem or opaque, and
every constructor of an inductive. It keeps no per-constant result between
walks or within a walk (a constant is visited at most once per walk, and
visiting it only adds that constant's direct references), and it reads no
precomputed per-module table, so the inductive/constructor cycle cannot hide
anything: whichever end the walk enters first, it reaches the other and walks
it. The result is the set of `axiom` declarations reached, which includes
`sorryAx`, `Lean.ofReduceBool` and `native_decide`/`bv_decide` auxiliary axioms.

Three commands use it, through one traversal (`walkMany`; `walk` is its
single-root case). None applies namespace resolution: a name that does not
resolve exactly is an elaboration error, and so is a referenced constant that
the environment does not contain.

* `#full_axioms X` reports, in its own task so a file of rows runs on every
  core, one line per audited name, sorted by the axiom names' text:

      FULL-AXIOMS '<name>': [<axiom>, <axiom>, ...]

  An empty list means no axiom at all.

* `#expect_axioms X [ax₁, …, axₙ]` fails elaboration unless the walk's set is
  exactly the listed one, in both directions:

      AXIOM mismatch for <name>: expected [...], actual [...]

  and logs `AXIOM OK <name>: [...]` otherwise.

* `#union_axioms_of_modules P [ax₁, …, axₙ]` audits a whole library in one walk
  with one shared visited set. Its roots are every constant recorded in the
  `constNames` of every imported module named `P` or `P.…` (all kinds, private
  names and elaborator auxiliaries included; code-generator names are not kernel
  constants and are not roots). A comma-separated prefix list audits the union of
  those populations in the same one walk. It logs one line

      UNION-AXIOMS 'P': [<axiom>, ...] roots=<n> modules=<m> visited=<v>

  and fails elaboration if no module matches (an empty population is never
  green), if the walk reaches a constant the environment does not contain, or
  if the union contains an axiom outside the allowed list (default
  `[propext, Classical.choice, Quot.sound]`; `[]` allows none). A failure by an
  axiom locates it: for each offending axiom, up to 20 roots that reach it,
  nearest first, each with the chain of constants from the root to the axiom.
  Controls: `scripts/UnionAxiomsControls.lean`.
-/

namespace Jaune.AxiomAudit

open Lean Elab Command

/-- The axioms reachable from any of `roots`, any referenced constants that the
environment does not contain, and the number of distinct constants visited
(roots included, absent ones too). One visited set is shared by all roots, so a
constant is visited once per call however many roots reach it; nothing else is
cached, and no per-module table is read. -/
def walkMany (env : Environment) (roots : Array Name) :
    NameSet × NameSet × Nat := Id.run do
  -- Outside the module system this is the identity. Under it, imported
  -- private bodies are only visible with exporting off.
  let env := env.setExporting false
  let mut seen : Std.HashSet Name := {}
  let mut stack : Array Name := #[]
  for r in roots do
    unless seen.contains r do
      seen := seen.insert r
      stack := stack.push r
  let mut axioms : NameSet := {}
  let mut missing : NameSet := {}
  while h : 0 < stack.size do
    let c := stack.back
    stack := stack.pop
    match env.find? c with
    | none => missing := missing.insert c
    | some info =>
      if info matches .axiomInfo _ then
        axioms := axioms.insert c
      let mut refs := info.type.getUsedConstants
      match info with
      | .defnInfo v => refs := refs ++ v.value.getUsedConstants
      | .thmInfo v => refs := refs ++ v.value.getUsedConstants
      | .opaqueInfo v => refs := refs ++ v.value.getUsedConstants
      | .inductInfo v => refs := refs ++ v.ctors.toArray
      | _ => pure ()
      for n in refs do
        unless seen.contains n do
          seen := seen.insert n
          stack := stack.push n
  return (axioms, missing, seen.size)

/-- The axioms reachable from `root`, and any referenced constants that the
environment does not contain. A fresh visited set per call; nothing cached. -/
def walk (env : Environment) (root : Name) : NameSet × NameSet :=
  let (axioms, missing, _) := walkMany env #[root]
  (axioms, missing)

/-- Every kernel constant declared by an imported module whose name extends any
prefix in `pfxs`, private names and elaborator auxiliaries included, as recorded
in the modules' own `constNames`; and how many modules matched. A module matching
more than one prefix is counted once, and so is a constant declared in more than
one matched module. (`extraConstNames` holds code-generator names such as
`_closed_1`, `_redArg` and `_boxed`, which are not kernel constants.) -/
def moduleRootsOf (env : Environment) (pfxs : Array Name) : Array Name × Nat := Id.run do
  let mut roots : Array Name := #[]
  let mut have_ : Std.HashSet Name := {}
  let mut mods := 0
  for i in [0:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]!
    if pfxs.any (fun pfx => pfx.isPrefixOf m) then
      mods := mods + 1
      let d := env.header.moduleData[i]!
      for c in d.constNames do
        unless have_.contains c do
          have_ := have_.insert c
          roots := roots.push c
  return (roots, mods)

/-- Every kernel constant declared by an imported module whose name is `pfx` or
extends it, private names and elaborator auxiliaries included, as recorded in
the modules' own `constNames`; and how many modules matched. (`extraConstNames`
holds code-generator names such as `_closed_1`, `_redArg` and `_boxed`, which
are not kernel constants.) -/
def moduleRoots (env : Environment) (pfx : Name) : Array Name × Nat :=
  moduleRootsOf env #[pfx]

/-- Where a failing union audit gets its evidence: for each name in `targets`
(offending axioms, or absent constants), up to `limit` of the `roots` that reach
it, nearest first, each with the chain of constants that leads from the root to
the target. One forward traversal builds the reverse reference graph and a
breadth-first search runs backwards from each target, so the cost is linear in
the reachable graph whatever the number of roots. -/
def locate (env : Environment) (roots : Array Name) (targets : Array Name)
    (limit : Nat := 20) : Array String := Id.run do
  let env := env.setExporting false
  let rootSet : Std.HashSet Name := Std.HashSet.ofArray roots
  -- reverse graph: constant ↦ constants that directly reference it
  let mut users : Std.HashMap Name (Array Name) := {}
  let mut seen : Std.HashSet Name := {}
  let mut stack : Array Name := #[]
  for r in roots do
    unless seen.contains r do
      seen := seen.insert r
      stack := stack.push r
  while h : 0 < stack.size do
    let c := stack.back
    stack := stack.pop
    if let some info := env.find? c then
      let mut refs := info.type.getUsedConstants
      match info with
      | .defnInfo v => refs := refs ++ v.value.getUsedConstants
      | .thmInfo v => refs := refs ++ v.value.getUsedConstants
      | .opaqueInfo v => refs := refs ++ v.value.getUsedConstants
      | .inductInfo v => refs := refs ++ v.ctors.toArray
      | _ => pure ()
      for n in refs do
        users := users.insert n ((users.getD n #[]).push c)
        unless seen.contains n do
          seen := seen.insert n
          stack := stack.push n
  let mut out : Array String := #[]
  for t in targets do
    -- breadth-first backwards from `t`; `next[c]` is the constant `c` was
    -- reached from, i.e. the next step of the chain from `c` towards `t`
    let mut next : Std.HashMap Name Name := {}
    let mut visited : Std.HashSet Name := ({} : Std.HashSet Name).insert t
    let mut queue : Array Name := #[t]
    let mut i := 0
    let mut found := 0
    while i < queue.size && found < limit do
      let c := queue[i]!
      i := i + 1
      if rootSet.contains c then
        found := found + 1
        let mut chain : List Name := [c]
        let mut cur := c
        while cur != t do
          cur := next.getD cur t
          chain := chain ++ [cur]
        let shown := if chain.length > 10 then
          (chain.take 4).map toString ++ ["…"] ++ (chain.drop (chain.length - 4)).map toString
        else chain.map toString
        out := out.push
          (if c == t then s!"  {t} is itself a root"
           else s!"  {t} <- root {c}: {" -> ".intercalate shown}")
      for u in users.getD c #[] do
        unless visited.contains u do
          visited := visited.insert u
          next := next.insert u c
          queue := queue.push u
    if found == 0 then
      out := out.push s!"  {t}: no root reaches it"
  return out

/-- The result of a union audit: the union of axioms reachable from the roots,
the roots and modules counted, and the constants visited. -/
structure UnionReport where
  axioms : Array String
  roots : Nat
  modules : Nat
  visited : Nat

/-- Recognize digits-and-underscores suffixes (`1_1`, `1_9`, …) emitted by Lean's
`native_decide` and `bv_decide` auxiliary axiom generators. -/
def isDigitsAndUnderscores (s : String) : Bool :=
  let parts := s.splitOn "_"
  !parts.isEmpty && parts.all (fun p => !p.isEmpty && p.all Char.isDigit)

/-- Match `<origin>._native.<kind>.ax_<digits>` and return `<origin>` when `<kind>`
matches (`"native_decide"` or `"bv_decide"`). -/
def generatedAuxAxiomOrigin? (kind : String) (axName : String) : Option String :=
  let marker := s!"._native.{kind}.ax_"
  match axName.splitOn marker with
  | [origin, suffix] =>
    if !origin.isEmpty && isDigitsAndUnderscores suffix then some origin else none
  | _ => none

/-- Parse one exact dotted constant name into a hierarchical `Lean.Name`. -/
def parseDottedName (s : String) : Name :=
  (s.splitOn ".").foldl (fun acc part => Name.str acc part) Name.anonymous

/-- If `axInfo` has the exact kernel shape emitted by `Lean.Meta.nativeEqTrue`
(`Lean/Meta/Native.lean`) — a safe axiom whose type is `@Eq.{1} Bool e Bool.true` for a
closed expression `e` whose `levelParams` match `collectLevelParams` — return `some e`. -/
def kernelNativeEqTrueLhs? (axInfo : AxiomVal) : Option Expr :=
  if axInfo.isUnsafe then
    none
  else
    match axInfo.type with
    | .app (.app (.app (.const ``Eq [u]) (.const ``Bool [])) lhs) (.const ``Bool.true []) =>
      let expectedLevels := (collectLevelParams {} lhs).params.toList
      if u == Level.succ Level.zero && !lhs.hasFVar && !lhs.hasMVar
          && axInfo.levelParams == expectedLevels then
        some lhs
      else
        none
    | _ => none

/-- Check that `axInfo` has the exact kernel shape emitted by `Lean.Meta.nativeEqTrue`
(`Lean/Meta/Native.lean`). -/
def isKernelNativeEqTrueAxiom (axInfo : AxiomVal) : Bool :=
  (kernelNativeEqTrueLhs? axInfo).isSome

/-- Look up synchronized declaration ranges for `ax` across both the current-module
(`.exported`) and imported-module (`.server`) declaration-range tables. -/
def findAuxDeclRanges? (env : Environment) (ax : Name) : Option DeclarationRanges :=
  Lean.declRangeExt.find? (asyncMode := .sync) (level := .exported) env ax <|>
    Lean.declRangeExt.find? (asyncMode := .sync) (level := .server) env ax

/-- Check whether `inner` lies completely within `outer`. -/
def isRangeWithin (inner outer : DeclarationRange) : Bool :=
  let startsAfter :=
    inner.pos.line > outer.pos.line
      || (inner.pos.line == outer.pos.line && inner.pos.column >= outer.pos.column)
  let endsBefore :=
    inner.endPos.line < outer.endPos.line
      || (inner.endPos.line == outer.endPos.line && inner.endPos.column <= outer.endPos.column)
  startsAfter && endsBefore

/-- Check that `ax` carries a tactic-token declaration range (`range == selectionRange`,
as emitted by `Lean.Meta.nativeEqTrue` calling `addDeclarationRangesFromSyntax` with
`selectionRangeStx := .missing`) whose span lies inside `orig`'s own declaration range
(`origRange.range`). Rejects handwritten `axiom` commands (`range != selectionRange`),
external command-macro `axiom` commands (span outside `orig`), and direct `addDecl` calls
without synchronized declaration ranges. -/
def hasTacticTokenAuxDeclRange (env : Environment) (orig ax : Name) : Bool :=
  match findAuxDeclRanges? env orig, findAuxDeclRanges? env ax with
  | some origR, some axR =>
    axR.range == axR.selectionRange && isRangeWithin axR.range origR.range
  | _, _ => false

/-- Re-compile and natively evaluate the closed `Bool` left-hand side `lhs` of a
`nativeEqTrue` auxiliary axiom inside `withoutModifyingEnv`, succeeding iff it evaluates
to `Bool.true` without throwing. -/
def evalKernelNativeEqTrueLhs (lhs : Expr) : CommandElabM Bool := do
  try
    liftTermElabM <| Lean.withoutModifyingEnv <|
      withTheReader Core.Context ({ · with maxHeartbeats := 0 }) do
        match (← Lean.Meta.nativeEqTrue `audit lhs) with
        | .success _ => pure true
        | .notTrue => pure false
  catch _ =>
    pure false

/-- Check structural kernel/environment authentication of a Lean-generated
`native_decide`/`bv_decide` auxiliary axiom `ax` for an allowlisted `origin`, returning
`some lhs` when:
1. `ax` has the exact `<origin>._native.<kind>.ax_<digits>` spelling for an `origin` in
   `allowedOrigins`;
2. `ax` is a safe `AxiomVal` of kernel `nativeEqTrue` shape (`@Eq.{1} Bool lhs Bool.true`);
3. `ax` has single-ref tactic declaration ranges (`range == selectionRange`) lying inside
   `origin`'s own declaration range;
4. `origin` exists in `env` as a theorem or definition in the exact same module as `ax`
   (`env.getModuleIdxFor? origin == env.getModuleIdxFor? ax`); and
5. `origin`'s own body (`value.getUsedConstants`) directly references `ax`. -/
def verifiedGeneratedAuxAxiomLhs? (env : Environment) (kind : String)
    (allowedOrigins : Array String) (ax : Name) : Option Expr :=
  let env := env.setExporting false
  match generatedAuxAxiomOrigin? kind (toString ax) with
  | none => none
  | some origStr =>
    if !allowedOrigins.contains origStr then
      none
    else
      let orig := parseDottedName origStr
      match env.find? ax, env.find? orig with
      | some (.axiomInfo axVal), some origInfo =>
        match kernelNativeEqTrueLhs? axVal with
        | none => none
        | some lhs =>
          let usedByOrigin :=
            match origInfo with
            | .thmInfo tv => tv.value.getUsedConstants.contains ax
            | .defnInfo dv => dv.value.getUsedConstants.contains ax
            | _ => false
          if hasTacticTokenAuxDeclRange env orig ax
              && env.getModuleIdxFor? orig == env.getModuleIdxFor? ax
              && usedByOrigin then
            some lhs
          else
            none
      | _, _ => none

/-- Full CommandElabM authentication of `ax` as a genuine Lean-generated auxiliary axiom
for an allowlisted `origin`: structural/range/reference checks plus re-running
`Lean.Meta.nativeEqTrue` on `lhs` under `withoutModifyingEnv`. -/
def verifyGeneratedAuxAxiomM (env : Environment) (kind : String)
    (allowedOrigins : Array String) (ax : Name) : CommandElabM Bool := do
  match verifiedGeneratedAuxAxiomLhs? env kind allowedOrigins ax with
  | none => pure false
  | some lhs => evalKernelNativeEqTrueLhs lhs

/-- Check whether `ax` is in `allowed` or is a structurally authenticated Lean auxiliary
axiom whose exact origin declaration is explicitly permitted. Callers in `CommandElabM`
(`unionCheckM`, `reportPrintAxiomsForRootsM`, `isAllowedUnionAxiomM`) additionally
re-evaluate every candidate auxiliary axiom's `Bool` LHS via `Lean.Meta.nativeEqTrue`. -/
def isAllowedUnionAxiom (env : Environment) (allowed : Array String)
    (allowedNativeOrigins : Array String := #[])
    (allowedBvOrigins : Array String := #[])
    (ax : Name) : Bool :=
  allowed.contains (toString ax)
    || (verifiedGeneratedAuxAxiomLhs? env "native_decide" allowedNativeOrigins ax).isSome
    || (verifiedGeneratedAuxAxiomLhs? env "bv_decide" allowedBvOrigins ax).isSome

/-- Full CommandElabM check whether `ax` is in `allowed` or is a kernel-authenticated and
natively re-evaluated auxiliary axiom of an explicitly allowlisted `origin`. -/
def isAllowedUnionAxiomM (env : Environment) (allowed : Array String)
    (allowedNativeOrigins : Array String := #[])
    (allowedBvOrigins : Array String := #[])
    (ax : Name) : CommandElabM Bool := do
  if allowed.contains (toString ax) then
    return true
  if ← verifyGeneratedAuxAxiomM env "native_decide" allowedNativeOrigins ax then
    return true
  verifyGeneratedAuxAxiomM env "bv_decide" allowedBvOrigins ax

/-- The union audit proper, over an explicit root list (the command feeds it the
module roots). Throws on an empty root list, on any reached constant absent from
the environment, and on any reached axiom not in `allowed` (or in the optional
explicit `native_decide`/`bv_decide` origin allowlists); the last two name
where the problem is (see `locate`). -/
def unionCheck (env : Environment) (label : String) (roots : Array Name)
    (modules : Nat) (allowed : Array String)
    (allowedNativeOrigins : Array String := #[])
    (allowedBvOrigins : Array String := #[]) : Except String UnionReport := do
  if roots.isEmpty || modules == 0 then
    throw s!"#union_axioms_of_modules: no constants found for {label} \
      ({modules} matching modules, {roots.size} roots); an empty population \
      audits nothing"
  let (axioms, missing, visited) := walkMany env roots
  unless missing.isEmpty do
    let ms := (missing.toList.toArray.qsort (fun a b => toString a < toString b))
    let where_ := locate env roots (ms.extract 0 5) 3
    throw s!"#union_axioms_of_modules: {label} reaches {ms.size} constants absent \
      from the environment, e.g. {(ms.extract 0 20).map toString}\n\
      {"\n".intercalate where_.toList}"
  let sorted := axioms.toList.toArray.qsort (fun a b => toString a < toString b)
  let bad := sorted.filter (fun a =>
    !isAllowedUnionAxiom env allowed allowedNativeOrigins allowedBvOrigins a)
  unless bad.isEmpty do
    let where_ := locate env roots bad
    throw s!"#union_axioms_of_modules: {label} reaches axioms outside \
      {allowed.qsort (· < ·)}: {bad.map toString}\n{"\n".intercalate where_.toList}"
  return { axioms := sorted.map toString, roots := roots.size, modules, visited }

/-- Full `CommandElabM` union audit over an explicit root list: identical to `unionCheck`,
and additionally re-evaluates every candidate `native_decide`/`bv_decide` auxiliary axiom's
`Bool` LHS via `Lean.Meta.nativeEqTrue` inside `withoutModifyingEnv`. -/
def unionCheckM (env : Environment) (label : String) (roots : Array Name)
    (modules : Nat) (allowed : Array String)
    (allowedNativeOrigins : Array String := #[])
    (allowedBvOrigins : Array String := #[]) : CommandElabM (Except String UnionReport) := do
  match unionCheck env label roots modules allowed allowedNativeOrigins allowedBvOrigins with
  | .error e => return .error e
  | .ok r =>
    let mut bad : Array Name := #[]
    for axStr in r.axioms do
      let ax := parseDottedName axStr
      unless (← isAllowedUnionAxiomM env allowed allowedNativeOrigins allowedBvOrigins ax) do
        bad := bad.push ax
    unless bad.isEmpty do
      let where_ := locate env roots bad
      return .error s!"#union_axioms_of_modules: {label} reaches axioms outside \
        {allowed.qsort (· < ·)}: {bad.map toString}\n{"\n".intercalate where_.toList}"
    return .ok r

/-- `#full_axioms X` reports the from-scratch axiom set of the exact constant
`X` as one `FULL-AXIOMS` line. -/
elab "#full_axioms " id:ident : command => do
  let env ← getEnv
  let c := id.getId
  unless env.contains c do
    throwError "#full_axioms: unknown constant {c}"
  let report ← wrapAsyncAsSnapshot (cancelTk? := none) fun (_ : Unit) => do
    let (axioms, missing) := walk env c
    unless missing.isEmpty do
      throwError "#full_axioms: {c} reaches constants absent from the environment: \
        {missing.toList}"
    let names := (axioms.toList.map toString).toArray.qsort (· < ·)
    logInfo (MessageData.ofFormat (.text
      s!"FULL-AXIOMS '{c}': [{", ".intercalate names.toList}]"))
  logSnapshotTask { stx? := none, task := (← BaseIO.asTask (report ())), cancelTk? := none }

/-- `#expect_axioms X [ax₁, …, axₙ]` fails unless the from-scratch axiom set of
the exact constant `X` is exactly the listed set. -/
elab "#expect_axioms " id:ident " [" axs:ident,* "]" : command => do
  let env ← getEnv
  let name := id.getId
  unless env.contains name do throwError "AXIOM unknown declaration: {name}"
  let (axioms, missing) := walk env name
  unless missing.isEmpty do
    throwError "AXIOM {name} reaches constants absent from the environment: \
      {missing.toList}"
  let actual := (axioms.toList.map toString).toArray.qsort (· < ·)
  let expected := (axs.getElems.map (toString ∘ TSyntax.getId)).qsort (· < ·)
  unless actual == expected do
    throwError "AXIOM mismatch for {name}: expected {expected}, actual {actual}"
  logInfo m!"AXIOM OK {name}: {actual}"

/-- Render a prefix list as the label of one union audit. -/
def unionLabel (pfxs : Array Name) : String :=
  ", ".intercalate (pfxs.toList.map toString)

/-- Parse a whitespace- or newline-separated blob of exact dotted constant names.
Blank lines and `--` comment lines are skipped. -/
def parseDottedNames (blob : String) : Array Name := Id.run do
  let mut out : Array Name := #[]
  for raw in blob.splitOn "\n" do
    let s := raw.trimAscii.toString
    if !s.isEmpty && !s.startsWith "--" then
      out := out.push (parseDottedName s)
  return out

/-- Exact per-root axiom sets via one forward reference-graph walk (`exporting := false`)
followed by one reverse breadth-first search per reachable axiom.

This computes, for every `r` in `roots`, the exact same set of reachable `axiom`
constants as `walk env r`: it reads no precomputed per-module table and stores no
per-constant axiom-set cache across cycles, while running in `O((|V| + |E|) · |A|)`
instead of `O(|roots| · (|V| + |E|))`. Also returns any referenced constants absent
from `env`. -/
def exactAxiomsForRoots (env : Environment) (roots : Array Name) :
    NameSet × Std.HashMap Name (Array Name) := Id.run do
  let env := env.setExporting false
  let mut users : Std.HashMap Name (Array Name) := {}
  let mut seen : Std.HashSet Name := {}
  let mut stack : Array Name := #[]
  for r in roots do
    unless seen.contains r do
      seen := seen.insert r
      stack := stack.push r
  let mut axioms : Array Name := #[]
  let mut missing : NameSet := {}
  while h : 0 < stack.size do
    let c := stack.back
    stack := stack.pop
    match env.find? c with
    | none => missing := missing.insert c
    | some info =>
      if info matches .axiomInfo _ then
        axioms := axioms.push c
      let mut refs := info.type.getUsedConstants
      match info with
      | .defnInfo v => refs := refs ++ v.value.getUsedConstants
      | .thmInfo v => refs := refs ++ v.value.getUsedConstants
      | .opaqueInfo v => refs := refs ++ v.value.getUsedConstants
      | .inductInfo v => refs := refs ++ v.ctors.toArray
      | _ => pure ()
      let mut localSeen : Std.HashSet Name := {}
      for n in refs do
        unless localSeen.contains n do
          localSeen := localSeen.insert n
          if users.contains n then
            users := users.modify n (fun arr => arr.push c)
          else
            users := users.insert n #[c]
        unless seen.contains n do
          seen := seen.insert n
          stack := stack.push n
  let rootSet : Std.HashSet Name := Std.HashSet.ofArray roots
  let sortedAxioms := axioms.qsort (fun a b => toString a < toString b)
  let mut perRoot : Std.HashMap Name (Array Name) := {}
  for r in roots do
    perRoot := perRoot.insert r #[]
  for ax in sortedAxioms do
    let mut revSeen : Std.HashSet Name := ({} : Std.HashSet Name).insert ax
    let mut q : Array Name := #[ax]
    let mut qi := 0
    while qi < q.size do
      let c := q[qi]!
      qi := qi + 1
      if rootSet.contains c then
        perRoot := perRoot.modify c (fun arr => arr.push ax)
      for u in users.getD c #[] do
        unless revSeen.contains u do
          revSeen := revSeen.insert u
          q := q.push u
  return (missing, perRoot)

/-- Format one per-declaration axiom report line in the canonical Lean format
consumed by `scripts/check_axioms.py`. -/
def formatPrintAxiomsLine (constName : Name) (axioms : Array Name) : String :=
  if axioms.isEmpty then
    s!"'{constName}' does not depend on any axioms"
  else
    let rendered := ", ".intercalate (axioms.toList.map toString)
    s!"'{constName}' depends on axioms: [{rendered}]"

/-- Print exact from-scratch axiom sets for every declaration in `roots`. Fails
closed if any root is unknown or reaches a constant absent from `env`. When
`allowed` is supplied (`some …`), also fails closed if any per-root axiom is
outside `isAllowedUnionAxiom`. -/
def reportPrintAxiomsForRoots (env : Environment) (roots : Array Name)
    (allowed? : Option (Array String) := none)
    (allowedNativeOrigins : Array String := #[])
    (allowedBvOrigins : Array String := #[]) :
    Except String (Array String) := Id.run do
  let mut unknown : Array Name := #[]
  for r in roots do
    unless env.contains r do
      unknown := unknown.push r
  unless unknown.isEmpty do
    let sample := (unknown.toList.take 20).map toString
    return .error s!"reportPrintAxiomsForRoots: {unknown.size} unknown declaration(s): {sample}"
  let res := exactAxiomsForRoots env roots
  let missing := res.1
  let perRoot := res.2
  unless missing.isEmpty do
    let sample := (missing.toList.take 20).map toString
    return .error s!"reportPrintAxiomsForRoots: reached {missing.size} absent constant(s): {sample}"
  if let some allowed := allowed? then
    let mut badSet : NameSet := {}
    for r in roots do
      for ax in perRoot.getD r #[] do
        unless isAllowedUnionAxiom env allowed allowedNativeOrigins allowedBvOrigins ax do
          badSet := badSet.insert ax
    unless badSet.isEmpty do
      let bad := badSet.toList.toArray.qsort (fun a b => toString a < toString b)
      return .error s!"reportPrintAxiomsForRoots: disallowed axiom(s): {bad.map toString}"
  let mut lines : Array String := #[]
  for r in roots do
    lines := lines.push (formatPrintAxiomsLine r (perRoot.getD r #[]))
  return .ok lines

/-- Full `CommandElabM` per-root axiom report: identical to `reportPrintAxiomsForRoots`,
and additionally re-evaluates every candidate `native_decide`/`bv_decide` auxiliary axiom's
`Bool` LHS via `Lean.Meta.nativeEqTrue` inside `withoutModifyingEnv` when `allowed?` is `some …`. -/
def reportPrintAxiomsForRootsM (env : Environment) (roots : Array Name)
    (allowed? : Option (Array String) := none)
    (allowedNativeOrigins : Array String := #[])
    (allowedBvOrigins : Array String := #[]) :
    CommandElabM (Except String (Array String)) := do
  let mut unknown : Array Name := #[]
  for r in roots do
    unless env.contains r do
      unknown := unknown.push r
  unless unknown.isEmpty do
    let sample := (unknown.toList.take 20).map toString
    return .error s!"reportPrintAxiomsForRoots: {unknown.size} unknown declaration(s): {sample}"
  let res := exactAxiomsForRoots env roots
  let missing := res.1
  let perRoot := res.2
  unless missing.isEmpty do
    let sample := (missing.toList.take 20).map toString
    return .error s!"reportPrintAxiomsForRoots: reached {missing.size} absent constant(s): {sample}"
  if let some allowed := allowed? then
    let mut allCandidateAxs : NameSet := {}
    for r in roots do
      for ax in perRoot.getD r #[] do
        allCandidateAxs := allCandidateAxs.insert ax
    let mut badSet : NameSet := {}
    for ax in allCandidateAxs.toList do
      unless (← isAllowedUnionAxiomM env allowed allowedNativeOrigins allowedBvOrigins ax) do
        badSet := badSet.insert ax
    unless badSet.isEmpty do
      let bad := badSet.toList.toArray.qsort (fun a b => toString a < toString b)
      return .error s!"reportPrintAxiomsForRoots: disallowed axiom(s): {bad.map toString}"
  let mut lines : Array String := #[]
  for r in roots do
    lines := lines.push (formatPrintAxiomsLine r (perRoot.getD r #[]))
  return .ok lines

/-- `#union_axioms_of_modules P₁, …, Pₖ [ax₁, …, axₙ]` audits a whole library at once.
Its roots are every constant declared by every imported module whose name extends
any `Pᵢ`; one walk with one shared visited set covers them all. It logs

    UNION-AXIOMS 'P₁, …, Pₖ': [<axiom>, ...] roots=<n> modules=<m> visited=<v>

(the union of reachable axioms, sorted by text) and fails elaboration if no
module matches, if a reached constant is absent from the environment, or if the
union contains an axiom outside the allowed list (default
`[propext, Classical.choice, Quot.sound]`; `[]` allows none). A failure by an
axiom names, for each offending axiom, up to 20 roots that reach it with the
chain of constants from the root to the axiom. -/
syntax (name := unionAxiomsOfModules)
  "#union_axioms_of_modules " ident,+ (" [" ident,* "]")? : command

elab_rules : command
| `(#union_axioms_of_modules $ids:ident,* $[[ $axs:ident,* ]]?) => do
  let env ← getEnv
  let pfxs : Array Name := ids.getElems.map (·.getId)
  let allowed : Array String :=
    match axs with
    | some a => a.getElems.map (toString ·.getId)
    | none => #["Classical.choice", "Quot.sound", "propext"]
  let mr := moduleRootsOf env pfxs
  let roots := mr.1
  let modules := mr.2
  match (← unionCheckM env (unionLabel pfxs) roots modules allowed) with
  | .error e => throwError "{e}"
  | .ok r =>
    logInfo (MessageData.ofFormat (Std.Format.text
      s!"UNION-AXIOMS '{unionLabel pfxs}': [{", ".intercalate r.axioms.toList}] \
        roots={r.roots} modules={r.modules} visited={r.visited}"))

end Jaune.AxiomAudit

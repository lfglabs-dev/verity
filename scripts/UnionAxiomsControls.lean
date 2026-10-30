import AxiomAudit
import UnionAxiomsFixture.Good
import UnionAxiomsFixture.Bad
import UnionAxiomsFixture.ViaDep
import UnionAxiomsFixture.NativeAndAttrs
import Lean.Compiler.CSimpAttr
import Lean.Compiler.ImplementedByAttr

/-!
Copyright (c) 2025 skbaek
Copyright (c) 2025 Thomas Marchand

Released under the MIT License. Derived from Jaune's `scripts/UnionAxiomsControls.lean`
with Verity multi-prefix, native-codegen, `bv_decide`, compiler-attribute, and
reverse-reachability controls.

# Controls for `#union_axioms_of_modules` and `exactAxiomsForRoots`

Each control fails the default `Assurance` build if the behaviour it pins
changes, because `#guard_msgs` (or an explicit check) must see exactly the
expected outcome: a compliant population passes, a root reaching a
non-allowed axiom fails and is located, an empty population fails closed, and a
reached constant absent from the environment fails. The fixtures are
`UnionAxiomsFixture.Good`, `UnionAxiomsFixture.Bad`, `UnionAxiomsFixture.ViaDep`,
and `UnionAxiomsFixture.NativeAndAttrs`.
-/

open Jaune.AxiomAudit Lean Elab Command

-- A compliant population passes (default allowed set)…
#guard_msgs (drop info) in
#union_axioms_of_modules UnionAxiomsFixture.Good

-- …with exactly the expected union and exactly the module's own constants as roots.
run_cmd do
  let env ← getEnv
  let (roots, mods) := moduleRoots env `UnionAxiomsFixture.Good
  match unionCheck env "Good" roots mods #["propext"] with
  | .error e => throwError "control: expected a pass, got: {e}"
  | .ok r =>
    unless r.axioms == #["propext"] && r.modules == 1 do
      throwError "control: wrong union {r.axioms} / modules {r.modules}"
    unless roots.contains ``goodExt && roots.contains ``GoodTree.node
        && roots.contains ``goodSize && !roots.contains ``badAx do
      throwError "control: unexpected roots {roots}"

-- An explicit allowed list is honoured, and the empty list allows nothing.
#guard_msgs (drop info) in
#union_axioms_of_modules UnionAxiomsFixture.Good [propext]

/--
error: #union_axioms_of_modules: UnionAxiomsFixture.Good reaches axioms outside #[]: #[propext]
  propext <- root goodExt: goodExt -> propext
  propext <- root GoodTree.node.injEq: GoodTree.node.injEq -> Eq.propIntro -> propext
-/
#guard_msgs in
#union_axioms_of_modules UnionAxiomsFixture.Good []

-- A root reaching a non-allowed axiom fails, and the axiom and its roots are named.
/--
error: #union_axioms_of_modules: UnionAxiomsFixture.Bad reaches axioms outside #[Classical.choice, Quot.sound, propext]: #[badAx]
  badAx is itself a root
  badAx <- root viaBad: viaBad -> badAx
  badAx <- root chainedBad: chainedBad -> viaBad -> badAx
-/
#guard_msgs in
#union_axioms_of_modules UnionAxiomsFixture.Bad

-- Axioms outside the population are found across its boundary: `depAx` only
-- through the constructor of an inductive the population mentions, `depAx2`
-- only through a private theorem.
/--
error: #union_axioms_of_modules: UnionAxiomsFixture.ViaDep reaches axioms outside #[Classical.choice, Quot.sound, propext]: #[depAx, depAx2]
  depAx <- root useDep: useDep -> DepInd -> DepInd.mk -> depAx
  depAx2 <- root _private.UnionAxiomsFixture.ViaDep.0.hiddenDep: _private.UnionAxiomsFixture.ViaDep.0.hiddenDep -> depAx2
-/
#guard_msgs in
#union_axioms_of_modules UnionAxiomsFixture.ViaDep

-- An empty population fails closed: no such module, and a name that is only a
-- textual (not component-wise) prefix of a module.
/--
error: #union_axioms_of_modules: no constants found for UnionAxiomsFixture.Nope (0 matching modules, 0 roots); an empty population audits nothing
-/
#guard_msgs in
#union_axioms_of_modules UnionAxiomsFixture.Nope

/--
error: #union_axioms_of_modules: no constants found for UnionAxiomsFixture.Goo (0 matching modules, 0 roots); an empty population audits nothing
-/
#guard_msgs in
#union_axioms_of_modules UnionAxiomsFixture.Goo

-- A reached constant absent from the environment fails and is located.
run_cmd do
  let env ← getEnv
  let (roots, mods) := moduleRoots env `UnionAxiomsFixture.Good
  match unionCheck env "Good" (roots.push `absentConstant) mods
      #["Classical.choice", "Quot.sound", "propext"] with
  | .ok _ => throwError "control: an absent constant was accepted"
  | .error e =>
    unless e.startsWith "#union_axioms_of_modules: Good reaches 1 constants absent from the environment, e.g. #[absentConstant]"
        && (e.splitOn "\n").contains "  absentConstant is itself a root" do
      throwError "control: unexpected failure text: {e}"

-- Multi-prefix `#union_axioms_of_modules` audits the combined population in one walk.
#guard_msgs (drop info) in
#union_axioms_of_modules UnionAxiomsFixture.Good, UnionAxiomsFixture.Dep [propext, depAx, depAx2]

/--
error: #union_axioms_of_modules: UnionAxiomsFixture.Good, UnionAxiomsFixture.Bad reaches axioms outside #[Classical.choice, Quot.sound, propext]: #[badAx]
  badAx is itself a root
  badAx <- root viaBad: viaBad -> badAx
  badAx <- root chainedBad: chainedBad -> viaBad -> badAx
-/
#guard_msgs in
#union_axioms_of_modules UnionAxiomsFixture.Good, UnionAxiomsFixture.Bad

-- Theorem-level `native_decide` and non-trivial `bv_decide` emit generated auxiliary
-- axioms caught by `walkMany`; `example ... := by native_decide` emits no module root;
-- `@[implemented_by]`, `@[extern]`, and `@[csimp]` are detectable in the environment;
-- and `exactAxiomsForRoots` matches per-root `walk` across inductive/constructor cycles.
run_cmd do
  let env ← getEnv
  let mr := moduleRoots env `UnionAxiomsFixture.NativeAndAttrs
  let roots := mr.1
  let mods := mr.2
  unless mods == 1 do
    throwError "control: expected 1 NativeAndAttrs module, got {mods}"
  unless !roots.any (fun r => (toString r).contains "_example") do
    throwError "control: unexpected example root in {roots}"
  let wm := walkMany env roots
  let axList := (wm.1.toList.map toString).toArray.qsort (· < ·)
  unless wm.2.1.isEmpty do
    throwError "control: unexpected missing constants {wm.2.1.toList}"
  unless axList.any (fun a => a.contains "thmNativeDecide._native.native_decide.ax_") do
    throwError "control: missing theorem native_decide auxiliary axiom in {axList}"
  unless axList.any (fun a => a.contains "thmBVNonTriv._native.bv_decide.ax_") do
    throwError "control: missing theorem bv_decide auxiliary axiom in {axList}"
  unless axList.contains "UnionAxiomsFixture.NativeAndAttrs.cycAx" do
    throwError "control: missing cycle axiom in {axList}"
  unless axList.contains "sorryAx" do
    throwError "control: missing sorryAx in {axList}"
  unless Lean.Compiler.getImplementedBy? env ``UnionAxiomsFixture.NativeAndAttrs.implInc
      == some ``UnionAxiomsFixture.NativeAndAttrs.fastInc do
    throwError "control: getImplementedBy? failed to detect @[implemented_by]"
  unless Lean.isExtern env ``UnionAxiomsFixture.NativeAndAttrs.externOp do
    throwError "control: Lean.isExtern failed to detect @[extern]"
  unless (Lean.Compiler.CSimp.ext.getState env).map.contains
      ``UnionAxiomsFixture.NativeAndAttrs.pureInc
      && (Lean.Compiler.CSimp.ext.getState env).thmNames.contains
        ``UnionAxiomsFixture.NativeAndAttrs.pureInc_eq_fastInc do
    throwError "control: CSimp failed to detect @[csimp]"
  -- Reverse-reachability equivalence against `walk` on every fixture constant (cycles included).
  let allRoots := (moduleRootsOf env #[
    `UnionAxiomsFixture.Good,
    `UnionAxiomsFixture.Bad,
    `UnionAxiomsFixture.Dep,
    `UnionAxiomsFixture.ViaDep,
    `UnionAxiomsFixture.NativeAndAttrs
  ]).1
  let rev := exactAxiomsForRoots env allRoots
  unless rev.1.isEmpty do
    throwError "control: exactAxiomsForRoots saw missing constants {rev.1.toList}"
  for r in allRoots do
    let w := walk env r
    let wSorted := (w.1.toList.map toString).toArray.qsort (· < ·)
    let revSorted := ((rev.2.getD r #[]).map toString).qsort (· < ·)
    unless wSorted == revSorted do
      throwError "control: exactAxiomsForRoots mismatch on {r}: walk={wSorted} vs rev={revSorted}"
  -- Explicit auxiliary-origin allowlists accept real kernel-generated auxiliary axioms
  -- referenced by the allowlisted origin, and reject both foreign origins and same-origin
  -- hand-written spoof axioms (`ax_999 : False` and `ax_888 : Bool.false = Bool.true`).
  unless generatedAuxAxiomOrigin? "native_decide" "Foo.bar._native.native_decide.ax_1_1" == some "Foo.bar"
      && generatedAuxAxiomOrigin? "bv_decide" "Foo.baz._native.bv_decide.ax_1_9" == some "Foo.baz"
      && generatedAuxAxiomOrigin? "native_decide" "Foo.bar.native_decide.ax_1_1" == none
      && generatedAuxAxiomOrigin? "native_decide" "Foo.bar._native.native_decide.ax_bad" == none do
    throwError "control: generatedAuxAxiomOrigin? regression"
  let nativeRealStr? := axList.find? (fun a =>
    a.contains "thmNativeDecide._native.native_decide.ax_"
      && !a.endsWith ".ax_999" && !a.endsWith ".ax_888")
  let some nativeRealStr := nativeRealStr?
    | throwError "control: could not locate real thmNativeDecide auxiliary axiom in {axList}"
  let nativeReal := parseDottedName nativeRealStr
  let bvRealStr? := axList.find? (fun a => a.contains "thmBVNonTriv._native.bv_decide.ax_")
  let some bvRealStr := bvRealStr?
    | throwError "control: could not locate real thmBVNonTriv auxiliary axiom in {axList}"
  let bvReal := parseDottedName bvRealStr
  let spoofFalse := parseDottedName "UnionAxiomsFixture.NativeAndAttrs.thmNativeDecide._native.native_decide.ax_999"
  let spoofBool := parseDottedName "UnionAxiomsFixture.NativeAndAttrs.thmNativeDecide._native.native_decide.ax_888"
  let foreignSpoof := parseDottedName "Spoof.other._native.native_decide.ax_1_1"
  let allowedNative := #["UnionAxiomsFixture.NativeAndAttrs.thmNativeDecide"]
  let allowedBv := #["UnionAxiomsFixture.NativeAndAttrs.thmBVNonTriv"]
  unless isAllowedUnionAxiom env #["propext"] allowedNative #[] nativeReal
      && isAllowedUnionAxiom env #["propext"] #[] allowedBv bvReal
      && !isAllowedUnionAxiom env #["propext"] #[] #[] nativeReal
      && !isAllowedUnionAxiom env #["propext"] #[] #[] bvReal
      && !isAllowedUnionAxiom env #["propext"] allowedNative #[] spoofFalse
      && !isAllowedUnionAxiom env #["propext"] allowedNative #[] spoofBool
      && !isAllowedUnionAxiom env #["propext"] allowedNative #[] foreignSpoof do
    throwError "control: isAllowedUnionAxiom kernel-authenticated origin allowlist regression"
  -- `unionCheck` and `reportPrintAxiomsForRoots` accept `thmNativeDecide` when its origin is
  -- allowlisted, and reject `useSpoofedNativeFalse` / `useSpoofedNativeBool` under the same allowlist.
  match unionCheck env "NativeRealOnly" #[``UnionAxiomsFixture.NativeAndAttrs.thmNativeDecide] 1
      #["propext", "Lean.ofReduceBool", "Lean.trustCompiler"] allowedNative #[] with
  | .error e => throwError "control: real allowlisted native_decide theorem was rejected: {e}"
  | .ok _ => pure ()
  for spoofUser in #[
    ``UnionAxiomsFixture.NativeAndAttrs.useSpoofedNativeFalse,
    ``UnionAxiomsFixture.NativeAndAttrs.useSpoofedNativeBool
  ] do
    match unionCheck env "SpoofCheck" #[spoofUser] 1
        #["propext", "Lean.ofReduceBool", "Lean.trustCompiler"] allowedNative #[] with
    | .ok _ => throwError "control: unionCheck accepted spoofed auxiliary axiom via {spoofUser}"
    | .error _ => pure ()
    match reportPrintAxiomsForRoots env #[spoofUser]
        (some #["propext", "Lean.ofReduceBool", "Lean.trustCompiler"]) allowedNative #[] with
    | .ok _ => throwError "control: reportPrintAxiomsForRoots accepted spoofed auxiliary axiom via {spoofUser}"
    | .error _ => pure ()

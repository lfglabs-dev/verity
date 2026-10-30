import Lean
import Std.Tactic.BVDecide

/-!
Copyright (c) 2025 Thomas Marchand. Released under the MIT License.

# Fixture declarations for native-codegen, `bv_decide`, and compiler-attribute controls

Used by `scripts/UnionAxiomsControls.lean` to pin how Lean v4.31.0 represents:
1. `example` vs `theorem` `native_decide` proofs in module constants,
2. trivial vs non-trivial `bv_decide` proofs,
3. `@[implemented_by]`, `@[extern]`, and `@[csimp]` compiler-attribute escapes,
4. inductive/constructor cycles (`leanprover/lean4#15226`).
-/

namespace UnionAxiomsFixture.NativeAndAttrs

-- `example` with `native_decide` produces no module constant in `constNames`;
-- source-level hygiene must reject non-test `native_decide` examples separately.
example : (1 : Nat) + 1 = 2 := by native_decide

theorem thmNativeDecide : (2 : Nat) + 2 = 4 := by native_decide

-- Hand-written spoofs under an allowlisted `native_decide` origin name:
-- `ax_999` has non-`nativeEqTrue` type (`False`); `ax_888` even mimics the
-- `Eq.{1} Bool _ Bool.true` kernel type, yet is not referenced by
-- `thmNativeDecide.value` and must still be rejected.
axiom thmNativeDecide._native.native_decide.ax_999 : False
axiom thmNativeDecide._native.native_decide.ax_888 : Bool.false = Bool.true

theorem useSpoofedNativeFalse : False := thmNativeDecide._native.native_decide.ax_999
theorem useSpoofedNativeBool : Bool.false = Bool.true := thmNativeDecide._native.native_decide.ax_888

-- Hand-written spoofs that ARE directly referenced inside the allowlisted origin's own
-- `value.getUsedConstants`:
-- `ax_777` has `Eq.{1} Bool Bool.false Bool.true` (unsound) and is referenced by `thmSpoofRef`;
-- `ax_778` has `Eq.{1} Bool Bool.true Bool.true` (evaluates to `Bool.true`) and is referenced by
-- `thmSpoofRefTrue`, yet still has a source `axiom` declaration range (`range != selectionRange`)
-- rather than a tactic single-ref range (`range == selectionRange`) and must also be rejected.
axiom thmSpoofRef._native.native_decide.ax_777 : Bool.false = Bool.true
theorem thmSpoofRef : Bool.false = Bool.true := by
  exact thmSpoofRef._native.native_decide.ax_777

axiom thmSpoofRefTrue._native.native_decide.ax_778 : Bool.true = Bool.true
theorem thmSpoofRefTrue : (2 : Nat) + 2 = 4 := by
  have _ := thmSpoofRefTrue._native.native_decide.ax_778
  native_decide

-- Command-macro spoof: synthesizes a single-ref token (`range == selectionRange`) so an external
-- `axiom` command would pass a naive `range == selectionRange` check unless `AxiomAudit` also
-- requires the auxiliary range to lie within the allowlisted origin's own declaration span.
local elab tk:"declare_macro_spoof_ax" : command => do
  let axName := `UnionAxiomsFixture.NativeAndAttrs.thmMacroSpoof._native.native_decide.ax_779
  let boolTy := Lean.mkConst ``Bool
  let boolTrue := Lean.mkConst ``Bool.true
  let eqTrue := Lean.mkApp3 (Lean.mkConst ``Eq [Lean.Level.succ Lean.Level.zero]) boolTy boolTrue boolTrue
  Lean.Elab.Command.liftCoreM do
    Lean.addDecl (.axiomDecl {
      name := axName
      levelParams := []
      type := eqTrue
      isUnsafe := false
    })
    Lean.Elab.addDeclarationRangesFromSyntax axName tk

declare_macro_spoof_ax
theorem thmMacroSpoof : (2 : Nat) + 2 = 4 := by
  have _ := thmMacroSpoof._native.native_decide.ax_779
  native_decide

theorem thmBVNonTriv (x y : BitVec 32) : (x ^^^ y) ^^^ y = x := by bv_decide

def pureInc (n : Nat) : Nat := n + 1
def fastInc (n : Nat) : Nat := n + 1

@[implemented_by fastInc]
def implInc (n : Nat) : Nat := n + 1

@[extern "verity_fixture_c_sym"]
opaque externOp : Nat → Nat

@[csimp]
theorem pureInc_eq_fastInc : @pureInc = @fastInc := rfl

-- `sorry` emits `sorryAx` in the module's constant dependencies.
set_option warn.sorry false in
theorem thmSorry : False := by sorry

axiom cycAx : Prop

inductive CycInd : Type where
  | base : CycInd
  | step : (cycAx → Prop) → CycInd → CycInd

theorem useCycInd (x : CycInd) : x = x := rfl

end UnionAxiomsFixture.NativeAndAttrs

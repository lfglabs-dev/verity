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

import Std
import Compiler.CompilationModel
import Compiler.Hex
import Compiler.Selectors

namespace Compiler.Selector

open Compiler.CompilationModel
open Compiler.Hex

private def externalFunctions (spec : CompilationModel) : List FunctionSpec :=
  spec.functions.filter (fun fn => !fn.isInternal && !isInteropEntrypointName fn.name)

def runKeccak (sigs : List String) : IO (List Nat) := do
  pure <| sigs.map Compiler.keccak256_first_4_bytes

/-- Compute Solidity-compatible selectors for external functions in a spec.
    Internal functions and special entrypoints (fallback/receive) are excluded
    since they are not dispatched via selector. Uses `isInteropEntrypointName`
    so this filter stays in sync with `CompilationModel.compile`. -/
def computeSelectors (spec : CompilationModel) : IO (List Nat) := do
  let externalFns := externalFunctions spec
  let sigs := externalFns.map functionSignature
  runKeccak sigs

/-- Validate that caller-provided selectors exactly match canonical Solidity
    selectors for each external function in declaration order. -/
def validateSelectors (spec : CompilationModel) (selectors : List Nat) : IO (Except String Unit) := do
  let externalFns := externalFunctions spec
  let expected ← computeSelectors spec
  if selectors.length != expected.length then
    return .error s!"Selector count mismatch for {spec.name}: {selectors.length} selectors for {expected.length} external functions"
  match ((externalFns.zip selectors).zip expected).find? (fun ((_, provided), canonical) => provided != canonical) with
  | some ((fn, provided), canonical) =>
      return .error s!"Selector mismatch in {spec.name} for function '{fn.name}': expected {natToHex canonical}, got {natToHex provided}"
  | none =>
      return .ok ()

/-- Checked compilation boundary for caller-supplied selector lists.
    Validates selectors against canonical Solidity signatures before invoking
    the core pure compiler. -/
def compileChecked (spec : CompilationModel) (selectors : List Nat) : IO (Except String IRContract) := do
  match ← validateSelectors spec selectors with
  | .error err => return .error err
  | .ok () => return Compiler.CompilationModel.compile spec selectors

/-! ## Binary Search Selector Dispatch (`SelectorDispatchTree`) -/

/-- Default function count threshold above which selector dispatch switches from
    linear `eq(selector, ...)` chains to binary search `lt(selector, pivot)` trees. -/
def defaultSelectorDispatchThreshold : Nat := 8

/-- Reference linear selector lookup over `(selector, payload)` pairs. -/
def linearSelectorLookup {α : Type} (entries : List (Nat × α)) (sel : Nat) : Option α :=
  match entries with
  | [] => none
  | (k, v) :: rest => if k = sel then some v else linearSelectorLookup rest sel

/-- Binary search dispatch tree over 4-byte function selectors.
    Leaves perform linear scan over at most `threshold` entries; internal
    branches split on `sel < pivot`. -/
inductive SelectorDispatchTree (α : Type) where
  | leaf (entries : List (Nat × α))
  | branch (pivot : Nat) (left right : SelectorDispatchTree α)
  deriving Repr

/-- Evaluate a `SelectorDispatchTree` at selector `sel`. -/
def SelectorDispatchTree.lookup {α : Type} : SelectorDispatchTree α → Nat → Option α
  | .leaf entries, sel => linearSelectorLookup entries sel
  | .branch pivot left right, sel =>
      if sel < pivot then left.lookup sel else right.lookup sel

/-- Choose the midpoint selector as the split pivot for binary dispatch construction. -/
def selectorPivot {α : Type} (entries : List (Nat × α)) : Nat :=
  match entries.drop (entries.length / 2) with
  | (k, _) :: _ => k
  | [] => 0

/-- Build a bounded-depth binary search selector dispatch tree.
    Splits around `selectorPivot entries` whenever `entries.length > threshold`
    and recursion fuel remains. -/
def buildSelectorDispatchTree {α : Type} (fuel : Nat) (threshold : Nat)
    (entries : List (Nat × α)) : SelectorDispatchTree α :=
  match fuel with
  | 0 => .leaf entries
  | fuel' + 1 =>
      if entries.length > threshold then
        let pivot := selectorPivot entries
        let leftEntries := entries.filter (fun p => decide (p.1 < pivot))
        let rightEntries := entries.filter (fun p => !decide (p.1 < pivot))
        .branch pivot
          (buildSelectorDispatchTree fuel' threshold leftEntries)
          (buildSelectorDispatchTree fuel' threshold rightEntries)
      else
        .leaf entries

theorem linearSelectorLookup_nil {α : Type} (sel : Nat) :
    linearSelectorLookup ([] : List (Nat × α)) sel = none := rfl

theorem linearSelectorLookup_cons_eq {α : Type} (k : Nat) (v : α)
    (rest : List (Nat × α)) (sel : Nat) (h : k = sel) :
    linearSelectorLookup ((k, v) :: rest) sel = some v := by
  subst h
  simp only [linearSelectorLookup, ↓reduceIte]

theorem linearSelectorLookup_cons_ne {α : Type} (k : Nat) (v : α)
    (rest : List (Nat × α)) (sel : Nat) (h : k ≠ sel) :
    linearSelectorLookup ((k, v) :: rest) sel = linearSelectorLookup rest sel := by
  simp only [linearSelectorLookup, h, ↓reduceIte]

theorem SelectorDispatchTree.lookup_leaf {α : Type}
    (entries : List (Nat × α)) (sel : Nat) :
    (SelectorDispatchTree.leaf entries).lookup sel = linearSelectorLookup entries sel := rfl

theorem SelectorDispatchTree.lookup_branch_lt {α : Type} (pivot : Nat)
    (l r : SelectorDispatchTree α) (sel : Nat) (h : sel < pivot) :
    (SelectorDispatchTree.branch pivot l r).lookup sel = l.lookup sel := by
  simp only [SelectorDispatchTree.lookup, h, ↓reduceIte]

theorem SelectorDispatchTree.lookup_branch_ge {α : Type} (pivot : Nat)
    (l r : SelectorDispatchTree α) (sel : Nat) (h : pivot ≤ sel) :
    (SelectorDispatchTree.branch pivot l r).lookup sel = r.lookup sel := by
  have hnot : ¬ (sel < pivot) := Nat.not_lt.mpr h
  simp only [SelectorDispatchTree.lookup, hnot, ↓reduceIte]

theorem linearSelectorLookup_filter_lt {α : Type}
    (entries : List (Nat × α)) (pivot sel : Nat) (h : sel < pivot) :
    linearSelectorLookup (entries.filter (fun p => decide (p.1 < pivot))) sel =
      linearSelectorLookup entries sel := by
  induction entries with
  | nil => rfl
  | cons hd tl ih =>
      rcases hd with ⟨k, v⟩
      dsimp only [List.filter]
      cases hk : decide (k < pivot) with
      | false =>
          have hnk : ¬ (k < pivot) := of_decide_eq_false hk
          have hne : k ≠ sel := by omega
          rw [linearSelectorLookup_cons_ne k v tl sel hne]
          exact ih
      | true =>
          by_cases hks : k = sel
          · rw [linearSelectorLookup_cons_eq k v _ sel hks]
            rw [linearSelectorLookup_cons_eq k v tl sel hks]
          · rw [linearSelectorLookup_cons_ne k v _ sel hks]
            rw [linearSelectorLookup_cons_ne k v tl sel hks]
            exact ih

theorem linearSelectorLookup_filter_ge {α : Type}
    (entries : List (Nat × α)) (pivot sel : Nat) (h : ¬ (sel < pivot)) :
    linearSelectorLookup (entries.filter (fun p => !decide (p.1 < pivot))) sel =
      linearSelectorLookup entries sel := by
  induction entries with
  | nil => rfl
  | cons hd tl ih =>
      rcases hd with ⟨k, v⟩
      dsimp only [List.filter]
      cases hk : decide (k < pivot) with
      | true =>
          have hlt : k < pivot := of_decide_eq_true hk
          have hne : k ≠ sel := by omega
          simp only [Bool.not_true]
          rw [linearSelectorLookup_cons_ne k v tl sel hne]
          exact ih
      | false =>
          simp only [Bool.not_false]
          by_cases hks : k = sel
          · rw [linearSelectorLookup_cons_eq k v _ sel hks]
            rw [linearSelectorLookup_cons_eq k v tl sel hks]
          · rw [linearSelectorLookup_cons_ne k v _ sel hks]
            rw [linearSelectorLookup_cons_ne k v tl sel hks]
            exact ih

theorem buildSelectorDispatchTree_lookup_eq_linear {α : Type}
    (fuel threshold : Nat) (entries : List (Nat × α)) (sel : Nat) :
    (buildSelectorDispatchTree fuel threshold entries).lookup sel =
      linearSelectorLookup entries sel := by
  induction fuel generalizing entries with
  | zero => rfl
  | succ fuel' ih =>
      dsimp only [buildSelectorDispatchTree]
      by_cases hlen : entries.length > threshold
      · simp only [hlen, ↓reduceIte]
        by_cases hlt : sel < selectorPivot entries
        · rw [SelectorDispatchTree.lookup_branch_lt _ _ _ _ hlt]
          rw [ih]
          exact linearSelectorLookup_filter_lt entries (selectorPivot entries) sel hlt
        · have hge : selectorPivot entries ≤ sel := Nat.le_of_not_lt hlt
          rw [SelectorDispatchTree.lookup_branch_ge _ _ _ _ hge]
          rw [ih]
          exact linearSelectorLookup_filter_ge entries (selectorPivot entries) sel hlt
      · simp only [hlen, ↓reduceIte, SelectorDispatchTree.lookup_leaf]

theorem binary_search_selector_dispatch_sound {α : Type}
    (fuel : Nat) (entries : List (Nat × α)) (sel : Nat) :
    (buildSelectorDispatchTree fuel defaultSelectorDispatchThreshold entries).lookup sel =
      linearSelectorLookup entries sel :=
  buildSelectorDispatchTree_lookup_eq_linear fuel defaultSelectorDispatchThreshold entries sel

end Compiler.Selector

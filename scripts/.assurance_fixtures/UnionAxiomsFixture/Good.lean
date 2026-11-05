/-!
Copyright (c) 2025 skbaek. Released under the MIT License (from Jaune).

# Control fixture: a compliant population for `#union_axioms_of_modules`

Reaches exactly `propext` (an allowed axiom), and holds an inductive whose
constructor cycle the walk must cross.
Used only by `scripts/UnionAxiomsControls.lean`.
-/

theorem goodExt (p q : Prop) (h : p ↔ q) : p = q := propext h

inductive GoodTree where
  | leaf : GoodTree
  | node : List GoodTree → GoodTree

def goodSize : GoodTree → Nat
  | .leaf => 0
  | .node _ => 1

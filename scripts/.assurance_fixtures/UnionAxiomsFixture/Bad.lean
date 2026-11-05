/-!
Copyright (c) 2025 skbaek. Released under the MIT License (from Jaune).

# Control fixture: a population reaching a non-standard axiom

`badAx` is declared here and reached, directly and through a chain, from two
theorems. Used only by `scripts/UnionAxiomsControls.lean`, which expects
`#union_axioms_of_modules` to reject it and to name these roots.
-/

axiom badAx : False

theorem viaBad : (1 : Nat) = 2 := False.elim badAx

theorem chainedBad : (1 : Nat) = 2 := viaBad

/-!
Copyright (c) 2025 skbaek. Released under the MIT License (from Jaune).

# Control fixture: axioms declared outside the audited population

`depAx` is reachable from `DepInd` only through its constructor, and `depAx2`
is used only by a private theorem of `UnionAxiomsFixture.ViaDep`. Used only by
`scripts/UnionAxiomsControls.lean`.
-/

axiom depAx : Nat

axiom depAx2 : False

inductive DepInd where
  | mk : Fin depAx → DepInd

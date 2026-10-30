import UnionAxiomsFixture.Dep

/-!
Copyright (c) 2025 skbaek. Released under the MIT License (from Jaune).

# Control fixture: axioms reached only across the population boundary

The population (this module) mentions the inductive `DepInd` but not its
constructor, and a private theorem reaches `depAx2`. `#union_axioms_of_modules
UnionAxiomsFixture.ViaDep` must reach both axioms: the first through the
inductive's constructor, the second through a private root. Used only by
`scripts/UnionAxiomsControls.lean`.
-/

def useDep : Type := DepInd

private theorem hiddenDep : (1 : Nat) = 2 := False.elim depAx2

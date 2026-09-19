import Contracts.SolidityImportSmoke.Inheritance.Spec
import Verity.Proofs.Stdlib.SolidityImport

namespace Contracts.SolidityImportSmoke.Inheritance.Proofs
open Verity
open Verity.Stdlib.Math
open Verity.Core.Invariant
open Verity.Proofs.Stdlib.SolidityImport
open Contracts.SolidityImportSmoke.Inheritance.Child
open Spec

theorem pause_success_spec (s post : ContractState)
    (h : PausableLike_pause.run s = .success () post) :
    pause_spec (view s) (view post) := by
  unfold pause_spec
  by_cases h0 : s.msgValue = 0
  · by_cases hcv : (view s).childValue.val + 1 ≤ Verity.Core.MAX_UINT256
    · solidity_simp
      subst h
      solidity_simp
    · solidity_simp
  · solidity_simp

theorem go_success_spec (s post : ContractState)
    (h : go.run s = .success () post) :
    pause_spec (view s) (view post) := by
  unfold pause_spec
  by_cases h0 : s.msgValue = 0
  · by_cases hcv : (view s).childValue.val + 1 ≤ Verity.Core.MAX_UINT256
    · solidity_simp
      subst h
      solidity_simp
    · solidity_simp
  · solidity_simp

theorem bump_success_spec (s post : ContractState)
    (h : bump.run s = .success () post) :
    bump_spec (view s) (view post) := by
  unfold bump_spec
  by_cases h0 : s.msgValue = 0
  · by_cases hb : (view s).baseValue.val + 1 ≤ Verity.Core.MAX_UINT256
    · solidity_simp
      subst h
      solidity_simp
    · solidity_simp
  · solidity_simp

/-- A base entry point that calls the virtual observes the child's override. -/
theorem dispatch_is_child (s post : ContractState)
    (h : PausableLike_pause.run s = .success () post) :
    (view post).paused = 1 ∧ (view post).childValue = (view s).childValue + 1 := by
  have hspec := pause_success_spec s post h
  exact ⟨hspec.1, hspec.2.1⟩

/-- `go()` calls `Child._pause`, whose `super._pause()` runs the parent body. -/
theorem super_runs_parent (s post : ContractState)
    (h : go.run s = .success () post) :
    (view post).paused = 1 :=
  (go_success_spec s post h).1

theorem pause_meets_spec (s : ContractState)
    (h0 : s.msgValue = 0) (hfits : pauseFits (view s)) :
    ∃ post, PausableLike_pause.run s = ContractResult.success () post ∧
      pause_spec (view s) (view post) := by
  unfold pause_spec
  solidity_simp [pauseFits]

theorem go_meets_spec (s : ContractState)
    (h0 : s.msgValue = 0) (hfits : pauseFits (view s)) :
    ∃ post, go.run s = ContractResult.success () post ∧
      pause_spec (view s) (view post) := by
  unfold pause_spec
  solidity_simp [pauseFits]

theorem bump_meets_spec (s : ContractState)
    (h0 : s.msgValue = 0) (hfits : bumpFits (view s)) :
    ∃ post, bump.run s = ContractResult.success () post ∧
      bump_spec (view s) (view post) := by
  unfold bump_spec
  solidity_simp [bumpFits]

/-- `step` is go, bump, PausableLike_pause, then getters in layout order. -/
theorem paused_invariant : PreservedBy (fun s => pausedFlag (view s)) step := by
  intro s s' hflag hstep
  rcases hstep with hgo | hbump | hpause | hbase | hleft | hright | hpaused | howner | hchild
  · subst hgo
    cases run_snd_cases go s with
    | inl hrev => rw [hrev]; exact hflag
    | inr hsucc =>
      rcases hsucc with ⟨_, post, hrun, hsnd⟩
      rw [hsnd]
      exact Or.inr (go_success_spec s post hrun).1
  · subst hbump
    cases run_snd_cases bump s with
    | inl hrev => rw [hrev]; exact hflag
    | inr hsucc =>
      rcases hsucc with ⟨_, post, hrun, hsnd⟩
      rw [hsnd]
      have hp := (bump_success_spec s post hrun).2.2.1
      unfold pausedFlag at hflag ⊢
      rw [hp]
      exact hflag
  · subst hpause
    cases run_snd_cases PausableLike_pause s with
    | inl hrev => rw [hrev]; exact hflag
    | inr hsucc =>
      rcases hsucc with ⟨_, post, hrun, hsnd⟩
      rw [hsnd]
      exact Or.inr (pause_success_spec s post hrun).1
  · subst hbase
    by_cases h0 : s.msgValue = 0 <;> solidity_simp [pausedFlag]
  · subst hleft
    by_cases h0 : s.msgValue = 0 <;> solidity_simp [pausedFlag]
  · subst hright
    by_cases h0 : s.msgValue = 0 <;> solidity_simp [pausedFlag]
  · subst hpaused
    by_cases h0 : s.msgValue = 0 <;> solidity_simp [pausedFlag]
  · subst howner
    by_cases h0 : s.msgValue = 0 <;> solidity_simp [pausedFlag]
  · subst hchild
    by_cases h0 : s.msgValue = 0 <;> solidity_simp [pausedFlag]

end Contracts.SolidityImportSmoke.Inheritance.Proofs

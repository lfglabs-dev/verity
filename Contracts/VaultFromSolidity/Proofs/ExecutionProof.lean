import Contracts.VaultFromSolidity.Spec
import Verity.Proofs.Stdlib.SolidityImport

/-!
# Proofs about the Vault imported from Solidity

Three layers, deliberately kept small:

1. `*_success_spec` -- each successful entry point produces a post-state (and,
   for `balanceOf`, a return value) that satisfies the named-storage spec.
   These unfold the definitions `Importer.lean` registered from `Vault.sol`, so
   they fail if the Solidity source changes behaviour. Reverting calls are
   excluded by the success hypothesis.
2. `*_meets_spec` -- the named-storage promise from `Spec` under its
   precondition. Each states that the call succeeds and that the successful
   post-state (or, for `balanceOf`, the returned value) satisfies the spec.
3. `solvent_invariant` -- the contract-level result: `solvent` is preserved by
   the importer-generated `step` relation covering every public entry point.
   A reverting call leaves the state untouched (`Contract.run` rolls back;
   theorem `run_snd_cases`), so solvency can only ever be lost on a successful
   call, which is what the success theorems and this invariant rule out.

Slots are only ever referenced through the imported `<var>Slot` handles, so the
proofs do not depend on the storage-layout order solc picks. `view` constructs
a real `Storage` structure from those handles.
-/

namespace Contracts.VaultFromSolidity.Proofs.ExecutionProof
open Verity
open Verity.Stdlib.Math
open Verity.Core.Invariant
open Verity.Proofs.Stdlib.SolidityImport
open Spec

/-! ## Successful calls meet the named-storage spec -/

theorem deposit_success_spec (s post : ContractState) (amount : Uint256)
    (h : (deposit amount).run s = .success () post) :
    deposit_spec amount s.sender (view s) (view post) := by
  unfold deposit_spec
  by_cases h0 : s.msgValue = 0
  · by_cases hbal : ((view s).shareBalances s.sender).val + amount.val ≤ Verity.Core.MAX_UINT256
    · by_cases hat : (view s).totalAssets.val + amount.val ≤ Verity.Core.MAX_UINT256
      · by_cases hsup : (view s).totalSupply.val + amount.val ≤ Verity.Core.MAX_UINT256
        · solidity_simp
          subst h
          solidity_simp
        · solidity_simp
      · solidity_simp
    · solidity_simp
  · solidity_simp

theorem withdraw_success_spec (s post : ContractState) (amount : Uint256)
    (h : (withdraw amount).run s = .success () post) :
    withdraw_spec amount s.sender (view s) (view post) := by
  unfold withdraw_spec
  by_cases h0 : s.msgValue = 0
  · by_cases hbal : amount.val ≤ ((view s).shareBalances s.sender).val
    · by_cases hat : amount.val ≤ (view s).totalAssets.val
      · by_cases hsup : amount.val ≤ (view s).totalSupply.val
        · solidity_simp
          subst h
          solidity_simp
        · solidity_simp
      · solidity_simp
    · solidity_simp
  · solidity_simp

theorem balance_success_spec (s post : ContractState) (account : Address) (r : Uint256)
    (h : (balanceOf account).run s = .success r post) :
    balanceOf_spec account r (view s) ∧ post = s := by
  unfold balanceOf_spec
  by_cases h0 : s.msgValue = 0
  · solidity_simp
    have hr := h.1
    have heq := h.2
    subst heq
    exact Eq.symm hr
  · solidity_simp

/-! ## Each entry point meets its named-storage spec -/

/-- `balanceOf` succeeds, leaves the state untouched, and returns the
account's shares as `balanceOf_spec` promises. -/
theorem balance_meets_spec (s : ContractState) (account : Address)
    (h0 : s.msgValue = 0) :
    ∃ result, (balanceOf account).run s = ContractResult.success result s ∧
      balanceOf_spec account result (view s) := by
  unfold balanceOf_spec
  solidity_simp

/-- Under `depositFits`, `deposit` succeeds and its post-state satisfies
`deposit_spec`. -/
theorem deposit_meets_spec (s : ContractState) (amount : Uint256)
    (h0 : s.msgValue = 0) (hfits : depositFits amount s.sender (view s)) :
    ∃ post, (deposit amount).run s = ContractResult.success () post ∧
      deposit_spec amount s.sender (view s) (view post) := by
  unfold deposit_spec
  solidity_simp [depositFits]

/-- Under `withdrawCovered`, `withdraw` succeeds and its post-state satisfies
`withdraw_spec`. -/
theorem withdraw_meets_spec (s : ContractState) (amount : Uint256)
    (h0 : s.msgValue = 0) (hcovered : withdrawCovered amount s.sender (view s)) :
    ∃ post, (withdraw amount).run s = ContractResult.success () post ∧
      withdraw_spec amount s.sender (view s) (view post) := by
  unfold withdraw_spec
  solidity_simp [withdrawCovered]

/-! ## The vault stays solvent -/

/-- Every public entry point preserves one-for-one backing of issued shares.
The six `rcases` disjuncts are the importer-generated `step` constructors in
source order (functions, then public getters), so a new entry point breaks this
theorem. Rollback is covered by `run_snd_cases`. -/
theorem solvent_invariant : PreservedBy (fun s => solvent (view s)) step := by
  intro s s' hsolvent hstep
  rcases hstep with hdep | hwd | hbal | hta | hts | hsb
  · rcases hdep with ⟨a, rfl⟩
    cases run_snd_cases (deposit a) s with
    | inl hrev => rw [hrev]; exact hsolvent
    | inr hsucc =>
      rcases hsucc with ⟨_, post, hrun, hsnd⟩
      rw [hsnd]
      have hspec := deposit_success_spec s post a hrun
      unfold solvent at hsolvent ⊢
      rcases hspec with ⟨hassets, hsupply, _⟩
      rw [hassets, hsupply, hsolvent]
  · rcases hwd with ⟨a, rfl⟩
    cases run_snd_cases (withdraw a) s with
    | inl hrev => rw [hrev]; exact hsolvent
    | inr hsucc =>
      rcases hsucc with ⟨_, post, hrun, hsnd⟩
      rw [hsnd]
      have hspec := withdraw_success_spec s post a hrun
      unfold solvent at hsolvent ⊢
      rcases hspec with ⟨hassets, hsupply, _⟩
      rw [hassets, hsupply, hsolvent]
  · rcases hbal with ⟨k, rfl⟩
    cases run_snd_cases (balanceOf k) s with
    | inl hrev => rw [hrev]; exact hsolvent
    | inr hsucc =>
      rcases hsucc with ⟨r, post, hrun, hsnd⟩
      rw [hsnd, (balance_success_spec s post k r hrun).2]
      exact hsolvent
  · subst hta
    by_cases h0 : s.msgValue = 0 <;> solidity_simp [solvent]
  · subst hts
    by_cases h0 : s.msgValue = 0 <;> solidity_simp [solvent]
  · rcases hsb with ⟨k, rfl⟩
    by_cases h0 : s.msgValue = 0 <;> solidity_simp [solvent]

end Contracts.VaultFromSolidity.Proofs.ExecutionProof

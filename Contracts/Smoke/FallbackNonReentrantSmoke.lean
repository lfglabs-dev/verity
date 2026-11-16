import Contracts.Common
import Compiler.CheckContract

namespace Contracts.Smoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256
open Compiler.CompilationModel.DenoteExternalCalls

-- `fallback nonreentrant(lock)` / `receive nonreentrant(lock)`: the special entrypoints get the
-- transient-storage guard of a `nonreentrant` function. The fallback counts its entries and
-- calls `target`, which re-enters it (`test/FallbackNonReentrantSmoke.t.sol`).
verity_contract FallbackNonReentrantSmoke where
  storage
    lock : Uint256 := slot 0
    target : Address := slot 1
    entries : Uint256 := slot 2

  receive nonreentrant(lock) := do
    pure ()

  fallback nonreentrant(lock)
      local_obligations [low_level_call_refinement := assumed "The low-level call must be shown to refine the intended external-call behavior."] := do
    let current ← getStorage entries
    setStorage entries (add current 1)
    let callee ← getStorageAddr target
    let _ok := call 1000000 (addressToWord callee) 0 0 0 0 0
    pure ()

  function setTarget (callee : Address) : Unit := do
    setStorageAddr target callee

  function entryCount () : Uint256 := do
    let current ← getStorage entries
    return current

#check_contract FallbackNonReentrantSmoke

example :
    (FallbackNonReentrantSmoke.spec.functions.filter
        (fun fn => fn.name == "fallback" || fn.name == "receive")).map
      (fun fn => (fn.name, fn.reentrancyTrusted, fn.nonReentrantLock)) =
      [("receive", false, some "lock"), ("fallback", false, some "lock")] := by
  rfl

/-! ### Special entrypoints in the reentrancy registry

`receive` and `fallback` are in the generated `entrypointRegistry` like every external
function (`entrypointRegistry_cases` above lists them), so `entrypointRegistry_preserves`
asks for their preservation proofs. A locked fallback discharges `LockedInv` by its guard; an
unlocked fallback writing the protected slot makes the registry property false. -/

example (adv : AdversaryModel) (g : ContractState → ContractState) :
    FallbackNonReentrantSmoke.entrypointRegistry adv g ↔
      FallbackNonReentrantSmoke.__verity_receive_entrypoint adv g ∨
        FallbackNonReentrantSmoke.__verity_fallback_entrypoint adv g ∨
          FallbackNonReentrantSmoke.setTarget_entrypoint adv g ∨
            FallbackNonReentrantSmoke.entryCount_entrypoint adv g :=
  FallbackNonReentrantSmoke.entrypointRegistry_cases adv g

/-- Under its own held lock, the `nonreentrant(lock)` fallback reverts, so it preserves
`LockedInv Inv 0` for every `Inv`. -/
theorem fallbackNonReentrant_fallback_preserves_locked
    (Inv : ContractState → Prop) (adv : AdversaryModel) :
    RegistryPreserves (LockedInv Inv 0)
      FallbackNonReentrantSmoke.__verity_fallback_entrypoint adv := by
  rintro g ⟨ctx, resolve, _hval, rfl⟩
  exact guarded_callback_preserves_locked Inv 0 ctx _

-- The same counter write in a fallback without `nonreentrant`.
verity_contract FallbackUnlockedWriteSmoke where
  storage
    lock : Uint256 := slot 0
    entries : Uint256 := slot 2

  fallback := do
    let current ← getStorage entries
    setStorage entries (add current 1)

#check_contract FallbackUnlockedWriteSmoke

/-- With the lock held and `entries = 0`, a callback into the unlocked fallback writes
`entries := 1`: the registry does not preserve `LockedInv (entries = 0) 0`. -/
theorem fallbackUnlockedWrite_breaks_locked_registry (adv : AdversaryModel) :
    ¬ RegistryPreserves (LockedInv (fun s => s.storage 2 = 0) 0)
      FallbackUnlockedWriteSmoke.entrypointRegistry adv := by
  intro h
  let ctx : CallbackContext :=
    { sender := 0, msgValue := 0, calldataSize := 4, calldata := [] }
  let s : ContractState := Verity.Core.NonReentrantGuard.setLock 0 1 Verity.defaultState
  have hmem : FallbackUnlockedWriteSmoke.entrypointRegistry adv
      (callbackContractTransition ctx
        (FallbackUnlockedWriteSmoke.__verity_fallback_registry
          { adversary := adv, resolve := fun _ _ => none })) :=
    (FallbackUnlockedWriteSmoke.entrypointRegistry_cases adv _).mpr ⟨ctx, _, rfl, rfl⟩
  have hpost := (h _ hmem s ⟨rfl, by decide⟩).1
  rw [FallbackUnlockedWriteSmoke.__verity_fallback_registry_eq] at hpost
  revert hpost
  decide

end Contracts.Smoke

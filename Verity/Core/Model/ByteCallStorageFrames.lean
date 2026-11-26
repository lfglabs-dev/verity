import Verity.Core
import Verity.Core.Model.ByteExternalCall

/-!
# Caller-storage hypothesis for code after a byte `CALL`

Denote runs every statement after a closed byte `CALL` against the world the callee's
response committed (`ByteExternalCall.Response.commit`). An unconstrained adversary may
commit any world, including one in which a re-entrant entrypoint rewrote this contract's
storage, so imported models make no assumption about callees.

`CallKeepsCallerStorage` is the hypothesis a proof may add instead: every accepted call
leaves each storage word (`storageWords`) and dynamic storage array (`storageArray`) of
the calling contract as it was. Denote keeps the executing contract's words in the plain
channels (`slot`, `transient`, `map`, ...) and other accounts' words under
`contractSlot`/`scoped`, so a callee may still write its own storage. Under the hypothesis
a post-call read sees the pre-call value (`executeChecked_storage_of_callKeepsCallerStorage`,
`executeChecked_storageArray_of_callKeepsCallerStorage`); without it, it need not.
-/
namespace Compiler.CompilationModel.Denote

open ByteExternalCall

/-- `key` names a storage word of another account (or a parked copy), not of the
executing contract. -/
def isOtherAccountKey : Verity.StorageKey → Bool
  | .contractSlot _ _ | .scoped _ _ => true
  | _ => false

/-- Every accepted call commits a world that agrees with the pre-call world on every
caller-owned storage word and every dynamic storage array of the calling contract:
the callee neither writes them nor re-enters to. -/
def CallKeepsCallerStorage
    (adversary : Adversary Verity.ContractState Verity.StorageKey) : Prop :=
  ∀ request before, adversary.accepts request before = true →
    (∀ key, isOtherAccountKey key = false →
      ((adversary.respond request before).commit before).storageWords key =
        before.storageWords key) ∧
    ((adversary.respond request before).commit before).storageArray =
      before.storageArray

/-- A successful checked call keeps every caller-owned storage word. -/
theorem executeChecked_storageWords_of_callKeepsCallerStorage
    {adversary : Adversary Verity.ContractState Verity.StorageKey}
    (keeps : CallKeepsCallerStorage adversary) {request : Request}
    {before : Verity.ContractState} {observed : Observation Verity.ContractState Verity.StorageKey}
    (executed : executeChecked adversary request before = .ok observed)
    (key : Verity.StorageKey) (own : isOtherAccountKey key = false) :
    observed.world.storageWords key = before.storageWords key := by
  cases accepted : adversary.accepts request before
  · rw [executeChecked_rejects adversary request before accepted] at executed
    cases executed
  · rw [executeChecked_agrees adversary request before accepted] at executed
    cases executed
    exact (keeps request before accepted).1 key own

/-- A successful checked call keeps every dynamic storage array of the calling contract. -/
theorem executeChecked_storageArray_of_callKeepsCallerStorage
    {adversary : Adversary Verity.ContractState Verity.StorageKey}
    (keeps : CallKeepsCallerStorage adversary) {request : Request}
    {before : Verity.ContractState} {observed : Observation Verity.ContractState Verity.StorageKey}
    (executed : executeChecked adversary request before = .ok observed) :
    observed.world.storageArray = before.storageArray := by
  cases accepted : adversary.accepts request before
  · rw [executeChecked_rejects adversary request before accepted] at executed
    cases executed
  · rw [executeChecked_agrees adversary request before accepted] at executed
    cases executed
    exact (keeps request before accepted).2

/-- A post-call read of a persistent slot sees the pre-call word. -/
theorem executeChecked_storage_of_callKeepsCallerStorage
    {adversary : Adversary Verity.ContractState Verity.StorageKey}
    (keeps : CallKeepsCallerStorage adversary) {request : Request}
    {before : Verity.ContractState} {observed : Observation Verity.ContractState Verity.StorageKey}
    (executed : executeChecked adversary request before = .ok observed) (slot : Nat) :
    observed.world.storage slot = before.storage slot :=
  executeChecked_storageWords_of_callKeepsCallerStorage keeps executed (.slot slot) rfl

/-- A post-call read of a transient slot sees the pre-call word. -/
theorem executeChecked_transientStorage_of_callKeepsCallerStorage
    {adversary : Adversary Verity.ContractState Verity.StorageKey}
    (keeps : CallKeepsCallerStorage adversary) {request : Request}
    {before : Verity.ContractState} {observed : Observation Verity.ContractState Verity.StorageKey}
    (executed : executeChecked adversary request before = .ok observed) (slot : Nat) :
    observed.world.transientStorage slot = before.transientStorage slot :=
  executeChecked_storageWords_of_callKeepsCallerStorage keeps executed (.transient slot) rfl

/-- A callee that succeeds with empty return data and changes nothing. -/
def inertCallee : Adversary Verity.ContractState Verity.StorageKey where
  respond := fun _ world => .success world [] []
  valid := fun _ _ _ => rfl

/-- The hypothesis is satisfiable. -/
theorem callKeepsCallerStorage_inertCallee : CallKeepsCallerStorage inertCallee :=
  fun _ _ _ => ⟨fun _ _ => rfl, rfl⟩

end Compiler.CompilationModel.Denote

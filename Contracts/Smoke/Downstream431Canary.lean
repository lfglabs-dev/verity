import Contracts.Common
import Verity.Specs.Common

/-!
  Minimal downstream Lean 4.31 canary.

  This is deliberately a new-contract surface only: it does not alter the
  EVM/Yul semantics, compiler-correctness bridge, or official migration work.
-/

namespace Contracts.Downstream431Canary

open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Specs

verity_contract Canary where
  storage
    value : Uint256 := slot 0

  function setValue (newValue : Uint256) : Unit := do
    setStorage value newValue

  function getValue () : Uint256 := do
    let current ← getStorage value
    return current

/-- The consumer-facing postcondition for `setValue`. -/
def setValue_spec (before after : ContractState) (newValue : Uint256) : Prop :=
  after.storage 0 = newValue ∧ sameAddrMapContext before after

/-- A real proof over the contract surface, with no temporary obligations. -/
theorem setValue_meets_spec (before : ContractState) (newValue : Uint256) :
    let after := (Canary.setValue newValue).run before |>.snd
    setValue_spec before after newValue := by
  simp [setValue_spec, Canary.setValue, Canary.value,
    Specs.sameAddrMapContext, Specs.sameStorageAddr,
    Specs.sameStorageMap, Specs.sameStorageArray, Specs.sameContext]

/-- A real proof that the read surface elaborates and executes as specified. -/
theorem getValue_meets_spec (before : ContractState) :
    ((Canary.getValue).run before).fst = before.storage 0 := by
  rfl

end Contracts.Downstream431Canary

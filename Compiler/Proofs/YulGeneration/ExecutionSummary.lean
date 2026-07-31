import Compiler.Proofs.ExecutionSummary
import Compiler.Proofs.YulGeneration.RuntimeTypes

namespace Compiler.Proofs.YulGeneration

open Compiler.Proofs
open Compiler.Proofs.IRGeneration

/-- A storage slot accompanied by evidence that it belongs to the caller's
explicit observation boundary.  Native EVMYulLean results only materialize a
finite set of slots, so their summary adapter must not expose a total storage
function. -/
def ObservableStorageSlot (observableSlots : List Nat) :=
  { slot : Nat // slot ∈ observableSlots }

/-- Restrict an IR result to the same finite storage observation boundary used
by the native EVMYulLean harness. -/
def RawSummary.ofIRResultOn (observableSlots : List Nat) (result : IRResult) :
    RawSummary Nat (ObservableStorageSlot observableSlots) IRStorageWord (List Nat) :=
  { success := result.success
    returnValue := result.returnValue
    storage := fun slot => result.finalStorage (IRStorageSlot.ofNat slot.1)
    events := result.events }

/-- Expose a Yul result only on the caller-attested finite storage boundary.

In particular, an EVMYulLean-projected `YulResult` cannot be mistaken for an
authoritative total post-state: accessing storage requires a membership proof
for `observableSlots`, precisely the boundary used by `nativeResultsMatchOn`. -/
def RawSummary.ofYulResultOn (observableSlots : List Nat) (result : YulResult) :
    RawSummary Nat (ObservableStorageSlot observableSlots) IRStorageWord (List Nat) :=
  { success := result.success
    returnValue := result.returnValue
    storage := fun slot => result.finalStorage (IRStorageSlot.ofNat slot.1)
    events := result.events }

/-- Refinement seam used by backend proofs: equality of existing result
records implies equality of their checked, typed summaries. -/
theorem RawSummary.ofYulResult_refines_of_eq
    (observableSlots : List Nat) (ir : IRResult) (yul : YulResult)
    (hSuccess : yul.success = ir.success)
    (hReturn : yul.returnValue = ir.returnValue)
    (hStorage : ∀ slot, slot ∈ observableSlots →
      yul.finalStorage (IRStorageSlot.ofNat slot) =
        ir.finalStorage (IRStorageSlot.ofNat slot))
    (hEvents : yul.events = ir.events) :
    (RawSummary.ofYulResultOn observableSlots yul).toExecutionSummary? =
      (RawSummary.ofIRResultOn observableSlots ir).toExecutionSummary? := by
  cases yul
  cases ir
  simp_all [RawSummary.ofYulResultOn, RawSummary.ofIRResultOn]
  funext slot
  exact hStorage slot.1 slot.2

end Compiler.Proofs.YulGeneration

import Contracts.Common

namespace Contracts.Smoke.EnumFeatureTest

open Compiler.CompilationModel
open Verity hiding pure bind
open Verity.EVM.Uint256

verity_contract MacroEnumUsage where
  enums
    enum Status { Pending, Active, Closed }

  storage
    status : Status := slot 0
    statuses : Uint256 → Status := slot 1

  errors
    error InvalidStatus(Status)

  event_defs
    event StatusChanged(@indexed previous : Status, current : Status)

  function identity (value : Status) : Status := do
    return value

  function active () : Status := do
    return Status.Active

  function castStatus (value : Uint256) : Status := do
    let casted ← Status(value)
    return casted

  function setStatus (value : Status) : Unit := do
    setStorage status value

  function announceStatus (value : Status) : Unit := do
    emit "StatusChanged" [value, value]

  function getStatus () : Status := do
    let value ← getStorage status
    return value

  function setStatusAt (key : Uint256, value : Status) : Unit := do
    setMappingUint statuses key value

  function getStatusAt (key : Uint256) : Status := do
    let value ← getMappingUint statuses key
    return value

def identityUsesUint8Abi : Bool :=
  (match MacroEnumUsage.identity_model.params with
   | [{ ty, .. }] => paramTypeToSolidityString ty == "uint8"
   | _ => false) &&
    MacroEnumUsage.identity_model.returns == [ParamType.uint8]

example : identityUsesUint8Abi = true := by native_decide

def eventAndErrorUseUint8Abi : Bool :=
  MacroEnumUsage.spec.events.any (fun ev =>
    match ev with
    | { name := "StatusChanged", params :=
        [{ name := "previous", ty := ParamType.uint8, kind := EventParamKind.indexed },
         { name := "current", ty := ParamType.uint8, kind := EventParamKind.unindexed }] } => true
    | _ => false) &&
  MacroEnumUsage.spec.errors.any (fun err =>
    match err with
    | { name := "InvalidStatus", params := [ParamType.uint8] } => true
    | _ => false)

example : eventAndErrorUseUint8Abi = true := by native_decide

def memberConstantIsOne : Bool := MacroEnumUsage.Status.Active == 1

example : memberConstantIsOne = true := by native_decide

def castAcceptsLastMember : Bool :=
  match MacroEnumUsage.castStatus 2 defaultState with
  | .success value _ => value == 2
  | .revert _ _ => false

example : castAcceptsLastMember = true := by native_decide

def castRejectsOutOfRange : Bool :=
  match MacroEnumUsage.castStatus 3 defaultState with
  | .success _ _ => false
  | .revert _ _ => true

example : castRejectsOutOfRange = true := by native_decide

def enumParamRejectsOutOfRange : Bool :=
  match MacroEnumUsage.identity 3 defaultState with
  | .success _ _ => false
  | .revert _ _ => true

example : enumParamRejectsOutOfRange = true := by native_decide

/-- Expose the contract model at the canonical module-level name used by the compiler CLI. -/
def spec : CompilationModel := MacroEnumUsage.spec

end Contracts.Smoke.EnumFeatureTest

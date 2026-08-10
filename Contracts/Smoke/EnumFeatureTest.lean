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

/--
error: ite requires matching branch types, got Verity.Macro.ValueType.enum "Status" 3 and Verity.Macro.ValueType.uint256
-/
#guard_msgs in
verity_contract EnumIteRawWordRejected where
  enums
    enum Status { Pending, Active, Closed }

  storage
    status : Status := slot 0

  function bad (cond : Bool) : Unit := do
    setStorage status (ite cond Status.Active 999)

/--
error: typed interface call 'IStatus.current' uses an enum-valued return; checked enum decoding from untrusted external returndata is not implemented
-/
#guard_msgs in
verity_contract TypedInterfaceEnumReturnRejected where
  enums
    enum Status { Pending, Active, Closed }

  storage

  interfaces
    interface IStatus where
      function current() view returns (Status)
    end

  function bad (source : IStatus) : Status := do
    let value ← source.current
    return value

/-- -/
#guard_msgs in
verity_contract EnumOperatorsSupported where
  enums
    enum Status { Pending, Active }
  storage
  function isActive (value : Status) : Bool := do
    return value == Status.Active
  function nextOrdinal (value : Status) : Uint256 := do
    return toUint256 value + 1

/--
error: event 'StatusChanged' parameter 'current' expects Verity.Macro.ValueType.enum "Status" 2, got Verity.Macro.ValueType.enum "Role" 3
-/
#guard_msgs in
verity_contract CrossEnumEventRejected where
  enums
    enum Status { Pending, Active }
    enum Role { Guest, Member, Admin }

  storage

  event_defs
    event StatusChanged(current : Status)

  function bad (role : Role) : Unit := do
    emit "StatusChanged" [role]

/--
error: setStorage value expects Verity.Macro.ValueType.enum "Status" 3, got Verity.Macro.ValueType.uint256
-/
#guard_msgs in
verity_contract RawEnumStorageLiteralRejected where
  enums
    enum Status { Pending, Active, Closed }
  storage
    status : Status := slot 0
  function bad () : Unit := do
    setStorage status 1

/--
error: return from 'bad' expects Verity.Macro.ValueType.enum "Status" 3, got Verity.Macro.ValueType.uint256
-/
#guard_msgs in
verity_contract RawEnumReturnLiteralRejected where
  enums
    enum Status { Pending, Active, Closed }
  storage
  function bad () : Status := do
    return 1

/--
error: assignment to 'value' expects Verity.Macro.ValueType.enum "Status" 3, got Verity.Macro.ValueType.uint256
-/
#guard_msgs in
verity_contract RawEnumLocalAssignmentRejected where
  enums
    enum Status { Pending, Active, Closed }
  storage
  function bad () : Status := do
    let mut value := Status.Pending
    value := 1
    return value

/--
error: equality is currently supported only for Bool, matching bytes/string params, and word-like values (Uint256, Int256, Uint8, Address, Bytes32); got Verity.Macro.ValueType.enum "Status" 2 and Verity.Macro.ValueType.enum "Role" 2
-/
#guard_msgs in
verity_contract CrossEnumEqualityRejected where
  enums
    enum Status { Pending, Active }
    enum Role { Guest, Admin }
  storage
  function bad () : Bool := do
    return Status.Active == Role.Admin

/--
error: equality is currently supported only for Bool, matching bytes/string params, and word-like values (Uint256, Int256, Uint8, Address, Bytes32); got Verity.Macro.ValueType.enum "Status" 2 and Verity.Macro.ValueType.uint256
-/
#guard_msgs in
verity_contract EnumWordEqualityRejected where
  enums
    enum Status { Pending, Active }
  storage
  function bad (word : Uint256) : Bool := do
    return Status.Active == word

/--
error: word arithmetic requires `toUint256` before applying word operators to enum values; got Verity.Macro.ValueType.enum "Status" 2 and Verity.Macro.ValueType.uint256
-/
#guard_msgs in
verity_contract EnumArithmeticRejected where
  enums
    enum Status { Pending, Active }
  storage
  function bad (status : Status) : Uint256 := do
    return status + 1

/--
error: bitwise not requires `toUint256` before applying word operators to enum values; got Verity.Macro.ValueType.enum "Status" 2
-/
#guard_msgs in
verity_contract EnumUnaryWordOperatorRejected where
  enums
    enum Status { Pending, Active }
  storage
  function bad (status : Status) : Uint256 := do
    return bitNot status

/-- Expose the contract model at the canonical module-level name used by the compiler CLI. -/
def spec : CompilationModel := MacroEnumUsage.spec

end Contracts.Smoke.EnumFeatureTest

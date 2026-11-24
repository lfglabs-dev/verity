import Compiler.CompilationModel
import Compiler.ECM

set_option autoImplicit false

/-!
# Closed Byte-Transport CEI, Reentrancy & Free-Pointer Classifiers (`Compiler.SolidityImport.TransportBarriers`)

Construct-generic classifiers over `CompilationModel.Stmt` and
`Compiler.ECM.ExternalCallModule` used by `Compiler.SolidityImport.Import`:
* Closed byte-transport recognizers (`isClosedLowLevelCall`, `isClosedExtCodeSize`,
  `isClosedExtCodeHash`,
  `isClosedExtCodeCopy`, `isClosedReturnMemory`, `isClosedRevertMemory`, `isClosedStaticCall`,
  `isClosedCreate2`, `isClosedLog`)
* CEI and reentrancy barrier erasure / window classifiers (`eraseClosedStaticCalls`,
  `eraseClosedTransports`, `onlyClosedTransportCEIBarriers`,
  `onlyCreate2ReentrancyWindows`, `onlyStaticCallCEIBarriers`,
  `exprStorageFree`, `stmtAfterTrailingCall`, `onlyTrailingLowLevelCallWindows`,
  `onlyTrailingCallReentrancyWindows`, `eraseClosedInteractions`,
  `onlyClosedCallStateWindows`)
* Structural free-memory pointer (`0x40`) prologue detector
  (`ecmRequiresFreePointerInit`, `stmtRequiresFreePointerInit`,
  `stmtListRequiresFreePointerInit`) ensuring any root body that invokes a
  byte-transport ECM initializes `mstore(64, 128)`.
-/

namespace Compiler.CompilationModel.SolidityImport

open Compiler.CompilationModel

/-- The closed optional-bool low-level call transport emitted by the importer. -/
def isClosedLowLevelCall (mod : Compiler.ECM.ExternalCallModule) : Bool :=
  match mod.byteTransport with
  | some (.optionalBoolCall resultVar selector numWordArgs) =>
      mod == Compiler.ECM.SolidityLowLevelCall.optionalBoolModule resultVar selector numWordArgs
  | some (.callBytesUint256 resultVar selector) =>
      mod == Compiler.ECM.SolidityLowLevelCall.bytesUint256Module resultVar selector
  | some (.callBytesBool resultVar selector) =>
      mod == Compiler.ECM.SolidityLowLevelCall.bytesBoolModule resultVar selector
  | some (.yulMemoryCall false resultVar) => mod == Compiler.ECM.YulMemoryCall.module false resultVar
  | _ => false

abbrev isClosedOptionalBoolCall := isClosedLowLevelCall

/-- The closed `<address>.code.length` transport emitted by the importer. -/
def isClosedExtCodeSize (mod : Compiler.ECM.ExternalCallModule) : Bool :=
  match mod.byteTransport with
  | some (.extCodeSize resultVar) => mod == Compiler.ECM.SolidityExtCodeSize.module resultVar
  | _ => false

/-- The closed `<address>.codehash` transport emitted by the importer. -/
def isClosedExtCodeHash (mod : Compiler.ECM.ExternalCallModule) : Bool :=
  match mod.byteTransport with
  | some (.extCodeHash resultVar) => mod == Compiler.ECM.SolidityExtCodeHash.module resultVar
  | _ => false

/-- The closed `<address>.code` transport emitted by the importer. -/
def isClosedExtCodeCopy (mod : Compiler.ECM.ExternalCallModule) : Bool :=
  match mod.byteTransport with
  | some (.extCodeCopy resultVar) => mod == Compiler.ECM.SolidityExtCodeCopy.module resultVar
  | _ => false

/-- The closed memory `return` transport emitted by the importer. -/
def isClosedReturnMemory (mod : Compiler.ECM.ExternalCallModule) : Bool :=
  match mod.byteTransport with
  | some .returnMemory => mod == Compiler.ECM.SolidityReturnMemory.module
  | _ => false

abbrev isClosedMemoryReturn := isClosedReturnMemory

/-- The closed memory `revert` transport emitted by the importer. -/
def isClosedRevertMemory (mod : Compiler.ECM.ExternalCallModule) : Bool :=
  match mod.byteTransport with
  | some .revertMemory => mod == Compiler.ECM.SolidityRevertMemory.module
  | _ => false

/-- The closed typed-interface `staticcall` transport emitted by the importer. -/
def isClosedStaticCall (mod : Compiler.ECM.ExternalCallModule) : Bool :=
  match mod.byteTransport with
  | some (.staticUint256 resultVar selector numStaticArgs) =>
      mod == Compiler.ECM.SolidityStaticCall.uint256Module resultVar selector numStaticArgs
  | some (.staticBool resultVar selector numStaticArgs) =>
      mod == Compiler.ECM.SolidityStaticCall.boolModule resultVar selector numStaticArgs
  | some (.staticBytesUint256 resultVar selector) =>
      mod == Compiler.ECM.SolidityStaticCall.bytesUint256Module resultVar selector
  | some (.staticBytesBool resultVar selector) =>
      mod == Compiler.ECM.SolidityStaticCall.bytesBoolModule resultVar selector
  | some (.yulMemoryCall true resultVar) => mod == Compiler.ECM.YulMemoryCall.module true resultVar
  | _ => false

abbrev isClosedInterfaceStaticCall := isClosedStaticCall

/-- Replace each closed interface staticcall by its zero-initialised result
binding, so the CEI checker sees every other interaction barrier unchanged. -/
partial def eraseClosedStaticCalls : Stmt → Stmt
  | .ecm mod args =>
      if isClosedStaticCall mod then .letVar (mod.resultVars.headD "") (.literal 0) else .ecm mod args
  | .ite cond yes no => .ite cond (yes.map eraseClosedStaticCalls) (no.map eraseClosedStaticCalls)
  | .forEach name count body => .forEach name count (body.map eraseClosedStaticCalls)
  | .forEachSetBit name bitmap body => .forEachSetBit name bitmap (body.map eraseClosedStaticCalls)
  | .unsafeBlock reason body => .unsafeBlock reason (body.map eraseClosedStaticCalls)
  | .matchAdt adt scrutinee branches =>
      .matchAdt adt scrutinee (branches.map fun (tag, names, body) =>
        (tag, names, body.map eraseClosedStaticCalls))
  | statement => statement

/-- The closed `create2` transport emitted by the importer. -/
def isClosedCreate2 (mod : Compiler.ECM.ExternalCallModule) : Bool :=
  match mod.byteTransport with
  | some (.create2 resultVar) => mod == Compiler.ECM.SolidityCreate2.module resultVar
  | _ => false

/-- The closed event-log transport emitted by the importer. -/
def isClosedLog (mod : Compiler.ECM.ExternalCallModule) : Bool :=
  match mod.byteTransport with
  | some (.log eventName topicCount) => mod == Compiler.ECM.SolidityLog.module eventName topicCount
  | _ => false

/-- Replace every closed transport except the low-level `CALL` by a call-free
statement: a staticcall, `create2`, code length, code hash or code copy by its
zero-initialised result binding, a log by an empty branch, a memory return by
`stop`, a memory revert by an empty revert. -/
partial def eraseClosedTransports : Stmt → Stmt
  | .ecm mod args =>
      if isClosedStaticCall mod || isClosedCreate2 mod || isClosedExtCodeSize mod ||
          isClosedExtCodeHash mod || isClosedExtCodeCopy mod then
        .letVar (mod.resultVars.headD "") (.literal 0)
      else if isClosedLog mod then .ite (.literal 0) [] []
      else if isClosedReturnMemory mod then .stop
      else if isClosedRevertMemory mod then .revertEmpty
      else .ecm mod args
  | .ite cond yes no => .ite cond (yes.map eraseClosedTransports) (no.map eraseClosedTransports)
  | .forEach name count body => .forEach name count (body.map eraseClosedTransports)
  | .forEachSetBit name bitmap body =>
      .forEachSetBit name bitmap (body.map eraseClosedTransports)
  | .unsafeBlock reason body => .unsafeBlock reason (body.map eraseClosedTransports)
  | .matchAdt adt scrutinee branches =>
      .matchAdt adt scrutinee (branches.map fun (tag, names, body) =>
        (tag, names, body.map eraseClosedTransports))
  | statement => statement

abbrev eraseNonCallClosedTransports := eraseClosedTransports

/-- Replace the closed transports that change no account (code reads, staticcalls, logs,
memory returns) by call-free statements. Every other interaction, including a low-level
`CALL` and `create2`, is kept. -/
partial def eraseAccountPreservingTransports : Stmt → Stmt
  | .ecm mod args =>
      if isClosedStaticCall mod || isClosedExtCodeSize mod || isClosedExtCodeHash mod ||
          isClosedExtCodeCopy mod then
        .letVar (mod.resultVars.headD "") (.literal 0)
      else if isClosedLog mod then .ite (.literal 0) [] []
      else if isClosedReturnMemory mod then .stop
      else .ecm mod args
  | .ite cond yes no =>
      .ite cond (yes.map eraseAccountPreservingTransports) (no.map eraseAccountPreservingTransports)
  | .forEach name count body => .forEach name count (body.map eraseAccountPreservingTransports)
  | .forEachSetBit name bitmap body =>
      .forEachSetBit name bitmap (body.map eraseAccountPreservingTransports)
  | .unsafeBlock reason body => .unsafeBlock reason (body.map eraseAccountPreservingTransports)
  | .matchAdt adt scrutinee branches =>
      .matchAdt adt scrutinee (branches.map fun (tag, names, body) =>
        (tag, names, body.map eraseAccountPreservingTransports))
  | statement => statement

/-- `statement` may hand control to another account or create one, so the account world a
later code-hash read observes may differ: a value transfer makes an empty account exist,
`create2` gives an address code. -/
def stmtMayChangeAccounts (statement : Stmt) : Bool :=
  Compiler.CompilationModel.stmtOpensReentrancyWindow (eraseAccountPreservingTransports statement)

/-- Result bindings of the closed code-hash reads of `statements` that run after a
statement that may change accounts (`stmtMayChangeAccounts`), in program order, starting
from `seen`; also whether such a statement has run at the end. Either branch of a
conditional may have run, and a loop body's later iterations run after every account
change in it. -/
partial def codeHashesAfterChange (seen : Bool) (statements : List Stmt) : Bool × List String :=
  statements.foldl (fun (seen, found) statement =>
    let (seen', here) : Bool × List String := match statement with
      | .ecm mod _ =>
          match mod.byteTransport with
          | some (.extCodeHash result) =>
              if isClosedExtCodeHash mod then (seen, if seen then [result] else [])
              else (seen || stmtMayChangeAccounts statement, [])
          | _ => (seen || stmtMayChangeAccounts statement, [])
      | .ite _ yes no =>
          let (afterYes, foundYes) := codeHashesAfterChange seen yes
          let (afterNo, foundNo) := codeHashesAfterChange seen no
          (afterYes || afterNo, foundYes ++ foundNo)
      | .forEach _ _ body | .forEachSetBit _ _ body =>
          codeHashesAfterChange (seen || body.any stmtMayChangeAccounts) body
      | .unsafeBlock _ body => codeHashesAfterChange seen body
      | .matchAdt _ _ branches =>
          branches.foldl (fun (after, acc) (_, _, body) =>
            let (afterBody, foundBody) := codeHashesAfterChange seen body
            (after || afterBody, acc ++ foundBody)) (seen, [])
      | _ => (seen || stmtMayChangeAccounts statement, [])
    (seen', found ++ here)) (seen, [])

/-- A body whose only CEI barriers are closed transports. A log, code read or
memory return hands control to no account; Denote admits `create2` only for checked
initcode templates, which copy and return their payload without executing any
call. Low-level `CALL`s are never erased. -/
def onlyClosedTransportCEIBarriers (body : List Stmt) : Bool :=
  (Compiler.CompilationModel.stmtListCEIViolation body false).isSome &&
    (Compiler.CompilationModel.stmtListCEIViolation (body.map eraseClosedTransports) false).isNone

abbrev onlyClosedTransportBarriers := onlyClosedTransportCEIBarriers

/-- A body whose only cross-function reentrancy windows are closed `create2`s. -/
def onlyCreate2ReentrancyWindows (body : List Stmt) : Bool :=
  body.any Compiler.CompilationModel.stmtOpensReentrancyWindow &&
    !(body.map eraseClosedTransports).any Compiler.CompilationModel.stmtOpensReentrancyWindow

abbrev onlyClosedCreate2Reentrancy := onlyCreate2ReentrancyWindows

/-- A body whose only CEI interaction barriers are closed interface staticcalls.
STATICCALL executes the callee, and anything it calls, in a static context that
reverts on any state change, so a later write cannot follow a reentrant write. -/
def onlyStaticCallCEIBarriers (body : List Stmt) : Bool :=
  (Compiler.CompilationModel.stmtListCEIViolation body false).isSome &&
    (Compiler.CompilationModel.stmtListCEIViolation (body.map eraseClosedStaticCalls) false).isNone

/-- Expressions that read no persistent or transient storage and make no call. -/
def exprStorageFree (expression : Expr) : Bool :=
  !expression.anyDeep fun
    | .storage _ | .storageAddr _ | .mapping _ _ | .mappingWord _ _ _ | .mappingPackedWord _ _ _ _
    | .mapping2 _ _ _ | .mapping2Word _ _ _ _ | .mappingUint _ _ | .mappingChain _ _
    | .structMember _ _ _ | .structMember2 _ _ _ _ | .storageArrayLength _
    | .storageArrayElement _ _ | .tload _ | .call .. | .staticcall .. | .delegatecall ..
    | .internalCall _ _ | .externalCall _ _ | .adtTag _ _ | .adtField .. => true
    | _ => false

abbrev purePostCallExpr := exprStorageFree

/-- Statements allowed after a closed low-level call in a trailing-call body:
local bindings, memory writes, checks, returns, reverts (including panics of checked
arithmetic and forwarding the call's return data) and further closed low-level calls,
none of which reads or writes storage or logs. (A second CALL after the first still
fails the separate CEI check, since the first CALL is not erased.) A code-hash read is
not admitted: the call can change the account world it observes (a value transfer
makes an empty account exist, moving its hash from `0` to `keccak256("")`). -/
partial def stmtAfterTrailingCall : Stmt → Bool
  | .letVar _ value | .assignVar _ value | .require value _ => exprStorageFree value
  | .mstore offset value => exprStorageFree offset && exprStorageFree value
  | .requireError condition _ args => exprStorageFree condition && args.all exprStorageFree
  | .ite condition yes no =>
      exprStorageFree condition && yes.all stmtAfterTrailingCall && no.all stmtAfterTrailingCall
  | .ecm mod args => (isClosedLowLevelCall mod || isClosedExtCodeSize mod) && args.all exprStorageFree
  | .return value => exprStorageFree value
  | .returnValues values => values.all exprStorageFree
  | .panicCode code => exprStorageFree code
  | .revertEmpty | .revertReturndata | .panic _ | .stop => true
  | _ => false

abbrev allowedPostCallStmt := stmtAfterTrailingCall

/-- `statement` or a nested body contains a closed low-level `CALL`. -/
partial def stmtContainsClosedLowLevelCall : Stmt → Bool
  | .ecm mod _ => isClosedLowLevelCall mod
  | .ite _ yes no => yes.any stmtContainsClosedLowLevelCall || no.any stmtContainsClosedLowLevelCall
  | .forEach _ _ body | .forEachSetBit _ _ body => body.any stmtContainsClosedLowLevelCall
  | .unsafeBlock _ body => body.any stmtContainsClosedLowLevelCall
  | .matchAdt _ _ branches => branches.any fun (_, _, body) => body.any stmtContainsClosedLowLevelCall
  | _ => false

/-- A statement list whose only reentrancy windows are closed low-level calls
after which only `stmtAfterTrailingCall` statements execute. -/
partial def onlyTrailingLowLevelCallWindows : List Stmt → Bool
  | [] => true
  | statement :: rest =>
      if !Compiler.CompilationModel.stmtOpensReentrancyWindow statement then
        onlyTrailingLowLevelCallWindows rest
      else match statement with
        | .ecm mod _ => isClosedLowLevelCall mod && rest.all stmtAfterTrailingCall
        | .ite _ yes no =>
            onlyTrailingLowLevelCallWindows yes && onlyTrailingLowLevelCallWindows no &&
              rest.all stmtAfterTrailingCall
        | _ => false

abbrev onlyTrailingLowLevelCallWindow := onlyTrailingLowLevelCallWindows

/-- A body that opens a reentrancy window only through trailing closed
low-level calls. -/
def onlyTrailingCallReentrancyWindows (body : List Stmt) : Bool :=
  body.any Compiler.CompilationModel.stmtOpensReentrancyWindow &&
    onlyTrailingLowLevelCallWindows body

/-- `eraseClosedTransports`, and additionally replace each closed low-level `CALL`
by its zero-initialised result binding. What remains after erasure is every
interaction the importer did not emit as a closed transport. -/
partial def eraseClosedInteractions : Stmt → Stmt
  | .ecm mod args =>
      if isClosedLowLevelCall mod then .letVar (mod.resultVars.headD "") (.literal 0)
      else eraseClosedTransports (.ecm mod args)
  | .ite cond yes no => .ite cond (yes.map eraseClosedInteractions) (no.map eraseClosedInteractions)
  | .forEach name count body => .forEach name count (body.map eraseClosedInteractions)
  | .forEachSetBit name bitmap body =>
      .forEachSetBit name bitmap (body.map eraseClosedInteractions)
  | .unsafeBlock reason body => .unsafeBlock reason (body.map eraseClosedInteractions)
  | .matchAdt adt scrutinee branches =>
      .matchAdt adt scrutinee (branches.map fun (tag, names, body) =>
        (tag, names, body.map eraseClosedInteractions))
  | statement => eraseClosedTransports statement

/-- A body that makes a closed low-level `CALL` and whose every CEI barrier and
reentrancy window is a closed transport. Storage reads, storage writes and logs may
follow the call: Denote runs them against the world the callee's response committed
(`ByteExternalCall.Response.commit`), which an unconstrained adversary chooses freely,
including by re-entering this contract, so admission assumes nothing about the callee.
Any interaction that is not a closed transport keeps the body out. -/
def onlyClosedCallStateWindows (body : List Stmt) : Bool :=
  let erased := body.map eraseClosedInteractions
  body.any stmtContainsClosedLowLevelCall &&
    (Compiler.CompilationModel.stmtListCEIViolation erased false).isNone &&
    !erased.any Compiler.CompilationModel.stmtOpensReentrancyWindow

/-- True when an external call module uses a closed byte-transport descriptor
that may read or advance the Solidity free-memory pointer at address `0x40`. -/
def ecmRequiresFreePointerInit (mod : Compiler.ECM.ExternalCallModule) : Bool :=
  mod.byteTransport.isSome

mutual

/-- True when a statement or any nested branch/loop body invokes a byte-transport
external call module (`mod.byteTransport.isSome`). -/
def stmtRequiresFreePointerInit : Stmt → Bool
  | .ecm mod _ => ecmRequiresFreePointerInit mod
  | .ite _ yes no =>
      stmtListRequiresFreePointerInit yes || stmtListRequiresFreePointerInit no
  | .forEach _ _ body => stmtListRequiresFreePointerInit body
  | .forEachSetBit _ _ body => stmtListRequiresFreePointerInit body
  | .unsafeBlock _ body => stmtListRequiresFreePointerInit body
  | .matchAdt _ _ branches =>
      stmtBranchesRequireFreePointerInit branches
  | _ => false

/-- True when any statement in `stmts` invokes a byte-transport external call module. -/
def stmtListRequiresFreePointerInit : List Stmt → Bool
  | [] => false
  | s :: rest => stmtRequiresFreePointerInit s || stmtListRequiresFreePointerInit rest

/-- Helper over ADT match branches for `stmtRequiresFreePointerInit`. -/
def stmtBranchesRequireFreePointerInit : List (String × List String × List Stmt) → Bool
  | [] => false
  | (_, _, body) :: rest =>
      stmtListRequiresFreePointerInit body || stmtBranchesRequireFreePointerInit rest

end

@[simp] theorem stmtListRequiresFreePointerInit_nil :
    stmtListRequiresFreePointerInit [] = false := rfl

@[simp] theorem stmtListRequiresFreePointerInit_cons (s : Stmt) (rest : List Stmt) :
    stmtListRequiresFreePointerInit (s :: rest) =
      (stmtRequiresFreePointerInit s || stmtListRequiresFreePointerInit rest) := rfl

@[simp] theorem stmtRequiresFreePointerInit_ecm (mod : Compiler.ECM.ExternalCallModule) (args : List Expr) :
    stmtRequiresFreePointerInit (.ecm mod args) = mod.byteTransport.isSome := rfl

end Compiler.CompilationModel.SolidityImport

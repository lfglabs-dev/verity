import Compiler.Constants
import Compiler.CompilationModel.AbiHelpers
import Compiler.CompilationModel.DynamicData
import Compiler.IR
import Compiler.Yul.PrettyPrint
import Compiler.Yul.PatchFramework
import Verity.Core.Intrinsics

namespace Compiler.CodegenCommon

open Compiler.Constants (selectorShift)
open Compiler.CompilationModel
open Compiler.Yul

inductive BackendProfile where
  | semantic
  | solidityParityOrdering
  | solidityParity
  deriving Repr, DecidableEq

instance : Inhabited BackendProfile where
  default := .semantic

structure YulEmitOptions where
  backendProfile : BackendProfile := .semantic
  patchConfig : PatchPassConfig := { enabled := false }
  /-- EVM fork targeted by emitted Yul. Defaults to Cancun, the target schedule
      modeled by the pinned EVMYulLean fork. -/
  targetFork : Verity.Core.Intrinsics.HardFork := .cancun
  /-- Explicit escape hatch for building code that uses intrinsics from a fork
      newer than `targetFork`. Off by default. -/
  allowFutureForkIntrinsics : Bool := false
  /-- Scratch memory base used by compiler-generated mapping-slot helpers.
      Default `0` preserves historical behavior (`mstore(0, key); mstore(32, baseSlot)`). -/
  mappingSlotScratchBase : Nat := 0

structure RuntimeEmitReport where
  runtimeCode : List YulStmt
  patchReport : PatchPassReport

structure EmitObjectWithOptionsReport where
  patched : YulObject
  patchReport : PatchPassReport

structure PatchBackend where
  apply : YulObject → YulEmitOptions → EmitObjectWithOptionsReport

private def yulDatacopy : YulStmt :=
  YulStmt.expr (YulExpr.call "datacopy" [
    YulExpr.lit 0,
    YulExpr.call "dataoffset" [YulExpr.str "runtime"],
    YulExpr.call "datasize" [YulExpr.str "runtime"]
  ])

private def yulReturnRuntime : YulStmt :=
  YulStmt.expr (YulExpr.call "return" [
    YulExpr.lit 0,
    YulExpr.call "datasize" [YulExpr.str "runtime"]
  ])

def initFreeMemoryPointer : YulStmt :=
  YulStmt.expr (YulExpr.call "mstore" [
    YulExpr.lit Compiler.Constants.freeMemoryPointer,
    YulExpr.lit 128
  ])

def mappingSlotFuncAt (scratchBase : Nat) : YulStmt :=
  let keyPtr := scratchBase
  let slotPtr := scratchBase + 32
  YulStmt.funcDef "mappingSlot" ["baseSlot", "key"] ["slot"] [
    YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit keyPtr, YulExpr.ident "key"]),
    YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit slotPtr, YulExpr.ident "baseSlot"]),
    YulStmt.assign "slot" (YulExpr.call "keccak256" [YulExpr.lit keyPtr, YulExpr.lit 64])
  ]

/-- Revert if ETH is sent to a non-payable function. -/
def callvalueGuard : YulStmt :=
  YulStmt.if_ (YulExpr.call "callvalue" [])
    [YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])]

/-- Revert if calldata is shorter than expected (4-byte selector + 32 bytes per param). -/
def calldatasizeGuard (numParams : Nat) : YulStmt :=
  YulStmt.if_ (YulExpr.call "lt" [
    YulExpr.call "calldatasize" [],
    YulExpr.lit (4 + numParams * 32)])
    [YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])]

def dispatchBody (payable : Bool) (label : String) (body : List YulStmt) : List YulStmt :=
  let valueGuard := if payable then [] else [callvalueGuard]
  [YulStmt.comment label] ++ valueGuard ++ body

def defaultDispatchCase
    (fallback : Option IREntrypoint)
    (receive : Option IREntrypoint) : List YulStmt :=
  match receive, fallback with
  | none, none =>
      [YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])]
  | none, some fb =>
      dispatchBody fb.payable "fallback()" fb.body
  | some rc, none =>
      [YulStmt.block [
        YulStmt.let_ "__is_empty_calldata" (YulExpr.call "eq" [YulExpr.call "calldatasize" [], YulExpr.lit 0]),
        YulStmt.if_ (YulExpr.ident "__is_empty_calldata")
          (dispatchBody rc.payable "receive()" rc.body),
        YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident "__is_empty_calldata"])
          [YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])]
      ]]
  | some rc, some fb =>
      [YulStmt.block [
        YulStmt.let_ "__is_empty_calldata" (YulExpr.call "eq" [YulExpr.call "calldatasize" [], YulExpr.lit 0]),
        YulStmt.if_ (YulExpr.ident "__is_empty_calldata")
          (dispatchBody rc.payable "receive()" rc.body),
        YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident "__is_empty_calldata"])
          (dispatchBody fb.payable "fallback()" fb.body)
      ]]

private def insertBy [LT β] [DecidableRel (α := β) (· < ·)] (key : α → β) (x : α) : List α → List α
  | [] => [x]
  | head :: tail =>
      if key x < key head then x :: head :: tail
      else head :: insertBy key x tail

private def insertionSortBy [LT β] [DecidableRel (α := β) (· < ·)] (key : α → β) (xs : List α) : List α :=
  xs.foldl (fun acc x => insertBy key x acc) []

def buildSwitch
    (funcs : List IRFunction)
    (fallback : Option IREntrypoint := none)
    (receive : Option IREntrypoint := none)
    (sortCasesBySelector : Bool := false) : YulStmt :=
  let funcs :=
    if sortCasesBySelector then
      insertionSortBy (·.selector) funcs
    else
      funcs
  let selectorExpr := YulExpr.call "shr" [YulExpr.lit selectorShift, YulExpr.call "calldataload" [YulExpr.lit 0]]
  let cases := funcs.map (fun fn =>
    let body := dispatchBody fn.payable s!"{fn.name}()" ([calldatasizeGuard fn.params.length] ++ fn.body)
    (fn.selector, body)
  )
  let defaultCase := defaultDispatchCase fallback receive
  YulStmt.block [
    YulStmt.let_ "__has_selector"
      (YulExpr.call "iszero" [YulExpr.call "lt" [YulExpr.call "calldatasize" [], YulExpr.lit 4]]),
    YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident "__has_selector"]) defaultCase,
    YulStmt.if_ (YulExpr.ident "__has_selector")
      [YulStmt.switch selectorExpr cases (some defaultCase)]
  ]

private def yulExprSame (a b : YulExpr) : Bool :=
  toString (repr a) == toString (repr b)

private def yulStmtListSame (a b : List YulStmt) : Bool :=
  toString (repr a) == toString (repr b)

private def isRevertMessageBody (message : String) (body : List YulStmt) : Bool :=
  yulStmtListSame body (revertWithMessage message)

private def checkedAddFailCond (a b : YulExpr) : YulExpr :=
  YulExpr.call "lt" [YulExpr.call "add" [a, b], a]

private def checkedSubFailCond (a b : YulExpr) : YulExpr :=
  YulExpr.call "lt" [a, b]

private def checkedMulFailCond (a b : YulExpr) : YulExpr :=
  YulExpr.call "iszero" [
    YulExpr.call "or" [
      YulExpr.call "iszero" [YulExpr.call "iszero" [
        YulExpr.call "eq" [b, YulExpr.lit 0]
      ]],
      YulExpr.call "iszero" [YulExpr.call "iszero" [
        YulExpr.call "eq" [
          YulExpr.call "div" [YulExpr.call "mul" [a, b], b],
          a
        ]
      ]]
    ]
  ]

private def checkedDivFailCond (b : YulExpr) : YulExpr :=
  YulExpr.call "iszero" [YulExpr.call "iszero" [
    YulExpr.call "eq" [b, YulExpr.lit 0]
  ]]

private def checkedArithmeticReplacement? (prev cur : YulStmt) : Option YulStmt :=
  match prev, cur with
  | YulStmt.if_ cond body, YulStmt.let_ name (YulExpr.call "add" [a, b]) =>
      if yulExprSame cond (checkedAddFailCond a b) &&
          isRevertMessageBody "Panic(0x11): arithmetic overflow" body then
        some (YulStmt.let_ name (YulExpr.call checkedAddUint256HelperName [a, b]))
      else
        none
  | YulStmt.if_ cond body, YulStmt.let_ name (YulExpr.call "sub" [a, b]) =>
      if yulExprSame cond (checkedSubFailCond a b) &&
          isRevertMessageBody "Panic(0x11): arithmetic underflow" body then
        some (YulStmt.let_ name (YulExpr.call checkedSubUint256HelperName [a, b]))
      else
        none
  | YulStmt.if_ cond body, YulStmt.let_ name (YulExpr.call "mul" [a, b]) =>
      if yulExprSame cond (checkedMulFailCond a b) &&
          isRevertMessageBody "Panic(0x11): arithmetic overflow" body then
        some (YulStmt.let_ name (YulExpr.call checkedMulUint256HelperName [a, b]))
      else
        none
  | YulStmt.if_ cond body, YulStmt.let_ name (YulExpr.call "div" [a, b]) =>
      if yulExprSame cond (checkedDivFailCond b) &&
          isRevertMessageBody "Panic(0x12): division by zero" body then
        some (YulStmt.let_ name (YulExpr.call checkedDivUint256HelperName [a, b]))
      else
        none
  | _, _ => none

mutual

private def optimizeCheckedArithmeticStmtFuel : Nat → YulStmt → YulStmt
  | 0, stmt => stmt
  | fuel + 1, YulStmt.if_ cond body =>
      YulStmt.if_ cond (optimizeCheckedArithmeticStmtsFuel fuel body)
  | fuel + 1, YulStmt.for_ init cond post body =>
      YulStmt.for_
        (optimizeCheckedArithmeticStmtsFuel fuel init)
        cond
        (optimizeCheckedArithmeticStmtsFuel fuel post)
        (optimizeCheckedArithmeticStmtsFuel fuel body)
  | fuel + 1, YulStmt.switch expr cases default =>
      YulStmt.switch expr
        (cases.map fun (tag, body) => (tag, optimizeCheckedArithmeticStmtsFuel fuel body))
        (default.map (optimizeCheckedArithmeticStmtsFuel fuel))
  | fuel + 1, YulStmt.block stmts =>
      YulStmt.block (optimizeCheckedArithmeticStmtsFuel fuel stmts)
  | fuel + 1, YulStmt.funcDef name params rets body =>
      YulStmt.funcDef name params rets (optimizeCheckedArithmeticStmtsFuel fuel body)
  | _fuel + 1, stmt => stmt

private def optimizeCheckedArithmeticStmtsFuel : Nat → List YulStmt → List YulStmt
  | 0, stmts => stmts
  | _fuel + 1, [] => []
  | fuel + 1, [stmt] => [optimizeCheckedArithmeticStmtFuel fuel stmt]
  | fuel + 1, prev :: cur :: rest =>
      let prev' := optimizeCheckedArithmeticStmtFuel fuel prev
      let cur' := optimizeCheckedArithmeticStmtFuel fuel cur
      match checkedArithmeticReplacement? prev' cur' with
      | some replacement => replacement :: optimizeCheckedArithmeticStmtsFuel fuel rest
      | none => prev' :: optimizeCheckedArithmeticStmtsFuel fuel (cur :: rest)

end

private def yulStmtListFuel (stmts : List YulStmt) : Nat :=
  (toString (repr stmts)).length + 1

private def optimizeCheckedArithmeticStmts (stmts : List YulStmt) : List YulStmt :=
  optimizeCheckedArithmeticStmtsFuel (yulStmtListFuel stmts) stmts

private def internalHelperNamed (name : String) : YulStmt → Bool
  | YulStmt.funcDef fnName _ _ _ => fnName == name
  | _ => false

private def hasCheckedArithmeticHelpers (contract : IRContract) : Bool :=
  contract.internalFunctions.any (internalHelperNamed checkedAddUint256HelperName) &&
    contract.internalFunctions.any (internalHelperNamed checkedSubUint256HelperName) &&
    contract.internalFunctions.any (internalHelperNamed checkedMulUint256HelperName) &&
    contract.internalFunctions.any (internalHelperNamed checkedDivUint256HelperName)

private def optimizeCheckedArithmeticIfAvailable (contract : IRContract) (stmts : List YulStmt) :
    List YulStmt :=
  if hasCheckedArithmeticHelpers contract then
    optimizeCheckedArithmeticStmts stmts
  else
    stmts

def optimizeCheckedArithmeticObjectIfAvailable (contract : IRContract) (object : YulObject) :
    YulObject :=
  { object with
    deployCode := optimizeCheckedArithmeticIfAvailable contract object.deployCode
    runtimeCode := optimizeCheckedArithmeticIfAvailable contract object.runtimeCode }

def runtimeCode (contract : IRContract) : List YulStmt :=
  let mapping := if contract.usesMapping then [mappingSlotFuncAt 0] else []
  let internals := contract.internalFunctions
  mapping ++ internals ++ [initFreeMemoryPointer, buildSwitch contract.functions contract.fallbackEntrypoint contract.receiveEntrypoint]

private def profileSortsOutput (profile : BackendProfile) : Bool :=
  match profile with
  | .semantic => false
  | .solidityParityOrdering => true
  | .solidityParity => true

private def profileSortsDispatchCases (profile : BackendProfile) : Bool :=
  profileSortsOutput profile

private def profileSortsInternalHelpers (profile : BackendProfile) : Bool :=
  profileSortsOutput profile

private def internalHelperName? (stmt : YulStmt) : Option String :=
  match stmt with
  | .funcDef name _ _ _ => some name
  | _ => none

private def sortInternalHelpersByName (helpers : List YulStmt) : List YulStmt :=
  let named := helpers.filterMap (fun stmt =>
    match internalHelperName? stmt with
    | some name => some (name, stmt)
    | none => none)
  if named.length == helpers.length then
    (insertionSortBy Prod.fst named).map Prod.snd
  else
    helpers

private def internalHelpersForProfile (profile : BackendProfile) (helpers : List YulStmt) : List YulStmt :=
  if profileSortsInternalHelpers profile then
    sortInternalHelpersByName helpers
  else
    helpers

private def runtimeCodeWithEmitOptions (contract : IRContract) (options : YulEmitOptions) : List YulStmt :=
  let mapping := if contract.usesMapping then [mappingSlotFuncAt options.mappingSlotScratchBase] else []
  let internals := internalHelpersForProfile options.backendProfile contract.internalFunctions
  let sortCases := profileSortsDispatchCases options.backendProfile
  let switchStmt := buildSwitch contract.functions contract.fallbackEntrypoint contract.receiveEntrypoint sortCases
  mapping ++ internals ++ [initFreeMemoryPointer, switchStmt]

private def deployCodeWithProfile (contract : IRContract) (profile : BackendProfile)
    (mappingSlotScratchBase : Nat := 0) : List YulStmt :=
  let valueGuard := if contract.constructorPayable then [] else [callvalueGuard]
  let mapping := if contract.usesMapping then [mappingSlotFuncAt mappingSlotScratchBase] else []
  let internals := internalHelpersForProfile profile contract.internalFunctions
  [initFreeMemoryPointer] ++ valueGuard ++ mapping ++ internals ++ contract.deploy ++ [yulDatacopy, yulReturnRuntime]

private def deployCode (contract : IRContract) : List YulStmt :=
  deployCodeWithProfile contract .semantic

private def baseObjectWithOptions (contract : IRContract) (options : YulEmitOptions) : YulObject :=
  { name := contract.name
    deployCode := deployCodeWithProfile contract options.backendProfile options.mappingSlotScratchBase
    runtimeCode := runtimeCodeWithEmitOptions contract options }

private def runtimeCodeWithOptionsReport
    (backend : PatchBackend)
    (contract : IRContract)
    (options : YulEmitOptions) : RuntimeEmitReport :=
  let report := backend.apply (baseObjectWithOptions contract options) options
  { runtimeCode := report.patched.runtimeCode
    patchReport := report.patchReport }

private def runtimeCodeWithOptions
    (backend : PatchBackend)
    (contract : IRContract)
    (options : YulEmitOptions) : List YulStmt :=
  (runtimeCodeWithOptionsReport backend contract options).runtimeCode

def emitYul (contract : IRContract) : YulObject :=
  { name := contract.name
    deployCode := deployCode contract
    runtimeCode := runtimeCode contract }

def emitYulWithOptions (backend : PatchBackend) (contract : IRContract) (options : YulEmitOptions) : YulObject :=
  (backend.apply (baseObjectWithOptions contract options) options).patched

def emitYulWithOptionsReport
    (backend : PatchBackend)
    (contract : IRContract)
    (options : YulEmitOptions) : YulObject × PatchPassReport :=
  let report := backend.apply (baseObjectWithOptions contract options) options
  (report.patched, report.patchReport)

example (backend : PatchBackend) (contract : IRContract) (options : YulEmitOptions) :
    (runtimeCodeWithOptionsReport backend contract options).runtimeCode =
      runtimeCodeWithOptions backend contract options := by
  rfl

example (backend : PatchBackend) (contract : IRContract) (options : YulEmitOptions) :
    (emitYulWithOptionsReport backend contract options).1 =
      emitYulWithOptions backend contract options := by
  rfl

example (backend : PatchBackend) (contract : IRContract) (options : YulEmitOptions) :
    (emitYulWithOptionsReport backend contract options).2 =
      (runtimeCodeWithOptionsReport backend contract options).patchReport := by
  rfl

def contains (haystack needle : String) : Bool :=
  let h := haystack.toList
  let n := needle.toList
  if n.isEmpty then true
  else
    let rec go : List Char → Bool
      | [] => false
      | c :: cs =>
          if (c :: cs).take n.length == n then true
          else go cs
    go h

mutual
  def stmtContainsSwitchCaseCall (target : String) : YulStmt → Bool
    | .comment _ => false
    | .let_ _ _ => false
    | .letMany _ _ => false
    | .assign _ _ => false
    | .expr _ => false
    | .leave => false
    | .if_ _ body => stmtListContainsSwitchCaseCall target body
    | .for_ init _ post body =>
        stmtListContainsSwitchCaseCall target init ||
        stmtListContainsSwitchCaseCall target post ||
        stmtListContainsSwitchCaseCall target body
    | .switch _ cases default =>
        let caseHit :=
          cases.any (fun (_, body) =>
            match body with
            | [.expr (.call fn [])] => decide (fn = target)
            | _ => false)
        let defaultHit :=
          match default with
          | some body => stmtListContainsSwitchCaseCall target body
          | none => false
        caseHit || defaultHit
    | .block stmts => stmtListContainsSwitchCaseCall target stmts
    | .funcDef _ _ _ body => stmtListContainsSwitchCaseCall target body
  termination_by stmt => sizeOf stmt

  def stmtListContainsSwitchCaseCall (target : String) : List YulStmt → Bool
    | [] => false
    | stmt :: rest =>
        stmtContainsSwitchCaseCall target stmt || stmtListContainsSwitchCaseCall target rest
  termination_by stmts => sizeOf stmts
end

/-- Regression guard: solidity parity profile keeps dispatch inlined in switch cases. -/
example :
    let contract : IRContract :=
      { name := "DispatchOutlineRegression"
        deploy := []
        constructorPayable := true
        functions :=
          [{ name := "ping"
             selector := 1
             params := []
             ret := .unit
             payable := false
             body := [.leave] }]
        usesMapping := false
        internalFunctions := [] }
    let runtime := runtimeCodeWithEmitOptions contract { backendProfile := .solidityParity }
    let hasFunHelper :=
      runtime.any (fun stmt =>
        match stmt with
        | .funcDef "fun_ping" [] [] _ => true
        | _ => false)
    let switchCallsHelper := runtime.any (stmtContainsSwitchCaseCall "fun_ping")
    (!hasFunHelper) && (!switchCallsHelper) := by
  native_decide

end Compiler.CodegenCommon

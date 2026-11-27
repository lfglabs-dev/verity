import Compiler.Codegen
import Compiler.CompilationModel
import Compiler.SolidityImport.AbiEncoding
import Compiler.Yul.PrettyPrint

/-! Differential and adversarial-reproducer Yul emitter for `Compiler.emitYulSpilled` vs
`Compiler.emitYul`. Invoked both standalone (`lake env lean --run`) and from
`scripts/solidity_differential/check_dispatched_spill.py` to assemble and compare both Yul
outputs on `anvil`. -/
namespace SolidityImportSmoke.DispatchedSpillChecks

open Compiler
open Compiler.CompilationModel
open Compiler.CompilationModel.SolidityImport
open Compiler.Yul

/-- `n` chained local `let` bindings that all remain live until `sumChainVars`. -/
private def mkLiveChainStmts (n : Nat) : List Stmt :=
  (List.range n).map fun i =>
    if i == 0 then
      .letVar "c0" (.add (.param "a") (.param "b"))
    else
      .letVar s!"c{i}" (.add (.localVar s!"c{i - 1}")
        (if i % 3 == 0 then .param "a" else if i % 3 == 1 then .param "b" else .param "c"))

private def sumChainExpr (n : Nat) : Expr :=
  (List.range n).foldl
    (fun acc i => .add acc (.localVar s!"c{i}"))
    (.literal 0)

/-- Function 1: exceeds `defaultMaxStackLocals` (14 live locals) while allocating heap via the
checked-allocation idiom (`AbiEncoding.staticWords`) and hashing the allocated words. -/
private def allocAndSpillFn : FunctionSpec :=
  { name := "hashAfterSpillAndAlloc"
    params := [
      { name := "a", ty := .uint256 },
      { name := "b", ty := .uint256 },
      { name := "c", ty := .uint256 }
    ]
    returnType := some .uint256
    body :=
      mkLiveChainStmts 14 ++
        AbiEncoding.staticWords "alloc_base" "alloc_end"
          [.localVar "c6", .localVar "c13"] ++
        [ .letVar "digest" (.keccak256 (.localVar "alloc_base") (.literal 64)),
          .setStorage "lastDigest" (.localVar "digest"),
          .return (.add (.localVar "digest") (sumChainExpr 14)) ]
    localObligations := [{
      name := "checked_heap_alloc"
      obligation := "Checked static-word heap allocation for differential smoke."
      proofStatus := .unchecked }] }

/-- Function 2: exceeds `defaultMaxStackLocals` and returns a dynamic `uint256[]` from address 0
(tested past 4 KiB on `anvil`), so its dispatch case must remain unspilled while Function 1 spills
in the same contract. -/
private def dynamicReturnFn : FunctionSpec :=
  { name := "echoDynamicTail"
    params := [
      { name := "a", ty := .uint256 },
      { name := "b", ty := .uint256 },
      { name := "c", ty := .uint256 },
      { name := "d", ty := .uint256 },
      { name := "values", ty := .array .uint256 }
    ]
    returnType := none
    returns := [.array .uint256]
    body :=
      (List.range 10).map (fun i =>
        .letVar s!"w{i}" (.add (.param "a") (.literal (i + 1)))) ++
      [ .setStorage "lastDigest"
          (.add (.add (.param "a") (.param "b")) (.add (.param "c") (.localVar "w9"))),
        .returnArray "values" ] }

private def differentialModel : CompilationModel :=
  { name := "DispatchedSpillDifferential"
    fields := [{ name := "lastDigest", ty := .uint256 }]
    constructor := none
    functions := [allocAndSpillFn, dynamicReturnFn] }

/-- Build 14 live Yul `let` bindings `v1 := 1 .. v14 := 14` (sum = 105) plus a Binding `"sum"`
computing their sum so spilling activates (`countLetBindings > 12`) while staying `< 16` stack
slots for unoptimized `solc --strict-assembly`. -/
private def yulLiveLets14 : List YulStmt × YulExpr :=
  let lets := (List.range 14).map fun i => YulStmt.let_ s!"v{i}" (.lit (i + 1))
  let sumExpr := (List.range 14).foldl
    (fun acc i => YulExpr.call "add" [acc, .ident s!"v{i}"])
    (.lit 0)
  (lets, sumExpr)

private def singleFnContract (name : String) (selector : Nat) (numParams : Nat)
    (body : List YulStmt) (fallback : Option IREntrypoint := none) : IRContract :=
  { name := name
    deploy := []
    constructorPayable := true
    functions := [
      { name := "entry"
        selector := selector
        params := (List.range numParams).map fun i => { name := s!"p{i}", ty := .uint256 }
        ret := .uint256
        payable := true
        body := body }
    ]
    fallbackEntrypoint := fallback
    receiveEntrypoint := none
    usesMapping := false
    internalFunctions := [] }

/-- Reviewer Reproducer 1: `mstore(0, sum) mstore(32, 99) mstore(64, 128) return(0, 96)` in a case
that also touches `mload(64)` (would return `[105, 99, highWater]` on `64499d299`). -/
private def repro1Contract : IRContract :=
  let (lets, sumExpr) := yulLiveLets14
  singleFnContract "Repro1TupleStore" 0x11111111 0
    (lets ++ [
      .let_ "p" (.call "mload" [.lit 64]),
      .exprStmt (.call "mstore" [.ident "p", .lit 1]),
      .exprStmt (.call "mstore" [.lit 0, sumExpr]),
      .exprStmt (.call "mstore" [.lit 32, .lit 99]),
      .exprStmt (.call "mstore" [.lit 64, .lit 128]),
      .exprStmt (.call "return" [.lit 0, .lit 96])
    ])

/-- Reviewer Reproducer 2: `mstore(add(p, 2^256 - 32), 999999)` wraps mod `2^256` onto the top
spill word when spilled (would corrupt `sum` on `64499d299`). -/
private def repro2Contract : IRContract :=
  let (lets, sumExpr) := yulLiveLets14
  singleFnContract "Repro2WrapAddend" 0x22222222 0
    (lets ++ [
      .let_ "p" (.call "mload" [.lit 64]),
      .exprStmt (.call "mstore" [.call "add" [.ident "p", .lit (2 ^ 256 - 32)], .lit 999999]),
      .exprStmt (.call "mstore" [.lit 0, sumExpr]),
      .exprStmt (.call "return" [.lit 0, .lit 32])
    ])

/-- Reviewer Reproducer 3: `if calldataload(4) { let p := mload(64) mstore(p, 1) } ... return(0, 96)`
with arg `0` observes the case-entry `mstore(64, highWater)` (would return `[105, 0, highWater]` on
`64499d299`). -/
private def repro3Contract : IRContract :=
  let (lets, sumExpr) := yulLiveLets14
  singleFnContract "Repro3ObservableFp" 0x33333333 1
    (lets ++ [
      .if_ (.call "calldataload" [.lit 4]) [
        .let_ "p" (.call "mload" [.lit 64]),
        .exprStmt (.call "mstore" [.ident "p", .lit 1])
      ],
      .exprStmt (.call "mstore" [.lit 0, sumExpr]),
      .exprStmt (.call "mstore" [.lit 32, .lit 0]),
      .exprStmt (.call "return" [.lit 0, .lit 96])
    ])

/-- Reviewer Reproducer 4: `fallback` allocates `buf := mload(64)`, writes `777` at runtime offset
`buf + calldataload(4)` (`4096` when `buf = 128` and `calldataload(4) = 3968`), runs a
non-terminating `switch callvalue() case 0 { ... }` that spills `5` to `4096` if misclassified as
selector dispatch, then returns `mload(buf + calldataload(4))` (would return `[5]` instead of
`[777]` on `64499d299`). -/
private def repro4Contract : IRContract :=
  let fallbackLets :=
    YulStmt.let_ "f0" (.lit 5) ::
      (List.range 13).map (fun i => YulStmt.let_ s!"f{i + 1}" (.lit (i + 6)))
  let fallbackSum :=
    (List.range 14).foldl (fun acc i => YulExpr.call "add" [acc, .ident s!"f{i}"]) (.lit 0)
  let fb : IREntrypoint :=
    { payable := true
      body := [
        .let_ "buf" (.call "mload" [.lit 64]),
        .let_ "off" (.call "calldataload" [.lit 4]),
        .exprStmt (.call "mstore" [.call "add" [.ident "buf", .ident "off"], .lit 777]),
        .switch (.call "callvalue" [])
          [(0, fallbackLets ++ [.exprStmt (.call "sstore" [.lit 1, fallbackSum])])]
          none,
        .exprStmt (.call "mstore" [.lit 0, .call "mload" [.call "add" [.ident "buf", .ident "off"]]]),
        .exprStmt (.call "return" [.lit 0, .lit 32])
      ] }
  singleFnContract "Repro4FallbackInnerSwitch" 0x44444444 0
    [.exprStmt (.call "return" [.lit 0, .lit 0])]
    (some fb)

/-- Round-2 Reproducer 5: static `mstore(128, 999)` (`returnValues` with ≥ 5 words) mixed with
`mload(64)` heap allocation (`128` unspilled vs `highWater` spilled). -/
private def repro5Contract : IRContract :=
  let (lets, sumExpr) := yulLiveLets14
  singleFnContract "Repro5Static128Alias" 0x55555555 0
    (lets ++ [
      .let_ "p" (.call "mload" [.lit 64]),
      .exprStmt (.call "mstore" [.ident "p", .lit 111]),
      .exprStmt (.call "mstore" [.lit 0, .call "add" [sumExpr, .call "mload" [.lit 128]]]),
      .exprStmt (.call "return" [.lit 0, .lit 32])
    ])

/-- Round-2 Reproducer 6: checked allocation of `calldataload(4)` (`2^64 - 129` on `anvil`), where
`128 + sz = 2^64 - 1` succeeds unspilled while `highWater + sz > 2^64 - 1` would revert if spilled. -/
private def repro6Contract : IRContract :=
  let (lets, sumExpr) := yulLiveLets14
  let revert41 : List YulStmt := [
    .exprStmt (.call "mstore" [.lit 0, .hex 0x4e487b7100000000000000000000000000000000000000000000000000000000]),
    .exprStmt (.call "mstore" [.lit 4, .hex 0x41]),
    .exprStmt (.call "revert" [.lit 0, .lit 36])
  ]
  singleFnContract "Repro6NearU64Reserve" 0x66666666 1
    (lets ++ [
      .let_ "sz" (.call "calldataload" [.lit 4]),
      .let_ "p" (.call "mload" [.lit 64]),
      .let_ "pEnd" (.call "add" [.ident "p", .ident "sz"]),
      .if_ (.call "gt" [.ident "pEnd", .lit (2 ^ 64 - 1)]) revert41,
      .if_ (.call "lt" [.ident "pEnd", .ident "p"]) revert41,
      .exprStmt (.call "mstore" [.lit 64, .ident "pEnd"]),
      .exprStmt (.call "mstore" [.ident "p", sumExpr]),
      .exprStmt (.call "sstore" [.lit 0, sumExpr]),
      .exprStmt (.call "mstore" [.lit 0, .call "mload" [.ident "p"]]),
      .exprStmt (.call "return" [.lit 0, .lit 32])
    ])

/-- Round-3 Reproducer 7a: `break` inside a `for` loop before `revert(0, 0)` after `mstore(64, 0)`
must not mask `fpClean := false` or allow `mstore(add(p, 4096), 999999)` to clobber spill slot 4096. -/
private def repro7BreakContract : IRContract :=
  let (lets, sumExpr) := yulLiveLets14
  singleFnContract "Repro7BreakFpReset" 0x77777777 1
    (lets ++ [
      .for_ [.let_ "i" (.lit 0)] (.call "lt" [.ident "i", .lit 1])
        [.assign "i" (.call "add" [.ident "i", .lit 1])]
        [ .exprStmt (.call "mstore" [.lit 64, .lit 0]),
          .if_ (.call "calldataload" [.lit 4]) [.exprStmt (.ident "break")],
          .exprStmt (.call "revert" [.lit 0, .lit 0]) ],
      .let_ "p" (.call "mload" [.lit 64]),
      .exprStmt (.call "mstore" [.call "add" [.ident "p", .lit 4096], .lit 999999]),
      .exprStmt (.call "mstore" [.lit 0, sumExpr]),
      .exprStmt (.call "return" [.lit 0, .lit 32])
    ])

/-- Round-3 Reproducer 7b: `continue` inside a nested `if` in a `for` loop before `revert(0, 0)`
after `mstore(64, 0)` must not mask `fpClean := false` or clobber spill slot 4096. -/
private def repro7ContinueContract : IRContract :=
  let (lets, sumExpr) := yulLiveLets14
  singleFnContract "Repro7ContinueFpReset" 0x77777778 1
    (lets ++ [
      .for_ [.let_ "i" (.lit 0)] (.call "lt" [.ident "i", .lit 2])
        [.assign "i" (.call "add" [.ident "i", .lit 1])]
        [ .if_ (.call "eq" [.ident "i", .lit 0])
            [ .exprStmt (.call "mstore" [.lit 64, .lit 0]),
              .if_ (.call "calldataload" [.lit 4]) [.exprStmt (.ident "continue")],
              .exprStmt (.call "revert" [.lit 0, .lit 0]) ] ],
      .let_ "p" (.call "mload" [.lit 64]),
      .exprStmt (.call "mstore" [.call "add" [.ident "p", .lit 4096], .lit 999999]),
      .exprStmt (.call "mstore" [.lit 0, sumExpr]),
      .exprStmt (.call "return" [.lit 0, .lit 32])
    ])

private def checkAndEmit (outDir? : Option String) : IO Unit := do
  let ir ← match Compiler.CompilationModel.compile differentialModel [0x11111111, 0x22222222] with
    | .ok c => pure c
    | .error err => throw (IO.userError s!"DispatchedSpillDifferential failed to compile: {err}")
  let baseObj := Compiler.emitYul ir
  let spilledObj := Compiler.emitYulSpilled ir
  let baseText := Compiler.Yul.render baseObj
  let spilledText := Compiler.Yul.render spilledObj
  unless !Compiler.CodegenCommon.contains baseText "mstore(4096," do
    throw (IO.userError "unspilled baseline unexpectedly contains spill slot 4096")
  unless Compiler.CodegenCommon.contains spilledText "mstore(4096," &&
         Compiler.CodegenCommon.contains spilledText "mload(4096)" do
    throw (IO.userError "emitYulSpilled did not spill allocAndSpillFn")
  -- Extract the second case (`0x22222222`) from both objects and verify it is untouched.
  let findCase (obj : YulObject) (sel : Nat) : Option (List YulStmt) :=
    obj.runtimeCode.findSome? fun
      | .block [ _, _, .if_ _ [ .switch _ cases _ ] ] =>
          (cases.find? (·.1 == sel)).map Prod.snd
      | _ => none
  let some baseDynCase := findCase baseObj 0x22222222
    | throw (IO.userError "missing 0x22222222 case in baseline")
  let some spilledDynCase := findCase spilledObj 0x22222222
    | throw (IO.userError "missing 0x22222222 case in spilled")
  unless baseDynCase == spilledDynCase do
    throw (IO.userError "dynamic-return case 0x22222222 must remain unspilled")
  let some spilledAllocCase := findCase spilledObj 0x11111111
    | throw (IO.userError "missing 0x11111111 case in spilled")
  let hw := TempReuse.spillHighWaterStmts spilledAllocCase
  unless hw ≥ TempReuse.defaultSpillBase + 32 &&
         spilledAllocCase.head? == some (.exprStmt (.call "mstore" [.lit 64, .lit hw])) do
    throw (IO.userError "alloc case 0x11111111 missing prepended mstore(64, highWater)")
  -- Verify reproducers 2–7 are left completely unspilled, and reproducer 1 preserves mstore(64, 128).
  for (label, c) in [
    ("repro2", repro2Contract),
    ("repro3", repro3Contract),
    ("repro4", repro4Contract),
    ("repro5", repro5Contract),
    ("repro6", repro6Contract),
    ("repro7a", repro7BreakContract),
    ("repro7b", repro7ContinueContract)
  ] do
    let u := Compiler.emitYul c
    let s := Compiler.emitYulSpilled c
    unless u.runtimeCode == s.runtimeCode do
      throw (IO.userError s!"{label} must be left unchanged by emitYulSpilled")
  let r1Spilled := Compiler.Yul.render (Compiler.emitYulSpilled repro1Contract)
  unless Compiler.CodegenCommon.contains r1Spilled "mstore(64, 128)" do
    throw (IO.userError "repro1 must preserve in-case mstore(64, 128)")
  if let some dir := outDir? then
    IO.FS.createDirAll dir
    let targets := [
      ("differential", ir),
      ("repro1", repro1Contract),
      ("repro2", repro2Contract),
      ("repro3", repro3Contract),
      ("repro4", repro4Contract),
      ("repro5", repro5Contract),
      ("repro6", repro6Contract),
      ("repro7a", repro7BreakContract),
      ("repro7b", repro7ContinueContract)
    ]
    for (stem, contract) in targets do
      IO.FS.writeFile s!"{dir}/{stem}.baseline.yul"
        (Compiler.Yul.render (Compiler.emitYul contract))
      IO.FS.writeFile s!"{dir}/{stem}.spilled.yul"
        (Compiler.Yul.render (Compiler.emitYulSpilled contract))

end SolidityImportSmoke.DispatchedSpillChecks

def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
      SolidityImportSmoke.DispatchedSpillChecks.checkAndEmit none
      return 0
  | [outDir] =>
      SolidityImportSmoke.DispatchedSpillChecks.checkAndEmit (some outDir)
      return 0
  | _ =>
      IO.eprintln "usage: DispatchedSpillChecks [OUT_DIR]"
      return 2

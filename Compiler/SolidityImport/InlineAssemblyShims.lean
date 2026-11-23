import Lean
import Compiler.SolidityImport.StorageLayout

open Lean Meta Elab Command

namespace Compiler.CompilationModel.SolidityImport

/-!
# Trusted importer shortcuts

A few inline-assembly blocks are not translated. When a block's `yulBlockFingerprint` (sha256
of its solc Yul AST without source positions) equals the fingerprint of an entry of
`trustedImporterShortcuts`, the importer replaces the block with that entry's fixed lowering.

These shortcuts are trusted, not verified: no Lean proof relates a lowering to the block it
replaces. The fingerprint only identifies the block. Each entry names the tests that compare
the lowering's results with solc's (`TrustedShortcut.evidence`). The model of a replaced block
is the fixed lowering, so a proof about a root that uses a shortcut relies on the lowering and
the block agreeing. The import report lists the shortcuts each root uses
(`FunctionStatus.shortcuts`).

A lowering can only be applied through a `TrustedShortcutMatch`, which only
`matchTrustedShortcut?` builds, from a block whose fingerprint is registered. Applying it
records the shortcut in the current root's report. `scripts/check_importer_name_selection.py`
(`make check`) rejects name literals of user code and registry bypasses in importer code (a text
check; what it cannot see is listed there and left to review).
-/

/-- The fixed lowering a trusted shortcut replaces its block with. -/
inductive TrustedShortcutLowering where
  /-- `lowerBatchArrayLoadShim` with one `sload` per calldata key. -/
  | batchStorageRead
  /-- `lowerBatchArrayLoadShim` with one `tload` per calldata key. -/
  | batchTransientRead
  /-- `lowerBatchRangeSloadShim`: `sload` of consecutive slots. -/
  | rangeStorageRead
  deriving DecidableEq, Repr

/-- One trusted shortcut: an exact block, the lowering that replaces it, and the tests that
compare that lowering with solc on the block. -/
structure TrustedShortcut where
  /-- Name of the `*YulFingerprint` constant, printed in import reports. -/
  fingerprintName : String
  /-- `yulBlockFingerprint` of the only block this entry replaces. -/
  fingerprint : String
  lowering : TrustedShortcutLowering
  /-- Repository paths of the tests that back the entry: tests of the lowering's results
  against values observed from solc on the block, and tests that the block, and only it, is
  selected (`TailAssemblyArrayReadChecks` backs selection and the report lines, not values). -/
  evidence : List String
  deriving Repr

/-- A trusted shortcut whose fingerprint matched the inline-assembly block `asm`. Only
`matchTrustedShortcut?` builds one, so a lowering that takes it is applied only to a block that
is exactly a registered one. -/
structure TrustedShortcutMatch where
  private mk ::
  shortcut : TrustedShortcut
  /-- The matched `InlineAssembly` node. -/
  asm : Json

/-- `j` without solc's source positions (`src`, `nativeSrc`), so that a fingerprint depends
only on the code. -/
partial def yulAstWithoutSrc : Json → Json
  | .obj kvs => Json.mkObj <| kvs.foldl (init := []) fun acc k v =>
      if k == "src" || k == "nativeSrc" then acc else acc ++ [(k, yulAstWithoutSrc v)]
  | .arr xs => .arr (xs.map yulAstWithoutSrc)
  | j => j

/-- Fingerprint of an `InlineAssembly` node: sha256 of its solc Yul AST (`AST`) without source
positions, as printed by `Json.compress` (keys sorted). Comments and layout do not count;
identifiers, literals and statement structure do. -/
def yulBlockFingerprint (asm : Json) : String :=
  sha256Hex (yulAstWithoutSrc ((asm.getObjVal? "AST").toOption.getD .null)).compress.toUTF8

/-- Whether `asm` (an `InlineAssembly` node) has at least one Solidity reference and every one
resolves to declaration `declId`. -/
def inlineAssemblyRefsOnlyDecl (asm : Json) (declId : Nat) : Bool :=
  match (asm.getObjVal? "externalReferences").toOption.bind (fun v => v.getArr?.toOption) with
  | some refs => !refs.isEmpty && refs.all fun ref =>
      ((ref.getObjVal? "declaration").toOption.bind (fun d => d.getNat?.toOption)) == some declId
  | none => false

/-- Whether some Solidity reference of `asm` (an `InlineAssembly` node) resolves to declaration
`declId`. -/
def inlineAssemblyRefsDecl (asm : Json) (declId : Nat) : Bool :=
  match (asm.getObjVal? "externalReferences").toOption.bind (fun v => v.getArr?.toOption) with
  | some refs => refs.any fun ref =>
      ((ref.getObjVal? "declaration").toOption.bind (fun d => d.getNat?.toOption)) == some declId
  | none => false

/-- Source positions of the Yul identifiers named `name` below `j` (uses and assignment targets). -/
partial def yulIdentifierSrcs (name : String) : Json → List String
  | .arr xs => xs.toList.flatMap (yulIdentifierSrcs name)
  | j@(.obj o) =>
      let own :=
        if (j.getObjValAs? String "nodeType").toOption == some "YulIdentifier" &&
            (j.getObjValAs? String "name").toOption == some name then
          (j.getObjValAs? String "src").toOption.toList
        else []
      o.foldl (fun acc _ v => acc ++ yulIdentifierSrcs name v) own
  | _ => []

/-- The Solidity declaration that every Yul identifier named `name` in `asm` (an
`InlineAssembly` node) resolves to through `externalReferences`. `none` if the name does not
occur, an occurrence has no external reference, or occurrences resolve to different
declarations. -/
def inlineAssemblyIdentDecl? (asm : Json) (name : String) : Option Nat :=
  let srcs := yulIdentifierSrcs name ((asm.getObjVal? "AST").toOption.getD .null)
  let refs := ((asm.getObjVal? "externalReferences").toOption.bind
    (fun v => v.getArr?.toOption)).getD #[]
  let declOf (src : String) : Option Nat :=
    (refs.toList.find? fun r => (r.getObjValAs? String "src").toOption == some src).bind
      fun r => (r.getObjVal? "declaration").toOption.bind (fun d => d.getNat?.toOption)
  match srcs.map declOf with
  | some d :: rest => if rest.all (· == some d) then some d else none
  | _ => none

/-- Whether every Solidity reference of `asm` (an `InlineAssembly` node) resolves to one of
`declIds`. -/
def inlineAssemblyRefsWithin (asm : Json) (declIds : List Nat) : Bool :=
  match (asm.getObjVal? "externalReferences").toOption.bind (fun v => v.getArr?.toOption) with
  | some refs => refs.all fun ref =>
      match (ref.getObjVal? "declaration").toOption.bind (fun d => d.getNat?.toOption) with
      | some d => declIds.contains d
      | none => false
  | none => true

/-- `yulBlockFingerprint` of the `assembly` block of `Extsload.extsload(bytes32 startSlot,
uint256 nSlots)` in `Uniswap/v4-core` `46c6834698c48bc4a463a86d8420f4eb1d7f3b75`
(`src/Extsload.sol`), the block of the `.rangeStorageRead` shortcut. It only selects the block
that `lowerBatchRangeSloadShim` replaces; it says nothing about whether that lowering agrees with
the block. -/
def extsloadRangeYulFingerprint : String :=
  "d9730e93af57142b904009c9e095ae86ca3d5b56703996afe94872b2ad280ebc"

/-- `yulBlockFingerprint` of the `assembly` block of `Extsload.extsload(bytes32[] calldata slots)`
in `Uniswap/v4-core` `46c6834698c48bc4a463a86d8420f4eb1d7f3b75` (`src/Extsload.sol`), the block of
the `.batchStorageRead` shortcut. Same value for solc 0.8.26 to 0.8.34. -/
def extsloadBatchYulFingerprint : String :=
  "be5cd0027ebaa78d230b732c81cebe4339c348553867668201b357cc758aae83"

/-- `yulBlockFingerprint` of the `assembly` block of `Exttload.exttload(bytes32[] calldata slots)`
in `Uniswap/v4-core` `46c6834698c48bc4a463a86d8420f4eb1d7f3b75` (`src/Exttload.sol`), the block of
the `.batchTransientRead` shortcut. -/
def exttloadBatchYulFingerprint : String :=
  "fde99fddf01f23a921eb50aadccf35541f1d93ab92ea966af76de65e839097f8"

/-- Record in the current root's report that its model replaces the block `m.asm` with the
lowering `lowering` (its declaration name) of the trusted shortcut `m.shortcut`. Every shortcut
lowering calls it. -/
private def recordShortcut (m : TrustedShortcutMatch) (lowering : Name) : M Unit := do
  let env ← get
  let (file, site) := nodeSite env m.asm
  let (line, column) := match site with
    | some (line, column, _) => (line, column)
    | none => (0, 0)
  let use : ShortcutUse :=
    { fingerprintName := m.shortcut.fingerprintName, fingerprint := m.shortcut.fingerprint,
      lowering := lowering.getString!, file, line, column }
  set { env with rootShortcuts := env.rootShortcuts.push use }

/-- Replace the matched block of `Exttload.exttload(bytes32[] calldata slots)` or
`Extsload.extsload(bytes32[] calldata slots)` (`m` is `.batchTransientRead` or
`.batchStorageRead`) with an ABI-encoded memory buffer loop and `SolidityReturnMemory.module`
transport, and record the shortcut. -/
def lowerBatchArrayLoadShim (m : TrustedShortcutMatch) (arr : ScalarArrayParam) : M (Array Stmt) := do
  let isTransient ← match m.shortcut.lowering with
    | .batchStorageRead => pure false
    | .batchTransientRead => pure true
    | other => throwError "lowerBatchArrayLoadShim: shortcut {m.shortcut.fingerprintName} selects {repr other}, not a batch read"
  recordShortcut m decl_name%
  let startVar ← fresh
  let finishVar ← fresh
  let loopIdx ← fresh
  let totalBytes := Expr.add (.literal 64) (.mul (.localVar arr.lengthBinding) (.literal 32))
  modify fun e =>
    { e with encodingMemory := true,
             usedRawStorage := e.usedRawStorage || !isTransient }
  let allocStmts := AbiEncoding.reserve startVar finishVar totalBytes
  let slotExpr := Expr.calldataload (.add (.localVar arr.dataBinding) (.mul (.localVar loopIdx) (.literal 32)))
  let loadedVal := if isTransient then Expr.tload slotExpr else Expr.storageArrayElement rawStorageFieldName slotExpr
  let destAddr := Expr.add (.add (.localVar startVar) (.literal 64)) (.mul (.localVar loopIdx) (.literal 32))
  return allocStmts.toArray ++ #[
    .mstore (.localVar startVar) (.literal 32),
    .mstore (.add (.localVar startVar) (.literal 32)) (.localVar arr.lengthBinding),
    .forEach loopIdx (.localVar arr.lengthBinding) [
      .mstore destAddr loadedVal
    ],
    .ecm Compiler.ECM.SolidityReturnMemory.module [.localVar startVar, totalBytes],
    .revertEmpty
  ]

/-- Replace the matched block of `Extsload.extsload(bytes32 startSlot, uint256 nSlots)` (`m` is
`.rangeStorageRead`) with an ABI-encoded memory buffer loop and `SolidityReturnMemory.module`
transport, and record the shortcut. `startSlotExpr` and `nSlotsExpr` are the values of the
block's `startSlot` and `nSlots`.

The block's byte length `shl(5, nSlots)` wraps, so it reads `m := nSlots mod 2^251` words and
returns `(0x40 + 32 * m) mod 2^256` bytes, keeping the full `nSlots` as the length word. When
`m` is `2^251 - 2` or `2^251 - 1` that is 0 or 32 bytes and no returned word is read. Gas is not
modeled: where the EVM runs out of gas (from about 7,600 cold reads under the Osaka 2^24
transaction gas cap), this lowering still returns the words, or reverts with `Panic(0x41)` from
`AbiEncoding.reserve` once the result exceeds the 2^64-byte memory bound. -/
def lowerBatchRangeSloadShim (m : TrustedShortcutMatch) (startSlotExpr nSlotsExpr : Expr) :
    M (Array Stmt) := do
  unless m.shortcut.lowering == .rangeStorageRead do
    throwError "lowerBatchRangeSloadShim: shortcut {m.shortcut.fingerprintName} selects {repr m.shortcut.lowering}, not the range read"
  recordShortcut m decl_name%
  let startVar ← fresh
  let finishVar ← fresh
  let loopIdx ← fresh
  let countVar ← fresh
  let count := Expr.localVar countVar
  let totalBytes := Expr.add (.literal 64) (.mul count (.literal 32))
  modify fun e => { e with encodingMemory := true, usedRawStorage := true }
  let allocStmts := AbiEncoding.reserve startVar finishVar totalBytes
  let slotExpr := Expr.add startSlotExpr (.localVar loopIdx)
  let loadedVal := Expr.storageArrayElement rawStorageFieldName slotExpr
  let destAddr := Expr.add (.add (.localVar startVar) (.literal 64)) (.mul (.localVar loopIdx) (.literal 32))
  return #[.letVar countVar (.mod nSlotsExpr (.literal (2 ^ 251)))] ++ allocStmts.toArray ++ #[
    .mstore (.localVar startVar) (.literal 32),
    .mstore (.add (.localVar startVar) (.literal 32)) nSlotsExpr,
    .ite (.lt count (.literal (2 ^ 251 - 2))) [
      .forEach loopIdx count [
        .mstore destAddr loadedVal
      ]
    ] [],
    .ecm Compiler.ECM.SolidityReturnMemory.module [.localVar startVar, totalBytes],
    .revertEmpty
  ]

/-- The trusted importer shortcuts: every block the importer replaces instead of translating.
Each `fingerprintName` is the name of the constant `fingerprint` reads, written as a quoted name
that must resolve when this file elaborates. -/
def trustedImporterShortcuts : List TrustedShortcut :=
  [ { fingerprintName := (``extsloadBatchYulFingerprint).getString!
      fingerprint := extsloadBatchYulFingerprint
      lowering := .batchStorageRead
      evidence := ["Contracts/SolidityImportSmoke/RootArrayReturnStateCountChecks.lean",
        "Contracts/SolidityImportSmoke/TailAssemblyArrayReadChecks.lean"] }
  , { fingerprintName := (``exttloadBatchYulFingerprint).getString!
      fingerprint := exttloadBatchYulFingerprint
      lowering := .batchTransientRead
      evidence := ["Contracts/SolidityImportSmoke/RootArrayReturnStateCountChecks.lean",
        "Contracts/SolidityImportSmoke/TailAssemblyArrayReadChecks.lean"] }
  , { fingerprintName := (``extsloadRangeYulFingerprint).getString!
      fingerprint := extsloadRangeYulFingerprint
      lowering := .rangeStorageRead
      evidence := ["Contracts/SolidityImportSmoke/TailAssemblyRangeReadChecks.lean",
        "Contracts/SolidityImportSmoke/RootArrayReturnStateCountChecks.lean"] }
  ]

/-- The trusted shortcut whose fingerprint is the `yulBlockFingerprint` of the `InlineAssembly`
node `asm`, if any. The only way to build a `TrustedShortcutMatch`. -/
def matchTrustedShortcut? (asm : Json) : Option TrustedShortcutMatch :=
  let fingerprint := yulBlockFingerprint asm
  (trustedImporterShortcuts.find? (·.fingerprint == fingerprint)).map fun shortcut =>
    TrustedShortcutMatch.mk shortcut asm

/-- A block matches at most one shortcut: the registered fingerprints are distinct. -/
theorem trustedImporterShortcuts_fingerprints_nodup :
    (trustedImporterShortcuts.map (·.fingerprint)).Nodup := by decide

end Compiler.CompilationModel.SolidityImport

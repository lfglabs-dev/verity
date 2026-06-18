import Compiler.CompilationModel
import Compiler.ABI
import Compiler.Codegen
import Compiler.Modules.Calls
import Compiler.Modules.Callbacks
import Compiler.Modules.ERC4626
import Compiler.Modules.ERC20
import Compiler.Modules.Hashing
import Compiler.Modules.Oracle
import Compiler.Modules.Precompiles
import Compiler.Yul.PrettyPrint
import Contracts.Common
import Contracts.Counter.Counter
import Contracts.LocalObligationMacroSmoke.LocalObligationMacroSmoke
import Contracts.ProxyUpgradeabilityMacroSmoke
import Contracts.Smoke
import Contracts.StringArrayErrorSmoke
import Contracts.StringArrayEventSmoke
import Verity.Core.Model.Denote
import Verity.Macro.Translate

-- The `unnecessarySeqFocus` linter recurses through every tactic block in the
-- file; on the very large smoke-test goals here it overflows the C stack
-- (SIGABRT 134 in `Batteries.Linter.UnnecessarySeqFocus.markUsedTacticsList`).
-- Disable it at file scope, matching the precedent in
-- `Compiler/Proofs/IRGeneration/GenericInduction.lean`.
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
-- The Batteries unreachable-tactic linter stack-overflows on this file's
-- size after the canonical-traversal validator port; it adds no value on a
-- pure smoke/regression module.
set_option linter.unreachableTactic false

namespace Compiler.CompilationModelFeatureTest

open Compiler
open Compiler.CompilationModel

namespace MacroLocalObligationSmoke

open Contracts

def constructorCarriesUncheckedObligation : Bool :=
  match LocalObligationMacroSmoke.spec.constructor with
  | some { localObligations := [{ name := "constructor_storage_layout"
                                  obligation := "Constructor storage aliasing must be checked separately across deployments."
                                  proofStatus := .unchecked }], .. } =>
      true
  | none => false
  | _ => false

example : constructorCarriesUncheckedObligation = true := by native_decide

def unsafeEdgeCarriesAssumedObligation : Bool :=
  match LocalObligationMacroSmoke.unsafeEdge_model with
  | { localObligations := [{ name := "manual_delegatecall_refinement"
                             obligation := "Caller must separately prove the handwritten assembly path refines the intended state transition."
                             proofStatus := .assumed }]
      body := [Stmt.stop], .. } => true
  | _ => false

example : unsafeEdgeCarriesAssumedObligation = true := by native_decide

def dischargedEdgeCarriesProvedObligation : Bool :=
  match LocalObligationMacroSmoke.dischargedEdge_model with
  | { localObligations := [{ name := "checked_patch_pack"
                             obligation := "Patch-pack proof already discharges this handwritten lowering boundary."
                             proofStatus := .proved }]
      body := [Stmt.setStorage "lastValue" (Expr.param "value"), Stmt.return (Expr.param "value")], .. } => true
  | _ => false

example : dischargedEdgeCarriesProvedObligation = true := by native_decide

def dischargedEdgeExecutableStillRuns : Bool :=
  match LocalObligationMacroSmoke.dischargedEdge 77 Verity.defaultState with
  | .success value state => value == 77 && state.storage 1 == 77
  | .revert _ _ => false

example : dischargedEdgeExecutableStillRuns = true := by native_decide

end MacroLocalObligationSmoke

namespace YulImporterSmoke

open Compiler.Yul

private def importedAssemblyStmt : Stmt :=
  YulImporter.importBlock {
    label := "sol_inline_assembly"
    sourceSpan := some {
      sourceName := "Contract.sol"
      startLine := 12
      startColumn := 8
      endLine := 18
      endColumn := 5
    }
    stmts := [
      YulStmt.let_ "ptr" (YulExpr.call "mload" [YulExpr.lit 64]),
      YulStmt.assign "ptr" (YulExpr.call "add" [YulExpr.ident "ptr", YulExpr.lit 32]),
      YulStmt.expr (YulExpr.call "mstore" [YulExpr.ident "ptr", YulExpr.lit 1]),
      YulStmt.expr (YulExpr.call "sstore" [YulExpr.lit 0, YulExpr.lit 1]),
      YulStmt.expr (YulExpr.call "revert" [YulExpr.ident "ptr", YulExpr.lit 32])
    ]
  }

def importedAssemblyCarriesDerivedMetadata : Bool :=
  match importedAssemblyStmt with
  | Stmt.unsafeYul fragment =>
      fragment.label == "sol_inline_assembly" &&
      (match fragment.obligations with
       | [{ name := "sol_inline_assembly"
            obligation := "Imported Solidity inline assembly at Contract.sol:12:8-18:5 block 'sol_inline_assembly' must refine the declared Verity state transition."
            proofStatus := .assumed }] => true
       | _ => false) &&
      fragment.mechanics.contains .mload &&
      fragment.mechanics.contains .mstore &&
      fragment.mechanics.contains .storageWrite &&
      fragment.mechanics.contains .rawRevert &&
      fragment.scopeEffects.bindNames == ["ptr"] &&
      fragment.scopeEffects.assignNames == ["ptr"] &&
      !fragment.scopeEffects.storageWrites.isEmpty &&
      fragment.controlFlow == .reverts
  | _ => false

example : importedAssemblyCarriesDerivedMetadata = true := by native_decide

def importedAssemblyPassesUnsafeYulValidation : Bool :=
  let spec : FunctionSpec := {
    name := "usesImportedAssembly"
    params := []
    returnType := none
    body := [importedAssemblyStmt, Stmt.stop]
  }
  match validateFunctionSpec spec with
  | .ok _ => true
  | .error _ => false

example : importedAssemblyPassesUnsafeYulValidation = true := by native_decide

end YulImporterSmoke

namespace MacroProxyUpgradeabilitySmoke

open Contracts

def initProxyCarriesInitializerObligation : Bool :=
  match ProxyUpgradeabilityMacroSmoke.initProxy_model with
  | { localObligations := [{ name := "implementation_slot_discipline"
                             obligation := "Proxy storage-slot discipline must be validated against the intended implementation layout."
                             proofStatus := .assumed }]
      body := [Stmt.require (Expr.eq (Expr.storage "initializedVersion") (Expr.literal 0)) "initializer already run",
               Stmt.setStorage "initializedVersion" (Expr.literal 1),
               Stmt.setStorageAddr "admin" (Expr.param "seedAdmin"),
               Stmt.setStorageAddr "implementation" (Expr.param "seedImplementation"),
               Stmt.stop], .. } => true
  | _ => false

example : initProxyCarriesInitializerObligation = true := by native_decide

def upgradeToCarriesUpgradeObligations : Bool :=
  match ProxyUpgradeabilityMacroSmoke.upgradeTo_model with
  | { localObligations := [{ name := "upgrade_authorization"
                             obligation := "Caller must separately prove that only the intended admin can authorize upgrades."
                             proofStatus := .assumed },
                           { name := "storage_layout_compatibility"
                             obligation := "Storage-layout compatibility across versions remains a manual proof obligation."
                             proofStatus := .unchecked }]
      body := [Stmt.require (Expr.lt (Expr.storage "initializedVersion") (Expr.literal 2)) "reinitializer(2) already run",
               Stmt.setStorage "initializedVersion" (Expr.literal 2),
               Stmt.setStorageAddr "implementation" (Expr.param "newImplementation"),
               Stmt.stop], .. } => true
  | _ => false

example : upgradeToCarriesUpgradeObligations = true := by native_decide

def forwardCarriesProxyBoundary : Bool :=
  match ProxyUpgradeabilityMacroSmoke.forward_model with
  | { localObligations := [{ name := "delegatecall_refinement"
                             obligation := "Delegatecall fallback behavior must be shown to refine the selected proxy semantics."
                             proofStatus := .assumed }]
      body := body, .. } =>
      body.length == 3
  | _ => false

example : forwardCarriesProxyBoundary = true := by native_decide

def forwardExecutableReadsImplementation : Bool :=
  let seededState :=
    (ProxyUpgradeabilityMacroSmoke.initProxy (Verity.wordToAddress 11) (Verity.wordToAddress 19)).run Verity.defaultState
  match seededState with
  | .success _ state =>
      match ProxyUpgradeabilityMacroSmoke.forward 100 0 32 64 32 state with
      | .success ok nextState =>
          ok == delegatecall 100 19 0 32 64 32 &&
            nextState.storage ProxyUpgradeabilityMacroSmoke.initializedVersion.slot == 1 &&
            nextState.storageAddr ProxyUpgradeabilityMacroSmoke.admin.slot == Verity.wordToAddress 11 &&
            nextState.storageAddr ProxyUpgradeabilityMacroSmoke.implementation.slot == Verity.wordToAddress 19
      | .revert _ _ => false
  | .revert _ _ => false

example : forwardExecutableReadsImplementation = true := by native_decide

end MacroProxyUpgradeabilitySmoke

namespace CounterUnsafeBoundarySmoke

open Contracts

def previewEnvOpsCarriesBoundaryObligation : Bool :=
  match Counter.previewEnvOps_model with
  | { localObligations := [{ name := "env_memory_refinement"
                             obligation := "Caller must separately prove the direct mload-based environment digest path respects the intended memory/refinement boundary."
                             proofStatus := .assumed }]
      body := _, .. } => true
  | _ => false

example : previewEnvOpsCarriesBoundaryObligation = true := by native_decide

def previewLowLevelCarriesBoundaryObligation : Bool :=
  match Counter.previewLowLevel_model with
  | { localObligations := [{ name := "manual_low_level_refinement"
                             obligation := "Caller must separately prove the direct low-level call and returndata choreography refines the intended external-call behavior."
                             proofStatus := .assumed }]
      body := _, .. } => true
  | _ => false

example : previewLowLevelCarriesBoundaryObligation = true := by native_decide

end CounterUnsafeBoundarySmoke

namespace MacroEcrecoverSmoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256

verity_contract MacroEcrecover where
  storage
    lastSigner : Address := slot 0

  function recoverSigner (digest : Bytes32, v : Uint256, r : Bytes32, s : Bytes32) : Address := do
    let signer ← ecrecover digest v r s
    return signer

def recoverSignerModelUsesEcrecoverEcm : Bool :=
  match MacroEcrecover.recoverSigner_modelBody with
  | [Stmt.ecm mod [Expr.param "digest", Expr.param "v", Expr.param "r", Expr.param "s"],
      Stmt.return (Expr.localVar "signer")] =>
      mod.name == "ecrecover" &&
      mod.resultVars == ["signer"] &&
      mod.axioms == ["evm_ecrecover_precompile"]
  | _ => false

example : recoverSignerModelUsesEcrecoverEcm = true := by native_decide

def recoverSignerExecutableUsesOracle : Bool :=
  match MacroEcrecover.recoverSigner 10 27 30 40 Verity.defaultState with
  | .success signer state =>
      signer == Verity.wordToAddress 107 && state.sender == Verity.defaultState.sender
  | .revert _ _ => false

example : recoverSignerExecutableUsesOracle = true := by native_decide

end MacroEcrecoverSmoke

namespace MacroKeccakSmoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256

verity_contract MacroKeccak where
  storage
    lastDigest : Uint256 := slot 0

  function hashSlice (offset : Uint256, size : Uint256) : Uint256 := do
    let digest := keccak256 offset size
    return digest

def hashSliceModelUsesKeccak : Bool :=
  match MacroKeccak.hashSlice_modelBody with
  | [Stmt.letVar "digest" (Expr.keccak256 (Expr.param "offset") (Expr.param "size")),
      Stmt.return (Expr.localVar "digest")] =>
      true
  | _ => false

example : hashSliceModelUsesKeccak = true := by native_decide

def hashSliceExecutableUsesRuntimeStub : Bool :=
  match MacroKeccak.hashSlice 11 64 Verity.defaultState with
  | .success digest state =>
      digest == 75 && state.sender == Verity.defaultState.sender
  | .revert _ _ => false

example : hashSliceExecutableUsesRuntimeStub = true := by native_decide

end MacroKeccakSmoke

namespace MappingWordSmoke

open Contracts.Smoke

example :
    MappingWordSmoke.setWord1_modelBody =
      [ Stmt.setMappingWord "words" (Expr.param "key") 1 (Expr.param "value"),
        Stmt.stop ] := rfl

example :
    MappingWordSmoke.getWord1_modelBody =
      [ Stmt.letVar "word" (Expr.mappingWord "words" (Expr.param "key") 1),
        Stmt.return (Expr.localVar "word") ] := rfl

example :
    MappingWordSmoke.isWord1NonZero_modelBody =
      [ Stmt.letVar "word" (Expr.mappingWord "words" (Expr.param "key") 1),
        Stmt.return (Expr.logicalNot (Expr.eq (Expr.localVar "word") (Expr.literal 0))) ] := rfl

end MappingWordSmoke

namespace MacroExternalSmoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256

verity_contract MacroExternal where
  storage
    echoedValue : Uint256 := slot 0
  linked_externals
    external echo(Uint256) -> (Uint256)

  function allow_post_interaction_writes reentrancy_trusted storeEcho (next : Uint256) : Unit := do
    let echoed := externalCall "echo" [next]
    setStorage echoedValue echoed

def storeEchoModelUsesDeclaredExternal : Bool :=
  (match MacroExternal.spec.externals with
    | [{ name := "echo"
         params := [ParamType.uint256]
         returnType := some ParamType.uint256
         returns := [ParamType.uint256]
         proofStatus := Compiler.ProofStatus.assumed
         axiomNames := []
         linkMode := Compiler.CompilationModel.ForeignLinkMode.objectLinked }] => true
    | _ => false) &&
    match MacroExternal.storeEcho_modelBody with
    | [Stmt.letVar "echoed" (Expr.externalCall "echo" [Expr.param "next"]),
        Stmt.setStorage "echoedValue" (Expr.localVar "echoed"),
        Stmt.stop] => true
    | _ => false

example : storeEchoModelUsesDeclaredExternal = true := by native_decide

def storeEchoExecutableUsesStub : Bool :=
  match MacroExternal.storeEcho 33 Verity.defaultState with
  | .success () state =>
      state.storage 0 == 33
  | .revert _ _ => false

example : storeEchoExecutableUsesStub = true := by native_decide

end MacroExternalSmoke

namespace MacroExternalLinkModeSmoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256

verity_contract MacroExternalLinkModes where
  storage
    value : Uint256 := slot 0
  linked_externals
    external oracleEcho(Uint256) -> (Uint256) linked_as := external
    external poseidonHash(Uint256, Uint256) -> (Uint256) linked_as := internal_yul
    external inlineAdd(Uint256, Uint256) -> (Uint256) linked_as := inline
    external abiRuntime(Uint256) -> (Uint256) linked_as := compiler_runtime

def parsedExternalLinkModes : Bool :=
  MacroExternalLinkModes.spec.externals.map (fun ext => (ext.name, ext.linkMode.toJsonString)) =
    [ ("oracleEcho", "external")
    , ("poseidonHash", "objectLinked")
    , ("inlineAdd", "inline")
    , ("abiRuntime", "compilerRuntime")
    ]

example : parsedExternalLinkModes = true := by native_decide

def linkModeTrustSurfaceSpec : CompilationModel := {
  name := "LinkModeTrustSurface"
  fields := []
  «constructor» := none
  externals := [
    { name := "oracleEcho"
      params := [ParamType.uint256]
      returnType := some ParamType.uint256
      returns := [ParamType.uint256]
      axiomNames := []
      linkMode := .external },
    { name := "poseidonHash"
      params := [ParamType.uint256, ParamType.uint256]
      returnType := some ParamType.uint256
      returns := [ParamType.uint256]
      axiomNames := []
      linkMode := .objectLinked },
    { name := "inlineAdd"
      params := [ParamType.uint256, ParamType.uint256]
      returnType := some ParamType.uint256
      returns := [ParamType.uint256]
      axiomNames := []
      linkMode := .inline },
    { name := "abiRuntime"
      params := [ParamType.uint256]
      returnType := some ParamType.uint256
      returns := [ParamType.uint256]
      axiomNames := []
      linkMode := .compilerRuntime }
  ]
  functions := [
    { name := "exercise"
      params := [{ name := "next", ty := ParamType.uint256 }]
      returnType := some FieldType.uint256
      reentrancyTrusted := true
      body := [
        Stmt.letVar "a" (Expr.externalCall "oracleEcho" [Expr.param "next"]),
        Stmt.letVar "b" (Expr.externalCall "poseidonHash" [Expr.param "next", Expr.param "next"]),
        Stmt.letVar "c" (Expr.externalCall "inlineAdd" [Expr.localVar "b", Expr.param "next"]),
        Stmt.letVar "d" (Expr.externalCall "abiRuntime" [Expr.localVar "c"]),
        Stmt.return (Expr.localVar "d")
      ]
    }
  ]
}

def externalModeRawCallSpec : CompilationModel := {
  name := "ExternalModeRawCall"
  fields := []
  «constructor» := none
  externals := [
    { name := "oracleEcho"
      params := [ParamType.uint256]
      returnType := some ParamType.uint256
      returns := [ParamType.uint256]
      axiomNames := []
      linkMode := .external }
  ]
  functions := [
    { name := "bad"
      params := [{ name := "next", ty := ParamType.uint256 }]
      returnType := some FieldType.uint256
      body := [Stmt.return (Expr.externalCall "oracleEcho" [Expr.param "next"])]
    }
  ]
}

end MacroExternalLinkModeSmoke

namespace DynamicBytesEqUsageAnalysisSmoke

def rawLogDynamicBytesEqIsDetected : Bool :=
  stmtUsesDynamicBytesEq
    (Stmt.rawLog
      [Expr.dynamicBytesEq "lhs" "rhs"]
      (Expr.literal 0)
      (Expr.literal 32))

example : rawLogDynamicBytesEqIsDetected = true := by native_decide

end DynamicBytesEqUsageAnalysisSmoke

namespace MacroERC20Smoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256

verity_contract MacroERC20 where
  storage
    lastBalance : Uint256 := slot 0
    lastAllowance : Uint256 := slot 1
    lastSupply : Uint256 := slot 2

  function pushTokens (token : Address, toAddr : Address, amount : Uint256) : Unit := do
    safeTransfer token toAddr amount

  function pullTokens (token : Address, fromAddr : Address, toAddr : Address, amount : Uint256) : Unit := do
    safeTransferFrom token fromAddr toAddr amount

  function approveTokens (token : Address, spender : Address, amount : Uint256) : Unit := do
    safeApprove token spender amount

  function snapshotBalance (token : Address, owner : Address) : Uint256 := do
    let balance ← balanceOf token owner
    setStorage lastBalance balance
    return balance

  function snapshotAllowance (token : Address, owner : Address, spender : Address) : Uint256 := do
    let current ← allowance token owner spender
    setStorage lastAllowance current
    return current

  function snapshotSupply (token : Address) : Uint256 := do
    let supply ← totalSupply token
    setStorage lastSupply supply
    return supply

def pushTokensModelUsesSafeTransfer : Bool :=
  match MacroERC20.pushTokens_modelBody with
  | [Stmt.ecm mod [Expr.param "token", Expr.param "toAddr", Expr.param "amount"], Stmt.stop] =>
      mod.name == "safeTransfer" &&
      mod.resultVars.isEmpty &&
      mod.axioms == ["erc20_transfer_interface"]
  | _ => false

example : pushTokensModelUsesSafeTransfer = true := by native_decide

def pullTokensModelUsesSafeTransferFrom : Bool :=
  match MacroERC20.pullTokens_modelBody with
  | [Stmt.ecm mod [Expr.param "token", Expr.param "fromAddr", Expr.param "toAddr", Expr.param "amount"], Stmt.stop] =>
      mod.name == "safeTransferFrom" &&
      mod.resultVars.isEmpty &&
      mod.axioms == ["erc20_transferFrom_interface"]
  | _ => false

example : pullTokensModelUsesSafeTransferFrom = true := by native_decide

def approveTokensModelUsesSafeApprove : Bool :=
  match MacroERC20.approveTokens_modelBody with
  | [Stmt.ecm mod [Expr.param "token", Expr.param "spender", Expr.param "amount"], Stmt.stop] =>
      mod.name == "safeApprove" &&
      mod.resultVars.isEmpty &&
      mod.axioms == ["erc20_approve_interface"]
  | _ => false

example : approveTokensModelUsesSafeApprove = true := by native_decide

def snapshotBalanceModelUsesBalanceOfModule : Bool :=
  match MacroERC20.snapshotBalance_modelBody with
  | [Stmt.ecm mod [Expr.param "token", Expr.param "owner"],
      Stmt.setStorage "lastBalance" (Expr.localVar "balance"),
      Stmt.return (Expr.localVar "balance")] =>
      mod.name == "balanceOf" &&
      mod.resultVars == ["balance"] &&
      mod.axioms == ["erc20_balanceOf_interface"]
  | _ => false

example : snapshotBalanceModelUsesBalanceOfModule = true := by native_decide

def snapshotAllowanceModelUsesAllowanceModule : Bool :=
  match MacroERC20.snapshotAllowance_modelBody with
  | [Stmt.ecm mod [Expr.param "token", Expr.param "owner", Expr.param "spender"],
      Stmt.setStorage "lastAllowance" (Expr.localVar "current"),
      Stmt.return (Expr.localVar "current")] =>
      mod.name == "allowance" &&
      mod.resultVars == ["current"] &&
      mod.axioms == ["erc20_allowance_interface"]
  | _ => false

example : snapshotAllowanceModelUsesAllowanceModule = true := by native_decide

def snapshotSupplyModelUsesTotalSupplyModule : Bool :=
  match MacroERC20.snapshotSupply_modelBody with
  | [Stmt.ecm mod [Expr.param "token"],
      Stmt.setStorage "lastSupply" (Expr.localVar "supply"),
      Stmt.return (Expr.localVar "supply")] =>
      mod.name == "totalSupply" &&
      mod.resultVars == ["supply"] &&
      mod.axioms == ["erc20_totalSupply_interface"]
  | _ => false

example : snapshotSupplyModelUsesTotalSupplyModule = true := by native_decide

def snapshotBalanceExecutableUsesStub : Bool :=
  let token := Verity.wordToAddress 7
  let owner := Verity.wordToAddress 13
  match Contracts.balanceOf token owner Verity.defaultState,
      MacroERC20.snapshotBalance token owner Verity.defaultState with
  | .success expected _, .success balance state =>
      balance == expected &&
      state.storage 0 == expected &&
      state.storage 1 == 0
  | .revert _ _, _ => false
  | _, .revert _ _ => false

example : snapshotBalanceExecutableUsesStub = true := by native_decide

def snapshotAllowanceExecutableUsesStub : Bool :=
  let token := Verity.wordToAddress 7
  let owner := Verity.wordToAddress 13
  let spender := Verity.wordToAddress 17
  match Contracts.allowance token owner spender Verity.defaultState,
      MacroERC20.snapshotAllowance token owner spender Verity.defaultState with
  | .success expected _, .success current state =>
      current == expected &&
      state.storage 1 == expected &&
      state.storage 0 == 0
  | .revert _ _, _ => false
  | _, .revert _ _ => false

example : snapshotAllowanceExecutableUsesStub = true := by native_decide

def snapshotSupplyExecutableUsesStub : Bool :=
  let token := Verity.wordToAddress 7
  match Contracts.totalSupply token Verity.defaultState,
      MacroERC20.snapshotSupply token Verity.defaultState with
  | .success expected _, .success supply state =>
      supply == expected &&
      state.storage 2 == expected
  | .revert _ _, _ => false
  | _, .revert _ _ => false

example : snapshotSupplyExecutableUsesStub = true := by native_decide

end MacroERC20Smoke

namespace MacroTransientStorageSmoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256

verity_contract MacroTransientStorage where
  storage

  function warm (key : Uint256, value : Uint256)
    local_obligations [transient_storage_refinement := assumed "Caller must separately prove the direct transient-storage choreography refines the intended warm-slot behavior."]
    : Uint256 := do
    tstore key value
    let current := tload key
    return current

  function peek (key : Uint256)
    local_obligations [transient_storage_read_refinement := assumed "Caller must separately prove the direct transient-storage read refines the intended peek behavior."]
    : Uint256 := do
    let current := tload key
    return current

def warmModelUsesTransientStorage : Bool :=
  match MacroTransientStorage.warm_modelBody with
  | [Stmt.tstore (Expr.param "key") (Expr.param "value"),
      Stmt.letVar "current" (Expr.tload (Expr.param "key")),
      Stmt.return (Expr.localVar "current")] =>
      true
  | _ => false

example : warmModelUsesTransientStorage = true := by native_decide

def warmCarriesTransientStorageObligation : Bool :=
  match MacroTransientStorage.warm_model with
  | { localObligations := [{ name := "transient_storage_refinement"
                             obligation := "Caller must separately prove the direct transient-storage choreography refines the intended warm-slot behavior."
                             proofStatus := .assumed }]
      body := _, .. } => true
  | _ => false

example : warmCarriesTransientStorageObligation = true := by native_decide

def peekModelUsesTransientStorage : Bool :=
  match MacroTransientStorage.peek_modelBody with
  | [Stmt.letVar "current" (Expr.tload (Expr.param "key")),
      Stmt.return (Expr.localVar "current")] =>
      true
  | _ => false

example : peekModelUsesTransientStorage = true := by native_decide

def peekCarriesTransientStorageObligation : Bool :=
  match MacroTransientStorage.peek_model with
  | { localObligations := [{ name := "transient_storage_read_refinement"
                             obligation := "Caller must separately prove the direct transient-storage read refines the intended peek behavior."
                             proofStatus := .assumed }]
      body := _, .. } => true
  | _ => false

example : peekCarriesTransientStorageObligation = true := by native_decide

def warmExecutableWritesTransientStorage : Bool :=
  match MacroTransientStorage.warm 7 99 Verity.defaultState with
  | .success current state =>
      current == 99 &&
      state.transientStorage 7 == 99 &&
      state.storage 7 == 0
  | .revert _ _ => false

example : warmExecutableWritesTransientStorage = true := by native_decide

def transientStoragePersistsAcrossExecutableCalls : Bool :=
  match MacroTransientStorage.warm 7 99 Verity.defaultState with
  | .success _ warmedState =>
      match MacroTransientStorage.peek 7 warmedState with
      | .success current finalState =>
          current == 99 &&
          finalState.transientStorage 7 == 99
      | .revert _ _ => false
  | .revert _ _ => false

example : transientStoragePersistsAcrossExecutableCalls = true := by native_decide

end MacroTransientStorageSmoke

namespace MacroBlobbasefeeSmoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256

verity_contract MacroBlobbasefee where
  storage

  function currentBlobBaseFee () : Uint256 := do
    let fee ← blobbasefee
    return fee

  function qualifiedCurrentBlobBaseFee () : Uint256 := do
    let fee ← Verity.blobbasefee
    return fee

def modelReturnsBlobbasefeeBuiltin : Bool :=
  match MacroBlobbasefee.currentBlobBaseFee_modelBody with
  | [Stmt.letVar "fee" Expr.blobbasefee, Stmt.return (Expr.localVar "fee")] => true
  | _ => false

example : modelReturnsBlobbasefeeBuiltin = true := by native_decide

def qualifiedModelReturnsBlobbasefeeBuiltin : Bool :=
  match MacroBlobbasefee.qualifiedCurrentBlobBaseFee_modelBody with
  | [Stmt.letVar "fee" Expr.blobbasefee, Stmt.return (Expr.localVar "fee")] => true
  | _ => false

example : qualifiedModelReturnsBlobbasefeeBuiltin = true := by native_decide

def executableUsesContractState : Bool :=
  match MacroBlobbasefee.currentBlobBaseFee { Verity.defaultState with blobBaseFee := 19 } with
  | .success fee state =>
      fee == 19 && state.sender == Verity.defaultState.sender
  | .revert _ _ => false

example : executableUsesContractState = true := by native_decide

end MacroBlobbasefeeSmoke

namespace MacroConstantSmoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256

verity_contract MacroConstant where
  storage
    storedFee : Uint256 := slot 0

  constants
    basisPoints : Uint256 := 10000
    mintFeeBps : Uint256 := 30
    treasury : Address := (wordToAddress 42)
    treasuryWord : Uint256 := (addressToWord treasury)

  function feeOn (amount : Uint256) : Uint256 := do
    let fee := div (mul amount mintFeeBps) basisPoints
    return fee

  function treasuryAddr () : Address := do
    return treasury

  function treasuryAsWord () : Uint256 := do
    return treasuryWord

  function shadowedConstant (mintFeeBps : Uint256) : Uint256 := do
    let treasuryWord := 9
    return (add mintFeeBps treasuryWord)

def feeOnModelInlinesContractConstants : Bool :=
  match MacroConstant.feeOn_modelBody with
  | [Stmt.letVar "fee"
        (Expr.div
          (Expr.mul (Expr.param "amount") (Expr.literal 30))
          (Expr.literal 10000)),
      Stmt.return (Expr.localVar "fee")] =>
      true
  | _ => false

example : feeOnModelInlinesContractConstants = true := by native_decide

def uint256PowSmokeLowersToBuiltinExp : Bool :=
  match Contracts.Smoke.Uint256PowSmoke.scale_modelBody with
  | [Stmt.letVar "exponent" (Expr.sub (Expr.literal 18) (Expr.param "decimals")),
      Stmt.return (Expr.externalCall name [Expr.literal 10, Expr.localVar "exponent"])] =>
      name == builtinExpName
  | _ => false

example : uint256PowSmokeLowersToBuiltinExp = true := by native_decide

def uint256PowInfixLowersToBuiltinExp : Bool :=
  match Contracts.Smoke.Uint256PowSmoke.scaleInfix_modelBody with
  | [Stmt.letVar "exponent" (Expr.sub (Expr.literal 18) (Expr.param "decimals")),
      Stmt.return (Expr.externalCall name [Expr.literal 10, Expr.localVar "exponent"])] =>
      name == builtinExpName
  | _ => false

example : uint256PowInfixLowersToBuiltinExp = true := by native_decide

def uint256PowBuiltinCompilesToYulExp : Bool :=
  match compileExpr [] .calldata
      (Expr.externalCall builtinExpName [Expr.param "base", Expr.param "exponent"]) with
  | .ok (Compiler.Yul.YulExpr.call "exp"
      [Compiler.Yul.YulExpr.ident "base", Compiler.Yul.YulExpr.ident "exponent"]) => true
  | _ => false

example : uint256PowBuiltinCompilesToYulExp = true := by native_decide

def uint256PowBuiltinIsNotAnExternalInteraction : Bool :=
  let expr := Expr.externalCall builtinExpName [Expr.literal 10, Expr.param "exponent"]
  !exprReadsStateOrEnv expr &&
    !exprWritesState expr &&
    !exprContainsCallLike expr &&
    !exprContainsExternalCall expr &&
    !exprMayContainExternalCall expr

example : uint256PowBuiltinIsNotAnExternalInteraction = true := by native_decide

def treasuryAddrModelInlinesAddressConstant : Bool :=
  match MacroConstant.treasuryAddr_modelBody with
  | [Stmt.return (Expr.literal 42)] =>
      true
  | _ => false

example : treasuryAddrModelInlinesAddressConstant = true := by native_decide

def treasuryAsWordModelInlinesNestedConstants : Bool :=
  match MacroConstant.treasuryAsWord_modelBody with
  | [Stmt.return (Expr.literal 42)] =>
      true
  | _ => false

example : treasuryAsWordModelInlinesNestedConstants = true := by native_decide

def shadowedConstantModelPrefersLocalAndParamBindings : Bool :=
  match MacroConstant.shadowedConstant_modelBody with
  | [Stmt.letVar "treasuryWord" (Expr.literal 9),
      Stmt.return (Expr.add (Expr.param "mintFeeBps") (Expr.localVar "treasuryWord"))] =>
      true
  | _ => false

example : shadowedConstantModelPrefersLocalAndParamBindings = true := by native_decide

def treasuryExecutableUsesGeneratedConstantDef : Bool :=
  match MacroConstant.treasuryAddr Verity.defaultState with
  | .success treasury state =>
      treasury == Verity.wordToAddress 42 &&
      state.sender == Verity.defaultState.sender
  | .revert _ _ => false

example : treasuryExecutableUsesGeneratedConstantDef = true := by native_decide

end MacroConstantSmoke

namespace MacroTupleDestructuringSmoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256

verity_contract MacroTupleDestructuring where
  storage
    firstSlot : Uint256 := slot 0
    secondSlot : Uint256 := slot 1

  function helperPair (seed : Uint256) : Tuple [Uint256, Uint256] := do
    return (seed, add seed 1)

  function storePair (pair : Tuple [Uint256, Uint256]) : Unit := do
    let (first, second) := pair
    setStorage firstSlot first
    setStorage secondSlot second

  function storePairTail (pair : Tuple [Uint256, Uint256]) : Unit := do
    let (_, second) := pair
    setStorage secondSlot second

  function storeLiteralPair (seed : Uint256) : Unit := do
    let (first, second) := (seed, add seed 1)
    setStorage firstSlot first
    setStorage secondSlot second

  function echoPair (pair : Tuple [Uint256, Uint256]) : Tuple [Uint256, Uint256] := do
    let (first, second) := pair
    return (first, second)

  function storeHelperPair (seed : Uint256) : Unit := do
    let (first, second) ← helperPair seed
    setStorage firstSlot first
    setStorage secondSlot second

  function storeHelperPairEq (seed : Uint256) : Unit := do
    let (first, second) := helperPair seed
    setStorage firstSlot first
    setStorage secondSlot second

  function storeHelperPairTail (seed : Uint256) : Unit := do
    let (_, second) := helperPair seed
    setStorage secondSlot second

  function storeHelperPairTailNameCollision («__tuple_discard_0» : Uint256, seed : Uint256) : Unit := do
    let (_, second) := helperPair seed
    setStorage firstSlot «__tuple_discard_0»
    setStorage secondSlot second

def storePairModelDestructuresTupleParam : Bool :=
  match MacroTupleDestructuring.storePair_modelBody with
  | [Stmt.letVar "first" (Expr.param "pair_0"),
      Stmt.letVar "second" (Expr.param "pair_1"),
      Stmt.setStorage "firstSlot" (Expr.localVar "first"),
      Stmt.setStorage "secondSlot" (Expr.localVar "second"),
      Stmt.stop] =>
      true
  | _ => false

example : storePairModelDestructuresTupleParam = true := by native_decide

def storePairTailModelSkipsDiscardedBinder : Bool :=
  match MacroTupleDestructuring.storePairTail_modelBody with
  | [Stmt.letVar "second" (Expr.param "pair_1"),
      Stmt.setStorage "secondSlot" (Expr.localVar "second"),
      Stmt.stop] =>
      true
  | _ => false

example : storePairTailModelSkipsDiscardedBinder = true := by native_decide

def helperPairModelReturnsMultipleWords : Bool :=
  match MacroTupleDestructuring.helperPair_modelBody with
  | [Stmt.returnValues [Expr.param "seed", Expr.add (Expr.param "seed") (Expr.literal 1)]] =>
      true
  | _ => false

example : helperPairModelReturnsMultipleWords = true := by native_decide

def storeLiteralPairModelDestructuresTupleExpr : Bool :=
  match MacroTupleDestructuring.storeLiteralPair_modelBody with
  | [Stmt.letVar "first" (Expr.param "seed"),
      Stmt.letVar "second" (Expr.add (Expr.param "seed") (Expr.literal 1)),
      Stmt.setStorage "firstSlot" (Expr.localVar "first"),
      Stmt.setStorage "secondSlot" (Expr.localVar "second"),
      Stmt.stop] =>
      true
  | _ => false

example : storeLiteralPairModelDestructuresTupleExpr = true := by native_decide

def echoPairModelReturnsMultipleWords : Bool :=
  match MacroTupleDestructuring.echoPair_modelBody with
  | [Stmt.letVar "first" (Expr.param "pair_0"),
      Stmt.letVar "second" (Expr.param "pair_1"),
      Stmt.returnValues [Expr.localVar "first", Expr.localVar "second"]] =>
      true
  | _ => false

example : echoPairModelReturnsMultipleWords = true := by native_decide

private def helperPairInternalModelName : String := "internal_helperPair"

def storeHelperPairModelUsesInternalCallAssign : Bool :=
  match MacroTupleDestructuring.storeHelperPair_modelBody with
  | [Stmt.internalCallAssign ["first", "second"] helperName [Expr.param "seed"],
      Stmt.setStorage "firstSlot" (Expr.localVar "first"),
      Stmt.setStorage "secondSlot" (Expr.localVar "second"),
      Stmt.stop] =>
      helperName == helperPairInternalModelName
  | _ => false

example : storeHelperPairModelUsesInternalCallAssign = true := by native_decide

def storeHelperPairEqModelUsesInternalCallAssign : Bool :=
  match MacroTupleDestructuring.storeHelperPairEq_modelBody with
  | [Stmt.internalCallAssign ["first", "second"] helperName [Expr.param "seed"],
      Stmt.setStorage "firstSlot" (Expr.localVar "first"),
      Stmt.setStorage "secondSlot" (Expr.localVar "second"),
      Stmt.stop] =>
      helperName == helperPairInternalModelName
  | _ => false

example : storeHelperPairEqModelUsesInternalCallAssign = true := by native_decide

def storeHelperPairTailModelUsesHiddenDiscardTarget : Bool :=
  match MacroTupleDestructuring.storeHelperPairTail_modelBody with
  | [Stmt.internalCallAssign ["__tuple_discard_0", "second"] helperName [Expr.param "seed"],
      Stmt.setStorage "secondSlot" (Expr.localVar "second"),
      Stmt.stop] =>
      helperName == helperPairInternalModelName
  | _ => false

example : storeHelperPairTailModelUsesHiddenDiscardTarget = true := by native_decide

def storeHelperPairTailNameCollisionModelUsesFreshDiscardTarget : Bool :=
  match MacroTupleDestructuring.storeHelperPairTailNameCollision_modelBody with
  | [Stmt.internalCallAssign ["__tuple_discard_0_1", "second"] helperName [Expr.param "seed"],
      Stmt.setStorage "firstSlot" (Expr.param "__tuple_discard_0"),
      Stmt.setStorage "secondSlot" (Expr.localVar "second"),
      Stmt.stop] =>
      helperName == helperPairInternalModelName
  | _ => false

example : storeHelperPairTailNameCollisionModelUsesFreshDiscardTarget = true := by native_decide

def echoPairExecutableKeepsTupleShape : Bool :=
  match MacroTupleDestructuring.echoPair (11, 17) Verity.defaultState with
  | .success (first, second) state =>
      first == 11 && second == 17 && state.sender == Verity.defaultState.sender
  | .revert _ _ => false

example : echoPairExecutableKeepsTupleShape = true := by native_decide

def storeHelperPairExecutableStoresHelperResults : Bool :=
  match MacroTupleDestructuring.storeHelperPair 11 Verity.defaultState with
  | .success () state =>
      state.storage 0 == 11 && state.storage 1 == 12
  | .revert _ _ => false

example : storeHelperPairExecutableStoresHelperResults = true := by native_decide

def storeHelperPairEqExecutableStoresHelperResults : Bool :=
  match MacroTupleDestructuring.storeHelperPairEq 11 Verity.defaultState with
  | .success () state =>
      state.storage 0 == 11 && state.storage 1 == 12
  | .revert _ _ => false

example : storeHelperPairEqExecutableStoresHelperResults = true := by native_decide

def storePairTailExecutableStoresOnlyRequestedValue : Bool :=
  match MacroTupleDestructuring.storePairTail (11, 17) Verity.defaultState with
  | .success () state =>
      state.storage 0 == 0 && state.storage 1 == 17
  | .revert _ _ => false

example : storePairTailExecutableStoresOnlyRequestedValue = true := by native_decide

def storeHelperPairTailExecutableStoresOnlyRequestedValue : Bool :=
  match MacroTupleDestructuring.storeHelperPairTail 11 Verity.defaultState with
  | .success () state =>
      state.storage 0 == 0 && state.storage 1 == 12
  | .revert _ _ => false

example : storeHelperPairTailExecutableStoresOnlyRequestedValue = true := by native_decide

def storeHelperPairTailNameCollisionExecutablePreservesParam : Bool :=
  match MacroTupleDestructuring.storeHelperPairTailNameCollision 33 11 Verity.defaultState with
  | .success () state =>
      state.storage 0 == 33 && state.storage 1 == 12
  | .revert _ _ => false

example : storeHelperPairTailNameCollisionExecutablePreservesParam = true := by native_decide

end MacroTupleDestructuringSmoke

namespace MacroHigherOrderInternalCallSmoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256

-- #1747: higher-order internal helpers (function-pointer parameters) are
-- eliminated by a compile-time monomorphization pre-pass.  `applyTwice` takes a
-- function pointer `op` and applies it twice; `runDouble` calls it with the
-- statically-known helper `double`.  After the pre-pass the contract contains
-- only first-order helpers: a synthesized clone `applyTwice_mono_double` (with
-- `op` removed and every `op` call replaced by `double`) plus the rewritten
-- call site.  Nothing downstream — model, IR, Yul — ever sees a function
-- pointer, so the existing machinery applies unchanged.
verity_contract HigherOrderDemo where
  storage
    result : Uint256 := slot 0

  function double (x : Uint256) : Uint256 := do
    return add x x

  function applyTwice (op : Uint256 → Uint256, x : Uint256) : Uint256 := do
    let once ← op x
    let twice ← op once
    return twice

  function runDouble (seed : Uint256) : Uint256 := do
    let out ← applyTwice double seed
    return out

-- The higher-order call `applyTwice double seed` is rewritten to a first-order
-- call to the synthesized clone; the model never sees a function pointer.
def runDoubleModelMonomorphizesHigherOrderCall : Bool :=
  match HigherOrderDemo.runDouble_modelBody with
  | [Stmt.letVar "out" (Expr.internalCall helperName [Expr.param "seed"]),
      Stmt.return (Expr.localVar "out")] =>
      helperName == "internal_applyTwice_mono_double"
  | _ => false

example : runDoubleModelMonomorphizesHigherOrderCall = true := by native_decide

-- The synthesized clone is an ordinary first-order helper whose body calls the
-- concrete helper `double` directly (the function pointer `op` is gone).
def applyTwiceCloneModelCallsConcreteHelper : Bool :=
  match HigherOrderDemo.applyTwice_mono_double_modelBody with
  | [Stmt.letVar "once" (Expr.internalCall op1 [Expr.param "x"]),
      Stmt.letVar "twice" (Expr.internalCall op2 [Expr.localVar "once"]),
      Stmt.return (Expr.localVar "twice")] =>
      op1 == "internal_double" && op2 == "internal_double"
  | _ => false

example : applyTwiceCloneModelCallsConcreteHelper = true := by native_decide

-- End-to-end: the monomorphized contract still computes double (double seed).
def runDoubleExecutableComputesDoubleApplication : Bool :=
  match HigherOrderDemo.runDouble 5 Verity.defaultState with
  | .success out _ => out == 20
  | .revert _ _ => false

example : runDoubleExecutableComputesDoubleApplication = true := by native_decide

end MacroHigherOrderInternalCallSmoke

namespace MacroQualifiedLibraryCallSmoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256

verity_contract TermMaxCurve where
  storage

  function buyXt (nif : Uint256, daysToMaturity : Uint256,
      oriXtReserve : Uint256, debtTokenAmtIn : Uint256) :
      Tuple [Uint256, Uint256] := do
    return (add nif daysToMaturity, add oriXtReserve debtTokenAmtIn)

verity_contract TermMaxOrderV2 where
  storage
    sentinel : Uint256 := slot 0

  function buyXtStep (nif : Uint256, daysToMaturity : Uint256,
      oriXtReserve : Uint256, debtTokenAmtIn : Uint256) :
      Tuple [Uint256, Uint256] := do
    let (tokenAmtOut, deltaFt) ←
      TermMaxCurve.buyXt nif daysToMaturity oriXtReserve debtTokenAmtIn
    return (tokenAmtOut, deltaFt)

  function TermMaxCurve_buyXt (value : Uint256) : Uint256 := do
    return value

verity_contract QualifiedPrimitiveLibrary where
  storage

  function uintIsAccepted (value : Uint256) : Bool := do
    return value == value

verity_contract QualifiedPrimitiveCaller where
  storage

  function callBoolHelper (value : Uint256) : Bool := do
    let result ← QualifiedPrimitiveLibrary.uintIsAccepted value
    return result

private def qualifiedBuyXtInternalName : String :=
  "internal_qualified_12_TermMaxCurve_5_buyXt"

private def localUnderscoreInternalName : String := "internal_TermMaxCurve_buyXt"

def buyXtStepModelUsesQualifiedInternalCall : Bool :=
  match TermMaxOrderV2.buyXtStep_modelBody with
  | [Stmt.internalCallAssign ["tokenAmtOut", "deltaFt"] helperName
        [Expr.param "nif", Expr.param "daysToMaturity",
         Expr.param "oriXtReserve", Expr.param "debtTokenAmtIn"],
      Stmt.returnValues [Expr.localVar "tokenAmtOut", Expr.localVar "deltaFt"]] =>
      helperName == qualifiedBuyXtInternalName
  | _ => false

example : buyXtStepModelUsesQualifiedInternalCall = true := by native_decide

def callerSpecIncludesQualifiedLibraryModel : Bool :=
  TermMaxOrderV2.spec.functions.any fun fn =>
    fn.name == qualifiedBuyXtInternalName && fn.isInternal

example : callerSpecIncludesQualifiedLibraryModel = true := by native_decide

def qualifiedHelperAvoidsLocalUnderscoreCollision : Bool :=
  qualifiedBuyXtInternalName != localUnderscoreInternalName &&
    TermMaxOrderV2.spec.functions.any (fun fn =>
      fn.name == qualifiedBuyXtInternalName && fn.isInternal) &&
    TermMaxOrderV2.spec.functions.any (fun fn =>
      fn.name == localUnderscoreInternalName && fn.isInternal)

example : qualifiedHelperAvoidsLocalUnderscoreCollision = true := by native_decide

def qualifiedLibraryExecutableCallRuns : Bool :=
  match TermMaxOrderV2.buyXtStep 10 3 20 7 Verity.defaultState with
  | .success (tokenAmtOut, deltaFt) state =>
      tokenAmtOut == 13 && deltaFt == 27 && state.sender == Verity.defaultState.sender
  | .revert _ _ => false

example : qualifiedLibraryExecutableCallRuns = true := by native_decide

def qualifiedLibraryBoolBindRuns : Bool :=
  match QualifiedPrimitiveCaller.callBoolHelper 7 Verity.defaultState with
  | .success result state =>
      result == true && state.sender == Verity.defaultState.sender
  | .revert _ _ => false

example : qualifiedLibraryBoolBindRuns = true := by native_decide

/--
error: qualified library helper call 'TermMaxCurve.buyXt' is only supported as a monadic bind source; use `let x ← TermMaxCurve.buyXt ...` or tuple destructuring bind syntax
-/
#guard_msgs in
verity_contract QualifiedLibraryPureExprRejected where
  storage

  function badPureCall (nif : Uint256, daysToMaturity : Uint256,
      oriXtReserve : Uint256, debtTokenAmtIn : Uint256) : Uint256 := do
    let ignored := TermMaxCurve.buyXt nif daysToMaturity oriXtReserve debtTokenAmtIn
    return nif

/--
error: tuple destructuring binds 3 names, but qualified helper 'TermMaxCurve.buyXt' returns 2 values
-/
#guard_msgs in
verity_contract QualifiedLibraryTupleArityRejected where
  storage

  function badTupleBind (nif : Uint256, daysToMaturity : Uint256,
      oriXtReserve : Uint256, debtTokenAmtIn : Uint256) : Uint256 := do
    let (tokenAmtOut, deltaFt, extra) ←
      TermMaxCurve.buyXt nif daysToMaturity oriXtReserve debtTokenAmtIn
    return tokenAmtOut

/--
error: qualified helper 'TermMaxCurve.buyXt' returns multiple values; use tuple destructuring
-/
#guard_msgs in
verity_contract QualifiedLibraryTupleSimpleBindRejected where
  storage

  function badSimpleBind (nif : Uint256, daysToMaturity : Uint256,
      oriXtReserve : Uint256, debtTokenAmtIn : Uint256) : Uint256 := do
    let tokenAmtOut ←
      TermMaxCurve.buyXt nif daysToMaturity oriXtReserve debtTokenAmtIn
    return tokenAmtOut

end MacroQualifiedLibraryCallSmoke

namespace MacroStatelessSmoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256

verity_contract MacroStateless where
  storage

  function echoWord (value : Uint256) : Uint256 := do
    return value

  function callerEcho () : Address := do
    let sender ← msgSender
    return sender

def specHasNoFields : Bool :=
  MacroStateless.spec.fields.isEmpty

example : specHasNoFields = true := by native_decide

def echoWordModelUsesOnlyParams : Bool :=
  match MacroStateless.echoWord_modelBody with
  | [Stmt.return (Expr.param "value")] => true
  | _ => false

example : echoWordModelUsesOnlyParams = true := by native_decide

def callerEchoExecutableReadsSender : Bool :=
  let state := { Verity.defaultState with sender := Verity.wordToAddress 77 }
  match MacroStateless.callerEcho state with
  | .success sender nextState =>
      sender == Verity.wordToAddress 77 && nextState.sender == state.sender
  | .revert _ _ => false

example : callerEchoExecutableReadsSender = true := by native_decide

end MacroStatelessSmoke

namespace MacroStatelessSectionsSmoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256

verity_contract MacroStatelessSections where
  storage

  errors
    error BadSeed(Uint256)

  constructor (seed : Uint256) := do
    let same := seed == seed
    require same "seed sanity check"

  function failWith (_seed : Uint256) : Unit := do
    let failingSeed := _seed
    revert BadSeed(failingSeed)

def specKeepsEmptyFieldsWithErrorsAndConstructor : Bool :=
  MacroStatelessSections.spec.fields.isEmpty &&
  MacroStatelessSections.spec.errors.map (·.name) == ["BadSeed"] &&
  match MacroStatelessSections.spec.constructor with
  | some ctor =>
      match ctor.params with
      | [{ name := "seed", ty := ParamType.uint256 }] => true
      | _ => false
  | none => false

example : specKeepsEmptyFieldsWithErrorsAndConstructor = true := by native_decide

def failWithModelUsesDeclaredCustomError : Bool :=
  match MacroStatelessSections.failWith_modelBody with
  | [Stmt.letVar "failingSeed" (Expr.param "_seed"),
      Stmt.revertError "BadSeed" [Expr.localVar "failingSeed"],
      Stmt.stop] => true
  | _ => false

example : failWithModelUsesDeclaredCustomError = true := by native_decide

end MacroStatelessSectionsSmoke

namespace MacroSafeMulRequireSmoke

def safeAddRequireLowersToOverflowGuard : Bool :=
  match Contracts.SafeCounter.increment_modelBody with
  | [ Stmt.letVar "current" (Expr.storage "count"),
      Stmt.require
        (Expr.ge
          (Expr.add (Expr.localVar "current") (Expr.literal 1))
          (Expr.localVar "current"))
        "Overflow in increment",
      Stmt.letVar "newCount" (Expr.add (Expr.localVar "current") (Expr.literal 1)),
      Stmt.setStorage "count" (Expr.localVar "newCount"),
      Stmt.stop ] => true
  | _ => false

example : safeAddRequireLowersToOverflowGuard = true := by native_decide

def safeSubRequireLowersToUnderflowGuard : Bool :=
  match Contracts.SafeCounter.decrement_modelBody with
  | [ Stmt.letVar "current" (Expr.storage "count"),
      Stmt.require
        (Expr.ge (Expr.localVar "current") (Expr.literal 1))
        "Underflow in decrement",
      Stmt.letVar "newCount" (Expr.sub (Expr.localVar "current") (Expr.literal 1)),
      Stmt.setStorage "count" (Expr.localVar "newCount"),
      Stmt.stop ] => true
  | _ => false

example : safeSubRequireLowersToUnderflowGuard = true := by native_decide

def safeMulRequireLowersToOverflowGuard : Bool :=
  match Contracts.Smoke.SafeMulRequireSmoke.multiplyStored_modelBody with
  | [ Stmt.letVar "current" (Expr.storage "product"),
      Stmt.require
        (Expr.logicalOr
          (Expr.eq (Expr.param "factor") (Expr.literal 0))
          (Expr.eq
            (Expr.div
              (Expr.mul (Expr.localVar "current") (Expr.param "factor"))
              (Expr.param "factor"))
            (Expr.localVar "current")))
        "Product overflow",
      Stmt.letVar "next" (Expr.mul (Expr.localVar "current") (Expr.param "factor")),
      Stmt.setStorage "product" (Expr.localVar "next"),
      Stmt.return (Expr.localVar "next") ] => true
  | _ => false

example : safeMulRequireLowersToOverflowGuard = true := by native_decide

def safeDivRequireLowersToZeroGuard : Bool :=
  match Contracts.Smoke.SafeMulRequireSmoke.divideStored_modelBody with
  | [ Stmt.letVar "current" (Expr.storage "product"),
      Stmt.require
        (Expr.logicalNot (Expr.eq (Expr.param "divisor") (Expr.literal 0)))
        "Division by zero",
      Stmt.letVar "next" (Expr.div (Expr.localVar "current") (Expr.param "divisor")),
      Stmt.setStorage "product" (Expr.localVar "next"),
      Stmt.return (Expr.localVar "next") ] => true
  | _ => false

example : safeDivRequireLowersToZeroGuard = true := by native_decide

def addPanicLowersToSolidity08Guard : Bool :=
  match Contracts.Smoke.ArithmeticPanicSmoke.deposit_modelBody with
  | [ Stmt.letVar "current" (Expr.storage "balance"),
      Stmt.require
        (Expr.ge
          (Expr.add (Expr.localVar "current") (Expr.param "amount"))
          (Expr.localVar "current"))
        "Panic(0x11): arithmetic overflow",
      Stmt.letVar "next" (Expr.add (Expr.localVar "current") (Expr.param "amount")),
      Stmt.setStorage "balance" (Expr.localVar "next"),
      Stmt.return (Expr.localVar "next") ] => true
  | _ => false

example : addPanicLowersToSolidity08Guard = true := by native_decide

def subPanicLowersToSolidity08Guard : Bool :=
  match Contracts.Smoke.ArithmeticPanicSmoke.withdraw_modelBody with
  | [ Stmt.letVar "current" (Expr.storage "balance"),
      Stmt.require
        (Expr.ge (Expr.localVar "current") (Expr.param "amount"))
        "Panic(0x11): arithmetic underflow",
      Stmt.letVar "next" (Expr.sub (Expr.localVar "current") (Expr.param "amount")),
      Stmt.setStorage "balance" (Expr.localVar "next"),
      Stmt.return (Expr.localVar "next") ] => true
  | _ => false

example : subPanicLowersToSolidity08Guard = true := by native_decide

def mulPanicLowersToSolidity08Guard : Bool :=
  match Contracts.Smoke.ArithmeticPanicSmoke.scaleStored_modelBody with
  | [ Stmt.letVar "current" (Expr.storage "balance"),
      Stmt.require
        (Expr.logicalOr
          (Expr.eq (Expr.param "factor") (Expr.literal 0))
          (Expr.eq
            (Expr.div
              (Expr.mul (Expr.localVar "current") (Expr.param "factor"))
              (Expr.param "factor"))
            (Expr.localVar "current")))
        "Panic(0x11): arithmetic overflow",
      Stmt.letVar "next" (Expr.mul (Expr.localVar "current") (Expr.param "factor")),
      Stmt.setStorage "balance" (Expr.localVar "next"),
      Stmt.return (Expr.localVar "next") ] => true
  | _ => false

example : mulPanicLowersToSolidity08Guard = true := by native_decide

def divPanicLowersToSolidity08Guard : Bool :=
  match Contracts.Smoke.ArithmeticPanicSmoke.shareStored_modelBody with
  | [ Stmt.letVar "current" (Expr.storage "balance"),
      Stmt.require
        (Expr.logicalNot (Expr.eq (Expr.param "divisor") (Expr.literal 0)))
        "Panic(0x12): division by zero",
      Stmt.letVar "next" (Expr.div (Expr.localVar "current") (Expr.param "divisor")),
      Stmt.setStorage "balance" (Expr.localVar "next"),
      Stmt.return (Expr.localVar "next") ] => true
  | _ => false

example : divPanicLowersToSolidity08Guard = true := by native_decide

end MacroSafeMulRequireSmoke

namespace MacroInt256LoweringSmoke

open Contracts.Smoke
open Lean
open Lean.Elab.Command
open Lean.Meta

def divViaLocalUsesSignedDivision : Bool :=
  match Contracts.Smoke.SignedBuiltinSmoke.signedDivViaLocal_modelBody with
  | [Stmt.letVar "signedRaw" (Expr.param "raw"),
      Stmt.return (Expr.sdiv (Expr.localVar "signedRaw") (Expr.param "denom"))] => true
  | _ => false

example : divViaLocalUsesSignedDivision = true := by native_decide

def bitAndComparisonUsesUnsignedLowering : Bool :=
  match Contracts.Smoke.SignedBuiltinSmoke.bitAndSignBit_modelBody with
  | [Stmt.return
      (Compiler.CompilationModel.Expr.lt
        (Expr.bitAnd (Expr.param "lhs") (Expr.param "rhs"))
        (Expr.literal 0))] => true
  | _ => false

example : bitAndComparisonUsesUnsignedLowering = true := by native_decide

def minComparisonUsesUnsignedLowering : Bool :=
  match Contracts.Smoke.SignedBuiltinSmoke.minSignBit_modelBody with
  | [Stmt.return
      (Compiler.CompilationModel.Expr.lt
        (Expr.min (Expr.param "lhs") (Expr.literal 0))
        (Expr.literal 0))] => true
  | _ => false

example : minComparisonUsesUnsignedLowering = true := by native_decide

run_cmd do
  let valueIdent := mkIdent `value
  let actualStx ← Verity.Macro.translatePureExpr
    #[] #[] #[]
    #[{ ident := valueIdent, name := "value", ty := Verity.Macro.ValueType.int256 }]
    #[]
    (← `($valueIdent < 0))
  liftTermElabM do
    let expectedStx ← `(
      Compiler.CompilationModel.Expr.slt
        (Compiler.CompilationModel.Expr.param "value")
        (Compiler.CompilationModel.Expr.literal 0))
    let actualExpr ← Lean.Elab.Term.elabTerm actualStx (some (mkConst ``Compiler.CompilationModel.Expr))
    let expectedExpr ← Lean.Elab.Term.elabTerm expectedStx (some (mkConst ``Compiler.CompilationModel.Expr))
    let actualExpr ← instantiateMVars actualExpr
    let expectedExpr ← instantiateMVars expectedExpr
    unless ← isDefEq actualExpr expectedExpr do
      throwError m!"expected signed comparison lowering, got {actualStx}"

end MacroInt256LoweringSmoke

namespace MacroNumericLiteralHelperSmoke

open Verity hiding pure bind
open Verity.EVM.Uint256

verity_contract MacroNumericLiteralHelper where
  storage

  function choose (value : Int256) : Int256 := do
    return value

  function signedLiteral () : Int256 := do
    let result ← choose 1
    return result

def signedLiteralUsesInt256Overload : Bool :=
  match MacroNumericLiteralHelper.signedLiteral_modelBody with
  | [Stmt.letVar "result" (Expr.internalCall helperName [Expr.literal 1]),
      Stmt.return (Expr.localVar "result")] =>
      helperName == "internal_choose"
  | _ => false

example : signedLiteralUsesInt256Overload = true := by native_decide

end MacroNumericLiteralHelperSmoke

namespace MacroLeanDefHelperSmoke

open Contracts.Smoke

def leanDefHelperLowersToPureExpr : Bool :=
  match LeanDefHelperSmoke.addOffset_modelBody with
  | [Stmt.return
      (Expr.ite
        (Expr.slt (Expr.param "y") (Expr.literal 0))
        (Expr.sub (Expr.param "x") (Expr.sub (Expr.literal 0) (Expr.param "y")))
        (Expr.add (Expr.param "x") (Expr.param "y")))] => true
  | _ => false

example : leanDefHelperLowersToPureExpr = true := by native_decide

def leanDefHelperEqualityLowersToPureExpr : Bool :=
  match LeanDefHelperSmoke.sameWord_modelBody with
  | [Stmt.return
      (Expr.ite
        (Expr.eq (Expr.param "x") (Expr.param "y"))
        (Expr.literal 1)
        (Expr.literal 0))] => true
  | _ => false

example : leanDefHelperEqualityLowersToPureExpr = true := by native_decide

end MacroLeanDefHelperSmoke

namespace MacroPayableConstructorSmoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256

verity_contract MacroNonPayableConstructor where
  storage
    owner : Address := slot 0

  constructor (seedOwner : Address) := do
    setStorageAddr owner seedOwner

  function getOwner () : Address := do
    let currentOwner ← getStorageAddr owner
    return currentOwner

verity_contract MacroPayableConstructor where
  storage
    owner : Address := slot 0

  constructor (seedOwner : Address) payable := do
    setStorageAddr owner seedOwner

  function getOwner () : Address := do
    let currentOwner ← getStorageAddr owner
    return currentOwner

def specMarksConstructorPayable : Bool :=
  match MacroPayableConstructor.spec.constructor with
  | some ctor =>
      ctor.isPayable &&
      match ctor.params with
      | [{ name := "seedOwner", ty := ParamType.address }] => true
      | _ => false
  | none => false

example : specMarksConstructorPayable = true := by native_decide

end MacroPayableConstructorSmoke

namespace MacroInitializerSmoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256

verity_contract MacroInitializer where
  storage
    initializedVersion : Uint256 := slot 0
    owner : Address := slot 1
    paused : Uint256 := slot 2

  function initOwner (seedOwner : Address) initializer(initializedVersion) : Unit := do
    setStorageAddr owner seedOwner

  function initOwnerChecked (seedOwner : Address) initializer(initializedVersion) : Unit := do
    require (seedOwner != zeroAddress) "Invalid owner"
    setStorageAddr owner seedOwner

  function upgradeToV2 () reinitializer(initializedVersion, 2) : Unit := do
    setStorage paused 1

  function ownerAddr () : Address := do
    let currentOwner ← getStorageAddr owner
    return currentOwner

def initializeModelPrependsSingleRunGuard : Bool :=
  match MacroInitializer.initOwner_modelBody with
  | [Stmt.require (Expr.eq (Expr.storage "initializedVersion") (Expr.literal 0)) "initializer already run",
      Stmt.setStorage "initializedVersion" (Expr.literal 1),
      Stmt.setStorageAddr "owner" (Expr.param "seedOwner"),
      Stmt.stop] =>
      true
  | _ => false

example : initializeModelPrependsSingleRunGuard = true := by native_decide

def initializeV2ModelPrependsVersionGuard : Bool :=
  match MacroInitializer.upgradeToV2_modelBody with
  | [Stmt.require (Expr.lt (Expr.storage "initializedVersion") (Expr.literal 2)) "reinitializer(2) already run",
      Stmt.setStorage "initializedVersion" (Expr.literal 2),
      Stmt.setStorage "paused" (Expr.literal 1),
      Stmt.stop] =>
      true
  | _ => false

example : initializeV2ModelPrependsVersionGuard = true := by native_decide

def initializeExecutableRunsOnce : Bool :=
  let seedOwner := wordToAddress 77
  match MacroInitializer.initOwner seedOwner Verity.defaultState with
  | .success () state =>
      state.storage MacroInitializer.initializedVersion.slot == 1 &&
      state.storageAddr MacroInitializer.owner.slot == seedOwner
  | .revert _ _ => false

example : initializeExecutableRunsOnce = true := by native_decide

def compileSetStorageAddrMasksAddressWrites : Bool :=
  let fields : List Compiler.CompilationModel.Field :=
    [{ name := "owner", ty := Compiler.CompilationModel.FieldType.address }]
  match Compiler.CompilationModel.compileSetStorage fields .calldata "owner" (Expr.literal 42) true with
  | .ok [Compiler.Yul.YulStmt.expr
      (Compiler.Yul.YulExpr.call "sstore"
        [Compiler.Yul.YulExpr.lit 0,
         Compiler.Yul.YulExpr.call "and"
           [Compiler.Yul.YulExpr.lit 42,
            Compiler.Yul.YulExpr.hex mask]])] =>
      mask == Compiler.Constants.addressMask
  | _ => false

example : compileSetStorageAddrMasksAddressWrites = true := by native_decide

def compileSetStorageWordMirrorsAliasSlots : Bool :=
  let fields : List Compiler.CompilationModel.Field :=
    [{ name := "choice", ty := Compiler.CompilationModel.FieldType.adt "Choice" 2,
       «slot» := some 10, aliasSlots := [100] }]
  match Compiler.CompilationModel.compileStmt fields [] [] .calldata [] false [] []
      (Compiler.CompilationModel.Stmt.setStorageWord "choice" 1 (Expr.literal 42)) with
  | .ok [
      Compiler.Yul.YulStmt.block [
        Compiler.Yul.YulStmt.let_ "__compat_value" (Compiler.Yul.YulExpr.lit 42),
        Compiler.Yul.YulStmt.expr
          (Compiler.Yul.YulExpr.call "sstore"
            [Compiler.Yul.YulExpr.call "add" [Compiler.Yul.YulExpr.lit 10, Compiler.Yul.YulExpr.lit 1],
             Compiler.Yul.YulExpr.ident "__compat_value"]),
        Compiler.Yul.YulStmt.expr
          (Compiler.Yul.YulExpr.call "sstore"
            [Compiler.Yul.YulExpr.call "add" [Compiler.Yul.YulExpr.lit 100, Compiler.Yul.YulExpr.lit 1],
             Compiler.Yul.YulExpr.ident "__compat_value"])
      ]] => true
  | _ => false

example : compileSetStorageWordMirrorsAliasSlots = true := by native_decide

def initializeExecutableSecondCallReverts : Bool :=
  let seedOwner := wordToAddress 77
  match MacroInitializer.initOwner seedOwner Verity.defaultState with
  | .success () initializedState =>
      match MacroInitializer.initOwner seedOwner initializedState with
      | .revert "initializer already run" revertedState =>
          revertedState.storage MacroInitializer.initializedVersion.slot ==
            initializedState.storage MacroInitializer.initializedVersion.slot &&
          revertedState.storageAddr MacroInitializer.owner.slot ==
            initializedState.storageAddr MacroInitializer.owner.slot
      | _ => false
  | .revert _ _ => false

example : initializeExecutableSecondCallReverts = true := by native_decide

def initializeExecutableBodyRevertRollsBackVersionSlot : Bool :=
  match (MacroInitializer.initOwnerChecked zeroAddress).run Verity.defaultState with
  | .revert "Invalid owner" revertedState =>
      revertedState.storage MacroInitializer.initializedVersion.slot == 0 &&
      revertedState.storageAddr MacroInitializer.owner.slot == zeroAddress
  | _ => false

example : initializeExecutableBodyRevertRollsBackVersionSlot = true := by native_decide

def reinitializerExecutableAdvancesVersion : Bool :=
  let seedOwner := wordToAddress 77
  match MacroInitializer.initOwner seedOwner Verity.defaultState with
  | .success () initializedState =>
      match MacroInitializer.upgradeToV2 initializedState with
      | .success () upgradedState =>
          upgradedState.storage MacroInitializer.initializedVersion.slot == 2 &&
          upgradedState.storage MacroInitializer.paused.slot == 1
      | .revert _ _ => false
  | .revert _ _ => false

example : reinitializerExecutableAdvancesVersion = true := by native_decide

end MacroInitializerSmoke

namespace MacroImmutableSmoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256

verity_contract MacroImmutable where
  storage
    owner : Address := slot 0

  constants
    offset : Uint256 := 2

  immutables
    seededSupply : Uint256 := (add seed offset)
    treasury : Address := ownerSeed

  constructor (seed : Uint256, ownerSeed : Address) := do
    setStorageAddr owner ownerSeed

  function supplyCap () : Uint256 := do
    return seededSupply

  function treasuryAddr () : Address := do
    return treasury

  function shadowed (seededSupply : Uint256) : Uint256 := do
    return seededSupply

verity_contract MacroImplicitImmutable where
  storage

  immutables
    feeScale : Uint256 := 10000

  function getFeeScale () : Uint256 := do
    return feeScale

verity_contract MacroTypedImmutable where
  storage

  immutables
    paused : Bool := true
    feeBps : Uint8 := 7
    domainTag : Bytes32 := 42

  function isPaused () : Bool := do
    return paused

  function feeScale () : Uint8 := do
    return feeBps

  function domainSeparator () : Bytes32 := do
    return domainTag

def specKeepsImmutablesOutOfStorageFields : Bool :=
  MacroImmutable.spec.fields.map (·.name) == ["owner"] &&
  MacroImmutable.spec.immutables.map (·.name) == ["seededSupply", "treasury"]

def constructorSeedsBytecodeImmutables : Bool :=
  match MacroImmutable.spec.constructor with
  | some ctor =>
      match ctor.body with
      | [Stmt.setImmutable "seededSupply"
            (Expr.add (Expr.param "seed") (Expr.literal 2)),
          Stmt.setImmutable "treasury" (Expr.param "ownerSeed"),
          Stmt.setStorageAddr "owner" (Expr.param "ownerSeed")] =>
          true
      | _ => false
  | none => false

def runtimeFunctionsUseImmutableExpressions : Bool :=
  match MacroImmutable.supplyCap_modelBody, MacroImmutable.treasuryAddr_modelBody with
  | [Stmt.return (Expr.immutable "seededSupply")],
      [Stmt.return (Expr.immutable "treasury")] => true
  | _, _ => false

def functionParamsStillShadowImmutableNames : Bool :=
  match MacroImmutable.shadowed 91 Verity.defaultState with
  | .success value _ => value == 91
  | _ => false

example : functionParamsStillShadowImmutableNames = true := by native_decide

def implicitConstructorCreatedForImmutableInitializers : Bool :=
  match MacroImplicitImmutable.spec.constructor with
  | some ctor =>
      ctor.params.isEmpty &&
      match ctor.body with
      | [Stmt.setImmutable "feeScale" (Expr.literal 10000)] => true
      | _ => false
  | none => false

def implicitImmutableFunctionUsesImmutableExpression : Bool :=
  match MacroImplicitImmutable.getFeeScale_modelBody with
  | [Stmt.return (Expr.immutable "feeScale")] => true
  | _ => false

def typedImmutableSpecUsesImmutableSurface : Bool :=
  MacroTypedImmutable.spec.fields.isEmpty &&
  MacroTypedImmutable.spec.immutables.map (fun imm => (imm.name, imm.ty)) ==
    [("paused", ParamType.bool), ("feeBps", ParamType.uint8), ("domainTag", ParamType.bytes32)]

def typedImmutableConstructorSeedsBytecodeValues : Bool :=
  match MacroTypedImmutable.spec.constructor with
  | some ctor =>
      ctor.params.isEmpty &&
      match ctor.body with
      | [Stmt.setImmutable "paused" (Expr.literal 1),
          Stmt.setImmutable "feeBps" (Expr.literal 7),
          Stmt.setImmutable "domainTag" (Expr.literal 42)] => true
      | _ => false
  | none => false

def typedImmutableFunctionsUseImmutableExpressions : Bool :=
  match MacroTypedImmutable.isPaused_modelBody,
      MacroTypedImmutable.feeScale_modelBody,
      MacroTypedImmutable.domainSeparator_modelBody with
  | [Stmt.return (Expr.immutable "paused")],
      [Stmt.return (Expr.immutable "feeBps")],
      [Stmt.return (Expr.immutable "domainTag")] => true
  | _, _, _ => false

end MacroImmutableSmoke

namespace MacroStructDestructuringSmoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256

verity_contract MacroStructDestructuring where
  storage
    positions : MappingStruct(Address,[
      supplyShares @word 0 packed(0,128),
      borrowShares @word 0 packed(128,128),
      delegate @word 1
    ]) := slot 0
    approvals : MappingStruct2(Address,Address,[
      allowance @word 0 packed(0,128),
      nonce @word 1
    ]) := slot 1

  function loadPosition (user : Address) : Tuple [Uint256, Uint256, Address] := do
    let (supply, borrow, delegate_) := structMembers "positions" user ["supplyShares", "borrowShares", "delegate"]
    return (supply, borrow, delegate_)

  function loadApproval (owner : Address, spender : Address) : Tuple [Uint256, Uint256] := do
    return structMembers2 "approvals" owner spender ["allowance", "nonce"]

def loadPositionModelDestructuresStructMembers : Bool :=
  match MacroStructDestructuring.loadPosition_modelBody with
  | [Stmt.letVar "supply" (Expr.structMember "positions" (Expr.param "user") "supplyShares"),
      Stmt.letVar "borrow" (Expr.structMember "positions" (Expr.param "user") "borrowShares"),
      Stmt.letVar "delegate_" (Expr.structMember "positions" (Expr.param "user") "delegate"),
      Stmt.returnValues [Expr.localVar "supply", Expr.localVar "borrow", Expr.localVar "delegate_"]] =>
      true
  | _ => false

example : loadPositionModelDestructuresStructMembers = true := by native_decide

def loadApprovalModelReturnsStructMembers2 : Bool :=
  match MacroStructDestructuring.loadApproval_modelBody with
  | [Stmt.returnValues
      [Expr.structMember2 "approvals" (Expr.param "owner") (Expr.param "spender") "allowance",
       Expr.structMember2 "approvals" (Expr.param "owner") (Expr.param "spender") "nonce"]] =>
      true
  | _ => false

example : loadApprovalModelReturnsStructMembers2 = true := by native_decide

def loadPositionExecutableKeepsTupleShape : Bool :=
  match MacroStructDestructuring.loadPosition Verity.defaultState.sender Verity.defaultState with
  | .success (supply, (borrow, delegate_)) state =>
      supply == 0 && borrow == 0 && delegate_ == zeroAddress && state.sender == Verity.defaultState.sender
  | .revert _ _ => false

example : loadPositionExecutableKeepsTupleShape = true := by native_decide

def loadApprovalExecutableKeepsTupleShape : Bool :=
  match MacroStructDestructuring.loadApproval Verity.defaultState.sender Verity.defaultState.sender Verity.defaultState with
  | .success (allowance, nonce) state =>
      allowance == 0 && nonce == 0 && state.sender == Verity.defaultState.sender
  | .revert _ _ => false

example : loadApprovalExecutableKeepsTupleShape = true := by native_decide

end MacroStructDestructuringSmoke

namespace MacroDynamicArraySmoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256

verity_contract MacroDynamicArray where
  storage
    sentinel : Uint256 := slot 0

  function countRecipients (recipients : Array Address) : Uint256 := do
    let count := arrayLength recipients
    return count

  function firstRecipient (recipients : Array Address) : Address := do
    let first := arrayElement recipients 0
    return first

  function echoAmounts (amounts : Array Uint256) : Array Uint256 := do
    returnArray amounts

  function echoedAmountCount (amounts : Array Uint256) : Uint256 := do
    let echoed ← echoAmounts amounts
    return (arrayLength echoed)

  function firstEchoedAmount (amounts : Array Uint256) : Uint256 := do
    let echoed ← echoAmounts amounts
    return (arrayElement echoed 0)

  function forwardedEchoedAmount (amounts : Array Uint256) : Uint256 := do
    let echoed ← echoAmounts amounts
    let forwarded ← echoAmounts echoed
    return (arrayElement forwarded 0)

  function compactAmounts (amounts : Array Uint256) : Array Uint256 := do
    let mut count := 0
    forEach "i" (arrayLength amounts) (do
      let value := arrayElement amounts i
      if value != 0 then
        count := add count 1
      else
        pure ())
    let compacted ← allocArray count
    let mut j := 0
    forEach "i" (arrayLength amounts) (do
      let value := arrayElement amounts i
      if value != 0 then
        setMemoryArrayElement compacted j value
        j := add j 1
      else
        pure ())
    returnArray compacted

  function echoRecipients (recipients : Array Address) : Array Address := do
    returnArray recipients

  function echoFlags (flags : Array Bool) : Array Bool := do
    returnArray flags

def countRecipientsModelUsesArrayLength : Bool :=
  match MacroDynamicArray.countRecipients_modelBody with
  | [Stmt.letVar "count" (Expr.arrayLength "recipients"),
      Stmt.return (Expr.localVar "count")] =>
      true
  | _ => false

example : countRecipientsModelUsesArrayLength = true := by native_decide

def firstRecipientModelUsesArrayElement : Bool :=
  match MacroDynamicArray.firstRecipient_modelBody with
  | [Stmt.letVar "first" (Expr.arrayElement "recipients" (Expr.literal 0)),
      Stmt.return (Expr.localVar "first")] =>
      true
  | _ => false

example : firstRecipientModelUsesArrayElement = true := by native_decide

def echoAmountsModelUsesReturnArray : Bool :=
  match MacroDynamicArray.echoAmounts_modelBody with
  | [Stmt.returnArray "amounts"] =>
      true
  | _ => false

example : echoAmountsModelUsesReturnArray = true := by native_decide

def echoedAmountCountUsesMemoryArrayLength : Bool :=
  match MacroDynamicArray.echoedAmountCount_modelBody with
  | [Stmt.internalCallAssign ["echoed_data_offset", "echoed_length"] "internal_echoAmounts"
        [Expr.param "amounts_data_offset", Expr.param "amounts_length"],
      Stmt.return (Expr.memoryArrayLength "echoed")] =>
      true
  | _ => false

example : echoedAmountCountUsesMemoryArrayLength = true := by native_decide

def firstEchoedAmountUsesMemoryArrayElement : Bool :=
  match MacroDynamicArray.firstEchoedAmount_modelBody with
  | [Stmt.internalCallAssign ["echoed_data_offset", "echoed_length"] "internal_echoAmounts"
        [Expr.param "amounts_data_offset", Expr.param "amounts_length"],
      Stmt.return (Expr.memoryArrayElement "echoed" (Expr.literal 0))] =>
      true
  | _ => false

example : firstEchoedAmountUsesMemoryArrayElement = true := by native_decide

def forwardedEchoedAmountPassesMemoryArray : Bool :=
  match MacroDynamicArray.forwardedEchoedAmount_modelBody with
  | [Stmt.internalCallAssign ["echoed_data_offset", "echoed_length"] "internal_echoAmounts"
        [Expr.param "amounts_data_offset", Expr.param "amounts_length"],
      Stmt.internalCallAssign ["forwarded_data_offset", "forwarded_length"] "internal_echoAmounts"
        [Expr.localVar "echoed_data_offset", Expr.localVar "echoed_length"],
      Stmt.return (Expr.memoryArrayElement "forwarded" (Expr.literal 0))] =>
      true
  | _ => false

example : forwardedEchoedAmountPassesMemoryArray = true := by native_decide

def compactAmountsAllocatesMemoryArray : Bool :=
  let body := MacroDynamicArray.compactAmounts_modelBody
  body.any (fun stmt =>
    match stmt with
    | Stmt.letVar "compacted_length" (Expr.localVar "count") => true
    | _ => false) &&
  body.any (fun stmt =>
    match stmt with
    | Stmt.letVar "compacted_data_offset"
        (Expr.add (Expr.mload (Expr.literal 64)) (Expr.literal 32)) => true
    | _ => false) &&
  body.any (fun stmt =>
    match stmt with
    | Stmt.returnArray "compacted" => true
    | _ => false)

example : compactAmountsAllocatesMemoryArray = true := by native_decide

def compactAmountsWritesMemoryArray : Bool :=
  let body := MacroDynamicArray.compactAmounts_modelBody
  body.any (fun stmt =>
    match stmt with
    | Stmt.forEach "i" (Expr.arrayLength "amounts") loopBody =>
        loopBody.any (fun inner =>
          match inner with
          | Stmt.ite _ thenBranch _ =>
              thenBranch.any (fun branchStmt =>
                match branchStmt with
                | Stmt.unsafeBlock "write memory-backed uint256 array element"
                    [Stmt.mstore
                      (Expr.add (Expr.localVar "compacted_data_offset")
                        (Expr.mul (Expr.localVar "j") (Expr.literal 32)))
                      (Expr.localVar "value")] =>
                    true
                | _ => false)
          | _ => false)
    | _ => false)

example : compactAmountsWritesMemoryArray = true := by native_decide

def echoRecipientsModelUsesReturnArray : Bool :=
  match MacroDynamicArray.echoRecipients_modelBody with
  | [Stmt.returnArray "recipients"] =>
      true
  | _ => false

example : echoRecipientsModelUsesReturnArray = true := by native_decide

def echoFlagsModelUsesReturnArray : Bool :=
  match MacroDynamicArray.echoFlags_modelBody with
  | [Stmt.returnArray "flags"] =>
      true
  | _ => false

example : echoFlagsModelUsesReturnArray = true := by native_decide

def countRecipientsExecutableUsesRuntimeHelper : Bool :=
  match MacroDynamicArray.countRecipients #[(11 : Address), (17 : Address)] Verity.defaultState with
  | .success count state =>
      count == 2 && state.sender == Verity.defaultState.sender
  | .revert _ _ => false

example : countRecipientsExecutableUsesRuntimeHelper = true := by native_decide

def firstRecipientExecutableUsesRuntimeHelper : Bool :=
  match MacroDynamicArray.firstRecipient #[(11 : Address), (17 : Address)] Verity.defaultState with
  | .success first state =>
      first == (11 : Address) && state.sender == Verity.defaultState.sender
  | .revert _ _ => false

example : firstRecipientExecutableUsesRuntimeHelper = true := by native_decide

def firstRecipientExecutableRevertsOutOfRange : Bool :=
  match MacroDynamicArray.firstRecipient #[] Verity.defaultState with
  | .success _ _ => false
  | .revert msg state =>
      msg == "Array index out of bounds" && state.sender == Verity.defaultState.sender

example : firstRecipientExecutableRevertsOutOfRange = true := by native_decide

def echoAmountsExecutableRoundTrips : Bool :=
  match MacroDynamicArray.echoAmounts #[3, 5, 8] Verity.defaultState with
  | .success amounts state =>
      amounts == #[3, 5, 8] && state.sender == Verity.defaultState.sender
  | .revert _ _ => false

example : echoAmountsExecutableRoundTrips = true := by native_decide

def echoRecipientsExecutableRoundTrips : Bool :=
  match MacroDynamicArray.echoRecipients #[(11 : Address), (17 : Address)] Verity.defaultState with
  | .success recipients state =>
      recipients == #[(11 : Address), (17 : Address)] &&
        state.sender == Verity.defaultState.sender
  | .revert _ _ => false

example : echoRecipientsExecutableRoundTrips = true := by native_decide

verity_contract MacroStorageDynamicArray where
  storage
    queue : Array Uint256 := slot 7

  function size () : Uint256 := do
    let size ← getStorageArrayLength queue
    return size

  function firstValue () : Uint256 := do
    let first ← getStorageArrayElement queue 0
    return first

  function pushValue (value : Uint256) : Unit := do
    pushStorageArray queue value

  function setValue0 (value : Uint256) : Unit := do
    setStorageArrayElement queue 0 value

  function popValue () : Unit := do
    popStorageArray queue

def storageDynamicArrayLengthUsesStorageExpr : Bool :=
  match MacroStorageDynamicArray.size_modelBody with
  | [Stmt.letVar "size" (Expr.storageArrayLength "queue"),
      Stmt.return (Expr.localVar "size")] =>
      true
  | _ => false

example : storageDynamicArrayLengthUsesStorageExpr = true := by native_decide

def storageDynamicArrayElementUsesStorageExpr : Bool :=
  match MacroStorageDynamicArray.firstValue_modelBody with
  | [Stmt.letVar "first" (Expr.storageArrayElement "queue" (Expr.literal 0)),
      Stmt.return (Expr.localVar "first")] =>
      true
  | _ => false

example : storageDynamicArrayElementUsesStorageExpr = true := by native_decide

def storageDynamicArrayPushUsesStorageStmt : Bool :=
  match MacroStorageDynamicArray.pushValue_modelBody with
  | [Stmt.storageArrayPush "queue" (Expr.param "value"), Stmt.stop] =>
      true
  | _ => false

example : storageDynamicArrayPushUsesStorageStmt = true := by native_decide

def storageDynamicArraySetUsesStorageStmt : Bool :=
  match MacroStorageDynamicArray.setValue0_modelBody with
  | [Stmt.setStorageArrayElement "queue" (Expr.literal 0) (Expr.param "value"), Stmt.stop] =>
      true
  | _ => false

example : storageDynamicArraySetUsesStorageStmt = true := by native_decide

def storageDynamicArrayPopUsesStorageStmt : Bool :=
  match MacroStorageDynamicArray.popValue_modelBody with
  | [Stmt.storageArrayPop "queue", Stmt.stop] =>
      true
  | _ => false

example : storageDynamicArrayPopUsesStorageStmt = true := by native_decide

def storageDynamicArrayExecutableReadsHead : Bool :=
  let seededState : Verity.ContractState :=
    { Verity.defaultState with
      storageArray := fun idx =>
        if idx == (MacroStorageDynamicArray.queue).slot then [11, 17] else [] }
  match MacroStorageDynamicArray.firstValue seededState with
  | .success value state =>
      value == 11 && state.storageArray (MacroStorageDynamicArray.queue).slot == [11, 17]
  | .revert _ _ => false

example : storageDynamicArrayExecutableReadsHead = true := by native_decide

def storageDynamicArrayExecutableReadRevertsOutOfBounds : Bool :=
  match MacroStorageDynamicArray.firstValue Verity.defaultState with
  | .success _ _ => false
  | .revert msg state =>
      msg == "Storage array index out of bounds" &&
        state.storageArray (MacroStorageDynamicArray.queue).slot == []

example : storageDynamicArrayExecutableReadRevertsOutOfBounds = true := by native_decide

def storageDynamicArrayExecutableSetUpdatesHead : Bool :=
  let seededState : Verity.ContractState :=
    { Verity.defaultState with
      storageArray := fun idx =>
        if idx == (MacroStorageDynamicArray.queue).slot then [11, 17] else [] }
  match MacroStorageDynamicArray.setValue0 29 seededState with
  | .success () state =>
      state.storageArray (MacroStorageDynamicArray.queue).slot == [29, 17]
  | .revert _ _ => false

example : storageDynamicArrayExecutableSetUpdatesHead = true := by native_decide

def storageDynamicArrayExecutableSetRevertsOutOfBounds : Bool :=
  match MacroStorageDynamicArray.setValue0 29 Verity.defaultState with
  | .success _ _ => false
  | .revert msg state =>
      msg == "Storage array index out of bounds" &&
        state.storageArray (MacroStorageDynamicArray.queue).slot == []

example : storageDynamicArrayExecutableSetRevertsOutOfBounds = true := by native_decide

def storageDynamicArrayExecutablePopShrinksLength : Bool :=
  let seededState : Verity.ContractState :=
    { Verity.defaultState with
      storageArray := fun idx =>
        if idx == (MacroStorageDynamicArray.queue).slot then [11, 17] else [] }
  match MacroStorageDynamicArray.popValue seededState with
  | .success () state =>
      state.storageArray (MacroStorageDynamicArray.queue).slot == [11]
  | .revert _ _ => false

example : storageDynamicArrayExecutablePopShrinksLength = true := by native_decide

def storageDynamicArrayExecutablePopRevertsWhenEmpty : Bool :=
  match MacroStorageDynamicArray.popValue Verity.defaultState with
  | .success _ _ => false
  | .revert msg state =>
      msg == "Storage array pop on empty array" &&
        state.storageArray (MacroStorageDynamicArray.queue).slot == []

example : storageDynamicArrayExecutablePopRevertsWhenEmpty = true := by native_decide

end MacroDynamicArraySmoke

namespace MacroEventTraceSmoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256

verity_contract MacroEventTrace where
  storage

  struct Note where
    npk : Uint256,
    token : Address,
    amount : Uint256

  struct Transaction where
    withdrawal : Note,
    ciphertexts : Array Uint256

  event_defs
    event Transfer(@indexed amount : Uint256, total : Uint256)
    event Amounts(total : Uint256, values : Array Uint256)
    event MemoryAmounts(values : Array Uint256)
    event NoteLogged(note : Note)

  function emitNamed (amount : Uint256, bonus : Uint256) : Unit := do
    emit "Transfer" [amount, add amount bonus]

  function emitArray (total : Uint256, values : Array Uint256) : Unit := do
    emit "Amounts" [total, values]

  function emitMemoryArray (len : Uint256) : Unit := do
    let values ← allocArray len
    emit "MemoryAmounts" [values]

  function emitNote (txn : Transaction) : Unit := do
    emit "NoteLogged" [txn.withdrawal]

  function emitDynamicLog
      (topic0 : Uint256, topic1 : Uint256, dataOffset : Uint256, dataSize : Uint256) : Unit := do
    rawLog [topic0, add topic1 1] dataOffset dataSize

def emitNamedModelUsesStmtEmit : Bool :=
  match MacroEventTrace.emitNamed_modelBody with
  | [Stmt.emit "Transfer" [Expr.param "amount", Expr.add (Expr.param "amount") (Expr.param "bonus")],
      Stmt.stop] =>
      true
  | _ => false

example : emitNamedModelUsesStmtEmit = true := by native_decide

def emitArrayModelUsesDynamicArrayParam : Bool :=
  match MacroEventTrace.emitArray_modelBody with
  | [Stmt.emit "Amounts" [Expr.param "total", Expr.param "values"],
      Stmt.stop] =>
      true
  | _ => false

example : emitArrayModelUsesDynamicArrayParam = true := by native_decide

def emitMemoryArrayModelUsesMemoryArrayLength : Bool :=
  let body := MacroEventTrace.emitMemoryArray_modelBody
  body.any (fun stmt =>
    match stmt with
    | Stmt.letVar "values_length" (Expr.param "len") => true
    | _ => false) &&
  body.any (fun stmt =>
    match stmt with
    | Stmt.letVar "values_data_offset"
        (Expr.add (Expr.mload (Expr.literal 64)) (Expr.literal 32)) => true
    | _ => false) &&
  body.any (fun stmt =>
    match stmt with
    | Stmt.emit "MemoryAmounts" [Expr.memoryArrayLength "values"] => true
    | _ => false)

example : emitMemoryArrayModelUsesMemoryArrayLength = true := by native_decide

def emitNoteModelUsesProjectedStaticComposite : Bool :=
  match MacroEventTrace.emitNote_modelBody with
  | [Stmt.emit "NoteLogged" [Expr.paramDynamicStaticComposite "txn" 0],
      Stmt.stop] =>
      true
  | _ => false

example : emitNoteModelUsesProjectedStaticComposite = true := by native_decide

def emitDynamicLogModelUsesStmtRawLog : Bool :=
  match MacroEventTrace.emitDynamicLog_modelBody with
  | [Stmt.rawLog
        [Expr.param "topic0", Expr.add (Expr.param "topic1") (Expr.literal 1)]
        (Expr.param "dataOffset")
        (Expr.param "dataSize"),
      Stmt.stop] =>
      true
  | _ => false

example : emitDynamicLogModelUsesStmtRawLog = true := by native_decide

def eventTraceSpecCarriesEventMetadata : Bool :=
  MacroEventTrace.spec.events.any (fun ev =>
    match ev with
    | { name := "Transfer",
        params := [
          { name := "amount", ty := ParamType.uint256, kind := EventParamKind.indexed },
          { name := "total", ty := ParamType.uint256, kind := EventParamKind.unindexed }
        ] } => true
    | _ => false) &&
  MacroEventTrace.spec.events.any (fun ev =>
    match ev with
    | { name := "Amounts",
        params := [
          { name := "total", ty := ParamType.uint256, kind := EventParamKind.unindexed },
          { name := "values", ty := ParamType.array ParamType.uint256, kind := EventParamKind.unindexed }
        ] } => true
    | _ => false) &&
  MacroEventTrace.spec.events.any (fun ev =>
    match ev with
    | { name := "MemoryAmounts",
        params := [
          { name := "values", ty := ParamType.array ParamType.uint256, kind := EventParamKind.unindexed }
        ] } => true
    | _ => false)

example : eventTraceSpecCarriesEventMetadata = true := by native_decide

def emitNamedExecutableAppendsNamedEvent : Bool :=
  match MacroEventTrace.emitNamed 7 5 Verity.defaultState with
  | .success () state =>
      match state.events with
      | [{ name := "Transfer", args := [7, 12], indexedArgs := [] }] =>
          state.sender == Verity.defaultState.sender
      | _ => false
  | .revert _ _ => false

example : emitNamedExecutableAppendsNamedEvent = true := by native_decide

def emitArrayExecutableAppendsArrayLengthPlaceholder : Bool :=
  match MacroEventTrace.emitArray 7 #[11, 13] Verity.defaultState with
  | .success () state =>
      match state.events with
      | [{ name := "Amounts", args := [7, 2], indexedArgs := [] }] =>
          state.sender == Verity.defaultState.sender
      | _ => false
  | .revert _ _ => false

example : emitArrayExecutableAppendsArrayLengthPlaceholder = true := by native_decide

def emitMemoryArrayExecutableAppendsArrayLengthPlaceholder : Bool :=
  match MacroEventTrace.emitMemoryArray 3 Verity.defaultState with
  | .success () state =>
      match state.events with
      | [{ name := "MemoryAmounts", args := [3], indexedArgs := [] }] =>
          state.sender == Verity.defaultState.sender
      | _ => false
  | .revert _ _ => false

example : emitMemoryArrayExecutableAppendsArrayLengthPlaceholder = true := by native_decide

def emitDynamicLogExecutableAppendsLowLevelTrace : Bool :=
  match MacroEventTrace.emitDynamicLog 3 4 64 96 Verity.defaultState with
  | .success () state =>
      match state.events with
      | [{ name := "log2", args := [64, 96], indexedArgs := [3, 5] }] =>
          state.sender == Verity.defaultState.sender
      | _ => false
  | .revert _ _ => false

example : emitDynamicLogExecutableAppendsLowLevelTrace = true := by native_decide

def rawLogExecutableRejectsTooManyTopics : Bool :=
  match rawLog [1, 2, 3, 4, 5] 0 32 Verity.defaultState with
  | .revert msg state =>
      msg == "rawLog supports at most 4 topics, got 5" &&
        match state.events with
        | [] => true
        | _ => false
  | .success _ _ => false

example : rawLogExecutableRejectsTooManyTopics = true := by native_decide

end MacroEventTraceSmoke

private def expectTrue (label : String) (ok : Bool) : IO Unit := do
  if !ok then
    throw (IO.userError s!"✗ {label}")
  IO.println s!"✓ {label}"

private def contains (haystack needle : String) : Bool :=
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

private def countOccurrences (haystack needle : String) : Nat :=
  let h := haystack.toList
  let n := needle.toList
  if n.isEmpty then 0
  else
    let rec go : List Char → Nat
      | [] => 0
      | c :: cs =>
        if (c :: cs).take n.length == n then
          1 + go cs
        else
          go cs
    go h

private def selectorCount (spec : CompilationModel) : Nat :=
  (spec.functions.filter (fun fn => !fn.isInternal && fn.name != "fallback" && fn.name != "receive")).length

private def selectorsFor (spec : CompilationModel) : List Nat :=
  List.range (selectorCount spec)

private def expectCompileErrorContains (label : String)
    (spec : CompilationModel) (needle : String) : IO Unit := do
  match Compiler.CompilationModel.compile spec (selectorsFor spec) with
  | .ok _ =>
      throw (IO.userError s!"✗ {label}: expected compile failure")
  | .error msg =>
      expectTrue label (contains msg needle)

private def compileToYul (spec : CompilationModel) : Except String String := do
  let contract ← Compiler.CompilationModel.compile spec (selectorsFor spec)
  pure <| Compiler.Yul.render (Compiler.emitYulWithOptions contract {})

private def expectCompile (label : String) (spec : CompilationModel) : IO Compiler.IRContract := do
  match Compiler.CompilationModel.compile spec (selectorsFor spec) with
  | .ok contract => pure contract
  | .error err => throw (IO.userError s!"✗ {label} compile failed:\n{err}")

private def expectCompileToYul (label : String) (spec : CompilationModel) : IO String := do
  match compileToYul spec with
  | .ok yul => pure yul
  | .error err => throw (IO.userError s!"✗ {label} compile failed:\n{err}")

private def selectorSmokeSpec : CompilationModel := {
  name := "SelectorSmoke"
  fields := [{ name := "value", ty := FieldType.uint256 }]
  «constructor» := none
  functions := [
    { name := "store"
      params := [{ name := "next", ty := ParamType.uint256 }]
      returnType := none
      body := [
        Stmt.setStorage "value" (Expr.param "next"),
        Stmt.stop
      ]
    },
    { name := "load"
      params := []
      returnType := some FieldType.uint256
      body := [Stmt.return (Expr.storage "value")]
    }
  ]
}

private def envRuntimeSmokeSpec : CompilationModel := {
  name := "EnvRuntimeSmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "selfValueTimestampNumberAndChainId"
      params := []
      returnType := none
      returns := [ParamType.address, ParamType.uint256, ParamType.uint256, ParamType.uint256, ParamType.uint256, ParamType.uint256, ParamType.uint256]
      body := [
        Stmt.returnValues [Expr.contractAddress, Expr.msgValue, Expr.selfBalance, Expr.blockTimestamp, Expr.blockNumber, Expr.chainid, Expr.blobbasefee]
      ]
    }
  ]
}

private def reservedParamSpec : CompilationModel := {
  name := "ReservedParam"
  fields := [{ name := "value", ty := FieldType.uint256 }]
  «constructor» := none
  functions := [
    { name := "store"
      params := [{ name := "__has_selector", ty := ParamType.uint256 }]
      returnType := none
      body := [
        Stmt.setStorage "value" (Expr.param "__has_selector"),
        Stmt.stop
      ]
    }
  ]
}

private def duplicateInternalNameSpec : CompilationModel := {
  name := "DuplicateInternalName"
  fields := []
  «constructor» := none
  functions := [
    { name := "helper"
      params := [{ name := "amount", ty := ParamType.uint256 }]
      returnType := some FieldType.uint256
      body := [Stmt.return (Expr.param "amount")]
      isInternal := true
    },
    { name := "helper"
      params := [{ name := "target", ty := ParamType.uint256 }]
      returnType := some FieldType.uint256
      body := [Stmt.return (Expr.literal 1)]
      isInternal := true
    }
  ]
}

private def duplicateImmutableNameSpec : CompilationModel := {
  name := "DuplicateImmutableName"
  fields := []
  «immutables» := [
    { name := "cap", ty := ParamType.uint256, init := Expr.literal 1 },
    { name := "cap", ty := ParamType.uint256, init := Expr.literal 2 }
  ]
  «constructor» := none
  functions := []
}

private def uninitializedImmutableSpec : CompilationModel := {
  name := "UninitializedImmutable"
  fields := []
  «immutables» := [
    { name := "cap", ty := ParamType.uint256, init := Expr.literal 1 }
  ]
  «constructor» := some {
    params := []
    body := [Stmt.stop]
  }
  functions := [
    { name := "load"
      params := []
      returnType := some FieldType.uint256
      body := [Stmt.return (Expr.immutable "cap")]
    }
  ]
}

private def internalExternalNameCollisionSpec : CompilationModel := {
  name := "InternalExternalNameCollision"
  fields := []
  «constructor» := none
  functions := [
    { name := "helper"
      params := [{ name := "amount", ty := ParamType.uint256 }]
      returnType := some FieldType.uint256
      body := [Stmt.return (Expr.param "amount")]
    },
    { name := "helper"
      params := [{ name := "target", ty := ParamType.uint256 }]
      returnType := some FieldType.uint256
      body := [Stmt.return (Expr.literal 1)]
      isInternal := true
    }
  ]
}

private def reservedFieldSpec : CompilationModel := {
  name := "ReservedField"
  fields := [{ name := "__compat_value", ty := FieldType.uint256 }]
  «constructor» := none
  functions := [
    { name := "store"
      params := [{ name := "next", ty := ParamType.uint256 }]
      returnType := none
      body := [
        Stmt.setStorage "__compat_value" (Expr.param "next"),
        Stmt.stop
      ]
    }
  ]
}

private def reservedLocalBinderSpec : CompilationModel := {
  name := "ReservedLocalBinder"
  fields := [{ name := "value", ty := FieldType.uint256 }]
  «constructor» := none
  functions := [
    { name := "store"
      params := [{ name := "next", ty := ParamType.uint256 }]
      returnType := none
      body := [
        Stmt.letVar "__has_selector" (Expr.param "next"),
        Stmt.setStorage "value" (Expr.localVar "__has_selector"),
        Stmt.stop
      ]
    }
  ]
}

private def reservedAssignTargetSpec : CompilationModel := {
  name := "ReservedAssignTarget"
  fields := [{ name := "value", ty := FieldType.uint256 }]
  «constructor» := none
  functions := [
    { name := "store"
      params := [{ name := "next", ty := ParamType.uint256 }]
      returnType := none
      body := [
        Stmt.assignVar "__compat_value" (Expr.param "next"),
        Stmt.stop
      ]
    }
  ]
}

private def reservedConstructorParamSpec : CompilationModel := {
  name := "ReservedConstructorParam"
  fields := [{ name := "value", ty := FieldType.uint256 }]
  «constructor» := some {
    params := [{ name := "__init", ty := ParamType.uint256 }]
    body := [
      Stmt.setStorage "value" (Expr.constructorArg 0),
      Stmt.stop
    ]
  }
  functions := [
    { name := "load"
      params := []
      returnType := some FieldType.uint256
      body := [Stmt.return (Expr.storage "value")]
    }
  ]
}

private def reservedForEachBinderSpec : CompilationModel := {
  name := "ReservedForEachBinder"
  fields := [{ name := "value", ty := FieldType.uint256 }]
  «constructor» := none
  functions := [
    { name := "store"
      params := []
      returnType := none
      body := [
        Stmt.forEach "__loop_idx" (Expr.literal 1) [
          Stmt.setStorage "value" (Expr.literal 1)
        ],
        Stmt.stop
      ]
    }
  ]
}

private def reservedInternalAssignBinderSpec : CompilationModel := {
  name := "ReservedInternalAssignBinder"
  fields := [{ name := "value", ty := FieldType.uint256 }]
  «constructor» := none
  functions := [
    { name := "helper"
      params := [{ name := "next", ty := ParamType.uint256 }]
      returnType := some FieldType.uint256
      body := [Stmt.return (Expr.param "next")]
      isInternal := true
    },
    { name := "store"
      params := [{ name := "next", ty := ParamType.uint256 }]
      returnType := none
      body := [
        Stmt.internalCallAssign ["__ret"] "helper" [Expr.param "next"],
        Stmt.setStorage "value" (Expr.localVar "__ret"),
        Stmt.stop
      ]
    }
  ]
}

private def reservedExternalBindSpec : CompilationModel := {
  name := "ReservedExternalBind"
  fields := [{ name := "value", ty := FieldType.uint256 }]
  «constructor» := none
  functions := [
    { name := "store"
      params := [{ name := "next", ty := ParamType.uint256 }]
      returnType := none
      body := [
        Stmt.externalCallBind ["__external_ret"] "echo" [Expr.param "next"],
        Stmt.setStorage "value" (Expr.localVar "__external_ret"),
        Stmt.stop
      ]
    }
  ]
  externals := [
    { name := "echo"
      params := [ParamType.uint256]
      returnType := some ParamType.uint256
      returns := [ParamType.uint256]
      axiomNames := ["echo_matches_identity"]
    }
  ]
}

private def effectOnlyExternalBindSpec : CompilationModel := {
  name := "EffectOnlyExternalBind"
  fields := []
  «constructor» := none
  functions := [
    { name := "poke"
      params := [{ name := "next", ty := ParamType.uint256 }]
      returnType := none
      reentrancyTrusted := true
      body := [
        Stmt.externalCallBind [] "notify" [Expr.param "next"],
        Stmt.stop
      ]
    }
  ]
  externals := [
    { name := "notify"
      params := [ParamType.uint256]
      returnType := none
      returns := []
      axiomNames := ["notify_effect_only"]
    }
  ]
}

private def effectOnlyExternalBindMismatchSpec : CompilationModel := {
  name := "EffectOnlyExternalBindMismatch"
  fields := []
  «constructor» := none
  functions := [
    { name := "store"
      params := [{ name := "next", ty := ParamType.uint256 }]
      returnType := none
      body := [
        Stmt.externalCallBind [] "echo" [Expr.param "next"],
        Stmt.stop
      ]
    }
  ]
  externals := [
    { name := "echo"
      params := [ParamType.uint256]
      returnType := some ParamType.uint256
      returns := [ParamType.uint256]
      axiomNames := ["echo_matches_identity"]
    }
  ]
}

private def reservedBuiltinExpExternalSpec : CompilationModel := {
  name := "ReservedBuiltinExpExternal"
  fields := []
  «constructor» := none
  functions := [
    { name := "scale"
      params := [{ name := "exponent", ty := ParamType.uint256 }]
      returnType := some FieldType.uint256
      body := [Stmt.return (Expr.externalCall builtinExpName [Expr.literal 10, Expr.param "exponent"])]
    }
  ]
  externals := [
    { name := builtinExpName
      params := [ParamType.uint256, ParamType.uint256]
      returnType := some ParamType.uint256
      returns := [ParamType.uint256]
      axiomNames := ["malicious_shadow_exp"]
    }
  ]
}

private def rawLogTraceSmokeSpec : CompilationModel := {
  name := "RawLogTraceSmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "emitDynamicLog"
      params := [
        { name := "topic0", ty := ParamType.uint256 },
        { name := "topic1", ty := ParamType.uint256 },
        { name := "dataOffset", ty := ParamType.uint256 },
        { name := "dataSize", ty := ParamType.uint256 }
      ]
      returnType := none
      body := MacroEventTraceSmoke.MacroEventTrace.emitDynamicLog_modelBody
    }
  ]
}

private def rawLogTooManyTopicsSpec : CompilationModel := {
  name := "RawLogTooManyTopics"
  fields := []
  «constructor» := none
  functions := [
    { name := "bad"
      params := []
      returnType := none
      body := [
        Stmt.rawLog
          [Expr.literal 1, Expr.literal 2, Expr.literal 3, Expr.literal 4, Expr.literal 5]
          (Expr.literal 0)
          (Expr.literal 32),
        Stmt.stop
      ]
    }
  ]
}

private def rawRevertSmokeSpec : CompilationModel := {
  name := "RawRevertSmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "fail"
      params := [
        { name := "offset", ty := ParamType.uint256 },
        { name := "size", ty := ParamType.uint256 }
      ]
      returnType := none
      body := [
        Stmt.unsafeYul
          (UnsafeYulFragment.rawRevert
            (Compiler.Yul.YulExpr.ident "offset")
            (Compiler.Yul.YulExpr.ident "size")
            { name := "raw_revert_memory_slice_refinement"
              obligation := "Caller-provided raw revert memory slice must refine the intended failure payload."
              proofStatus := .assumed })
      ]
    }
  ]
}

private def unsafeYulScopeObligation (name : String) : LocalObligation :=
  { name := name
    obligation := "Raw Yul scope effects must conservatively describe the Yul payload."
    proofStatus := .assumed }

private def unsafeYulRawCallExpr : Compiler.Yul.YulExpr :=
  Compiler.Yul.YulExpr.call "call" [
    Compiler.Yul.YulExpr.lit 5000,
    Compiler.Yul.YulExpr.lit 0,
    Compiler.Yul.YulExpr.lit 0,
    Compiler.Yul.YulExpr.lit 0,
    Compiler.Yul.YulExpr.lit 0,
    Compiler.Yul.YulExpr.lit 0,
    Compiler.Yul.YulExpr.lit 0
  ]

private def unsafeYulRawCallStmt : Stmt :=
  Stmt.unsafeYul {
    label := "raw_yul_call"
    stmts := [Compiler.Yul.YulStmt.expr unsafeYulRawCallExpr]
    obligations := [unsafeYulScopeObligation "raw_yul_call_obligation"]
  }

private def unsafeYulRawCallAllowedSpec : CompilationModel := {
  name := "UnsafeYulRawCallAllowed"
  fields := []
  «constructor» := none
  functions := [
    { name := "bad"
      params := []
      returnType := none
      reentrancyTrusted := true
      body := [unsafeYulRawCallStmt, Stmt.stop]
    }
  ]
}

def unsafeYulRawCallPropagatesCEI : Bool :=
  match stmtListCEIViolation [
      unsafeYulRawCallStmt,
      Stmt.setStorage "value" (Expr.literal 1)
    ] false with
  | some msg => contains msg "state write after external call"
  | none => false

example : unsafeYulRawCallPropagatesCEI = true := by native_decide

private def unsafeYulUnderDeclaredBindSpec : CompilationModel := {
  name := "UnsafeYulUnderDeclaredBind"
  fields := []
  «constructor» := none
  functions := [
    { name := "bad"
      params := []
      returnType := none
      body := [
        Stmt.unsafeYul {
          label := "under_declared_bind"
          stmts := [Compiler.Yul.YulStmt.let_ "tmp" (Compiler.Yul.YulExpr.lit 1)]
          obligations := [unsafeYulScopeObligation "under_declared_bind_obligation"]
        }
      ]
    }
  ]
}

private def unsafeYulUnderDeclaredAssignSpec : CompilationModel := {
  name := "UnsafeYulUnderDeclaredAssign"
  fields := []
  «constructor» := none
  functions := [
    { name := "bad"
      params := []
      returnType := none
      body := [
        Stmt.letVar "tmp" (Expr.literal 0),
        Stmt.unsafeYul {
          label := "under_declared_assign"
          stmts := [Compiler.Yul.YulStmt.assign "tmp" (Compiler.Yul.YulExpr.lit 1)]
          obligations := [unsafeYulScopeObligation "under_declared_assign_obligation"]
        }
      ]
    }
  ]
}

private def unsafeYulUnderDeclaredStorageSpec : CompilationModel := {
  name := "UnsafeYulUnderDeclaredStorage"
  fields := [{ name := "value", ty := FieldType.uint256 }]
  «constructor» := none
  functions := [
    { name := "bad"
      params := []
      returnType := none
      body := [
        Stmt.unsafeYul {
          label := "under_declared_storage"
          stmts := [
            Compiler.Yul.YulStmt.expr
              (Compiler.Yul.YulExpr.call "sstore" [Compiler.Yul.YulExpr.lit 0, Compiler.Yul.YulExpr.lit 1])
          ]
          obligations := [unsafeYulScopeObligation "under_declared_storage_obligation"]
        }
      ]
    }
  ]
}

private def unsafeYulTstoreMechanicViewRejectedSpec : CompilationModel := {
  name := "UnsafeYulTstoreMechanicViewRejected"
  fields := []
  «constructor» := none
  functions := [
    { name := "bad"
      params := []
      returnType := none
      isView := true
      body := [
        Stmt.unsafeYul {
          label := "declared_tstore_mechanic"
          stmts := [Compiler.Yul.YulStmt.comment "mechanic-only tstore boundary"]
          obligations := [unsafeYulScopeObligation "declared_tstore_mechanic_obligation"]
          mechanics := [.tstore]
        }
      ]
    }
  ]
}

private def matchAdtAllBranchesTerminateSpec : CompilationModel := {
  name := "MatchAdtAllBranchesTerminate"
  fields := [{ name := "choice", ty := FieldType.adt "Choice" 1 }]
  «constructor» := none
  functions := [
    { name := "pick"
      params := []
      returnType := some FieldType.uint256
      body := [
        Stmt.matchAdt "Choice" (Expr.adtTag "Choice" "choice") [
          ("None", [], [Stmt.return (Expr.literal 0)]),
          ("Some", ["amount"], [Stmt.return (Expr.localVar "amount")])
        ]
      ]
    }
  ]
  adtTypes := [
    { name := "Choice"
      variants := [
        { name := "None", tag := 0, fields := [] },
        { name := "Some", tag := 1, fields := [{ name := "amount", ty := ParamType.uint256 }] }
      ]
    }
  ]
}

private def returnValueStopRejectedSpec : CompilationModel := {
  name := "ReturnValueStopRejected"
  fields := []
  «constructor» := none
  functions := [
    { name := "bad"
      params := []
      returnType := some FieldType.uint256
      body := [Stmt.stop]
    }
  ]
}

private def reservedEcmResultVarSpec : CompilationModel := {
  name := "ReservedEcmResultVar"
  fields := [{ name := "value", ty := FieldType.uint256 }]
  «constructor» := none
  functions := [
    { name := "store"
      params := []
      returnType := none
      body := [
        Stmt.ecm
          { name := "reservedResult"
            numArgs := 0
            resultVars := ["__ecm_result"]
            writesState := false
            readsState := false
            compile := fun _ _ => pure []
          }
          [],
        Stmt.setStorage "value" (Expr.localVar "__ecm_result"),
        Stmt.stop
      ]
    }
  ]
}

private def stringAbiSpec : CompilationModel := {
  name := "StringABI"
  fields := []
  «constructor» := none
  functions := [
    { name := "echo"
      params := [{ name := "message", ty := ParamType.string }]
      returnType := none
      returns := [ParamType.string]
      body := [Stmt.returnBytes "message"]
    }
    , { name := "echoAfterUint"
        params := [{ name := "tag", ty := ParamType.uint256 }, { name := "message", ty := ParamType.string }]
        returnType := none
        returns := [ParamType.string]
        body := [Stmt.returnBytes "message"]
      }
    , { name := "echoBeforeUint"
        params := [{ name := "message", ty := ParamType.string }, { name := "tag", ty := ParamType.uint256 }]
        returnType := none
        returns := [ParamType.string]
        body := [Stmt.returnBytes "message"]
      }
    , { name := "echoSecondString"
        params := [{ name := "prefix", ty := ParamType.string }, { name := "message", ty := ParamType.string }]
        returnType := none
        returns := [ParamType.string]
        body := [Stmt.returnBytes "message"]
      }
  ]
  events := [
    { name := "MessageLogged"
      params := [{ name := "message", ty := ParamType.string, kind := EventParamKind.unindexed }]
    }
    , { name := "TaggedMessageLogged"
        params := [
          { name := "tag", ty := ParamType.uint256, kind := EventParamKind.indexed }
        , { name := "message", ty := ParamType.string, kind := EventParamKind.unindexed }
        ]
      }
    , { name := "IndexedMessageLogged"
        params := [{ name := "message", ty := ParamType.string, kind := EventParamKind.indexed }]
      }
    , { name := "SecondMessageLogged"
        params := [
          { name := "prefix", ty := ParamType.string, kind := EventParamKind.unindexed }
        , { name := "message", ty := ParamType.string, kind := EventParamKind.unindexed }
        ]
      }
  ]
  «errors» := [
    { name := "BadMessage"
      params := [ParamType.string]
    }
    , { name := "TaggedMessage"
        params := [ParamType.uint256, ParamType.string]
      }
    , { name := "SecondMessage"
        params := [ParamType.string, ParamType.string]
      }
  ]
}

private def stringReturnMismatchSpec : CompilationModel := {
  name := "StringReturnMismatch"
  fields := []
  «constructor» := none
  functions := [
    { name := "echo"
      params := [{ name := "message", ty := ParamType.bytes }]
      returnType := none
      returns := [ParamType.string]
      body := [Stmt.returnBytes "message"]
    }
  ]
}

private def stringEventMismatchSpec : CompilationModel := {
  name := "StringEventMismatch"
  fields := []
  «constructor» := none
  functions := [
    { name := "log"
      params := [{ name := "message", ty := ParamType.bytes }]
      returnType := none
      body := [Stmt.emit "MessageLogged" [Expr.param "message"], Stmt.stop]
    }
  ]
  events := [
    { name := "MessageLogged"
      params := [{ name := "message", ty := ParamType.string, kind := EventParamKind.unindexed }]
    }
  ]
}

private def memoryArrayEventSourceSpec : CompilationModel := {
  name := "MemoryArrayEventSource"
  fields := []
  «constructor» := none
  functions := [
    { name := "log"
      params := []
      returnType := none
      body := [
        Stmt.letVar "values_length" (Expr.literal 2),
        Stmt.letVar "values_data_offset" (Expr.literal 128),
        Stmt.emit "Amounts" [Expr.memoryArrayLength "values"],
        Stmt.stop
      ]
    }
  ]
  events := [
    { name := "Amounts"
      params := [{ name := "values", ty := ParamType.array ParamType.uint256, kind := EventParamKind.unindexed }]
    }
  ]
}

private def projectedArrayEventSourceSpec : CompilationModel := {
  name := "ProjectedArrayEventSource"
  fields := []
  «constructor» := none
  functions := [
    { name := "log"
      params := [{ name := "payload", ty := ParamType.tuple [ParamType.array ParamType.uint256] }]
      returnType := none
      body := [
        Stmt.emit "Amounts" [Expr.paramDynamicMemberLength "payload" 0],
        Stmt.stop
      ]
    }
  ]
  events := [
    { name := "Amounts"
      params := [{ name := "values", ty := ParamType.array ParamType.uint256, kind := EventParamKind.unindexed }]
    }
  ]
}

private def projectedStaticCompositeEventSourceSpec : CompilationModel := {
  name := "ProjectedStaticCompositeEventSource"
  fields := []
  «constructor» := none
  functions := [
    { name := "log"
      params := [
        { name := "payload",
          ty := ParamType.tuple [
            ParamType.tuple [ParamType.uint256, ParamType.address, ParamType.uint256],
            ParamType.array ParamType.uint256
          ] }
      ]
      returnType := none
      body := [
        Stmt.emit "NoteLogged" [Expr.paramDynamicStaticComposite "payload" 0],
        Stmt.stop
      ]
    }
  ]
  events := [
    { name := "NoteLogged"
      params := [
        { name := "note",
          ty := ParamType.tuple [ParamType.uint256, ParamType.address, ParamType.uint256],
          kind := EventParamKind.unindexed }
      ]
    }
  ]
}

private def eventEncodingRegressionSpec : CompilationModel := {
  name := "EventEncodingRegression"
  fields := []
  «constructor» := none
  functions := [
    { name := "log"
      params := [
        { name := "choice", ty := ParamType.adt "Choice" 2 },
        { name := "who", ty := ParamType.newtypeOf "SafeAddress" ParamType.address }
      ]
      returnType := none
      body := [
        Stmt.emit "ChoiceStored" [Expr.param "choice"],
        Stmt.emit "ChoiceIndexed" [Expr.param "choice"],
        Stmt.emit "WhoIndexed" [Expr.param "who"],
        Stmt.stop
      ]
    }
  ]
  events := [
    { name := "ChoiceStored"
      params := [{ name := "choice", ty := ParamType.adt "Choice" 2, kind := EventParamKind.unindexed }]
    },
    { name := "ChoiceIndexed"
      params := [{ name := "choice", ty := ParamType.adt "Choice" 2, kind := EventParamKind.indexed }]
    },
    { name := "WhoIndexed"
      params := [{ name := "who", ty := ParamType.newtypeOf "SafeAddress" ParamType.address, kind := EventParamKind.indexed }]
    }
  ]
  adtTypes := [
    { name := "Choice"
      variants := [
        { name := "None", tag := 0, fields := [] },
        { name := "Some", tag := 1, fields := [
          { name := "amount", ty := ParamType.uint256 },
          { name := "recipient", ty := ParamType.address }
        ] }
      ]
    }
  ]
}

private def adtParamPayloadNameCollisionSpec : CompilationModel := {
  name := "AdtParamPayloadNameCollision"
  fields := []
  «constructor» := none
  functions := [
    { name := "store"
      params := [
        { name := "choice", ty := ParamType.adt "Choice" 1 },
        { name := "choice_f0", ty := ParamType.uint256 }
      ]
      returnType := none
      body := [Stmt.stop]
    }
  ]
  adtTypes := [
    { name := "Choice"
      variants := [
        { name := "None", tag := 0, fields := [] },
        { name := "Some", tag := 1, fields := [{ name := "amount", ty := ParamType.uint256 }] }
      ]
    }
  ]
}

private def adtAliasPayloadReservedSlotSpec : CompilationModel := {
  name := "AdtAliasPayloadReservedSlot"
  fields := [
    { name := "choice", ty := FieldType.adt "Choice" 2, «slot» := some 10, aliasSlots := [100] }
  ]
  reservedSlotRanges := [{ start := 101, end_ := 101 }]
  «constructor» := none
  functions := [
    { name := "noop"
      params := []
      returnType := none
      body := [Stmt.stop]
    }
  ]
  adtTypes := [
    { name := "Choice"
      variants := [
        { name := "None", tag := 0, fields := [] },
        { name := "Some", tag := 1, fields := [
          { name := "amount", ty := ParamType.uint256 },
          { name := "recipient", ty := ParamType.address }
        ] }
      ]
    }
  ]
}

private def adtAliasPayloadMemoizesExprSpec : CompilationModel := {
  name := "AdtAliasPayloadMemoizesExpr"
  fields := [
    { name := "choice", ty := FieldType.adt "Choice" 1, «slot» := some 10, aliasSlots := [100] }
  ]
  «constructor» := none
  functions := [
    { name := "store"
      params := [{ name := "input", ty := ParamType.uint256 }]
      returnType := none
      allowPostInteractionWrites := true
      reentrancyTrusted := true
      body := [
        Stmt.setStorage "choice"
          (Expr.adtConstruct "Choice" "Some" [Expr.externalCall "echo" [Expr.param "input"]]),
        Stmt.stop
      ]
    }
  ]
  externals := [
    { name := "echo"
      params := [ParamType.uint256]
      returnType := some ParamType.uint256
      returns := [ParamType.uint256]
      axiomNames := ["echo_matches_identity"]
    }
  ]
  adtTypes := [
    { name := "Choice"
      variants := [
        { name := "None", tag := 0, fields := [] },
        { name := "Some", tag := 1, fields := [{ name := "amount", ty := ParamType.uint256 }] }
      ]
    }
  ]
}

private def ceiInitialInternalCallAllowedSpec : CompilationModel := {
  name := "CEIInitialInternalCallAllowed"
  fields := [{ name := "value", ty := FieldType.uint256 }]
  «constructor» := none
  functions := [
    { name := "helper"
      params := []
      returnType := none
      isInternal := true
      body := [Stmt.setStorage "value" (Expr.literal 1), Stmt.stop]
    },
    { name := "run"
      params := []
      returnType := none
      body := [Stmt.internalCall "helper" [], Stmt.stop]
    }
  ]
}

private def viewInternalReadInferenceSpec : CompilationModel := {
  name := "ViewInternalReadInference"
  fields := [{ name := "value", ty := FieldType.uint256 }]
  «constructor» := none
  functions := [
    { name := "helper"
      params := []
      returnType := some FieldType.uint256
      isInternal := true
      body := [Stmt.return (Expr.storage "value")]
    },
    { name := "peek"
      params := []
      returnType := some FieldType.uint256
      isView := true
      body := [Stmt.return (Expr.internalCall "helper" [])]
    }
  ]
}

private def viewInternalWriteRejectedSpec : CompilationModel := {
  name := "ViewInternalWriteRejected"
  fields := [{ name := "value", ty := FieldType.uint256 }]
  «constructor» := none
  functions := [
    { name := "helper"
      params := []
      returnType := none
      isInternal := true
      body := [Stmt.setStorage "value" (Expr.literal 1), Stmt.stop]
    },
    { name := "peek"
      params := []
      returnType := none
      isView := true
      body := [Stmt.internalCall "helper" [], Stmt.stop]
    }
  ]
}

private def pureInternalCallInferenceSpec : CompilationModel := {
  name := "PureInternalCallInference"
  fields := []
  «constructor» := none
  functions := [
    { name := "helper"
      params := [{ name := "value", ty := ParamType.uint256 }]
      returnType := some FieldType.uint256
      isInternal := true
      body := [Stmt.return (Expr.add (Expr.param "value") (Expr.literal 1))]
    },
    { name := "next"
      params := [{ name := "value", ty := ParamType.uint256 }]
      returnType := some FieldType.uint256
      isPure := true
      body := [Stmt.return (Expr.internalCall "helper" [Expr.param "value"])]
    }
  ]
}

private def pureInternalReadRejectedSpec : CompilationModel := {
  name := "PureInternalReadRejected"
  fields := [{ name := "value", ty := FieldType.uint256 }]
  «constructor» := none
  functions := [
    { name := "helper"
      params := []
      returnType := some FieldType.uint256
      isInternal := true
      body := [Stmt.return (Expr.storage "value")]
    },
    { name := "peek"
      params := []
      returnType := some FieldType.uint256
      isPure := true
      body := [Stmt.return (Expr.internalCall "helper" [])]
    }
  ]
}

private def ceiEcmWriteAfterCallRejectedSpec : CompilationModel := {
  name := "CEIEcmWriteAfterCallRejected"
  fields := [{ name := "value", ty := FieldType.uint256 }]
  «constructor» := none
  functions := [
    { name := "run"
      params := []
      returnType := none
      body := [
        Stmt.externalCallBind [] "notify" [],
        Stmt.ecm
          { name := "writeEffect"
            numArgs := 0
            resultVars := []
            writesState := true
            readsState := false
            compile := fun _ _ => pure []
          }
          [],
        Stmt.stop
      ]
    }
  ]
}

private def addressArrayReturnSpec : CompilationModel := {
  name := "AddressArrayReturn"
  fields := []
  «constructor» := none
  functions := [
    { name := "echo"
      params := [{ name := "recipients", ty := ParamType.array ParamType.address }]
      returnType := none
      returns := [ParamType.array ParamType.address]
      body := [Stmt.returnArray "recipients"]
    }
  ]
}

private def internalAddressArrayReturnSpec : CompilationModel := {
  name := "InternalAddressArrayReturn"
  fields := []
  «constructor» := none
  functions := [
    { name := "echoArray"
      params := [{ name := "recipients", ty := ParamType.array ParamType.address }]
      returnType := none
      returns := [ParamType.array ParamType.address]
      body := [Stmt.returnArray "recipients"]
      isInternal := true
    },
    { name := "countEchoed"
      params := [{ name := "recipients", ty := ParamType.array ParamType.address }]
      returnType := some FieldType.address
      body := [
        Stmt.internalCallAssign
          ["echoed_data_offset", "echoed_length"]
          "echoArray"
          [Expr.param "recipients_data_offset", Expr.param "recipients_length"],
        Stmt.return (Expr.memoryArrayElement "echoed" (Expr.literal 0))
      ]
    }
  ]
}

private def addressStorageWordReturnSpec : CompilationModel := {
  name := "AddressStorageWordReturn"
  fields := []
  «constructor» := none
  functions := [
    { name := "extSloadsLike"
      params := [{ name := "slots", ty := ParamType.array ParamType.address }]
      returnType := none
      returns := [ParamType.array ParamType.uint256]
      body := [Stmt.returnStorageWords "slots"]
    }
  ]
}

private def boolStorageWordReturnSpec : CompilationModel := {
  name := "BoolStorageWordReturn"
  fields := []
  «constructor» := none
  functions := [
    { name := "extSloadsLike"
      params := [{ name := "slots", ty := ParamType.array ParamType.bool }]
      returnType := none
      returns := [ParamType.array ParamType.uint256]
      body := [Stmt.returnStorageWords "slots"]
    }
  ]
}

private def bytesStorageWordReturnSpec : CompilationModel := {
  name := "BytesStorageWordReturn"
  fields := []
  «constructor» := none
  functions := [
    { name := "extSloadsLike"
      params := [{ name := "slots", ty := ParamType.array ParamType.bytes }]
      returnType := none
      returns := [ParamType.array ParamType.uint256]
      body := [Stmt.returnStorageWords "slots"]
    }
  ]
}

private def bytesArrayReturnSpec : CompilationModel := {
  name := "BytesArrayReturn"
  fields := []
  «constructor» := none
  functions := [
    { name := "echo"
      params := [{ name := "calls", ty := ParamType.array ParamType.bytes }]
      returnType := none
      returns := [ParamType.array ParamType.bytes]
      body := [Stmt.returnArray "calls"]
    }
  ]
}

private def bytesArrayElementSpec : CompilationModel := {
  name := "BytesArrayElement"
  fields := []
  «constructor» := none
  functions := [
    { name := "headWord"
      params := [{ name := "calls", ty := ParamType.array ParamType.bytes }]
      returnType := some FieldType.uint256
      body := [Stmt.return (Expr.arrayElement "calls" (Expr.literal 0))]
    }
  ]
}

private def bytesArrayElementWordSpec : CompilationModel := {
  name := "BytesArrayElementWord"
  fields := []
  «constructor» := none
  functions := [
    { name := "headWord"
      params := [{ name := "calls", ty := ParamType.array ParamType.bytes }]
      returnType := some FieldType.uint256
      body := [Stmt.return (Expr.arrayElementWord "calls" (Expr.literal 0) 1 0)]
    }
  ]
}

private def uintArrayElementOnlySpec : CompilationModel := {
  name := "UintArrayElementOnly"
  fields := []
  «constructor» := none
  functions := [
    { name := "head"
      params := [{ name := "values", ty := ParamType.array ParamType.uint256 }]
      returnType := some FieldType.uint256
      body := [Stmt.return (Expr.arrayElement "values" (Expr.literal 0))]
    }
  ]
}

private def uintArrayForEachAccumulatorSpec : CompilationModel := {
  name := "UintArrayForEachAccumulator"
  fields := []
  «constructor» := none
  functions := [
    { name := "sum"
      params := [{ name := "values", ty := ParamType.array ParamType.uint256 }]
      returnType := some FieldType.uint256
      body := [
        Stmt.letVar "total" (Expr.literal 0),
        Stmt.forEach "i" (Expr.arrayLength "values") [
          Stmt.letVar "value" (Expr.arrayElement "values" (Expr.localVar "i")),
          Stmt.assignVar "total" (Expr.add (Expr.localVar "total") (Expr.localVar "value"))
        ],
        Stmt.return (Expr.localVar "total")
      ]
    }
  ]
}

private def tupleArrayElementWordOnlySpec : CompilationModel := {
  name := "TupleArrayElementWordOnly"
  fields := []
  «constructor» := none
  functions := [
    { name := "second"
      params := [{ name := "values", ty := ParamType.array (ParamType.tuple [ParamType.uint256, ParamType.uint256]) }]
      returnType := some FieldType.uint256
      body := [Stmt.return (Expr.arrayElementWord "values" (Expr.literal 0) 2 1)]
    }
  ]
}

private def arrayElementWordStorageIndexSpec : CompilationModel := {
  name := "ArrayElementWordStorageIndex"
  fields := [{ name := "queue", ty := FieldType.dynamicArray .uint256, «slot» := some 7 }]
  «constructor» := none
  functions := [
    { name := "selected"
      params := [{ name := "values", ty := ParamType.array (ParamType.tuple [ParamType.uint256, ParamType.uint256]) }]
      returnType := some FieldType.uint256
      body := [
        Stmt.return
          (Expr.arrayElementWord "values"
            (Expr.storageArrayElement "queue" (Expr.literal 0)) 2 1)
      ]
    }
  ]
}

private def storageArrayUint256SmokeSpec : CompilationModel := {
  name := "StorageArrayUint256Smoke"
  fields := [{ name := "queue", ty := FieldType.dynamicArray .uint256, «slot» := some 7 }]
  «constructor» := none
  functions := [
    { name := "size"
      params := []
      returnType := some FieldType.uint256
      body := [Stmt.return (Expr.storageArrayLength "queue")]
    },
    { name := "head"
      params := []
      returnType := some FieldType.uint256
      body := [Stmt.return (Expr.storageArrayElement "queue" (Expr.literal 0))]
    },
    { name := "enqueue"
      params := [{ name := "value", ty := ParamType.uint256 }]
      returnType := none
      body := [Stmt.storageArrayPush "queue" (Expr.param "value"), Stmt.stop]
    },
    { name := "setHead"
      params := [{ name := "value", ty := ParamType.uint256 }]
      returnType := none
      body := [Stmt.setStorageArrayElement "queue" (Expr.literal 0) (Expr.param "value"), Stmt.stop]
    },
    { name := "dequeue"
      params := []
      returnType := none
      body := [Stmt.storageArrayPop "queue", Stmt.stop]
    }
  ]
}

private def storageArrayBoolSmokeSpec : CompilationModel := {
  name := "StorageArrayBoolSmoke"
  fields := [{ name := "flags", ty := FieldType.dynamicArray .bool, «slot» := some 9 }]
  «constructor» := none
  functions := [
    { name := "firstFlag"
      params := []
      returnType := none
      returns := [ParamType.bool]
      body := [Stmt.return (Expr.storageArrayElement "flags" (Expr.literal 0))]
    },
    { name := "pushFlag"
      params := [{ name := "flag", ty := ParamType.bool }]
      returnType := none
      body := [Stmt.storageArrayPush "flags" (Expr.param "flag"), Stmt.stop]
    },
    { name := "setFirstFlag"
      params := [{ name := "flag", ty := ParamType.bool }]
      returnType := none
      body := [Stmt.setStorageArrayElement "flags" (Expr.literal 0) (Expr.param "flag"), Stmt.stop]
    }
  ]
}

private def ecrecoverSmokeSpec : CompilationModel := {
  name := "EcrecoverSmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "recover"
      params := [
        { name := "hash", ty := ParamType.bytes32 }
        , { name := "v", ty := ParamType.uint256 }
        , { name := "r", ty := ParamType.bytes32 }
        , { name := "s", ty := ParamType.bytes32 }
      ]
      returnType := none
      returns := [ParamType.address]
      body := [
        Compiler.Modules.Precompiles.ecrecover
          "signer"
          (Expr.param "hash")
          (Expr.param "v")
          (Expr.param "r")
          (Expr.param "s"),
        Stmt.returnValues [Expr.localVar "signer"]
      ]
    }
  ]
}

private def sha256MemorySmokeSpec : CompilationModel := {
  name := "Sha256MemorySmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "hash"
      params := [
        { name := "inputOffset", ty := ParamType.uint256 }
        , { name := "inputSize", ty := ParamType.uint256 }
        , { name := "outputOffset", ty := ParamType.uint256 }
      ]
      returnType := none
      returns := [ParamType.bytes32]
      body := [
        Compiler.Modules.Precompiles.sha256
          "digest"
          (Expr.param "inputOffset")
          (Expr.param "inputSize")
          (Expr.param "outputOffset"),
        Stmt.returnValues [Expr.localVar "digest"]
      ]
    }
  ]
}

private def sha256MemoryTwiceSmokeSpec : CompilationModel := {
  name := "Sha256MemoryTwiceSmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "hashBoth"
      params := [
        { name := "inputOffset", ty := ParamType.uint256 }
        , { name := "inputSize", ty := ParamType.uint256 }
        , { name := "firstOutputOffset", ty := ParamType.uint256 }
        , { name := "secondOutputOffset", ty := ParamType.uint256 }
      ]
      returnType := none
      returns := [ParamType.bytes32, ParamType.bytes32]
      body := [
        Compiler.Modules.Precompiles.sha256
          "firstDigest"
          (Expr.param "inputOffset")
          (Expr.param "inputSize")
          (Expr.param "firstOutputOffset"),
        Compiler.Modules.Precompiles.sha256
          "secondDigest"
          (Expr.param "inputOffset")
          (Expr.param "inputSize")
          (Expr.param "secondOutputOffset"),
        Stmt.returnValues [Expr.localVar "firstDigest", Expr.localVar "secondDigest"]
      ]
    }
  ]
}

private def bn256AddSmokeSpec : CompilationModel := {
  name := "Bn256AddSmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "add"
      params := [
        { name := "x1", ty := ParamType.uint256 }
        , { name := "y1", ty := ParamType.uint256 }
        , { name := "x2", ty := ParamType.uint256 }
        , { name := "y2", ty := ParamType.uint256 }
      ]
      returnType := none
      returns := [ParamType.uint256, ParamType.uint256]
      body := [
        Compiler.Modules.Precompiles.bn256Add
          "x3" "y3"
          (Expr.param "x1") (Expr.param "y1")
          (Expr.param "x2") (Expr.param "y2"),
        Stmt.returnValues [Expr.localVar "x3", Expr.localVar "y3"]
      ]
    }
  ]
}

private def bn256AddBadAritySpec : CompilationModel := {
  name := "Bn256AddBadArity"
  fields := []
  «constructor» := none
  functions := [
    { name := "bad"
      params := [{ name := "x1", ty := ParamType.uint256 }]
      returnType := none
      body := [
        Stmt.ecm (Compiler.Modules.Precompiles.bn256AddModule "x3" "y3")
          [Expr.param "x1"],
        Stmt.stop
      ]
    }
  ]
}

private def bn256ScalarMulSmokeSpec : CompilationModel := {
  name := "Bn256ScalarMulSmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "mul"
      params := [
        { name := "x", ty := ParamType.uint256 }
        , { name := "y", ty := ParamType.uint256 }
        , { name := "k", ty := ParamType.uint256 }
      ]
      returnType := none
      returns := [ParamType.uint256, ParamType.uint256]
      body := [
        Compiler.Modules.Precompiles.bn256ScalarMul
          "x2" "y2"
          (Expr.param "x") (Expr.param "y") (Expr.param "k"),
        Stmt.returnValues [Expr.localVar "x2", Expr.localVar "y2"]
      ]
    }
  ]
}

private def bn256ScalarMulBadAritySpec : CompilationModel := {
  name := "Bn256ScalarMulBadArity"
  fields := []
  «constructor» := none
  functions := [
    { name := "bad"
      params := [{ name := "x", ty := ParamType.uint256 }]
      returnType := none
      body := [
        Stmt.ecm (Compiler.Modules.Precompiles.bn256ScalarMulModule "x2" "y2")
          [Expr.param "x"],
        Stmt.stop
      ]
    }
  ]
}

private def bn256PairingSmokeSpec : CompilationModel := {
  name := "Bn256PairingSmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "pair"
      params := [
        { name := "inputOffset", ty := ParamType.uint256 }
        , { name := "inputSize", ty := ParamType.uint256 }
        , { name := "outputOffset", ty := ParamType.uint256 }
      ]
      returnType := none
      returns := [ParamType.uint256]
      body := [
        Compiler.Modules.Precompiles.bn256Pairing
          "ok"
          (Expr.param "inputOffset")
          (Expr.param "inputSize")
          (Expr.param "outputOffset"),
        Stmt.returnValues [Expr.localVar "ok"]
      ]
    }
  ]
}

private def bn256PairingBadAritySpec : CompilationModel := {
  name := "Bn256PairingBadArity"
  fields := []
  «constructor» := none
  functions := [
    { name := "bad"
      params := [{ name := "inputOffset", ty := ParamType.uint256 }]
      returnType := none
      body := [
        Stmt.ecm (Compiler.Modules.Precompiles.bn256PairingModule "ok")
          [Expr.param "inputOffset"],
        Stmt.stop
      ]
    }
  ]
}

private def abiEncodePackedWordsSmokeSpec : CompilationModel := {
  name := "AbiEncodePackedWordsSmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "hash"
      params := [
        { name := "a", ty := ParamType.bytes32 }
        , { name := "b", ty := ParamType.bytes32 }
        , { name := "c", ty := ParamType.bytes32 }
      ]
      returnType := none
      returns := [ParamType.bytes32]
      body := [
        Compiler.Modules.Hashing.abiEncodePacked
          "digest"
          [Expr.param "a", Expr.param "b", Expr.param "c"],
        Stmt.returnValues [Expr.localVar "digest"]
      ]
    }
  ]
}

private def sha256PackedWordsSmokeSpec : CompilationModel := {
  name := "Sha256PackedWordsSmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "hash"
      params := [
        { name := "root", ty := ParamType.bytes32 }
        , { name := "context", ty := ParamType.bytes32 }
      ]
      returnType := none
      returns := [ParamType.bytes32]
      body := [
        Compiler.Modules.Hashing.sha256Packed
          "digest"
          [Expr.param "root", Expr.param "context"],
        Stmt.returnValues [Expr.localVar "digest"]
      ]
    }
  ]
}

private def abiEncodeStaticWordsSmokeSpec : CompilationModel := {
  name := "AbiEncodeStaticWordsSmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "hash"
      params := [
        { name := "marketId", ty := ParamType.bytes32 }
        , { name := "assets", ty := ParamType.uint256 }
        , { name := "shares", ty := ParamType.uint256 }
      ]
      returnType := none
      returns := [ParamType.bytes32]
      body := [
        Compiler.Modules.Hashing.abiEncodeStaticWords
          "digest"
          [Expr.param "marketId", Expr.param "assets", Expr.param "shares"],
        Stmt.returnValues [Expr.localVar "digest"]
      ]
    }
  ]
}

private def abiEncodeStaticArraySmokeSpec : CompilationModel := {
  name := "AbiEncodeStaticArraySmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "hash"
      params := [
        { name := "items", ty := ParamType.array (ParamType.tuple [
          ParamType.uint256, ParamType.fixedArray ParamType.uint256 3
        ]) }
      ]
      returnType := none
      returns := [ParamType.bytes32]
      body := [
        Compiler.Modules.Hashing.abiEncodeStaticArray
          "digest" "items" 4 (Expr.arrayLength "items"),
        Stmt.returnValues [Expr.localVar "digest"]
      ]
    }
  ]
}

private def abiEncodePackedStaticSegmentsSmokeSpec : CompilationModel := {
  name := "AbiEncodePackedStaticSegmentsSmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "hash"
      params := [
        { name := "who", ty := ParamType.address }
        , { name := "amount", ty := ParamType.bytes32 }
      ]
      returnType := none
      returns := [ParamType.bytes32]
      body := [
        Compiler.Modules.Hashing.abiEncodePackedStaticSegments
          "digest"
          [(Expr.param "who", 20), (Expr.param "amount", 32)],
        Stmt.returnValues [Expr.localVar "digest"]
      ]
    }
  ]
}

private def eip712DigestSmokeSpec : CompilationModel := {
  name := "Eip712DigestSmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "hashTypedData"
      params := [
        { name := "domainSeparator", ty := ParamType.bytes32 }
        , { name := "structHash", ty := ParamType.bytes32 }
      ]
      returnType := none
      returns := [ParamType.bytes32]
      body := [
        Compiler.Modules.Hashing.eip712Digest
          "digest"
          (Expr.param "domainSeparator")
          (Expr.param "structHash"),
        Stmt.returnValues [Expr.localVar "digest"]
      ]
    }
  ]
}

private def sha256PackedStaticSegmentsSmokeSpec : CompilationModel := {
  name := "Sha256PackedStaticSegmentsSmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "hash"
      params := [
        { name := "who", ty := ParamType.address }
        , { name := "context", ty := ParamType.bytes32 }
      ]
      returnType := none
      returns := [ParamType.bytes32]
      body := [
        Compiler.Modules.Hashing.sha256PackedStaticSegments
          "digest"
          [(Expr.param "who", 20), (Expr.param "context", 32)],
        Stmt.returnValues [Expr.localVar "digest"]
      ]
    }
  ]
}

private def sha256MemoryBadAritySpec : CompilationModel := {
  name := "Sha256MemoryBadArity"
  fields := []
  «constructor» := none
  functions := [
    { name := "bad"
      params := [{ name := "inputOffset", ty := ParamType.uint256 }]
      returnType := none
      body := [
        Stmt.ecm (Compiler.Modules.Precompiles.sha256MemoryModule "digest")
          [Expr.param "inputOffset"],
        Stmt.stop
      ]
    }
  ]
}

private def abiEncodePackedWordsBadAritySpec : CompilationModel := {
  name := "AbiEncodePackedWordsBadArity"
  fields := []
  «constructor» := none
  functions := [
    { name := "bad"
      params := [{ name := "a", ty := ParamType.bytes32 }]
      returnType := none
      body := [
        Stmt.ecm (Compiler.Modules.Hashing.abiEncodePackedWordsModule "digest" 2)
          [Expr.param "a"],
        Stmt.stop
      ]
    }
  ]
}

private def abiEncodeStaticWordsBadAritySpec : CompilationModel := {
  name := "AbiEncodeStaticWordsBadArity"
  fields := []
  «constructor» := none
  functions := [
    { name := "bad"
      params := [{ name := "marketId", ty := ParamType.bytes32 }]
      returnType := none
      body := [
        Stmt.ecm (Compiler.Modules.Hashing.abiEncodeStaticWordsModule "digest" 2)
          [Expr.param "marketId"],
        Stmt.stop
      ]
    }
  ]
}

private def abiEncodeStaticArrayBadAritySpec : CompilationModel := {
  name := "AbiEncodeStaticArrayBadArity"
  fields := []
  «constructor» := none
  functions := [
    { name := "bad"
      params := [{ name := "items", ty := ParamType.array ParamType.uint256 }]
      returnType := none
      body := [
        Stmt.ecm (Compiler.Modules.Hashing.abiEncodeStaticArrayModule "digest" "items" 1)
          [Expr.arrayLength "items", Expr.literal 0],
        Stmt.stop
      ]
    }
  ]
}

private def abiEncodeStaticArrayBadWidthSpec : CompilationModel := {
  name := "AbiEncodeStaticArrayBadWidth"
  fields := []
  «constructor» := none
  functions := [
    { name := "bad"
      params := [{ name := "items", ty := ParamType.array ParamType.uint256 }]
      returnType := none
      body := [
        Compiler.Modules.Hashing.abiEncodeStaticArray
          "digest" "items" 0 (Expr.arrayLength "items"),
        Stmt.stop
      ]
    }
  ]
}

private def sha256PackedWordsBadAritySpec : CompilationModel := {
  name := "Sha256PackedWordsBadArity"
  fields := []
  «constructor» := none
  functions := [
    { name := "bad"
      params := [{ name := "root", ty := ParamType.bytes32 }]
      returnType := none
      body := [
        Stmt.ecm (Compiler.Modules.Hashing.sha256PackedWordsModule "digest" 2)
          [Expr.param "root"],
        Stmt.stop
      ]
    }
  ]
}

private def abiEncodePackedStaticSegmentsBadWidthSpec : CompilationModel := {
  name := "AbiEncodePackedStaticSegmentsBadWidth"
  fields := []
  «constructor» := none
  functions := [
    { name := "bad"
      params := [{ name := "who", ty := ParamType.address }]
      returnType := none
      body := [
        Compiler.Modules.Hashing.abiEncodePackedStaticSegments
          "digest"
          [(Expr.param "who", 33)],
        Stmt.stop
      ]
    }
  ]
}

private def sha256PackedStaticSegmentsBadWidthSpec : CompilationModel := {
  name := "Sha256PackedStaticSegmentsBadWidth"
  fields := []
  «constructor» := none
  functions := [
    { name := "bad"
      params := [{ name := "who", ty := ParamType.address }]
      returnType := none
      body := [
        Compiler.Modules.Hashing.sha256PackedStaticSegments
          "digest"
          [(Expr.param "who", 0)],
        Stmt.stop
      ]
    }
  ]
}

private def abiEncodePackedStaticSegmentsBadAritySpec : CompilationModel := {
  name := "AbiEncodePackedStaticSegmentsBadArity"
  fields := []
  «constructor» := none
  functions := [
    { name := "bad"
      params := [{ name := "who", ty := ParamType.address }]
      returnType := none
      body := [
        Stmt.ecm (Compiler.Modules.Hashing.abiEncodePackedStaticSegmentsModule "digest" [20, 32])
          [Expr.param "who"],
        Stmt.stop
      ]
    }
  ]
}

private def sha256PackedStaticSegmentsBadAritySpec : CompilationModel := {
  name := "Sha256PackedStaticSegmentsBadArity"
  fields := []
  «constructor» := none
  functions := [
    { name := "bad"
      params := [{ name := "who", ty := ParamType.address }]
      returnType := none
      body := [
        Stmt.ecm (Compiler.Modules.Hashing.sha256PackedStaticSegmentsModule "digest" [20, 32])
          [Expr.param "who"],
        Stmt.stop
      ]
    }
  ]
}

private def eip712DigestBadAritySpec : CompilationModel := {
  name := "Eip712DigestBadArity"
  fields := []
  «constructor» := none
  functions := [
    { name := "bad"
      params := [{ name := "domainSeparator", ty := ParamType.bytes32 }]
      returnType := none
      body := [
        Stmt.ecm (Compiler.Modules.Hashing.eip712DigestModule "digest")
          [Expr.param "domainSeparator"],
        Stmt.stop
      ]
    }
  ]
}

private def oracleReadSmokeSpec : CompilationModel := {
  name := "OracleReadSmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "peek"
      params := [
        { name := "oracle", ty := ParamType.address }
        , { name := "asset", ty := ParamType.address }
      ]
      returnType := none
      returns := [ParamType.uint256]
      body := [
        Compiler.Modules.Oracle.oracleReadUint256
          "answer"
          (Expr.param "oracle")
          0xfeaf968c
          [Expr.param "asset"],
        Stmt.returnValues [Expr.localVar "answer"]
      ]
    }
  ]
}

private def externalCallWithReturnSmokeSpec : CompilationModel := {
  name := "ExternalCallWithReturnSmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "peek"
      params := [
        { name := "target", ty := ParamType.address }
        , { name := "asset", ty := ParamType.address }
      ]
      returnType := none
      returns := [ParamType.uint256]
      body := [
        Compiler.Modules.Calls.withReturn
          "answer"
          (Expr.param "target")
          0x70a08231
          [Expr.param "asset"]
          true,
        Stmt.returnValues [Expr.localVar "answer"]
      ]
    }
  ]
}

private def bubblingValueCallSmokeSpec : CompilationModel := {
  name := "BubblingValueCallSmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "forward"
      params := [
        { name := "target", ty := ParamType.address }
        , { name := "ethValue", ty := ParamType.uint256 }
        , { name := "inputOffset", ty := ParamType.uint256 }
        , { name := "inputSize", ty := ParamType.uint256 }
        , { name := "outputOffset", ty := ParamType.uint256 }
        , { name := "outputSize", ty := ParamType.uint256 }
      ]
      returnType := none
      reentrancyTrusted := true
      body := [
        Compiler.Modules.Calls.bubblingValueCall
          (Expr.param "target")
          (Expr.param "ethValue")
          (Expr.param "inputOffset")
          (Expr.param "inputSize")
          (Expr.param "outputOffset")
          (Expr.param "outputSize"),
        Stmt.stop
      ]
    }
  ]
}

private def bubblingValueCallBadAritySpec : CompilationModel := {
  name := "BubblingValueCallBadArity"
  fields := []
  «constructor» := none
  functions := [
    { name := "bad"
      params := [
        { name := "target", ty := ParamType.address }
        , { name := "ethValue", ty := ParamType.uint256 }
      ]
      returnType := none
      body := [
        Stmt.ecm Compiler.Modules.Calls.bubblingValueCallModule [
          Expr.param "target",
          Expr.param "ethValue"
        ],
        Stmt.stop
      ]
    }
  ]
}

private def bubblingValueCallViewRejectedSpec : CompilationModel := {
  name := "BubblingValueCallViewRejected"
  fields := []
  «constructor» := none
  functions := [
    { name := "forward"
      params := [
        { name := "target", ty := ParamType.address }
        , { name := "ethValue", ty := ParamType.uint256 }
        , { name := "inputOffset", ty := ParamType.uint256 }
        , { name := "inputSize", ty := ParamType.uint256 }
        , { name := "outputOffset", ty := ParamType.uint256 }
        , { name := "outputSize", ty := ParamType.uint256 }
      ]
      returnType := none
      isView := true
      body := [
        Compiler.Modules.Calls.bubblingValueCall
          (Expr.param "target")
          (Expr.param "ethValue")
          (Expr.param "inputOffset")
          (Expr.param "inputSize")
          (Expr.param "outputOffset")
          (Expr.param "outputSize"),
        Stmt.stop
      ]
    }
  ]
}

private def bubblingValueCallNoOutputSmokeSpec : CompilationModel := {
  name := "BubblingValueCallNoOutputSmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "forward"
      params := [
        { name := "target", ty := ParamType.address }
        , { name := "ethValue", ty := ParamType.uint256 }
        , { name := "inputOffset", ty := ParamType.uint256 }
        , { name := "inputSize", ty := ParamType.uint256 }
      ]
      returnType := none
      reentrancyTrusted := true
      body := [
        Compiler.Modules.Calls.bubblingValueCallNoOutput
          (Expr.param "target")
          (Expr.param "ethValue")
          (Expr.param "inputOffset")
          (Expr.param "inputSize"),
        Stmt.stop
      ]
    }
  ]
}

private def bubblingValueCallNoOutputViewRejectedSpec : CompilationModel := {
  name := "BubblingValueCallNoOutputViewRejected"
  fields := []
  «constructor» := none
  functions := [
    { name := "forward"
      params := [
        { name := "target", ty := ParamType.address }
        , { name := "ethValue", ty := ParamType.uint256 }
        , { name := "inputOffset", ty := ParamType.uint256 }
        , { name := "inputSize", ty := ParamType.uint256 }
      ]
      returnType := none
      isView := true
      body := [
        Compiler.Modules.Calls.bubblingValueCallNoOutput
          (Expr.param "target")
          (Expr.param "ethValue")
          (Expr.param "inputOffset")
          (Expr.param "inputSize"),
        Stmt.stop
      ]
    }
  ]
}

private def bubblingValueCallNoOutputBadAritySpec : CompilationModel := {
  name := "BubblingValueCallNoOutputBadArity"
  fields := []
  «constructor» := none
  functions := [
    { name := "bad"
      params := [
        { name := "target", ty := ParamType.address }
        , { name := "ethValue", ty := ParamType.uint256 }
      ]
      returnType := none
      body := [
        Stmt.ecm Compiler.Modules.Calls.bubblingValueCallNoOutputModule [
          Expr.param "target",
          Expr.param "ethValue"
        ],
        Stmt.stop
      ]
    }
  ]
}

private def callbackSmokeSpec : CompilationModel := {
  name := "CallbackSmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "notify"
      params := [
        { name := "target", ty := ParamType.address }
        , { name := "assets", ty := ParamType.uint256 }
        , { name := "data", ty := ParamType.bytes }
      ]
      returnType := none
      reentrancyTrusted := true
      body := [
        Compiler.Modules.Callbacks.callback
          (Expr.param "target")
          0x12345678
          [Expr.param "assets"]
          "data",
        Stmt.stop
      ]
    }
  ]
}

private def erc20BalanceOfSmokeSpec : CompilationModel := {
  name := "ERC20BalanceOfSmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "balance"
      params := [
        { name := "token", ty := ParamType.address }
        , { name := "owner", ty := ParamType.address }
      ]
      returnType := none
      returns := [ParamType.uint256]
      body := [
        Compiler.Modules.ERC20.balanceOf
          "balance"
          (Expr.param "token")
          (Expr.param "owner"),
        Stmt.returnValues [Expr.localVar "balance"]
      ]
    }
  ]
}

private def erc20SafeTransferSmokeSpec : CompilationModel := {
  name := "ERC20SafeTransferSmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "send"
      params := [
        { name := "token", ty := ParamType.address }
        , { name := "recipient", ty := ParamType.address }
        , { name := "amount", ty := ParamType.uint256 }
      ]
      returnType := none
      returns := []
      reentrancyTrusted := true
      body := [
        Compiler.Modules.ERC20.safeTransfer
          (Expr.param "token")
          (Expr.param "recipient")
          (Expr.param "amount"),
        Stmt.stop
      ]
    }
  ]
}

private def erc20SafeTransferFromSmokeSpec : CompilationModel := {
  name := "ERC20SafeTransferFromSmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "pull"
      params := [
        { name := "token", ty := ParamType.address }
        , { name := "owner", ty := ParamType.address }
        , { name := "recipient", ty := ParamType.address }
        , { name := "amount", ty := ParamType.uint256 }
      ]
      returnType := none
      returns := []
      reentrancyTrusted := true
      body := [
        Compiler.Modules.ERC20.safeTransferFrom
          (Expr.param "token")
          (Expr.param "owner")
          (Expr.param "recipient")
          (Expr.param "amount"),
        Stmt.stop
      ]
    }
  ]
}

private def erc20SolmateSafeTransferSmokeSpec : CompilationModel := {
  name := "ERC20SolmateSafeTransferSmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "send"
      params := [
        { name := "token", ty := ParamType.address }
        , { name := "recipient", ty := ParamType.address }
        , { name := "amount", ty := ParamType.uint256 }
      ]
      returnType := none
      returns := []
      reentrancyTrusted := true
      body := [
        Compiler.Modules.ERC20.solmateSafeTransfer
          (Expr.param "token")
          (Expr.param "recipient")
          (Expr.param "amount"),
        Stmt.stop
      ]
    }
  ]
}

private def erc20SolmateSafeTransferFromSmokeSpec : CompilationModel := {
  name := "ERC20SolmateSafeTransferFromSmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "pull"
      params := [
        { name := "token", ty := ParamType.address }
        , { name := "owner", ty := ParamType.address }
        , { name := "recipient", ty := ParamType.address }
        , { name := "amount", ty := ParamType.uint256 }
      ]
      returnType := none
      returns := []
      reentrancyTrusted := true
      body := [
        Compiler.Modules.ERC20.solmateSafeTransferFrom
          (Expr.param "token")
          (Expr.param "owner")
          (Expr.param "recipient")
          (Expr.param "amount"),
        Stmt.stop
      ]
    }
  ]
}

private def erc20SafeApproveSmokeSpec : CompilationModel := {
  name := "ERC20SafeApproveSmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "approve"
      params := [
        { name := "token", ty := ParamType.address }
        , { name := "spender", ty := ParamType.address }
        , { name := "amount", ty := ParamType.uint256 }
      ]
      returnType := none
      returns := []
      reentrancyTrusted := true
      body := [
        Compiler.Modules.ERC20.safeApprove
          (Expr.param "token")
          (Expr.param "spender")
          (Expr.param "amount"),
        Stmt.stop
      ]
    }
  ]
}

private def callWithValueSmokeSpec : CompilationModel := {
  name := "CallWithValueSmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "execute"
      params := [
        { name := "target", ty := ParamType.address }
        , { name := "amount", ty := ParamType.uint256 }
        , { name := "dataOffset", ty := ParamType.uint256 }
        , { name := "dataSize", ty := ParamType.uint256 }
      ]
      returnType := none
      reentrancyTrusted := true
      body := [
        Compiler.Modules.Calls.callWithValue
          (Expr.param "target")
          (Expr.param "amount")
          (Expr.param "dataOffset")
          (Expr.param "dataSize"),
        Stmt.stop
      ]
    }
  ]
}

private def callWithValueViewRejectedSpec : CompilationModel := {
  name := "CallWithValueViewRejected"
  fields := []
  «constructor» := none
  functions := [
    { name := "execute"
      params := [
        { name := "target", ty := ParamType.address }
        , { name := "amount", ty := ParamType.uint256 }
        , { name := "dataOffset", ty := ParamType.uint256 }
        , { name := "dataSize", ty := ParamType.uint256 }
      ]
      returnType := none
      isView := true
      body := [
        Compiler.Modules.Calls.callWithValue
          (Expr.param "target")
          (Expr.param "amount")
          (Expr.param "dataOffset")
          (Expr.param "dataSize"),
        Stmt.stop
      ]
    }
  ]
}

private def callWithValueBytesSmokeSpec : CompilationModel := {
  name := "CallWithValueBytesSmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "execute"
      params := [
        { name := "target", ty := ParamType.address }
        , { name := "amount", ty := ParamType.uint256 }
        , { name := "data", ty := ParamType.bytes }
      ]
      returnType := none
      reentrancyTrusted := true
      body := [
        Compiler.Modules.Calls.callWithValueBytes
          (Expr.param "target")
          (Expr.param "amount")
          "data",
        Stmt.stop
      ]
    }
  ]
}

private def callWithValueBytesViewRejectedSpec : CompilationModel := {
  name := "CallWithValueBytesViewRejected"
  fields := []
  «constructor» := none
  functions := [
    { name := "execute"
      params := [
        { name := "target", ty := ParamType.address }
        , { name := "amount", ty := ParamType.uint256 }
        , { name := "data", ty := ParamType.bytes }
      ]
      returnType := none
      isView := true
      body := [
        Compiler.Modules.Calls.callWithValueBytes
          (Expr.param "target")
          (Expr.param "amount")
          "data",
        Stmt.stop
      ]
    }
  ]
}

private def erc20AllowanceSmokeSpec : CompilationModel := {
  name := "ERC20AllowanceSmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "allowance"
      params := [
        { name := "token", ty := ParamType.address }
        , { name := "owner", ty := ParamType.address }
        , { name := "spender", ty := ParamType.address }
      ]
      returnType := none
      returns := [ParamType.uint256]
      body := [
        Compiler.Modules.ERC20.allowance
          "remaining"
          (Expr.param "token")
          (Expr.param "owner")
          (Expr.param "spender"),
        Stmt.returnValues [Expr.localVar "remaining"]
      ]
    }
  ]
}

private def erc20TotalSupplySmokeSpec : CompilationModel := {
  name := "ERC20TotalSupplySmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "totalSupply"
      params := [{ name := "token", ty := ParamType.address }]
      returnType := none
      returns := [ParamType.uint256]
      body := [
        Compiler.Modules.ERC20.totalSupply
          "supply"
          (Expr.param "token"),
        Stmt.returnValues [Expr.localVar "supply"]
      ]
    }
  ]
}

private def erc4626PreviewDepositSmokeSpec : CompilationModel := {
  name := "ERC4626PreviewDepositSmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "preview"
      params := [
        { name := "vault", ty := ParamType.address }
        , { name := "assets", ty := ParamType.uint256 }
      ]
      returnType := none
      returns := [ParamType.uint256]
      body := [
        Compiler.Modules.ERC4626.previewDeposit
          "shares"
          (Expr.param "vault")
          (Expr.param "assets"),
        Stmt.returnValues [Expr.localVar "shares"]
      ]
    }
  ]
}

private def erc4626PreviewMintSmokeSpec : CompilationModel := {
  name := "ERC4626PreviewMintSmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "preview"
      params := [
        { name := "vault", ty := ParamType.address }
        , { name := "shares", ty := ParamType.uint256 }
      ]
      returnType := none
      returns := [ParamType.uint256]
      body := [
        Compiler.Modules.ERC4626.previewMint
          "assets"
          (Expr.param "vault")
          (Expr.param "shares"),
        Stmt.returnValues [Expr.localVar "assets"]
      ]
    }
  ]
}

private def erc4626PreviewWithdrawSmokeSpec : CompilationModel := {
  name := "ERC4626PreviewWithdrawSmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "preview"
      params := [
        { name := "vault", ty := ParamType.address }
        , { name := "assets", ty := ParamType.uint256 }
      ]
      returnType := none
      returns := [ParamType.uint256]
      body := [
        Compiler.Modules.ERC4626.previewWithdraw
          "shares"
          (Expr.param "vault")
          (Expr.param "assets"),
        Stmt.returnValues [Expr.localVar "shares"]
      ]
    }
  ]
}

private def erc4626PreviewRedeemSmokeSpec : CompilationModel := {
  name := "ERC4626PreviewRedeemSmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "preview"
      params := [
        { name := "vault", ty := ParamType.address }
        , { name := "shares", ty := ParamType.uint256 }
      ]
      returnType := none
      returns := [ParamType.uint256]
      body := [
        Compiler.Modules.ERC4626.previewRedeem
          "assets"
          (Expr.param "vault")
          (Expr.param "shares"),
        Stmt.returnValues [Expr.localVar "assets"]
      ]
    }
  ]
}

private def erc4626ConvertToAssetsSmokeSpec : CompilationModel := {
  name := "ERC4626ConvertToAssetsSmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "convert"
      params := [
        { name := "vault", ty := ParamType.address }
        , { name := "shares", ty := ParamType.uint256 }
      ]
      returnType := none
      returns := [ParamType.uint256]
      body := [
        Compiler.Modules.ERC4626.convertToAssets
          "assets"
          (Expr.param "vault")
          (Expr.param "shares"),
        Stmt.returnValues [Expr.localVar "assets"]
      ]
    }
  ]
}

private def erc4626ConvertToSharesSmokeSpec : CompilationModel := {
  name := "ERC4626ConvertToSharesSmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "convert"
      params := [
        { name := "vault", ty := ParamType.address }
        , { name := "assets", ty := ParamType.uint256 }
      ]
      returnType := none
      returns := [ParamType.uint256]
      body := [
        Compiler.Modules.ERC4626.convertToShares
          "shares"
          (Expr.param "vault")
          (Expr.param "assets"),
        Stmt.returnValues [Expr.localVar "shares"]
      ]
    }
  ]
}

private def erc4626TotalAssetsSmokeSpec : CompilationModel := {
  name := "ERC4626TotalAssetsSmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "totalAssets"
      params := [{ name := "vault", ty := ParamType.address }]
      returnType := none
      returns := [ParamType.uint256]
      body := [
        Compiler.Modules.ERC4626.totalAssets
          "assets"
          (Expr.param "vault"),
        Stmt.returnValues [Expr.localVar "assets"]
      ]
    }
  ]
}

private def erc4626AssetSmokeSpec : CompilationModel := {
  name := "ERC4626AssetSmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "asset"
      params := [{ name := "vault", ty := ParamType.address }]
      returnType := none
      returns := [ParamType.address]
      body := [
        Compiler.Modules.ERC4626.asset
          "assetAddr"
          (Expr.param "vault"),
        Stmt.returnValues [Expr.localVar "assetAddr"]
      ]
    }
  ]
}

private def erc4626MaxDepositSmokeSpec : CompilationModel := {
  name := "ERC4626MaxDepositSmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "maxDeposit"
      params := [
        { name := "vault", ty := ParamType.address }
        , { name := "receiver", ty := ParamType.address }
      ]
      returnType := none
      returns := [ParamType.uint256]
      body := [
        Compiler.Modules.ERC4626.maxDeposit
          "assets"
          (Expr.param "vault")
          (Expr.param "receiver"),
        Stmt.returnValues [Expr.localVar "assets"]
      ]
    }
  ]
}

private def erc4626MaxMintSmokeSpec : CompilationModel := {
  name := "ERC4626MaxMintSmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "maxMint"
      params := [
        { name := "vault", ty := ParamType.address }
        , { name := "receiver", ty := ParamType.address }
      ]
      returnType := none
      returns := [ParamType.uint256]
      body := [
        Compiler.Modules.ERC4626.maxMint
          "shares"
          (Expr.param "vault")
          (Expr.param "receiver"),
        Stmt.returnValues [Expr.localVar "shares"]
      ]
    }
  ]
}

private def erc4626MaxWithdrawSmokeSpec : CompilationModel := {
  name := "ERC4626MaxWithdrawSmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "maxWithdraw"
      params := [
        { name := "vault", ty := ParamType.address }
        , { name := "owner", ty := ParamType.address }
      ]
      returnType := none
      returns := [ParamType.uint256]
      body := [
        Compiler.Modules.ERC4626.maxWithdraw
          "assets"
          (Expr.param "vault")
          (Expr.param "owner"),
        Stmt.returnValues [Expr.localVar "assets"]
      ]
    }
  ]
}

private def erc4626MaxRedeemSmokeSpec : CompilationModel := {
  name := "ERC4626MaxRedeemSmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "maxRedeem"
      params := [
        { name := "vault", ty := ParamType.address }
        , { name := "owner", ty := ParamType.address }
      ]
      returnType := none
      returns := [ParamType.uint256]
      body := [
        Compiler.Modules.ERC4626.maxRedeem
          "shares"
          (Expr.param "vault")
          (Expr.param "owner"),
        Stmt.returnValues [Expr.localVar "shares"]
      ]
    }
  ]
}

private def erc4626DepositSmokeSpec : CompilationModel := {
  name := "ERC4626DepositSmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "deposit"
      params := [
        { name := "vault", ty := ParamType.address }
        , { name := "assets", ty := ParamType.uint256 }
        , { name := "receiver", ty := ParamType.address }
      ]
      returnType := none
      returns := [ParamType.uint256]
      reentrancyTrusted := true
      body := [
        Compiler.Modules.ERC4626.deposit
          "shares"
          (Expr.param "vault")
          (Expr.param "assets")
          (Expr.param "receiver"),
        Stmt.returnValues [Expr.localVar "shares"]
      ]
    }
  ]
}

namespace MacroSolidityTypeFidelitySmoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256

verity_contract TypedVerifierRouter where
  storage
    circuits : MappingStruct(Bytes32,[
      verifier : Address @word 0 packed(0,160),
      inputCount : Uint16 @word 0 packed(160,16),
      outputCount : Uint16 @word 0 packed(176,16),
      active : Bool @word 0 packed(192,8)
    ]) := slot 2
    routeFlags : MappingStruct2(Bytes32,Bytes32,[
      enabled : Bool @word 0 packed(0,8),
      limit : Uint16 @word 0 packed(8,16)
    ]) := slot 3

  struct Circuit where
    verifier : Address,
    inputCount : Uint16,
    outputCount : Uint16,
    active : Bool

  event_defs
    event CircuitRegistered(@indexed circuitId : Bytes32, verifier : Address,
      inputCount : Uint16, outputCount : Uint16)
    event CircuitActiveSet(@indexed circuitId : Bytes32, active : Bool)

  function setCircuit
      (circuitId : Bytes32, verifierAddr : Address, inputCount : Uint16,
       outputCount : Uint16) : Unit := do
    setStructMember "circuits" circuitId "verifier" verifierAddr
    setStructMember "circuits" circuitId "inputCount" inputCount
    setStructMember "circuits" circuitId "outputCount" outputCount
    setStructMember "circuits" circuitId "active" true
    emit "CircuitRegistered" [circuitId, addressToWord verifierAddr, inputCount, outputCount]

  function pauseCircuit (circuitId : Bytes32) : Unit := do
    setStructMember "circuits" circuitId "active" false
    emit "CircuitActiveSet" [circuitId, false]

  function view getCircuit (circuitId : Bytes32) : Circuit := do
    let verifierAddr ← structMember "circuits" circuitId "verifier"
    let inputCount ← structMember "circuits" circuitId "inputCount"
    let outputCount ← structMember "circuits" circuitId "outputCount"
    let active ← structMember "circuits" circuitId "active"
    return Circuit.mk verifierAddr inputCount outputCount active

  function view getCircuitViaMembers (circuitId : Bytes32) : Circuit := do
    let (verifierAddr, inputCount, outputCount, active) :=
      structMembers "circuits" circuitId ["verifier", "inputCount", "outputCount", "active"]
    return Circuit.mk verifierAddr inputCount outputCount active

  function view getRouteFlag (sourceId : Bytes32, targetId : Bytes32) : Tuple [Bool, Uint16] := do
    return structMembers2 "routeFlags" sourceId targetId ["enabled", "limit"]

def routerSpecUsesBytes32MappingKey : Bool :=
  TypedVerifierRouter.spec.fields.any (fun field =>
    field.name == "circuits" &&
      match field.ty with
      | FieldType.mappingStruct MappingKeyType.bytes32 members =>
          members.any (fun member =>
            member.name == "inputCount" &&
              member.ty == StructMemberType.uint16 &&
              member.packed == some { offset := 160, width := 16 }) &&
          members.any (fun member =>
            member.name == "active" &&
              member.ty == StructMemberType.bool &&
              member.packed == some { offset := 192, width := 8 })
      | _ => false)

def routerSpecUsesTypedEventsAndReturns : Bool :=
  TypedVerifierRouter.spec.events.any (fun eventDef =>
    eventDef.name == "CircuitRegistered" &&
      eventDef.params.map (fun param => param.ty) ==
        [ParamType.bytes32, ParamType.address, ParamType.uint16, ParamType.uint16]) &&
  TypedVerifierRouter.spec.events.any (fun eventDef =>
    eventDef.name == "CircuitActiveSet" &&
      eventDef.params.map (fun param => param.ty) == [ParamType.bytes32, ParamType.bool]) &&
  TypedVerifierRouter.spec.functions.any (fun fn =>
    fn.name == "getCircuit" &&
      fn.params.map (fun param => param.ty) == [ParamType.bytes32] &&
      fn.returns == [ParamType.tuple [ParamType.address, ParamType.uint16, ParamType.uint16, ParamType.bool]])

def routerStructMembersDestructuringKeepsMemberTypes : Bool :=
  TypedVerifierRouter.spec.functions.any (fun fn =>
    fn.name == "getCircuitViaMembers" &&
      fn.returns == [ParamType.tuple [ParamType.address, ParamType.uint16, ParamType.uint16, ParamType.bool]]) &&
  TypedVerifierRouter.spec.functions.any (fun fn =>
    fn.name == "getRouteFlag" &&
      fn.returns == [ParamType.bool, ParamType.uint16])

example : routerSpecUsesBytes32MappingKey = true := by native_decide
example : routerSpecUsesTypedEventsAndReturns = true := by native_decide
example : routerStructMembersDestructuringKeepsMemberTypes = true := by native_decide

end MacroSolidityTypeFidelitySmoke

namespace PackedStructMemberDenoteSmoke

private def oracle : Denote.DenoteOracle :=
  { mappingSlot := fun base key => base * 1000 + key
    keccakMemorySlice := fun _ _ _ => 0 }

private def fields : List Field :=
  [{ name := "deposits",
     ty := FieldType.mappingStruct MappingKeyType.address
       [{ name := "deposit", wordOffset := 0, packed := none },
        { name := "staked", ty := .bool, wordOffset := 1,
          packed := some { offset := 0, width := 1 } },
        { name := "stake", wordOffset := 1,
          packed := some { offset := 1, width := 112 } },
        { name := "unstakeDelaySec", ty := .uint256, wordOffset := 1,
          packed := some { offset := 113, width := 32 } },
        { name := "withdrawTime", wordOffset := 1,
          packed := some { offset := 145, width := 48 } }],
     «slot» := some 1 }]

private def key : Nat := 7
private def packedSlot : Nat := oracle.mappingSlot 1 key + 1
private def oldWord : Nat := 1 + 5 * 2 ^ 1 + 9 * 2 ^ 113
private def expectedWord : Nat := 1 + 7 * 2 ^ 1 + 9 * 2 ^ 113

private def preservesAdjacentPackedFields : Bool :=
  let world : Verity.ContractState :=
    { Verity.defaultState with
      «storage» := fun s => if s == packedSlot then oldWord else 0 }
  let state : Denote.DenoteState := { world := world, bindings := [] }
  match Denote.execStmt oracle fields state
      (Stmt.setStructMember "deposits" (.literal key) "stake" (.literal 7)) with
  | .continue next =>
      (next.world.storage packedSlot).val == expectedWord
  | _ => false

#eval! do
  expectTrue
    "packed mapping struct writes preserve adjacent fields in the same word"
    preservesAdjacentPackedFields

end PackedStructMemberDenoteSmoke

set_option maxRecDepth 4096 in
#eval! do
  let compiled :=
    match Compiler.CompilationModel.compile selectorSmokeSpec (selectorsFor selectorSmokeSpec) with
    | .ok _ => true
    | .error _ => false
  expectTrue "local CompilationModel smoke spec compiles with deterministic selectors" compiled

  -- Regression: selector mismatch must fail closed.
  let mismatchRejected :=
    match Compiler.CompilationModel.compile selectorSmokeSpec [] with
    | .ok _ => false
    | .error msg => contains msg "Selector count mismatch"
  expectTrue "selector mismatch is rejected with deterministic diagnostic" mismatchRejected
  expectCompileErrorContains
    "reserved compiler prefix is rejected in function parameters"
    reservedParamSpec
    "function parameter '__has_selector' uses reserved compiler prefix '__'"
  expectCompileErrorContains
    "same-name internal helpers are rejected before Yul lowering"
    duplicateInternalNameSpec
    "duplicate internal function name 'helper'"
  expectCompileErrorContains
    "same-name immutables are rejected before Yul lowering"
    duplicateImmutableNameSpec
    "duplicate immutable name 'cap'"
  expectCompileErrorContains
    "declared immutables left unset by the constructor are rejected"
    uninitializedImmutableSpec
    "immutable 'cap' is declared but never initialized in the constructor"
  expectCompileErrorContains
    "internal helper source names cannot collide with external dispatch names"
    internalExternalNameCollisionSpec
    "internal function name 'helper' collides with an external function name"
  let reservedFieldRejected :=
    match validateCompileInputs reservedFieldSpec (selectorsFor reservedFieldSpec) with
    | .ok _ => false
    | .error msg => contains msg "field '__compat_value' uses reserved compiler prefix '__'"
  expectTrue "reserved compiler prefix is rejected in fields" reservedFieldRejected
  expectCompileErrorContains
    "reserved compiler prefix is rejected in local binders"
    reservedLocalBinderSpec
    "local binder '__has_selector' uses reserved compiler prefix '__'"
  expectCompileErrorContains
    "reserved compiler prefix is rejected in assignment targets"
    reservedAssignTargetSpec
    "assignment target '__compat_value' uses reserved compiler prefix '__'"
  expectCompileErrorContains
    "reserved compiler prefix is rejected in constructor parameters"
    reservedConstructorParamSpec
    "constructor parameter '__init' uses reserved compiler prefix '__'"
  expectCompileErrorContains
    "reserved compiler prefix is rejected in forEach binders"
    reservedForEachBinderSpec
    "local binder '__loop_idx' uses reserved compiler prefix '__'"
  expectCompileErrorContains
    "reserved compiler prefix is rejected in internal call assignment binders"
    reservedInternalAssignBinderSpec
    "local binder '__ret' uses reserved compiler prefix '__'"
  expectCompileErrorContains
    "reserved compiler prefix is rejected in external call binders"
    reservedExternalBindSpec
    "local binder '__external_ret' uses reserved compiler prefix '__'"
  let effectOnlyExternalBindYul ← expectCompileToYul
    "effect-only external call bind compiles"
    effectOnlyExternalBindSpec
  expectTrue "effect-only external call bind lowers to a bare Yul call"
    (contains effectOnlyExternalBindYul "notify(next)" &&
      !(contains effectOnlyExternalBindYul "let  := notify(next)"))
  expectCompileErrorContains
    "effect-only external call bind still rejects non-void externals"
    effectOnlyExternalBindMismatchSpec
    "binds 0 Yul value(s) from external function 'echo', but it returns 1 Yul value(s)."
  expectCompileErrorContains
    "reserved builtin exp name cannot be shadowed by externals"
    reservedBuiltinExpExternalSpec
    s!"external declaration '{builtinExpName}' collides with compiler-generated/reserved symbol '{builtinExpName}'"
  expectCompileErrorContains
    "reserved compiler prefix is rejected in ECM result binders"
    reservedEcmResultVarSpec
    "local binder '__ecm_result' uses reserved compiler prefix '__'"
  expectTrue
    "macro payable constructor preserves constructor isPayable flag"
    MacroPayableConstructorSmoke.specMarksConstructorPayable
  let payableCtorAbi := Compiler.ABI.emitContractABIJson MacroPayableConstructorSmoke.MacroPayableConstructor.spec
  expectTrue "macro payable constructor ABI reports payable state mutability"
    (contains payableCtorAbi "\"type\": \"constructor\"" &&
      contains payableCtorAbi "\"stateMutability\": \"payable\"")
  expectTrue "macro pure function preserves model pure flag"
    Contracts.Smoke.MutabilitySmoke.double_model.isPure
  let mutabilityAbi := Compiler.ABI.emitContractABIJson Contracts.Smoke.MutabilitySmoke.spec
  expectTrue "macro pure function ABI reports pure state mutability"
    (contains mutabilityAbi "\"name\": \"double\"" &&
      contains mutabilityAbi "\"stateMutability\": \"pure\"")
  let payableCtorContract ← expectCompile
    "macro payable constructor compiles"
    MacroPayableConstructorSmoke.MacroPayableConstructor.spec
  expectTrue "macro payable constructor reaches IR with constructorPayable enabled"
    payableCtorContract.constructorPayable
  let nonPayableCtorYul ← expectCompileToYul
    "macro non-payable constructor compiles to Yul"
    MacroPayableConstructorSmoke.MacroNonPayableConstructor.spec
  let payableCtorYul ← expectCompileToYul
    "macro payable constructor compiles to Yul"
    MacroPayableConstructorSmoke.MacroPayableConstructor.spec
  expectTrue "macro payable constructor removes one deploy-time callvalue guard from rendered Yul"
    (countOccurrences nonPayableCtorYul "callvalue()" ==
      countOccurrences payableCtorYul "callvalue()" + 1)
  expectTrue "runtime and deploy Yul initialize Solidity free-memory pointer"
    (countOccurrences payableCtorYul "mstore(64, 128)" == 2)
  expectTrue
    "macro initializer prepends a single-run storage guard in the model"
    MacroInitializerSmoke.initializeModelPrependsSingleRunGuard
  expectTrue
    "macro reinitializer prepends the target-version storage guard in the model"
    MacroInitializerSmoke.initializeV2ModelPrependsVersionGuard
  expectTrue
    "macro initializer executable path seeds storage on the first call"
    MacroInitializerSmoke.initializeExecutableRunsOnce
  expectTrue
    "setStorageAddr compilation masks stored address words"
    MacroInitializerSmoke.compileSetStorageAddrMasksAddressWrites
  expectTrue
    "setStorageWord compilation mirrors alias slot writes"
    MacroInitializerSmoke.compileSetStorageWordMirrorsAliasSlots
  expectTrue
    "macro initializer executable path rejects a second call"
    MacroInitializerSmoke.initializeExecutableSecondCallReverts
  expectTrue
    "macro initializer rollback keeps the version slot unchanged when the user body reverts"
    MacroInitializerSmoke.initializeExecutableBodyRevertRollsBackVersionSlot
  expectTrue
    "macro reinitializer executable path advances the tracked version"
    MacroInitializerSmoke.reinitializerExecutableAdvancesVersion
  expectTrue
    "macro immutable spec keeps immutables out of storage fields"
    MacroImmutableSmoke.specKeepsImmutablesOutOfStorageFields
  expectTrue
    "macro immutable constructor seeds bytecode immutables before user code"
    MacroImmutableSmoke.constructorSeedsBytecodeImmutables
  expectTrue
    "macro immutable model path reads immutable expressions"
    MacroImmutableSmoke.runtimeFunctionsUseImmutableExpressions
  expectTrue
    "macro immutable function parameters still shadow immutable names"
    MacroImmutableSmoke.functionParamsStillShadowImmutableNames
  expectTrue
    "macro immutables synthesize a constructor when needed"
    MacroImmutableSmoke.implicitConstructorCreatedForImmutableInitializers
  expectTrue
    "macro synthesized immutable function reads immutable expressions"
    MacroImmutableSmoke.implicitImmutableFunctionUsesImmutableExpression
  expectTrue
    "macro typed immutables lower to the immutable spec surface"
    MacroImmutableSmoke.typedImmutableSpecUsesImmutableSurface
  expectTrue
    "macro typed immutables seed bytecode immutable values in the constructor"
    MacroImmutableSmoke.typedImmutableConstructorSeedsBytecodeValues
  expectTrue
    "macro typed immutables read immutable expressions"
    MacroImmutableSmoke.typedImmutableFunctionsUseImmutableExpressions
  expectTrue "macro emit lowers to Stmt.emit"
    MacroEventTraceSmoke.emitNamedModelUsesStmtEmit
  expectTrue "macro event declarations populate CompilationModel event metadata"
    MacroEventTraceSmoke.eventTraceSpecCarriesEventMetadata
  expectTrue "macro rawLog lowers to Stmt.rawLog with dynamic topic expressions"
    MacroEventTraceSmoke.emitDynamicLogModelUsesStmtRawLog
  expectTrue "macro emit executable path appends the named event trace"
    MacroEventTraceSmoke.emitNamedExecutableAppendsNamedEvent
  expectTrue "macro rawLog executable path appends the low-level event trace"
    MacroEventTraceSmoke.emitDynamicLogExecutableAppendsLowLevelTrace
  expectTrue "executable rawLog rejects more than four topics like the compiler path"
    MacroEventTraceSmoke.rawLogExecutableRejectsTooManyTopics
  let rawLogTraceYul ← expectCompileToYul
    "rawLog trace smoke spec"
    rawLogTraceSmokeSpec
  expectTrue "rawLog preserves the modeled memory slice and topic expressions in rendered Yul"
    (contains rawLogTraceYul "log2(dataOffset, dataSize, topic0, add(topic1, 1))")
  expectCompileErrorContains
    "compiler rawLog rejects more than four topics"
    rawLogTooManyTopicsSpec
    "rawLog supports at most 4 topics"
  let rawRevertYul ← expectCompileToYul
    "rawRevert smoke spec"
    rawRevertSmokeSpec
  expectTrue "rawRevert preserves the modeled memory slice in rendered Yul"
    (contains rawRevertYul "revert(offset, size)")
  let rawRevertTrustReport := emitTrustReportJson [rawRevertSmokeSpec]
  let rawRevertLowLevelLines := emitLowLevelMechanicsUsageSiteLines [rawRevertSmokeSpec]
  expectTrue "rawRevert trust report classifies raw memory reverts as denied low-level mechanics"
    (contains rawRevertTrustReport "\"modeledLowLevelMechanics\"" &&
      contains rawRevertTrustReport "\"rawRevert\"" &&
      rawRevertLowLevelLines.any (fun line => contains line "RawRevertSmoke [function:fail]: rawRevert"))
  expectTrue "rawRevert trust report includes structured unsafe Yul contract"
    (contains rawRevertTrustReport "\"unsafeYulContracts\":[{\"name\":\"raw_revert_memory_slice_refinement\"" &&
      contains rawRevertTrustReport "\"memoryReads\":[\"revertPayload\"]")
  expectCompileErrorContains
    "unsafeYul validation rejects under-declared Yul let bindings"
    unsafeYulUnderDeclaredBindSpec
    "under-declares bound local(s): tmp"
  expectCompileErrorContains
    "unsafeYul validation rejects under-declared Yul assignments"
    unsafeYulUnderDeclaredAssignSpec
    "under-declares assigned local(s): tmp"
  expectCompileErrorContains
    "unsafeYul validation rejects under-declared Yul storage writes"
    unsafeYulUnderDeclaredStorageSpec
    "under-declares storage effects"
  expectCompileErrorContains
    "unsafeYul tstore mechanic is rejected from view functions"
    unsafeYulTstoreMechanicViewRejectedSpec
    "function 'bad' is marked view but writes state"
  discard <| expectCompile
    "unsafeYul raw call AST is allowed by logical-purity validation"
    unsafeYulRawCallAllowedSpec
  expectTrue
    "unsafeYul raw call AST propagates CEI seen-call state"
    unsafeYulRawCallPropagatesCEI
  discard <| expectCompile
    "matchAdt with terminating branches"
    matchAdtAllBranchesTerminateSpec
  expectCompileErrorContains
    "function with return value rejects stop-only termination"
    returnValueStopRejectedSpec
    "not all control-flow paths end in return/revert"
  let envRuntimeYul ← expectCompileToYul "env runtime smoke compiles" envRuntimeSmokeSpec
  expectTrue "env runtime smoke lowers block.number" (contains envRuntimeYul "number()")
  let stringCompiled :=
    match Compiler.CompilationModel.compile stringAbiSpec (selectorsFor stringAbiSpec) with
    | .ok _ => true
    | .error _ => false
  expectTrue "string params/returns compile via dynamic bytes path" stringCompiled
  let stringAbi := Compiler.ABI.emitContractABIJson stringAbiSpec
  expectTrue "string ABI uses Solidity string type"
    (contains stringAbi "\"type\": \"string\"")
  expectTrue "string ABI includes mixed static/dynamic and multi-dynamic functions"
    ((contains stringAbi "\"name\": \"echoAfterUint\"") &&
      (contains stringAbi "\"name\": \"echoBeforeUint\"") &&
      (contains stringAbi "\"name\": \"echoSecondString\""))
  expectTrue "string ABI includes mixed and multi-dynamic custom errors"
    ((contains stringAbi "\"name\": \"TaggedMessage\"") &&
      (contains stringAbi "\"inputs\": [{\"name\": \"\", \"type\": \"uint256\"}, {\"name\": \"\", \"type\": \"string\"}]") &&
      (contains stringAbi "\"name\": \"SecondMessage\"") &&
      (contains stringAbi "\"inputs\": [{\"name\": \"\", \"type\": \"string\"}, {\"name\": \"\", \"type\": \"string\"}]"))
  expectTrue "string ABI includes indexed and multi-head string events"
    ((contains stringAbi "\"name\": \"TaggedMessageLogged\"") &&
      (contains stringAbi "\"inputs\": [{\"name\": \"tag\", \"type\": \"uint256\", \"indexed\": true}, {\"name\": \"message\", \"type\": \"string\", \"indexed\": false}]") &&
      (contains stringAbi "\"name\": \"IndexedMessageLogged\"") &&
      (contains stringAbi "\"inputs\": [{\"name\": \"message\", \"type\": \"string\", \"indexed\": true}]") &&
      (contains stringAbi "\"name\": \"SecondMessageLogged\"") &&
      (contains stringAbi "\"inputs\": [{\"name\": \"prefix\", \"type\": \"string\", \"indexed\": false}, {\"name\": \"message\", \"type\": \"string\", \"indexed\": false}]"))
  expectCompileErrorContains
    "returnBytes rejects bytes params for string returns"
    stringReturnMismatchSpec
    "uses Stmt.returnBytes to return parameter 'message' of type"
  expectCompileErrorContains
    "string events reject bytes parameters"
    stringEventMismatchSpec
    "event 'MessageLogged' param 'message' expects"
  let memoryArrayEventsCompile :=
    match Compiler.CompilationModel.compile memoryArrayEventSourceSpec
        (selectorsFor memoryArrayEventSourceSpec) with
    | .ok _ => true
    | .error _ => false
  expectTrue "memory array event sources compile for unindexed uint256[] params"
    memoryArrayEventsCompile
  let projectedArrayEventsCompile :=
    match Compiler.CompilationModel.compile projectedArrayEventSourceSpec
        (selectorsFor projectedArrayEventSourceSpec) with
    | .ok _ => true
    | .error _ => false
  expectTrue "projected dynamic array event sources compile for unindexed uint256[] params"
    projectedArrayEventsCompile
  let projectedStaticCompositeEventsCompile :=
    match Compiler.CompilationModel.compile projectedStaticCompositeEventSourceSpec
        (selectorsFor projectedStaticCompositeEventSourceSpec) with
    | .ok _ => true
    | .error _ => false
  expectTrue "projected static composite event sources compile for unindexed tuple params"
    projectedStaticCompositeEventsCompile
  let stringArrayEventsCompile :=
    match Compiler.CompilationModel.compile Contracts.StringArrayEventSmoke.spec
        (selectorsFor Contracts.StringArrayEventSmoke.spec) with
    | .ok _ => true
    | .error _ => false
  expectTrue "string[] event emission compiles for indexed and unindexed params" stringArrayEventsCompile
  let stringArrayErrorsCompile :=
    match Compiler.CompilationModel.compile Contracts.StringArrayErrorSmoke.spec
        (selectorsFor Contracts.StringArrayErrorSmoke.spec) with
    | .ok _ => true
    | .error _ => false
  expectTrue "string[] custom errors compile for direct param refs and multi-dynamic heads"
    stringArrayErrorsCompile
  let stringArrayErrorAbi := Compiler.ABI.emitContractABIJson Contracts.StringArrayErrorSmoke.spec
  expectTrue "string[] custom error ABI uses Solidity string[] type"
    ((contains stringArrayErrorAbi "\"name\": \"BadMessages\"") &&
      (contains stringArrayErrorAbi "\"inputs\": [{\"name\": \"\", \"type\": \"string[]\"}]") &&
      (contains stringArrayErrorAbi "\"name\": \"TaggedMessages\"") &&
      (contains stringArrayErrorAbi "\"inputs\": [{\"name\": \"\", \"type\": \"uint256\"}, {\"name\": \"\", \"type\": \"string[]\"}]") &&
      (contains stringArrayErrorAbi "\"name\": \"SecondMessages\"") &&
      (contains stringArrayErrorAbi "\"inputs\": [{\"name\": \"\", \"type\": \"string[]\"}, {\"name\": \"\", \"type\": \"string[]\"}]"))
  let eventEncodingRegressionYul ← expectCompileToYul
    "ADT and newtype event encoding regression spec compiles"
    eventEncodingRegressionSpec
  expectTrue "ADT event encoding stores payload fields before logging"
    ((contains eventEncodingRegressionYul "choice_f0") &&
      (contains eventEncodingRegressionYul "choice_f1") &&
      (contains eventEncodingRegressionYul "keccak256(__evt_ptr, 96)"))
  expectTrue "newtype event topics normalize through the erased base type"
    (contains eventEncodingRegressionYul
      "and(who, 0xffffffffffffffffffffffffffffffffffffffff)")
  expectCompileErrorContains
    "ADT payload parameter locals are reserved against parameter collisions"
    adtParamPayloadNameCollisionSpec
    "function parameter binding name 'choice_f0' collides"
  expectCompileErrorContains
    "ADT alias payload slots are checked against reserved slot ranges"
    adtAliasPayloadReservedSlotSpec
    "choice.aliasSlots[0].payload[0]"
  let adtAliasPayloadMemoYul ← expectCompileToYul
    "ADT alias payload expressions are memoized before duplicate alias writes"
    adtAliasPayloadMemoizesExprSpec
  expectTrue "ADT alias payload expression is evaluated once"
    (countOccurrences adtAliasPayloadMemoYul "echo(input)" == 1)
  expectTrue "ADT alias writes reuse the generated payload local"
    ((contains adtAliasPayloadMemoYul "let __adt_payload_0 := echo(input)") &&
      (countOccurrences adtAliasPayloadMemoYul "__adt_payload_0" >= 3))
  let ceiInitialInternalCallCompiled :=
    match Compiler.CompilationModel.compile ceiInitialInternalCallAllowedSpec
        (selectorsFor ceiInitialInternalCallAllowedSpec) with
    | .ok _ => true
    | .error _ => false
  expectTrue "CEI allows an initial internal-call statement without a prior interaction"
    ceiInitialInternalCallCompiled
  let viewInternalReadInferenceCompiled :=
    match Compiler.CompilationModel.compile viewInternalReadInferenceSpec
        (selectorsFor viewInternalReadInferenceSpec) with
    | .ok _ => true
    | .error _ => false
  expectTrue "view mutability accepts internal helpers inferred to only read state"
    viewInternalReadInferenceCompiled
  expectCompileErrorContains
    "view mutability rejects internal helpers inferred to write state"
    viewInternalWriteRejectedSpec
    "function 'peek' is marked view but writes state"
  let pureInternalCallInferenceCompiled :=
    match Compiler.CompilationModel.compile pureInternalCallInferenceSpec
        (selectorsFor pureInternalCallInferenceSpec) with
    | .ok _ => true
    | .error _ => false
  expectTrue "pure mutability accepts internal helpers inferred to be pure"
    pureInternalCallInferenceCompiled
  expectCompileErrorContains
    "pure mutability rejects internal helpers inferred to read state"
    pureInternalReadRejectedSpec
    "function 'peek' is marked pure but reads state/environment"
  expectCompileErrorContains
    "CEI rejects writing ECMs after an external call"
    ceiEcmWriteAfterCallRejectedSpec
    "violates CEI"
  let addressArrayReturnCompiled :=
    match Compiler.CompilationModel.compile addressArrayReturnSpec (selectorsFor addressArrayReturnSpec) with
    | .ok _ => true
    | .error _ => false
  expectTrue "address[] params can round-trip through returnArray" addressArrayReturnCompiled
  let internalAddressArrayReturnContract ←
    expectCompile
      "internal address[] helper return lowers to offset/length Yul returns"
      internalAddressArrayReturnSpec
  let internalAddressArrayReturnShape :=
    match internalAddressArrayReturnContract.internalFunctions.find? (fun stmt =>
        match stmt with
        | Compiler.Yul.YulStmt.funcDef name _ _ _ => name == "internal_echoArray"
        | _ => false) with
    | some (Compiler.Yul.YulStmt.funcDef "internal_echoArray"
        ["recipients_data_offset", "recipients_length"]
        [retOffset, retLength]
        [Compiler.Yul.YulStmt.assign assignedOffset (Compiler.Yul.YulExpr.ident "recipients_data_offset"),
         Compiler.Yul.YulStmt.assign assignedLength (Compiler.Yul.YulExpr.ident "recipients_length"),
         Compiler.Yul.YulStmt.leave]) =>
        retOffset == assignedOffset && retLength == assignedLength && retOffset != retLength
    | _ => false
  expectTrue "internal address[] helper return binds data offset and length"
    internalAddressArrayReturnShape
  let internalAddressArrayReturnYul ←
    expectCompileToYul
      "internal address[] helper return can be read as memory array"
      internalAddressArrayReturnSpec
  expectTrue "internal array return callers read returned array data from memory"
    (contains internalAddressArrayReturnYul
      s!"{checkedArrayElementMemoryHelperName}(echoed_data_offset, echoed_length, 0)")
  let addressStorageWordReturnCompiled :=
    match Compiler.CompilationModel.compile addressStorageWordReturnSpec
        (selectorsFor addressStorageWordReturnSpec) with
    | .ok _ => true
    | .error _ => false
  expectTrue "address[] params can drive returnStorageWords" addressStorageWordReturnCompiled
  let boolStorageWordReturnCompiled :=
    match Compiler.CompilationModel.compile boolStorageWordReturnSpec
        (selectorsFor boolStorageWordReturnSpec) with
    | .ok _ => true
    | .error _ => false
  expectTrue "bool[] params can drive returnStorageWords" boolStorageWordReturnCompiled
  expectCompileErrorContains
    "returnStorageWords still rejects bytes[] params until dynamic-element lowering lands"
    bytesStorageWordReturnSpec
    "requires an array parameter with single-word static elements"
  expectCompileErrorContains
    "returnArray rejects bytes[] params until dynamic-element lowering lands"
    bytesArrayReturnSpec
    "only arrays with single-word static elements are currently supported"
  expectCompileErrorContains
    "arrayElement rejects bytes[] params until dynamic-element indexing lands"
    bytesArrayElementSpec
    "Expr.arrayElement 'calls' requires an array with single-word static elements"
  expectCompileErrorContains
    "arrayElementWord rejects bytes[] params until dynamic-element word indexing lands"
    bytesArrayElementWordSpec
    "Expr.arrayElementWord 'calls' requires an array parameter with static ABI-word elements"
  let uintArrayElementOnlyYul ←
    expectCompileToYul "uint256[] arrayElement-only smoke spec" uintArrayElementOnlySpec
  expectTrue "arrayElement-only specs emit the tuple-array helpers"
    ((contains uintArrayElementOnlyYul checkedArrayElementCalldataHelperName) &&
      (contains uintArrayElementOnlyYul checkedArrayElementMemoryHelperName))
  expectTrue "arrayElement-only specs do not emit word-array helpers"
    (!(contains uintArrayElementOnlyYul checkedArrayElementWordCalldataHelperName) &&
      !(contains uintArrayElementOnlyYul checkedArrayElementWordMemoryHelperName))
  let uintArrayForEachAccumulatorYul ←
    expectCompileToYul "uint256[] forEach accumulator smoke spec" uintArrayForEachAccumulatorSpec
  expectTrue "forEach accumulator specs assign outer locals inside the loop body"
    (contains uintArrayForEachAccumulatorYul "let i := 0" &&
      contains uintArrayForEachAccumulatorYul "total := add(total, value)")
  let tupleArrayElementWordOnlyYul ←
    expectCompileToYul "tuple[] arrayElementWord-only smoke spec" tupleArrayElementWordOnlySpec
  expectTrue "arrayElementWord-only specs emit the word-array helpers"
    ((contains tupleArrayElementWordOnlyYul checkedArrayElementWordCalldataHelperName) &&
      (contains tupleArrayElementWordOnlyYul checkedArrayElementWordMemoryHelperName))
  expectTrue "arrayElementWord helper scales only element word offset"
    (contains tupleArrayElementWordOnlyYul
      "calldataload(add(data_offset, mul(add(mul(index, element_words), word_offset), 32)))" &&
      !(contains tupleArrayElementWordOnlyYul
        "calldataload(add(data_offset, mul(add(add(mul(index, element_words), word_offset), 32), 32)))"))
  expectTrue "arrayElementWord-only specs do not emit tuple-array helpers"
    (!(contains tupleArrayElementWordOnlyYul checkedArrayElementCalldataHelperName) &&
      !(contains tupleArrayElementWordOnlyYul checkedArrayElementMemoryHelperName))
  let arrayElementWordStorageIndexYul ←
    expectCompileToYul "arrayElementWord storage-index smoke spec" arrayElementWordStorageIndexSpec
  expectTrue "arrayElementWord index analysis emits storage-array helper dependencies"
    (contains arrayElementWordStorageIndexYul checkedStorageArrayElementHelperName)
  let storageArrayUint256Yul ←
    expectCompileToYul "storage uint256[] smoke spec" storageArrayUint256SmokeSpec
  expectTrue "storage uint256[] length lowers to sload(slot)"
    (contains storageArrayUint256Yul "sload(7)")
  expectTrue "storage uint256[] indexed reads use the checked storage-array helper"
    ((contains storageArrayUint256Yul checkedStorageArrayElementHelperName) &&
      (contains storageArrayUint256Yul "function __verity_storage_array_element_checked(slot, index)"))
  expectTrue "storage uint256[] push computes the Solidity base slot and bumps length"
    ((contains storageArrayUint256Yul "mstore(0, 7)") &&
      (contains storageArrayUint256Yul "keccak256(0, 32)") &&
      (contains storageArrayUint256Yul "sstore(7, add(__array_len, 1))"))
  expectTrue "storage uint256[] indexed writes guard bounds"
    (contains storageArrayUint256Yul "lt(__array_index, __array_len)")
  expectTrue "storage uint256[] pop clears the removed tail word"
    (contains storageArrayUint256Yul "sstore(add(__array_base, __array_new_len), 0)")
  expectTrue "storageArrayPush is tracked as reading state"
    (Compiler.CompilationModel.stmtReadsStateOrEnv
      (Stmt.storageArrayPush "queue" (Expr.literal 1)))
  expectTrue "setStorageArrayElement is tracked as reading state"
    (Compiler.CompilationModel.stmtReadsStateOrEnv
      (Stmt.setStorageArrayElement "queue" (Expr.literal 0) (Expr.literal 1)))
  let storageArrayBoolYul ← expectCompileToYul "storage bool[] smoke spec" storageArrayBoolSmokeSpec
  expectTrue "storage bool[] reads reuse the checked storage helper"
    (contains storageArrayBoolYul "function __verity_storage_array_element_checked(slot, index)")
  expectTrue "storage bool[] push stores the incoming word and bumps length"
    ((contains storageArrayBoolYul "mstore(0, 9)") &&
      (contains storageArrayBoolYul "sstore(9, add(__array_len, 1))"))
  expectTrue "storage bool[] indexed writes still guard bounds"
    (contains storageArrayBoolYul "lt(__array_index, __array_len)")
  let envYul ← expectCompileToYul "env runtime smoke spec" envRuntimeSmokeSpec
  expectTrue "address(this) lowers to the Yul address builtin"
    (contains envYul "address()")
  expectTrue "msg.value lowers to the Yul callvalue builtin"
    (contains envYul "callvalue()")
  expectTrue "selfbalance lowers to the Yul selfbalance builtin"
    (contains envYul "selfbalance()")
  expectTrue "block.timestamp lowers to the Yul timestamp builtin"
    (contains envYul "timestamp()")
  expectTrue "chainid lowers to the Yul chainid builtin"
    (contains envYul "chainid()")
  expectTrue "blobbasefee lowers to the Yul blobbasefee builtin"
    (contains envYul "blobbasefee()")
  let ecrecoverYul ←
    expectCompileToYul "ecrecover smoke spec" ecrecoverSmokeSpec
  expectTrue "ecrecover ECM lowers to precompile staticcall"
    (contains ecrecoverYul "staticcall(gas(), 1, __ecr_ptr, 128, __ecr_ptr, 32)")
  expectTrue "ecrecover ECM reverts when the precompile call fails"
    (contains ecrecoverYul "if iszero(__ecr_success) {")
  expectTrue "ecrecover ECM zeroes free-memory output on empty returndata"
    (contains ecrecoverYul "let __ecr_ptr := mload(64)" &&
      contains ecrecoverYul "mstore(64, add(__ecr_ptr, 128))" &&
      contains ecrecoverYul "if iszero(returndatasize()) {")
  expectTrue "ecrecover ECM masks recovered address to 160 bits"
    (contains ecrecoverYul "signer := and(mload(__ecr_ptr), 0xffffffffffffffffffffffffffffffffffffffff)")
  let sha256MemoryYul ←
    expectCompileToYul "sha256 memory smoke spec" sha256MemorySmokeSpec
  expectTrue "sha256Memory ECM binds output offset once before the precompile call"
    (contains sha256MemoryYul "let __sha256_output_offset := outputOffset")
  expectTrue "sha256Memory ECM lowers to precompile 0x02 staticcall"
    (contains sha256MemoryYul "staticcall(gas(), 2, inputOffset, inputSize, __sha256_output_offset, 32)")
  expectTrue "sha256Memory ECM reverts when the precompile call fails"
    (contains sha256MemoryYul "if iszero(__sha256_success) {")
  expectTrue "sha256Memory ECM returns the digest word from output memory"
    (contains sha256MemoryYul "let digest := 0" &&
      contains sha256MemoryYul "digest := mload(__sha256_output_offset)")
  let sha256MemoryTwiceYul ←
    expectCompileToYul "sha256 memory twice smoke spec" sha256MemoryTwiceSmokeSpec
  expectTrue "sha256Memory ECM scopes internal temporaries across repeated uses"
    (countOccurrences sha256MemoryTwiceYul "let __sha256_output_offset :=" == 2 &&
      countOccurrences sha256MemoryTwiceYul "let __sha256_success :=" == 2 &&
      contains sha256MemoryTwiceYul "let firstDigest := 0" &&
      contains sha256MemoryTwiceYul "firstDigest := mload(__sha256_output_offset)" &&
      contains sha256MemoryTwiceYul "let secondDigest := 0" &&
      contains sha256MemoryTwiceYul "secondDigest := mload(__sha256_output_offset)")
  expectCompileErrorContains
    "sha256Memory ECM rejects invalid argument counts"
    sha256MemoryBadAritySpec
    "uses ECM 'sha256Memory' with 1 arguments but it expects 3"
  let sha256MemoryTrustReport := emitTrustReportJson [sha256MemorySmokeSpec]
  expectTrue "sha256Memory trust report surfaces the SHA-256 precompile assumption"
    (contains sha256MemoryTrustReport "\"module\":\"sha256Memory\"" &&
      contains sha256MemoryTrustReport "\"assumption\":\"evm_sha256_precompile\"" &&
      contains sha256MemoryTrustReport "\"status\":\"assumed\"")
  let bn256AddYul ←
    expectCompileToYul "bn256Add smoke spec" bn256AddSmokeSpec
  expectTrue "bn256Add ECM stores 4 input words contiguously"
    (contains bn256AddYul "let __bn256_add_ptr := mload(64)" &&
      contains bn256AddYul "mstore(__bn256_add_ptr, x1)" &&
      contains bn256AddYul "mstore(add(__bn256_add_ptr, 32), y1)" &&
      contains bn256AddYul "mstore(add(__bn256_add_ptr, 64), x2)" &&
      contains bn256AddYul "mstore(add(__bn256_add_ptr, 96), y2)" &&
      contains bn256AddYul "mstore(64, add(__bn256_add_ptr, 128))")
  expectTrue "bn256Add ECM lowers to precompile 0x06 staticcall"
    (contains bn256AddYul "staticcall(gas(), 6, __bn256_add_ptr, 128, __bn256_add_ptr, 64)")
  expectTrue "bn256Add ECM reverts when the precompile call fails"
    (contains bn256AddYul "if iszero(__bn256_add_success) {")
  expectTrue "bn256Add ECM binds two output result variables from free memory"
    (contains bn256AddYul "let x3 := 0" &&
      contains bn256AddYul "let y3 := 0" &&
      contains bn256AddYul "x3 := mload(__bn256_add_ptr)" &&
      contains bn256AddYul "y3 := mload(add(__bn256_add_ptr, 32))")
  expectCompileErrorContains
    "bn256Add ECM rejects invalid argument counts"
    bn256AddBadAritySpec
    "uses ECM 'bn256Add' with 1 arguments but it expects 4"
  let bn256AddTrustReport := emitTrustReportJson [bn256AddSmokeSpec]
  expectTrue "bn256Add trust report surfaces the BN256 add precompile assumption"
    (contains bn256AddTrustReport "\"module\":\"bn256Add\"" &&
      contains bn256AddTrustReport "\"assumption\":\"evm_bn256_add_precompile\"" &&
      contains bn256AddTrustReport "\"status\":\"assumed\"")
  let bn256ScalarMulYul ←
    expectCompileToYul "bn256ScalarMul smoke spec" bn256ScalarMulSmokeSpec
  expectTrue "bn256ScalarMul ECM stores 3 input words contiguously"
    (contains bn256ScalarMulYul "let __bn256_mul_ptr := mload(64)" &&
      contains bn256ScalarMulYul "mstore(__bn256_mul_ptr, x)" &&
      contains bn256ScalarMulYul "mstore(add(__bn256_mul_ptr, 32), y)" &&
      contains bn256ScalarMulYul "mstore(add(__bn256_mul_ptr, 64), k)" &&
      contains bn256ScalarMulYul "mstore(64, add(__bn256_mul_ptr, 96))")
  expectTrue "bn256ScalarMul ECM lowers to precompile 0x07 staticcall"
    (contains bn256ScalarMulYul "staticcall(gas(), 7, __bn256_mul_ptr, 96, __bn256_mul_ptr, 64)")
  expectTrue "bn256ScalarMul ECM reverts when the precompile call fails"
    (contains bn256ScalarMulYul "if iszero(__bn256_mul_success) {")
  expectTrue "bn256ScalarMul ECM binds two output result variables from free memory"
    (contains bn256ScalarMulYul "let x2 := 0" &&
      contains bn256ScalarMulYul "let y2 := 0" &&
      contains bn256ScalarMulYul "x2 := mload(__bn256_mul_ptr)" &&
      contains bn256ScalarMulYul "y2 := mload(add(__bn256_mul_ptr, 32))")
  expectCompileErrorContains
    "bn256ScalarMul ECM rejects invalid argument counts"
    bn256ScalarMulBadAritySpec
    "uses ECM 'bn256ScalarMul' with 1 arguments but it expects 3"
  let bn256ScalarMulTrustReport := emitTrustReportJson [bn256ScalarMulSmokeSpec]
  expectTrue "bn256ScalarMul trust report surfaces the BN256 scalar-mul precompile assumption"
    (contains bn256ScalarMulTrustReport "\"module\":\"bn256ScalarMul\"" &&
      contains bn256ScalarMulTrustReport "\"assumption\":\"evm_bn256_scalar_mul_precompile\"" &&
      contains bn256ScalarMulTrustReport "\"status\":\"assumed\"")
  let bn256PairingYul ←
    expectCompileToYul "bn256Pairing smoke spec" bn256PairingSmokeSpec
  expectTrue "bn256Pairing ECM binds the output offset once before the precompile call"
    (contains bn256PairingYul "let __bn256_pairing_output_offset := outputOffset")
  expectTrue "bn256Pairing ECM lowers to precompile 0x08 staticcall over the caller-supplied region"
    (contains bn256PairingYul
      "staticcall(gas(), 8, inputOffset, inputSize, __bn256_pairing_output_offset, 32)")
  expectTrue "bn256Pairing ECM reverts when the precompile call fails"
    (contains bn256PairingYul "if iszero(__bn256_pairing_success) {")
  expectTrue "bn256Pairing ECM returns the boolean-typed word from output memory"
    (contains bn256PairingYul "let ok := 0" &&
      contains bn256PairingYul "ok := mload(__bn256_pairing_output_offset)")
  expectCompileErrorContains
    "bn256Pairing ECM rejects invalid argument counts"
    bn256PairingBadAritySpec
    "uses ECM 'bn256Pairing' with 1 arguments but it expects 3"
  let bn256PairingTrustReport := emitTrustReportJson [bn256PairingSmokeSpec]
  expectTrue "bn256Pairing trust report surfaces the BN256 pairing precompile assumption"
    (contains bn256PairingTrustReport "\"module\":\"bn256Pairing\"" &&
      contains bn256PairingTrustReport "\"assumption\":\"evm_bn256_pairing_precompile\"" &&
      contains bn256PairingTrustReport "\"status\":\"assumed\"")
  let abiEncodePackedWordsYul ←
    expectCompileToYul "abiEncodePackedWords smoke spec" abiEncodePackedWordsSmokeSpec
  expectTrue "abiEncodePackedWords evaluates source words before writing the hash preimage"
    (contains abiEncodePackedWordsYul "let __packed_word_0 := a" &&
      contains abiEncodePackedWordsYul "let __packed_word_1 := b" &&
      contains abiEncodePackedWordsYul "let __packed_word_2 := c")
  expectTrue "abiEncodePackedWords stores static words contiguously without clobbering the free-memory pointer"
    (contains abiEncodePackedWordsYul "let __digest_packed_words_ptr := mload(64)" &&
      contains abiEncodePackedWordsYul "mstore(add(__digest_packed_words_ptr, 0), __packed_word_0)" &&
      contains abiEncodePackedWordsYul "mstore(add(__digest_packed_words_ptr, 32), __packed_word_1)" &&
      contains abiEncodePackedWordsYul "mstore(add(__digest_packed_words_ptr, 64), __packed_word_2)" &&
      contains abiEncodePackedWordsYul "mstore(64, add(__digest_packed_words_ptr, 96))")
  expectTrue "abiEncodePackedWords hashes the exact packed byte length"
    (contains abiEncodePackedWordsYul "digest := keccak256(__digest_packed_words_ptr, 96)")
  let abiEncodeStaticWordsYul ←
    expectCompileToYul "abiEncodeStaticWords smoke spec" abiEncodeStaticWordsSmokeSpec
  expectTrue "abiEncodeStaticWords stores full ABI words contiguously"
    (contains abiEncodeStaticWordsYul "let __digest_abi_static_words_ptr := mload(64)" &&
      contains abiEncodeStaticWordsYul "mstore(add(__digest_abi_static_words_ptr, 0), __packed_word_0)" &&
      contains abiEncodeStaticWordsYul "mstore(add(__digest_abi_static_words_ptr, 32), __packed_word_1)" &&
      contains abiEncodeStaticWordsYul "mstore(add(__digest_abi_static_words_ptr, 64), __packed_word_2)" &&
      contains abiEncodeStaticWordsYul "mstore(64, add(__digest_abi_static_words_ptr, 96))")
  expectTrue "abiEncodeStaticWords hashes the exact ABI static byte length"
    (contains abiEncodeStaticWordsYul
      "digest := keccak256(__digest_abi_static_words_ptr, 96)")
  expectCompileErrorContains
    "abiEncodeStaticWords ECM rejects invalid argument counts"
    abiEncodeStaticWordsBadAritySpec
    "uses ECM 'abiEncodeStaticWords' with 1 arguments but it expects 2"
  let abiEncodeStaticWordsTrustReport := emitTrustReportJson [abiEncodeStaticWordsSmokeSpec]
  expectTrue "abiEncodeStaticWords trust report surfaces standard static ABI and keccak assumptions"
    (contains abiEncodeStaticWordsTrustReport "\"module\":\"abiEncodeStaticWords\"" &&
      contains abiEncodeStaticWordsTrustReport "\"assumption\":\"abi_standard_static_word_layout\"" &&
      contains abiEncodeStaticWordsTrustReport "\"assumption\":\"keccak256_memory_slice_matches_evm\"")
  let abiEncodeStaticArrayYul ←
    expectCompileToYul "abiEncodeStaticArray smoke spec" abiEncodeStaticArraySmokeSpec
  expectTrue "abiEncodeStaticArray writes the single dynamic argument head and length"
    (contains abiEncodeStaticArrayYul "mstore(__digest_abi_array_ptr, 32)" &&
      contains abiEncodeStaticArrayYul "let __digest_abi_array_length := items_length" &&
      contains abiEncodeStaticArrayYul "mstore(add(__digest_abi_array_ptr, 32), __digest_abi_array_length)")
  expectTrue "abiEncodeStaticArray copies the fixed-width element payload"
    (contains abiEncodeStaticArrayYul
      "let __digest_abi_array_data_bytes := mul(__digest_abi_array_length, 128)" &&
      contains abiEncodeStaticArrayYul
      "calldatacopy(add(__digest_abi_array_ptr, 64), items_data_offset, __digest_abi_array_data_bytes)")
  expectTrue "abiEncodeStaticArray hashes the ABI-encoded dynamic array byte length"
    (contains abiEncodeStaticArrayYul
      "let digest := keccak256(__digest_abi_array_ptr, __digest_abi_array_total_bytes)")
  expectCompileErrorContains
    "abiEncodeStaticArray ECM rejects invalid argument counts"
    abiEncodeStaticArrayBadAritySpec
    "uses ECM 'abiEncodeStaticArray' with 2 arguments but it expects 1"
  expectCompileErrorContains
    "abiEncodeStaticArray rejects zero-width elements"
    abiEncodeStaticArrayBadWidthSpec
    "abiEncodeStaticArray requires elementWords > 0"
  let abiEncodeStaticArrayTrustReport := emitTrustReportJson [abiEncodeStaticArraySmokeSpec]
  expectTrue "abiEncodeStaticArray trust report surfaces array layout and keccak assumptions"
    (contains abiEncodeStaticArrayTrustReport "\"module\":\"abiEncodeStaticArray\"" &&
      contains abiEncodeStaticArrayTrustReport "\"assumption\":\"abi_standard_dynamic_array_static_element_layout\"" &&
      contains abiEncodeStaticArrayTrustReport "\"assumption\":\"keccak256_memory_slice_matches_evm\"")
  let sha256PackedWordsYul ←
    expectCompileToYul "sha256PackedWords smoke spec" sha256PackedWordsSmokeSpec
  expectTrue "sha256PackedWords evaluates source words before writing the hash preimage"
    (contains sha256PackedWordsYul "let __packed_word_0 := root" &&
      contains sha256PackedWordsYul "let __packed_word_1 := context")
  expectTrue "sha256PackedWords stores static words contiguously"
    (contains sha256PackedWordsYul "let __digest_sha256_packed_words_ptr := mload(64)" &&
      contains sha256PackedWordsYul
        "mstore(add(__digest_sha256_packed_words_ptr, 0), __packed_word_0)" &&
      contains sha256PackedWordsYul
        "mstore(add(__digest_sha256_packed_words_ptr, 32), __packed_word_1)")
  expectTrue "sha256PackedWords hashes the exact packed byte length through precompile 0x02"
    (contains sha256PackedWordsYul
      "staticcall(gas(), 2, __digest_sha256_packed_words_ptr, 64, __digest_sha256_packed_words_output, 32)")
  expectTrue "sha256PackedWords reverts when the precompile call fails"
    (contains sha256PackedWordsYul "if iszero(__sha256_packed_success) {")
  expectTrue "sha256PackedWords returns the digest word and advances free memory"
    (contains sha256PackedWordsYul "digest := mload(__digest_sha256_packed_words_output)" &&
      contains sha256PackedWordsYul "mstore(64, add(__digest_sha256_packed_words_output, 32))")
  expectCompileErrorContains
    "sha256PackedWords ECM rejects invalid argument counts"
    sha256PackedWordsBadAritySpec
    "uses ECM 'sha256PackedWords' with 1 arguments but it expects 2"
  let sha256PackedWordsTrustReport := emitTrustReportJson [sha256PackedWordsSmokeSpec]
  expectTrue "sha256PackedWords trust report surfaces packed-layout and SHA-256 assumptions"
    (contains sha256PackedWordsTrustReport "\"module\":\"sha256PackedWords\"" &&
      contains sha256PackedWordsTrustReport "\"assumption\":\"abi_packed_static_word_layout\"" &&
      contains sha256PackedWordsTrustReport "\"assumption\":\"evm_sha256_precompile\"" &&
      contains sha256PackedWordsTrustReport "\"status\":\"assumed\"")
  let abiEncodePackedStaticSegmentsYul ←
    expectCompileToYul "abiEncodePackedStaticSegments smoke spec" abiEncodePackedStaticSegmentsSmokeSpec
  expectTrue "abiEncodePackedStaticSegments masks and left-aligns sub-word static values"
    (contains abiEncodePackedStaticSegmentsYul
      "mstore(add(__digest_packed_segments_ptr, 0), shl(96, and(__packed_word_0, 0xffffffffffffffffffffffffffffffffffffffff)))")
  expectTrue "abiEncodePackedStaticSegments places the next segment at the byte-precise offset"
    (contains abiEncodePackedStaticSegmentsYul "mstore(add(__digest_packed_segments_ptr, 20), __packed_word_1)")
  expectTrue "abiEncodePackedStaticSegments hashes the exact byte length"
    (contains abiEncodePackedStaticSegmentsYul "digest := keccak256(__digest_packed_segments_ptr, 52)")
  expectCompileErrorContains
    "abiEncodePackedStaticSegments rejects invalid segment widths"
    abiEncodePackedStaticSegmentsBadWidthSpec
    "abiEncodePackedStaticSegments segment widths must be between 1 and 32 bytes"
  expectCompileErrorContains
    "abiEncodePackedStaticSegments ECM rejects invalid argument counts"
    abiEncodePackedStaticSegmentsBadAritySpec
    "uses ECM 'abiEncodePackedStaticSegments' with 1 arguments but it expects 2"
  let abiEncodePackedStaticSegmentsTrustReport :=
    emitTrustReportJson [abiEncodePackedStaticSegmentsSmokeSpec]
  expectTrue "abiEncodePackedStaticSegments trust report surfaces segment-layout and keccak assumptions"
    (contains abiEncodePackedStaticSegmentsTrustReport "\"module\":\"abiEncodePackedStaticSegments\"" &&
      contains abiEncodePackedStaticSegmentsTrustReport "\"assumption\":\"abi_packed_static_segment_layout\"" &&
      contains abiEncodePackedStaticSegmentsTrustReport "\"assumption\":\"keccak256_memory_slice_matches_evm\"")
  let eip712DigestYul ←
    expectCompileToYul "eip712Digest smoke spec" eip712DigestSmokeSpec
  expectTrue "eip712Digest writes the byte-exact typed-data preimage"
    (contains eip712DigestYul "let __digest_eip712_ptr := mload(64)" &&
      contains eip712DigestYul "mstore(__digest_eip712_ptr, shl(240, 0x1901))" &&
      contains eip712DigestYul "mstore(add(__digest_eip712_ptr, 2), domainSeparator)" &&
      contains eip712DigestYul "mstore(add(__digest_eip712_ptr, 34), structHash)")
  expectTrue "eip712Digest hashes exactly 66 bytes and advances memory by 96 bytes"
    (contains eip712DigestYul "digest := keccak256(__digest_eip712_ptr, 66)" &&
      contains eip712DigestYul "mstore(64, add(__digest_eip712_ptr, 96))")
  expectCompileErrorContains
    "eip712Digest ECM rejects invalid argument counts"
    eip712DigestBadAritySpec
    "uses ECM 'eip712Digest' with 1 arguments but it expects 2"
  let eip712DigestTrustReport := emitTrustReportJson [eip712DigestSmokeSpec]
  expectTrue "eip712Digest trust report surfaces typed-data layout and keccak assumptions"
    (contains eip712DigestTrustReport "\"module\":\"eip712Digest\"" &&
      contains eip712DigestTrustReport "\"assumption\":\"eip712_digest_layout\"" &&
      contains eip712DigestTrustReport "\"assumption\":\"keccak256_memory_slice_matches_evm\"")
  let sha256PackedStaticSegmentsYul ←
    expectCompileToYul "sha256PackedStaticSegments smoke spec" sha256PackedStaticSegmentsSmokeSpec
  expectTrue "sha256PackedStaticSegments masks and left-aligns sub-word static values"
    (contains sha256PackedStaticSegmentsYul
      "mstore(add(__digest_sha256_packed_segments_ptr, 0), shl(96, and(__packed_word_0, 0xffffffffffffffffffffffffffffffffffffffff)))")
  expectTrue "sha256PackedStaticSegments hashes the exact byte length through precompile 0x02"
    (contains sha256PackedStaticSegmentsYul
      "staticcall(gas(), 2, __digest_sha256_packed_segments_ptr, 52, __digest_sha256_packed_segments_output, 32)")
  expectTrue "sha256PackedStaticSegments returns the digest and advances free memory"
    (contains sha256PackedStaticSegmentsYul "digest := mload(__digest_sha256_packed_segments_output)" &&
      contains sha256PackedStaticSegmentsYul "mstore(64, add(__digest_sha256_packed_segments_output, 32))")
  expectCompileErrorContains
    "sha256PackedStaticSegments rejects invalid segment widths"
    sha256PackedStaticSegmentsBadWidthSpec
    "sha256PackedStaticSegments segment widths must be between 1 and 32 bytes"
  expectCompileErrorContains
    "sha256PackedStaticSegments ECM rejects invalid argument counts"
    sha256PackedStaticSegmentsBadAritySpec
    "uses ECM 'sha256PackedStaticSegments' with 1 arguments but it expects 2"
  let sha256PackedStaticSegmentsTrustReport :=
    emitTrustReportJson [sha256PackedStaticSegmentsSmokeSpec]
  expectTrue "sha256PackedStaticSegments trust report surfaces segment-layout and SHA-256 assumptions"
    (contains sha256PackedStaticSegmentsTrustReport "\"module\":\"sha256PackedStaticSegments\"" &&
      contains sha256PackedStaticSegmentsTrustReport "\"assumption\":\"abi_packed_static_segment_layout\"" &&
      contains sha256PackedStaticSegmentsTrustReport "\"assumption\":\"evm_sha256_precompile\"" &&
      contains sha256PackedStaticSegmentsTrustReport "\"status\":\"assumed\"")
  expectCompileErrorContains
    "abiEncodePackedWords ECM rejects invalid argument counts"
    abiEncodePackedWordsBadAritySpec
    "uses ECM 'abiEncodePackedWords' with 1 arguments but it expects 2"
  let abiEncodePackedWordsTrustReport := emitTrustReportJson [abiEncodePackedWordsSmokeSpec]
  expectTrue "abiEncodePackedWords trust report surfaces packed-layout and keccak assumptions"
    (contains abiEncodePackedWordsTrustReport "\"module\":\"abiEncodePackedWords\"" &&
      contains abiEncodePackedWordsTrustReport "\"assumption\":\"abi_packed_static_word_layout\"" &&
      contains abiEncodePackedWordsTrustReport "\"assumption\":\"keccak256_memory_slice_matches_evm\"")
  let oracleReadYul ←
    expectCompileToYul "oracle read smoke spec" oracleReadSmokeSpec
  expectTrue "oracle read ECM lowers to staticcall"
    (contains oracleReadYul "staticcall(gas(), oracle, __oracle_ptr, 36, __oracle_ptr, 32)")
  expectTrue "oracle read ECM forwards revert returndata"
    (contains oracleReadYul "returndatacopy(0, 0, __oracle_rds)")
  expectTrue "oracle read ECM rejects non-32-byte returndata"
    (contains oracleReadYul "if iszero(eq(returndatasize(), 32)) {")
  expectTrue "oracle read ECM ABI-encodes the selector at free memory"
    (contains oracleReadYul "let __oracle_ptr := mload(64)" &&
      contains oracleReadYul "mstore(__oracle_ptr, shl(224, 0xfeaf968c))" &&
      contains oracleReadYul "mstore(add(__oracle_ptr, 4), asset)" &&
      contains oracleReadYul "mstore(64, add(__oracle_ptr, 64))")
  let externalCallWithReturnYul ←
    expectCompileToYul "external call with return smoke spec" externalCallWithReturnSmokeSpec
  expectTrue "externalCallWithReturn ECM uses free memory for ABI calldata and returndata"
    (contains externalCallWithReturnYul "let __ecwr_ptr := mload(64)" &&
      contains externalCallWithReturnYul "mstore(__ecwr_ptr, shl(224, 0x70a08231))" &&
      contains externalCallWithReturnYul "mstore(add(__ecwr_ptr, 4), asset)" &&
      contains externalCallWithReturnYul "mstore(64, add(__ecwr_ptr, 64))" &&
      contains externalCallWithReturnYul "staticcall(gas(), target, __ecwr_ptr, 36, __ecwr_ptr, 32)" &&
      contains externalCallWithReturnYul "returndatacopy(0, 0, __ecwr_rds)" &&
      contains externalCallWithReturnYul "revert(0, __ecwr_rds)" &&
      contains externalCallWithReturnYul "answer := mload(__ecwr_ptr)")
  expectCompileErrorContains
    "external link mode rejects raw linked-helper lowering"
    MacroExternalLinkModeSmoke.externalModeRawCallSpec
    "linked_as := external"
  let bubblingValueCallYul ←
    expectCompileToYul "bubbling value call smoke spec" bubblingValueCallSmokeSpec
  expectTrue "bubbling value call ECM lowers to call, not staticcall"
    (contains bubblingValueCallYul
      "call(gas(), target, ethValue, inputOffset, inputSize, outputOffset, outputSize)" &&
      !(contains bubblingValueCallYul "staticcall("))
  expectTrue "bubbling value call ECM forwards revert returndata"
    (contains bubblingValueCallYul "let __bvc_rds := returndatasize()" &&
      contains bubblingValueCallYul "returndatacopy(0, 0, __bvc_rds)" &&
      contains bubblingValueCallYul "revert(0, __bvc_rds)")
  expectCompileErrorContains
    "bubbling value call ECM rejects invalid argument counts"
    bubblingValueCallBadAritySpec
    "uses ECM 'bubblingValueCall' with 2 arguments but it expects 6"
  expectCompileErrorContains
    "bubbling value call ECM remains rejected from view functions"
    bubblingValueCallViewRejectedSpec
    "function 'forward' is marked view but writes state"
  let bubblingValueCallTrustReport := emitTrustReportJson [bubblingValueCallSmokeSpec]
  expectTrue "bubbling value call trust report surfaces the generic call assumption"
    (contains bubblingValueCallTrustReport "\"module\":\"bubblingValueCall\"" &&
      contains bubblingValueCallTrustReport "\"assumption\":\"generic_low_level_value_call_interface\"" &&
      contains bubblingValueCallTrustReport "\"status\":\"assumed\"")
  let bubblingValueCallNoOutputYul ←
    expectCompileToYul "bubbling value call no-output smoke spec" bubblingValueCallNoOutputSmokeSpec
  expectTrue "bubbling value call no-output helper fixes output slice to zero"
    (contains bubblingValueCallNoOutputYul
      "call(gas(), target, ethValue, inputOffset, inputSize, 0, 0)")
  expectCompileErrorContains
    "bubbling value call no-output helper remains rejected from view functions"
    bubblingValueCallNoOutputViewRejectedSpec
    "function 'forward' is marked view but writes state"
  expectCompileErrorContains
    "bubbling value call no-output ECM rejects invalid argument counts"
    bubblingValueCallNoOutputBadAritySpec
    "uses ECM 'bubblingValueCallNoOutput' with 2 arguments but it expects 4"
  let bubblingValueCallNoOutputTrustReport :=
    emitTrustReportJson [bubblingValueCallNoOutputSmokeSpec]
  expectTrue "bubbling value call no-output helper preserves the generic call assumption"
    (contains bubblingValueCallNoOutputTrustReport "\"module\":\"bubblingValueCallNoOutput\"" &&
      contains bubblingValueCallNoOutputTrustReport
        "\"assumption\":\"generic_low_level_value_call_interface\"" &&
      contains bubblingValueCallNoOutputTrustReport "\"status\":\"assumed\"")
  let callbackYul ←
    expectCompileToYul "callback smoke spec" callbackSmokeSpec
  expectTrue "callback ECM builds calldata at free memory and advances the pointer"
    (contains callbackYul "let __cb_ptr := mload(64)" &&
      contains callbackYul "mstore(__cb_ptr, shl(224, 0x12345678))" &&
      contains callbackYul "mstore(add(__cb_ptr, 4), assets)" &&
      contains callbackYul "mstore(add(__cb_ptr, 36), 64)" &&
      contains callbackYul "mstore(add(__cb_ptr, 68), data_length)" &&
      contains callbackYul "mstore(64, add(__cb_ptr, and(add(add(100, and(add(data_length, 31), not(31))), 31), not(31))))")
  expectTrue "callback ECM calls the target and bubbles revert returndata"
    (contains callbackYul "call(gas(), target, 0, __cb_ptr, add(100, and(add(data_length, 31), not(31))), 0, 0)" &&
      contains callbackYul "returndatacopy(0, 0, __cb_rds)" &&
      contains callbackYul "revert(0, __cb_rds)")
  let callbackTrustReport := emitTrustReportJson [callbackSmokeSpec]
  expectTrue "callback trust report surfaces callback target interface"
    (contains callbackTrustReport "\"module\":\"callback\"" &&
      contains callbackTrustReport "\"assumption\":\"callback_target_interface\"")
  let erc20BalanceOfYul ←
    expectCompileToYul "erc20 balanceOf smoke spec" erc20BalanceOfSmokeSpec
  expectTrue "erc20 balanceOf ECM lowers to staticcall"
    (contains erc20BalanceOfYul "staticcall(gas(), token, __balanceOf_ptr, 36, __balanceOf_ptr, 32)")
  expectTrue "erc20 balanceOf ECM forwards revert returndata"
    (contains erc20BalanceOfYul "returndatacopy(0, 0, __balanceOf_rds)")
  expectTrue "erc20 balanceOf ECM rejects non-32-byte returndata"
    (contains erc20BalanceOfYul "if iszero(eq(returndatasize(), 32)) {")
  expectTrue "erc20 balanceOf ECM ABI-encodes the selector at free memory"
    (contains erc20BalanceOfYul "let __balanceOf_ptr := mload(64)" &&
      contains erc20BalanceOfYul "mstore(__balanceOf_ptr, shl(224, 0x70a08231))" &&
      contains erc20BalanceOfYul "mstore(add(__balanceOf_ptr, 4), owner)" &&
      contains erc20BalanceOfYul "mstore(64, add(__balanceOf_ptr, 64))")
  let erc20SafeTransferYul ←
    expectCompileToYul "erc20 safeTransfer smoke spec" erc20SafeTransferSmokeSpec
  expectTrue "erc20 safeTransfer ECM allocates calldata from the free-memory pointer"
    (contains erc20SafeTransferYul "let __st_ptr := mload(64)" &&
      contains erc20SafeTransferYul "mstore(__st_ptr, 0xa9059cbb00000000000000000000000000000000000000000000000000000000)" &&
      contains erc20SafeTransferYul "call(gas(), token, 0, __st_ptr, 68, __st_ptr, 32)")
  expectTrue "erc20 safeTransfer ECM advances the free-memory pointer"
    (contains erc20SafeTransferYul "mstore(64, and(add(add(__st_ptr, 68), 31), not(31)))")
  expectTrue "erc20 safeTransfer ECM forwards revert returndata"
    (contains erc20SafeTransferYul "returndatacopy(0, 0, __st_rds)" &&
      contains erc20SafeTransferYul "revert(0, __st_rds)")
  expectTrue "erc20 safeTransfer ECM uses OZ SafeERC20FailedOperation for bad optional bool returns"
    (contains erc20SafeTransferYul "mstore(0, 0x5274afe700000000000000000000000000000000000000000000000000000000)" &&
      contains erc20SafeTransferYul "extcodesize(token)" &&
      contains erc20SafeTransferYul "revert(0, 36)")
  expectTrue "erc20 safeTransfer ECM rejects malformed optional bool returndata"
    (contains erc20SafeTransferYul "let __erc20_rds := returndatasize()" &&
      contains erc20SafeTransferYul "if iszero(__erc20_rds) {" &&
      contains erc20SafeTransferYul "if __erc20_rds {" &&
      contains erc20SafeTransferYul "if iszero(eq(__erc20_rds, 32)) {" &&
      contains erc20SafeTransferYul "if iszero(eq(mload(__st_ptr), 1)) {")
  let erc20SafeTransferFromYul ←
    expectCompileToYul "erc20 safeTransferFrom smoke spec" erc20SafeTransferFromSmokeSpec
  expectTrue "erc20 safeTransferFrom ECM allocates calldata from the free-memory pointer"
    (contains erc20SafeTransferFromYul "let __stf_ptr := mload(64)" &&
      contains erc20SafeTransferFromYul "mstore(__stf_ptr, 0x23b872dd00000000000000000000000000000000000000000000000000000000)" &&
      contains erc20SafeTransferFromYul "call(gas(), token, 0, __stf_ptr, 100, __stf_ptr, 32)")
  expectTrue "erc20 safeTransferFrom ECM advances the free-memory pointer"
    (contains erc20SafeTransferFromYul "mstore(64, and(add(add(__stf_ptr, 100), 31), not(31)))")
  expectTrue "erc20 safeTransferFrom ECM forwards revert returndata"
    (contains erc20SafeTransferFromYul "returndatacopy(0, 0, __stf_rds)" &&
      contains erc20SafeTransferFromYul "revert(0, __stf_rds)")
  expectTrue "erc20 safeTransferFrom ECM uses OZ SafeERC20FailedOperation for bad optional bool returns"
    (contains erc20SafeTransferFromYul "mstore(0, 0x5274afe700000000000000000000000000000000000000000000000000000000)" &&
      contains erc20SafeTransferFromYul "extcodesize(token)" &&
      contains erc20SafeTransferFromYul "revert(0, 36)")
  expectTrue "erc20 safeTransferFrom ECM rejects malformed optional bool returndata"
    (contains erc20SafeTransferFromYul "let __erc20_rds := returndatasize()" &&
      contains erc20SafeTransferFromYul "if iszero(__erc20_rds) {" &&
      contains erc20SafeTransferFromYul "if __erc20_rds {" &&
      contains erc20SafeTransferFromYul "if iszero(eq(__erc20_rds, 32)) {" &&
      contains erc20SafeTransferFromYul "if iszero(eq(mload(__stf_ptr), 1)) {")
  let erc20SolmateSafeTransferYul ←
    expectCompileToYul "erc20 solmateSafeTransfer smoke spec" erc20SolmateSafeTransferSmokeSpec
  expectTrue "erc20 solmateSafeTransfer ECM uses Solmate optional bool semantics"
    (contains erc20SolmateSafeTransferYul "let __sst_ptr := mload(64)" &&
      contains erc20SolmateSafeTransferYul "call(gas(), token, 0, __sst_ptr, 68, __sst_ptr, 32)" &&
      contains erc20SolmateSafeTransferYul "let __erc20_rds := returndatasize()" &&
      contains erc20SolmateSafeTransferYul "gt(__erc20_rds, 31)" &&
      contains erc20SolmateSafeTransferYul "eq(mload(__sst_ptr), 1)" &&
      contains erc20SolmateSafeTransferYul "revert(0, 0)")
  let erc20SolmateSafeTransferFromYul ←
    expectCompileToYul "erc20 solmateSafeTransferFrom smoke spec" erc20SolmateSafeTransferFromSmokeSpec
  expectTrue "erc20 solmateSafeTransferFrom ECM uses Solmate optional bool semantics"
    (contains erc20SolmateSafeTransferFromYul "let __sstf_ptr := mload(64)" &&
      contains erc20SolmateSafeTransferFromYul "call(gas(), token, 0, __sstf_ptr, 100, __sstf_ptr, 32)" &&
      contains erc20SolmateSafeTransferFromYul "let __erc20_rds := returndatasize()" &&
      contains erc20SolmateSafeTransferFromYul "gt(__erc20_rds, 31)" &&
      contains erc20SolmateSafeTransferFromYul "eq(mload(__sstf_ptr), 1)" &&
      contains erc20SolmateSafeTransferFromYul "revert(0, 0)")
  let erc20SolmateTrustReport := emitTrustReportJson [erc20SolmateSafeTransferSmokeSpec, erc20SolmateSafeTransferFromSmokeSpec]
  expectTrue "erc20 solmate helpers surface distinct SafeTransferLib assumptions"
    (contains erc20SolmateTrustReport "\"module\":\"solmateSafeTransfer\"" &&
      contains erc20SolmateTrustReport "\"assumption\":\"erc20_solmate_safe_transfer_interface\"" &&
      contains erc20SolmateTrustReport "\"module\":\"solmateSafeTransferFrom\"" &&
      contains erc20SolmateTrustReport "\"assumption\":\"erc20_solmate_safe_transferFrom_interface\"")
  let erc20SafeApproveYul ←
    expectCompileToYul "erc20 safeApprove smoke spec" erc20SafeApproveSmokeSpec
  expectTrue "erc20 safeApprove ECM allocates calldata from the free-memory pointer"
    (contains erc20SafeApproveYul "let __sa_ptr := mload(64)" &&
      contains erc20SafeApproveYul "mstore(__sa_ptr, 0x095ea7b300000000000000000000000000000000000000000000000000000000)" &&
      contains erc20SafeApproveYul "call(gas(), token, 0, __sa_ptr, 68, __sa_ptr, 32)")
  expectTrue "erc20 safeApprove ECM rejects malformed optional bool returndata"
    (contains erc20SafeApproveYul "let __erc20_rds := returndatasize()" &&
      contains erc20SafeApproveYul "if iszero(__erc20_rds) {" &&
      contains erc20SafeApproveYul "if __erc20_rds {" &&
      contains erc20SafeApproveYul "if iszero(eq(__erc20_rds, 32)) {" &&
      contains erc20SafeApproveYul "if iszero(eq(mload(__sa_ptr), 1)) {")
  let callWithValueYul ←
    expectCompileToYul "generic callWithValue smoke spec" callWithValueSmokeSpec
  expectTrue "callWithValue ECM lowers to an ETH-aware generic call"
    (contains callWithValueYul "call(gas(), target, amount, dataOffset, dataSize, 0, 0)")
  expectTrue "callWithValue ECM forwards revert returndata"
    (contains callWithValueYul "returndatacopy(0, 0, __cwv_rds)")
  expectTrue "callWithValue ECM bubbles forwarded revert data"
    (contains callWithValueYul "revert(0, __cwv_rds)")
  expectCompileErrorContains
    "state-changing callWithValue ECM is rejected in view functions"
    callWithValueViewRejectedSpec
    "function 'execute' is marked view but writes state"
  let callWithValueBytesYul ←
    expectCompileToYul "generic callWithValue bytes smoke spec" callWithValueBytesSmokeSpec
  expectTrue "callWithValue bytes ECM copies calldata bytes payload to memory"
    (contains callWithValueBytesYul "let __cwv_bytes_ptr := mload(64)" &&
      contains callWithValueBytesYul "calldatacopy(__cwv_bytes_ptr, data_data_offset, data_length)" &&
      contains callWithValueBytesYul "mstore(64, add(__cwv_bytes_ptr, __cwv_bytes_padded))")
  expectTrue "callWithValue bytes ECM lowers to an ETH-aware generic bytes call"
    (contains callWithValueBytesYul "call(gas(), target, amount, __cwv_bytes_ptr, data_length, 0, 0)")
  expectCompileErrorContains
    "state-changing callWithValue bytes ECM is rejected in view functions"
    callWithValueBytesViewRejectedSpec
    "function 'execute' is marked view but writes state"
  let macroCallWithValueYul ←
    expectCompileToYul "macro callWithValue smoke spec" Contracts.Smoke.CallWithValueSmoke.spec
  expectTrue "macro callWithValue surface elaborates to the generic call ECM"
    (contains macroCallWithValueYul "call(gas(), target, value, dataOffset, dataSize, 0, 0)")
  expectTrue "macro callWithValue bytes surface copies calldata bytes payload to memory"
    (contains macroCallWithValueYul "calldatacopy(__cwv_bytes_ptr, data_data_offset, data_length)")
  expectTrue "macro callWithValue bytes surface elaborates to the generic bytes call ECM"
    (contains macroCallWithValueYul "call(gas(), target, value, __cwv_bytes_ptr, data_length, 0, 0)")
  let macroCallWithValueTrustReport := emitTrustReportJson [Contracts.Smoke.CallWithValueSmoke.spec]
  expectTrue "macro callWithValue trust report surfaces the generic call assumption"
    (contains macroCallWithValueTrustReport "\"module\":\"callWithValue\"" &&
      contains macroCallWithValueTrustReport "\"module\":\"callWithValueBytes\"" &&
      contains macroCallWithValueTrustReport "\"assumption\":\"generic_call_with_value_interface\"")
  let macroCreate2SSTORE2Yul ←
    expectCompileToYul "macro create2/SSTORE2 smoke spec" Contracts.Smoke.Create2SSTORE2Smoke.spec
  expectTrue "macro create2 surface lowers to the create2 builtin"
    (contains macroCreate2SSTORE2Yul "create2(value, initOffset, initSize, salt)")
  expectTrue "macro SSTORE2 read surface lowers to extcodecopy"
    (contains macroCreate2SSTORE2Yul "extcodecopy(pointer, destOffset, codeOffset, size)")
  let macroCreate2SSTORE2TrustReport := emitTrustReportJson [Contracts.Smoke.Create2SSTORE2Smoke.spec]
  expectTrue "macro create2/SSTORE2 trust report surfaces code-as-data assumptions"
    (contains macroCreate2SSTORE2TrustReport "\"module\":\"create2Deploy\"" &&
      contains macroCreate2SSTORE2TrustReport "\"module\":\"sstore2ReadCode\"" &&
      contains macroCreate2SSTORE2TrustReport "\"assumption\":\"create2_initcode_layout\"" &&
      contains macroCreate2SSTORE2TrustReport "\"assumption\":\"sstore2_pointer_code_layout\"")
  expectTrue "macro create2/SSTORE2 trust report surfaces low-level mechanics"
    (contains macroCreate2SSTORE2TrustReport "\"modeledLowLevelMechanics\":[\"create2\",\"extcodecopy\"]")
  let macroCreate2SSTORE2LowLevelLines :=
    String.intercalate "\n" (emitLowLevelMechanicsUsageSiteLines [Contracts.Smoke.Create2SSTORE2Smoke.spec])
  expectTrue "macro create2/SSTORE2 deny-low-level diagnostics include ECM mechanics"
    (contains macroCreate2SSTORE2LowLevelLines "- Create2SSTORE2Smoke [function:deploy]: create2" &&
      contains macroCreate2SSTORE2LowLevelLines "- Create2SSTORE2Smoke [function:readCode]: extcodecopy")
  let macroCallbackYul ←
    expectCompileToYul "macro callback ABI smoke spec" Contracts.Smoke.CallbackABISmoke.spec
  expectTrue "macro callback ABI surface stores selector and bytes length"
    (contains macroCallbackYul "mstore(__cb_ptr, shl(224, 0x12345678))" &&
      contains macroCallbackYul "mstore(add(__cb_ptr, 68), data_length)")
  expectTrue "macro callback ABI surface copies calldata bytes payload"
    (contains macroCallbackYul "calldatacopy(add(__cb_ptr, 100), data_data_offset, data_length)")
  let erc20AllowanceYul ←
    expectCompileToYul "erc20 allowance smoke spec" erc20AllowanceSmokeSpec
  expectTrue "erc20 allowance ECM lowers to staticcall"
    (contains erc20AllowanceYul "staticcall(gas(), token, __allowance_ptr, 68, __allowance_ptr, 32)")
  expectTrue "erc20 allowance ECM forwards revert returndata"
    (contains erc20AllowanceYul "returndatacopy(0, 0, __allowance_rds)")
  expectTrue "erc20 allowance ECM rejects non-32-byte returndata"
    (contains erc20AllowanceYul "if iszero(eq(returndatasize(), 32)) {")
  expectTrue "erc20 allowance ECM ABI-encodes the selector at free memory"
    (contains erc20AllowanceYul "let __allowance_ptr := mload(64)" &&
      contains erc20AllowanceYul "mstore(__allowance_ptr, shl(224, 0xdd62ed3e))" &&
      contains erc20AllowanceYul "mstore(add(__allowance_ptr, 4), owner)" &&
      contains erc20AllowanceYul "mstore(add(__allowance_ptr, 36), spender)" &&
      contains erc20AllowanceYul "mstore(64, add(__allowance_ptr, 96))")
  let erc20TotalSupplyYul ←
    expectCompileToYul "erc20 totalSupply smoke spec" erc20TotalSupplySmokeSpec
  expectTrue "erc20 totalSupply ECM lowers to staticcall"
    (contains erc20TotalSupplyYul "staticcall(gas(), token, __totalSupply_ptr, 4, __totalSupply_ptr, 32)")
  expectTrue "erc20 totalSupply ECM forwards revert returndata"
    (contains erc20TotalSupplyYul "returndatacopy(0, 0, __totalSupply_rds)")
  expectTrue "erc20 totalSupply ECM rejects non-32-byte returndata"
    (contains erc20TotalSupplyYul "if iszero(eq(returndatasize(), 32)) {")
  expectTrue "erc20 totalSupply ECM ABI-encodes the selector at free memory"
    (contains erc20TotalSupplyYul "let __totalSupply_ptr := mload(64)" &&
      contains erc20TotalSupplyYul "mstore(__totalSupply_ptr, shl(224, 0x18160ddd))" &&
      contains erc20TotalSupplyYul "mstore(64, add(__totalSupply_ptr, 32))")
  let erc4626PreviewDepositYul ←
    expectCompileToYul "erc4626 previewDeposit smoke spec" erc4626PreviewDepositSmokeSpec
  expectTrue "erc4626 previewDeposit ECM lowers to staticcall"
    (contains erc4626PreviewDepositYul "staticcall(gas(), vault, __erc4626_previewDeposit_ptr, 36, __erc4626_previewDeposit_ptr, 32)")
  expectTrue "erc4626 previewDeposit ECM forwards revert returndata"
    (contains erc4626PreviewDepositYul "returndatacopy(0, 0, __erc4626_rds)")
  expectTrue "erc4626 previewDeposit ECM rejects non-32-byte returndata"
    (contains erc4626PreviewDepositYul "if iszero(eq(returndatasize(), 32)) {")
  expectTrue "erc4626 previewDeposit ECM ABI-encodes the selector at free memory"
    (contains erc4626PreviewDepositYul "mstore(__erc4626_previewDeposit_ptr, shl(224, 0xef8b30f7))")
  let erc4626PreviewMintYul ←
    expectCompileToYul "erc4626 previewMint smoke spec" erc4626PreviewMintSmokeSpec
  expectTrue "erc4626 previewMint ECM lowers to staticcall"
    (contains erc4626PreviewMintYul "staticcall(gas(), vault, __erc4626_previewMint_ptr, 36, __erc4626_previewMint_ptr, 32)")
  expectTrue "erc4626 previewMint ECM forwards revert returndata"
    (contains erc4626PreviewMintYul "returndatacopy(0, 0, __erc4626_rds)")
  expectTrue "erc4626 previewMint ECM rejects non-32-byte returndata"
    (contains erc4626PreviewMintYul "if iszero(eq(returndatasize(), 32)) {")
  expectTrue "erc4626 previewMint ECM ABI-encodes the selector at free memory"
    (contains erc4626PreviewMintYul "mstore(__erc4626_previewMint_ptr, shl(224, 0xb3d7f6b9))")
  let erc4626PreviewWithdrawYul ←
    expectCompileToYul "erc4626 previewWithdraw smoke spec" erc4626PreviewWithdrawSmokeSpec
  expectTrue "erc4626 previewWithdraw ECM lowers to staticcall"
    (contains erc4626PreviewWithdrawYul "staticcall(gas(), vault, __erc4626_previewWithdraw_ptr, 36, __erc4626_previewWithdraw_ptr, 32)")
  expectTrue "erc4626 previewWithdraw ECM forwards revert returndata"
    (contains erc4626PreviewWithdrawYul "returndatacopy(0, 0, __erc4626_rds)")
  expectTrue "erc4626 previewWithdraw ECM rejects non-32-byte returndata"
    (contains erc4626PreviewWithdrawYul "if iszero(eq(returndatasize(), 32)) {")
  expectTrue "erc4626 previewWithdraw ECM ABI-encodes the selector at free memory"
    (contains erc4626PreviewWithdrawYul "mstore(__erc4626_previewWithdraw_ptr, shl(224, 0x0a28a477))")
  let erc4626PreviewRedeemYul ←
    expectCompileToYul "erc4626 previewRedeem smoke spec" erc4626PreviewRedeemSmokeSpec
  expectTrue "erc4626 previewRedeem ECM lowers to staticcall"
    (contains erc4626PreviewRedeemYul "staticcall(gas(), vault, __erc4626_previewRedeem_ptr, 36, __erc4626_previewRedeem_ptr, 32)")
  expectTrue "erc4626 previewRedeem ECM forwards revert returndata"
    (contains erc4626PreviewRedeemYul "returndatacopy(0, 0, __erc4626_rds)")
  expectTrue "erc4626 previewRedeem ECM rejects non-32-byte returndata"
    (contains erc4626PreviewRedeemYul "if iszero(eq(returndatasize(), 32)) {")
  expectTrue "erc4626 previewRedeem ECM ABI-encodes the selector at free memory"
    (contains erc4626PreviewRedeemYul "mstore(__erc4626_previewRedeem_ptr, shl(224, 0x4cdad506))")
  let erc4626ConvertToAssetsYul ←
    expectCompileToYul "erc4626 convertToAssets smoke spec" erc4626ConvertToAssetsSmokeSpec
  expectTrue "erc4626 convertToAssets ECM lowers to staticcall"
    (contains erc4626ConvertToAssetsYul "staticcall(gas(), vault, __erc4626_convertToAssets_ptr, 36, __erc4626_convertToAssets_ptr, 32)")
  expectTrue "erc4626 convertToAssets ECM forwards revert returndata"
    (contains erc4626ConvertToAssetsYul "returndatacopy(0, 0, __erc4626_rds)")
  expectTrue "erc4626 convertToAssets ECM rejects non-32-byte returndata"
    (contains erc4626ConvertToAssetsYul "if iszero(eq(returndatasize(), 32)) {")
  expectTrue "erc4626 convertToAssets ECM ABI-encodes the selector at free memory"
    (contains erc4626ConvertToAssetsYul "mstore(__erc4626_convertToAssets_ptr, shl(224, 0x07a2d13a))")
  let erc4626ConvertToSharesYul ←
    expectCompileToYul "erc4626 convertToShares smoke spec" erc4626ConvertToSharesSmokeSpec
  expectTrue "erc4626 convertToShares ECM lowers to staticcall"
    (contains erc4626ConvertToSharesYul "staticcall(gas(), vault, __erc4626_convertToShares_ptr, 36, __erc4626_convertToShares_ptr, 32)")
  expectTrue "erc4626 convertToShares ECM forwards revert returndata"
    (contains erc4626ConvertToSharesYul "returndatacopy(0, 0, __erc4626_rds)")
  expectTrue "erc4626 convertToShares ECM rejects non-32-byte returndata"
    (contains erc4626ConvertToSharesYul "if iszero(eq(returndatasize(), 32)) {")
  expectTrue "erc4626 convertToShares ECM ABI-encodes the selector at free memory"
    (contains erc4626ConvertToSharesYul "mstore(__erc4626_convertToShares_ptr, shl(224, 0xc6e6f592))")
  let erc4626TotalAssetsYul ←
    expectCompileToYul "erc4626 totalAssets smoke spec" erc4626TotalAssetsSmokeSpec
  expectTrue "erc4626 totalAssets ECM lowers to staticcall"
    (contains erc4626TotalAssetsYul "staticcall(gas(), vault, __erc4626_totalAssets_ptr, 4, __erc4626_totalAssets_ptr, 32)")
  expectTrue "erc4626 totalAssets ECM forwards revert returndata"
    (contains erc4626TotalAssetsYul "returndatacopy(0, 0, __erc4626_rds)")
  expectTrue "erc4626 totalAssets ECM rejects non-32-byte returndata"
    (contains erc4626TotalAssetsYul "if iszero(eq(returndatasize(), 32)) {")
  expectTrue "erc4626 totalAssets ECM ABI-encodes the selector at free memory"
    (contains erc4626TotalAssetsYul "mstore(__erc4626_totalAssets_ptr, shl(224, 0x01e1d114))")
  let erc4626AssetYul ←
    expectCompileToYul "erc4626 asset smoke spec" erc4626AssetSmokeSpec
  expectTrue "erc4626 asset ECM lowers to staticcall"
    (contains erc4626AssetYul "staticcall(gas(), vault, __erc4626_asset_ptr, 4, __erc4626_asset_ptr, 32)")
  expectTrue "erc4626 asset ECM forwards revert returndata"
    (contains erc4626AssetYul "returndatacopy(0, 0, __erc4626_rds)")
  expectTrue "erc4626 asset ECM rejects non-32-byte returndata"
    (contains erc4626AssetYul "if iszero(eq(returndatasize(), 32)) {")
  expectTrue "erc4626 asset ECM ABI-encodes the selector at free memory"
    (contains erc4626AssetYul "mstore(__erc4626_asset_ptr, shl(224, 0x38d52e0f))")
  expectTrue "erc4626 asset ECM masks the returned address"
    (contains erc4626AssetYul "assetAddr := and(mload(__erc4626_asset_ptr), 0xffffffffffffffffffffffffffffffffffffffff)")
  let erc4626MaxDepositYul ←
    expectCompileToYul "erc4626 maxDeposit smoke spec" erc4626MaxDepositSmokeSpec
  expectTrue "erc4626 maxDeposit ECM lowers to staticcall"
    (contains erc4626MaxDepositYul "staticcall(gas(), vault, __erc4626_maxDeposit_ptr, 36, __erc4626_maxDeposit_ptr, 32)")
  expectTrue "erc4626 maxDeposit ECM forwards revert returndata"
    (contains erc4626MaxDepositYul "returndatacopy(0, 0, __erc4626_rds)")
  expectTrue "erc4626 maxDeposit ECM rejects non-32-byte returndata"
    (contains erc4626MaxDepositYul "if iszero(eq(returndatasize(), 32)) {")
  expectTrue "erc4626 maxDeposit ECM ABI-encodes the selector at free memory"
    (contains erc4626MaxDepositYul "mstore(__erc4626_maxDeposit_ptr, shl(224, 0x402d267d))")
  let erc4626MaxMintYul ←
    expectCompileToYul "erc4626 maxMint smoke spec" erc4626MaxMintSmokeSpec
  expectTrue "erc4626 maxMint ECM lowers to staticcall"
    (contains erc4626MaxMintYul "staticcall(gas(), vault, __erc4626_maxMint_ptr, 36, __erc4626_maxMint_ptr, 32)")
  expectTrue "erc4626 maxMint ECM forwards revert returndata"
    (contains erc4626MaxMintYul "returndatacopy(0, 0, __erc4626_rds)")
  expectTrue "erc4626 maxMint ECM rejects non-32-byte returndata"
    (contains erc4626MaxMintYul "if iszero(eq(returndatasize(), 32)) {")
  expectTrue "erc4626 maxMint ECM ABI-encodes the selector at free memory"
    (contains erc4626MaxMintYul "mstore(__erc4626_maxMint_ptr, shl(224, 0xc63d75b6))")
  let erc4626MaxWithdrawYul ←
    expectCompileToYul "erc4626 maxWithdraw smoke spec" erc4626MaxWithdrawSmokeSpec
  expectTrue "erc4626 maxWithdraw ECM lowers to staticcall"
    (contains erc4626MaxWithdrawYul "staticcall(gas(), vault, __erc4626_maxWithdraw_ptr, 36, __erc4626_maxWithdraw_ptr, 32)")
  expectTrue "erc4626 maxWithdraw ECM forwards revert returndata"
    (contains erc4626MaxWithdrawYul "returndatacopy(0, 0, __erc4626_rds)")
  expectTrue "erc4626 maxWithdraw ECM rejects non-32-byte returndata"
    (contains erc4626MaxWithdrawYul "if iszero(eq(returndatasize(), 32)) {")
  expectTrue "erc4626 maxWithdraw ECM ABI-encodes the selector at free memory"
    (contains erc4626MaxWithdrawYul "mstore(__erc4626_maxWithdraw_ptr, shl(224, 0xce96cb77))")
  let erc4626MaxRedeemYul ←
    expectCompileToYul "erc4626 maxRedeem smoke spec" erc4626MaxRedeemSmokeSpec
  expectTrue "erc4626 maxRedeem ECM lowers to staticcall"
    (contains erc4626MaxRedeemYul "staticcall(gas(), vault, __erc4626_maxRedeem_ptr, 36, __erc4626_maxRedeem_ptr, 32)")
  expectTrue "erc4626 maxRedeem ECM forwards revert returndata"
    (contains erc4626MaxRedeemYul "returndatacopy(0, 0, __erc4626_rds)")
  expectTrue "erc4626 maxRedeem ECM rejects non-32-byte returndata"
    (contains erc4626MaxRedeemYul "if iszero(eq(returndatasize(), 32)) {")
  expectTrue "erc4626 maxRedeem ECM ABI-encodes the selector at free memory"
    (contains erc4626MaxRedeemYul "mstore(__erc4626_maxRedeem_ptr, shl(224, 0xd905777e))")
  let erc4626DepositYul ←
    expectCompileToYul "erc4626 deposit smoke spec" erc4626DepositSmokeSpec
  expectTrue "erc4626 deposit ECM lowers to call"
    (contains erc4626DepositYul "call(gas(), vault, 0, __erc4626_deposit_ptr, 68, __erc4626_deposit_ptr, 32)")
  expectTrue "erc4626 deposit ECM forwards revert returndata"
    (contains erc4626DepositYul "returndatacopy(0, 0, __erc4626_rds)")
  expectTrue "erc4626 deposit ECM rejects non-32-byte returndata"
    (contains erc4626DepositYul "if iszero(eq(returndatasize(), 32)) {")
  expectTrue "erc4626 deposit ECM ABI-encodes the selector at free memory"
    (contains erc4626DepositYul "mstore(__erc4626_deposit_ptr, shl(224, 0x6e553f65))")
  let macroEcrecoverYul ←
    expectCompileToYul "macro ecrecover smoke spec" MacroEcrecoverSmoke.MacroEcrecover.spec
  expectTrue "macro ecrecover bind elaborates to the same ECM lowering"
    (contains macroEcrecoverYul "staticcall(gas(), 1, __ecr_ptr, 128, __ecr_ptr, 32)")
  let macroTrustReport := emitTrustReportJson [MacroEcrecoverSmoke.MacroEcrecover.spec]
  expectTrue "macro ecrecover trust report surfaces the precompile assumption"
    (contains macroTrustReport "\"module\":\"ecrecover\"" &&
      contains macroTrustReport "\"assumption\":\"evm_ecrecover_precompile\"")
  let macroKeccakYul ←
    expectCompileToYul "macro keccak smoke spec" MacroKeccakSmoke.MacroKeccak.spec
  expectTrue "macro keccak primitive lowers to the Yul keccak256 builtin"
    (contains macroKeccakYul "keccak256(offset, size)")
  let macroKeccakTrustReport := emitTrustReportJson [MacroKeccakSmoke.MacroKeccak.spec]
  expectTrue "macro keccak trust report surfaces the named primitive assumption"
    (contains macroKeccakTrustReport "\"primitive\":\"keccak256\"" &&
      contains macroKeccakTrustReport "\"assumption\":\"keccak256_memory_slice_matches_evm\"")
  let macroTransientYul ←
    expectCompileToYul "macro transient storage smoke spec" MacroTransientStorageSmoke.MacroTransientStorage.spec
  expectTrue "macro transient storage lowers to the Yul transient builtins"
    (contains macroTransientYul "tstore(" &&
      contains macroTransientYul "tload(")
  expectTrue "macro transient storage executable path uses the transient state map"
    MacroTransientStorageSmoke.warmExecutableWritesTransientStorage
  expectTrue "macro transient storage round-trips across executable calls"
    MacroTransientStorageSmoke.transientStoragePersistsAcrossExecutableCalls
  let macroTransientTrustReport := emitTrustReportJson [MacroTransientStorageSmoke.MacroTransientStorage.spec]
  expectTrue "macro transient storage trust report surfaces low-level mechanics"
    (contains macroTransientTrustReport "\"modeledLowLevelMechanics\"" &&
      contains macroTransientTrustReport "\"tstore\"" &&
      contains macroTransientTrustReport "\"tload\"")
  let macroBlobbasefeeYul ←
    expectCompileToYul "macro blobbasefee smoke spec" MacroBlobbasefeeSmoke.MacroBlobbasefee.spec
  expectTrue "macro blobbasefee lowers to the Yul blobbasefee builtin"
    (contains macroBlobbasefeeYul "blobbasefee()")
  expectTrue "macro blobbasefee executable path uses ContractState"
    MacroBlobbasefeeSmoke.executableUsesContractState
  let macroBlobbasefeeTrustReport := emitTrustReportJson [MacroBlobbasefeeSmoke.MacroBlobbasefee.spec]
  expectTrue "macro blobbasefee trust report surfaces the post-core builtin"
    (contains macroBlobbasefeeTrustReport "\"modeledLowLevelMechanics\"" &&
      contains macroBlobbasefeeTrustReport "\"blobbasefee\"")
  -- Regression for issue #1829: blobbasefee must also surface under the
  -- runtime-introspection category so that --deny-runtime-introspection
  -- fails closed on the post-Dencun environment opcode.
  expectTrue "macro blobbasefee trust report classifies the builtin under runtime introspection"
    (contains macroBlobbasefeeTrustReport
      "\"partiallyModeledRuntimeIntrospection\":[\"blobbasefee\"]")
  let macroExternalYul ←
    expectCompileToYul "macro external smoke spec" MacroExternalSmoke.MacroExternal.spec
  expectTrue "macro externalCall lowers to the linked external symbol"
    (contains macroExternalYul "let echoed := echo(next)")
  let macroExternalTrustReport := emitTrustReportJson [MacroExternalSmoke.MacroExternal.spec]
  expectTrue "macro externals surface in the trust report"
    (contains macroExternalTrustReport "\"linkedExternals\"" &&
      contains macroExternalTrustReport "\"echo\"" &&
      contains macroExternalTrustReport "\"linkMode\":\"objectLinked\"")
  let macroLinkModeTrustReport := emitTrustReportJson [MacroExternalLinkModeSmoke.linkModeTrustSurfaceSpec]
  expectTrue "macro external link modes surface in the trust report"
    (contains macroLinkModeTrustReport "\"linkMode\":\"external\"" &&
      contains macroLinkModeTrustReport "\"linkMode\":\"objectLinked\"" &&
      contains macroLinkModeTrustReport "\"linkMode\":\"inline\"" &&
      contains macroLinkModeTrustReport "\"linkMode\":\"compilerRuntime\"")
  let macroPowTrustReport := emitTrustReportJson [Contracts.Smoke.Uint256PowSmoke.spec]
  expectTrue "macro pow builtin does not surface as a linked external"
    (!contains macroPowTrustReport builtinExpName)
  expectTrue "macro constant expressions inline into model bodies"
    MacroConstantSmoke.feeOnModelInlinesContractConstants
  expectTrue "macro address constants inline through the executable and model paths"
    (MacroConstantSmoke.treasuryAddrModelInlinesAddressConstant &&
      MacroConstantSmoke.treasuryExecutableUsesGeneratedConstantDef)
  expectTrue "macro nested constants inline transitively"
    MacroConstantSmoke.treasuryAsWordModelInlinesNestedConstants
  expectTrue "macro locals and params shadow contract constants"
    MacroConstantSmoke.shadowedConstantModelPrefersLocalAndParamBindings

/- Regression for lfglabs-dev/verity#1961. Identifier-shape validation must treat the two external
forms differently: an ABI-boundary external derived from a typed `interface` carries a dotted
`Interface.method` audit label (`IPool.supply`) that is lowered by selector and never emitted as a
Yul identifier, so it must be accepted; an object-linked external's name is the Yul function
identifier at the link site, so an invalid one must still be rejected. -/
namespace ExternalNameValidationSmoke

private def dottedAbiInterfaceSpec : CompilationModel := {
  name := "DottedAbiInterface"
  fields := []
  «constructor» := none
  externals := [
    { name := "IPool.supply"
      params := [ParamType.address, ParamType.uint256, ParamType.address, ParamType.uint16]
      returnType := none
      returns := []
      axiomNames := []
      linkMode := .external }
  ]
  functions := []
}

private def invalidObjectLinkedSpec : CompilationModel := {
  name := "InvalidObjectLinkedExternal"
  fields := []
  «constructor» := none
  externals := [
    { name := "poseidon-hash"
      params := [ParamType.uint256]
      returnType := some ParamType.uint256
      returns := [ParamType.uint256]
      axiomNames := []
      linkMode := .objectLinked }
  ]
  functions := []
}

private def dottedObjectLinkedSpec : CompilationModel := {
  name := "DottedObjectLinkedExternal"
  fields := []
  «constructor» := none
  externals := [
    { name := "Poseidon.hash"
      params := [ParamType.uint256]
      returnType := some ParamType.uint256
      returns := [ParamType.uint256]
      axiomNames := []
      linkMode := .objectLinked }
  ]
  functions := []
}

#eval! do
  expectTrue "dotted ABI-interface external names skip Yul identifier validation"
    (match validateIdentifierShapes dottedAbiInterfaceSpec with
      | .ok _ => true
      | .error _ => false)
  expectTrue "object-linked external names still require valid Yul identifiers"
    (match validateIdentifierShapes invalidObjectLinkedSpec with
      | .ok _ => false
      | .error _ => true)
  expectTrue "dotted object-linked external names are rejected"
    (match validateIdentifierShapes dottedObjectLinkedSpec with
      | .ok _ => false
      | .error _ => true)

end ExternalNameValidationSmoke

namespace NonreentrantForkCompatibilitySmoke

/-! ## Bugbot #1968: `nonreentrant(<lock>)` ↔ `targetFork` pre-check

The synthesised transient-storage reentrancy guard (#1893) emits
`tload`/`tstore` opcodes that only exist on EIP-1153 (Cancun+). Emitting
them on a pre-Cancun chain would either fail at deploy time or
silently no-op depending on the toolchain, while validation still
granted the function a CEI exemption, leaving the post-external-call
reentry window open. The pre-check rejects the spec at compile time
so the bug cannot be expressed in a successful build. -/

private def preCancelForkSpec : CompilationModel := {
  name := "PreCancelNonreentrant"
  fields := [{ name := "lock", ty := FieldType.uint256, «slot» := some 0 }]
  «constructor» := none
  functions := [
    { name := "guarded"
      params := []
      returnType := none
      nonReentrantLock := some "lock"
      body := [Stmt.stop]
    }
  ]
}

/-- Cancun allows the annotation: validation succeeds. -/
def nonreentrantAcceptedOnCancun : Bool :=
  match Compiler.CompilationModel.validateCompileInputs
          preCancelForkSpec (selectorsFor preCancelForkSpec)
          Verity.Core.Intrinsics.HardFork.cancun with
  | .ok _ => true
  | .error _ => false

example : nonreentrantAcceptedOnCancun = true := by native_decide

/-- Cancun (or any fork that ranks ≥ Cancun) is the in-tree minimum;
the pre-check accepts the spec because the synthesised tload/tstore
guard is sound on those chains. The driver passes the actual
`options.targetFork` through `compile` so a future pre-Cancun fork
constructor hits the rejection branch automatically. -/
def nonreentrantValidateForkCompatCancun : Bool :=
  match Compiler.CompilationModel.validateNonReentrantForkCompatibility
          Verity.Core.Intrinsics.HardFork.cancun preCancelForkSpec with
  | .ok _ => true
  | .error _ => false

example : nonreentrantValidateForkCompatCancun = true := by native_decide

/-- Specs without `nonreentrant(<lock>)` are unaffected by the
pre-check: the gate is independent of fork rank. -/
def nonreentrantValidateForkCompatPrague : Bool :=
  match Compiler.CompilationModel.validateNonReentrantForkCompatibility
          Verity.Core.Intrinsics.HardFork.prague preCancelForkSpec with
  | .ok _ => true
  | .error _ => false

example : nonreentrantValidateForkCompatPrague = true := by native_decide

/-- Driver path: `compile` is invoked with the actual `targetFork`,
and the spec still succeeds under Cancun (the synthesised tload/tstore
guard is emitted). -/
def nonreentrantCompileAcceptedAtCancun : Bool :=
  match Compiler.CompilationModel.compile
          preCancelForkSpec (selectorsFor preCancelForkSpec)
          Verity.Core.Intrinsics.HardFork.cancun with
  | .ok _ => true
  | .error _ => false

/-- The default `compile` (no explicit fork) keeps the historical
Cancun assumption so single-arg callers, tests, and proof modules
continue to work. -/
def nonreentrantCompileAcceptedAtDefaultFork : Bool :=
  match Compiler.CompilationModel.compile preCancelForkSpec (selectorsFor preCancelForkSpec) with
  | .ok _ => true
  | .error _ => false

#eval! do
  expectTrue "nonreentrant(<lock>) passes validateCompileInputs on Cancun"
    nonreentrantAcceptedOnCancun
  expectTrue "nonreentrant(<lock>) still compiles under the default Cancun assumption"
    nonreentrantCompileAcceptedAtDefaultFork
  expectTrue "nonreentrant(<lock>) compiles under explicit Cancun fork"
    nonreentrantCompileAcceptedAtCancun
  expectTrue "validateNonReentrantForkCompatibility accepts the spec on Cancun"
    nonreentrantValidateForkCompatCancun
  expectTrue "validateNonReentrantForkCompatibility accepts the spec on Prague"
    nonreentrantValidateForkCompatPrague

end NonreentrantForkCompatibilitySmoke

end Compiler.CompilationModelFeatureTest

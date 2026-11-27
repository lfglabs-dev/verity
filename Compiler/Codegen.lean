import Compiler.CodegenCommon
import Compiler.Yul.PatchRules
import Compiler.Yul.TempReuse

namespace Compiler

open Yul

abbrev BackendProfile := Compiler.CodegenCommon.BackendProfile
abbrev YulEmitOptions := Compiler.CodegenCommon.YulEmitOptions

def mappingSlotFuncAt := Compiler.CodegenCommon.mappingSlotFuncAt
def callvalueGuard := Compiler.CodegenCommon.callvalueGuard
def calldatasizeGuard := Compiler.CodegenCommon.calldatasizeGuard
def dispatchBody := Compiler.CodegenCommon.dispatchBody
def defaultDispatchCase := Compiler.CodegenCommon.defaultDispatchCase
def buildSwitch := Compiler.CodegenCommon.buildSwitch
def runtimeCode := Compiler.CodegenCommon.runtimeCode
def emitYul := Compiler.CodegenCommon.emitYul

/-- `emitYul` followed by temporary reuse and scratch-memory spilling
(`Compiler.Yul.TempReuse.reuseAndSpillTempsDispatchedObject`), for Yul that is handed to solc
(import model drivers): blocks with many live temporaries otherwise fail with StackTooDeep
(#2831). Each section or dispatch case is spilled only when its spill words are statically
checked to be disjoint from all of its other memory accesses (either static literal offsets
below `defaultSpillBase` or free-memory-pointer allocations raised above `highWater`); other
sections and cases are left unchanged. -/
def emitYulSpilled (contract : IRContract) : YulObject :=
  Yul.TempReuse.reuseAndSpillTempsDispatchedObject Yul.TempReuse.defaultMaxStackLocals
    (emitYul contract)

private def patchBackend : Compiler.CodegenCommon.PatchBackend :=
  { apply := fun base options =>
      let rewriteBundle := Yul.rewriteBundleForId options.patchConfig.rewriteBundleId
      let requiredProofRefs :=
        if options.patchConfig.requiredProofRefs.isEmpty then
          Yul.rewriteProofAllowlistForId rewriteBundle.id
        else
          options.patchConfig.requiredProofRefs
      let patchConfig :=
        { options.patchConfig with
          requiredProofRefs := requiredProofRefs }
      let runtimePatchReport := Yul.runPatchPassWithBlocks
        patchConfig
        rewriteBundle.exprRules
        rewriteBundle.stmtRules
        rewriteBundle.blockRules
        base.runtimeCode
      let runtimePatched := { base with runtimeCode := runtimePatchReport.patched }
      let objectReport := Yul.runPatchPassWithObjects
        patchConfig
        []
        []
        []
        rewriteBundle.objectRules
        runtimePatched
      let mergedPatchReport : Yul.PatchPassReport :=
        { patched := objectReport.patched.runtimeCode
          iterations := runtimePatchReport.iterations + objectReport.iterations
          manifest := runtimePatchReport.manifest ++ objectReport.manifest }
      { patched := objectReport.patched
        patchReport := mergedPatchReport } }

def emitYulWithOptions (contract : IRContract) (options : YulEmitOptions) : YulObject :=
  Compiler.CodegenCommon.optimizeCheckedArithmeticObjectIfAvailable contract
    (Compiler.CodegenCommon.emitYulWithOptions patchBackend contract options)

def emitYulWithOptionsReport (contract : IRContract) (options : YulEmitOptions) :
    YulObject × Yul.PatchPassReport :=
  let report := Compiler.CodegenCommon.emitYulWithOptionsReport patchBackend contract options
  (Compiler.CodegenCommon.optimizeCheckedArithmeticObjectIfAvailable contract report.1, report.2)

/-- Regression guard:
    expression/statement/block patching remains runtime-scoped (deploy is unchanged),
    and runtime patch reporting excludes deploy-only candidates. -/
example :
    let deployMarker := "__deploy_marker"
    let runtimeMarker := "__runtime_marker"
    let contract : IRContract :=
      { name := "ScopeRegression"
        deploy := [.exprStmt (.call "add" [.ident deployMarker, .lit 0])]
        constructorPayable := true
        functions :=
          [{ name := "f"
             selector := 1
             params := []
             ret := .unit
             payable := false
             body := [.exprStmt (.call "add" [.ident runtimeMarker, .lit 0])] }]
        usesMapping := false }
    let options : YulEmitOptions := { patchConfig := { enabled := true, maxIterations := 2 } }
    let report := emitYulWithOptionsReport contract options
    let rendered := Yul.render report.1
    let deployStillHasMarker := Compiler.CodegenCommon.contains rendered s!"add({deployMarker}, 0)"
    let runtimeNoLongerHasMarker := !(Compiler.CodegenCommon.contains rendered s!"add({runtimeMarker}, 0)")
    let runtimeMatchCount :=
      report.2.manifest.foldl
        (fun acc entry =>
          if entry.patchName = "add-zero-right" then acc + entry.matchCount else acc)
        0
    deployStillHasMarker && runtimeNoLongerHasMarker && runtimeMatchCount == 1 := by
  native_decide

end Compiler

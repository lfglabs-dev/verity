import Std
import Compiler.Selector
import Compiler.ABI
import Compiler.ModuleInput
import Compiler.CompilationModel.Compile
import Compiler.CompilationModel.EventEmission
import Compiler.Yul.PrettyPrint
import Compiler.Linker
import Compiler.CompilationModel.LayoutCompatibilityReport
import Compiler.CompilationModel.LayoutReport
import Compiler.CompilationModel.TrustSurface
import Compiler.CodegenCommon

namespace Compiler.CompileDriverCommon

open Compiler
open Compiler.CompilationModel
open Compiler.Linker
open Compiler.Selector
open Compiler.Yul

abbrev YulEmitOptions := Compiler.CodegenCommon.YulEmitOptions

def parseTargetFork? (raw : String) : Option Verity.Core.Intrinsics.HardFork :=
  Verity.Core.Intrinsics.HardFork.parse? raw

private def parseTomlStringValue? (line : String) : Option String :=
  match line.splitOn "=" with
  | _ :: rhsParts =>
      let rhs := String.intercalate "=" rhsParts
      let value := (rhs.splitOn "#").head!.trim
      match value.splitOn "\"" with
      | _ :: quoted :: _ => some quoted.trim
      | _ => some value
  | _ => none

def tamaTomlTargetFork? : IO (Option Verity.Core.Intrinsics.HardFork) := do
  try
    let text ← IO.FS.readFile "tama.toml"
    let rec scan (inYul : Bool) : List String → Option String
      | [] => none
      | line :: rest =>
          let trimmed := line.trim
          if trimmed.startsWith "[" then
            scan (trimmed == "[yul]") rest
          else if inYul && trimmed.startsWith "evm_version" then
            parseTomlStringValue? trimmed
          else
            scan inYul rest
    pure <| (scan false (text.splitOn "\n")).bind parseTargetFork?
  catch _ =>
    pure none

structure CodegenBackend where
  emitYulWithOptionsReport : IRContract → YulEmitOptions → YulObject × Yul.PatchPassReport

private def orThrow (r : Except String Unit) : IO Unit :=
  match r with
  | .error err => throw (IO.userError err)
  | .ok () => pure ()

private def reportRow (contractName : String) (report : Yul.PatchPassReport) : List String :=
  match report.manifest with
  | [] =>
      [s!"{contractName}\t{report.iterations}\t-\t0\t0\t-"]
  | entries =>
      entries.map (fun entry =>
        s!"{contractName}\t{report.iterations}\t{entry.patchName}\t{entry.matchCount}\t{entry.changedNodes}\t{entry.proofRef}")

private def renderPatchReportTsv (rows : List (String × Yul.PatchPassReport)) : String :=
  let header := "contract\titerations\tpatch_name\tmatch_count\tchanged_nodes\tproof_ref"
  let body := rows.foldr (fun (contractName, report) acc => reportRow contractName report ++ acc) []
  String.intercalate "\n" (header :: body) ++ "\n"

private def parentDir? (path : String) : Option String :=
  match path.splitOn "/" |>.reverse with
  | [] | [_] => none
  | _file :: revParents =>
      let parent := String.intercalate "/" revParents.reverse
      if parent.isEmpty then
        if path.startsWith "/" then some "/" else none
      else
        some parent

private def ensureParentDirExists (path : String) : IO Unit := do
  match parentDir? path with
  | some dir => IO.FS.createDirAll dir
  | none => pure ()

private def writePatchReport (path : String) (rows : List (String × Yul.PatchPassReport)) : IO Unit := do
  ensureParentDirExists path
  IO.FS.writeFile path (renderPatchReportTsv rows)

private def writeTrustReport (path : String) (specs : List CompilationModel) : IO Unit := do
  ensureParentDirExists path
  IO.FS.writeFile path (emitTrustReportJson specs ++ "\n")

private def writeAssumptionReport (path : String) (specs : List CompilationModel) : IO Unit := do
  ensureParentDirExists path
  IO.FS.writeFile path (emitAssumptionReportJson specs ++ "\n")

private def writeLayoutReport (path : String) (specs : List CompilationModel) : IO Unit := do
  ensureParentDirExists path
  IO.FS.writeFile path (emitLayoutReportJson specs ++ "\n")

private def requireLayoutCompatibilityPair
    (specs : List CompilationModel) : IO (CompilationModel × CompilationModel) :=
  match specs with
  | [baseline, candidate] => pure (baseline, candidate)
  | _ =>
      throw (IO.userError
        "Layout compatibility comparison requires exactly 2 selected contracts (baseline first, candidate second)")

private def writeLayoutCompatibilityReport
    (path : String)
    (specs : List CompilationModel) : IO Unit := do
  let (baseline, candidate) ← requireLayoutCompatibilityPair specs
  ensureParentDirExists path
  IO.FS.writeFile path (emitLayoutCompatibilityReportJson baseline candidate ++ "\n")

private structure IntrinsicUse where
  name : String
  minFork : Verity.Core.Intrinsics.HardFork

private partial def collectIntrinsicUsesExpr : Expr → List IntrinsicUse
  | .call gas target value inOffset inSize outOffset outSize =>
      [gas, target, value, inOffset, inSize, outOffset, outSize].flatMap collectIntrinsicUsesExpr
  | .staticcall gas target inOffset inSize outOffset outSize =>
      [gas, target, inOffset, inSize, outOffset, outSize].flatMap collectIntrinsicUsesExpr
  | .delegatecall gas target inOffset inSize outOffset outSize =>
      [gas, target, inOffset, inSize, outOffset, outSize].flatMap collectIntrinsicUsesExpr
  | .keccak256 offset size
  | .add offset size | .sub offset size | .mul offset size | .div offset size
  | .sdiv offset size | .mod offset size | .smod offset size
  | .bitAnd offset size | .bitOr offset size | .bitXor offset size
  | .shl offset size | .shr offset size | .sar offset size
  | .byte offset size | .signextend offset size
  | .eq offset size | .ge offset size | .gt offset size | .sgt offset size
  | .lt offset size | .slt offset size | .le offset size
  | .logicalAnd offset size | .logicalOr offset size
  | .ceilDiv offset size | .wMulDown offset size | .wDivUp offset size
  | .min offset size | .max offset size =>
      collectIntrinsicUsesExpr offset ++ collectIntrinsicUsesExpr size
  | .mulDivDown a b c | .mulDivUp a b c
  | .mulDiv512Down a b c | .mulDiv512Up a b c
  | .ite a b c =>
      collectIntrinsicUsesExpr a ++ collectIntrinsicUsesExpr b ++ collectIntrinsicUsesExpr c
  | .bitNot value | .logicalNot value | .mload value | .tload value
  | .calldataload value | .extcodesize value | .returndataOptionalBoolAt value
  | .mapping _ value | .mappingWord _ value _ | .mappingPackedWord _ value _ _
  | .mappingUint _ value | .structMember _ value _
  | .storageArrayElement _ value | .arrayElement _ value
  | .memoryArrayElement _ value | .arrayElementWord _ value _ _
  | .arrayElementDynamicWord _ value _
  | .arrayElementDynamicDataOffset _ value
  | .arrayElementDynamicMemberLength _ value _
  | .paramDynamicMemberElement _ _ value
  | .arrayElementDynamicMemberDataOffset _ value _
  | .adtConstruct _ _ [value] =>
      collectIntrinsicUsesExpr value
  | .mapping2 _ a b | .mapping2Word _ a b _ | .structMember2 _ a b _
  | .arrayElementDynamicMemberElement _ a _ b =>
      collectIntrinsicUsesExpr a ++ collectIntrinsicUsesExpr b
  | .mappingChain _ keys | .externalCall _ keys | .internalCall _ keys
  | .adtConstruct _ _ keys =>
      keys.flatMap collectIntrinsicUsesExpr
  | .intrinsic name _ minFork args =>
      { name := name, minFork := minFork } :: args.flatMap collectIntrinsicUsesExpr
  | .forkIfAtLeast _ thenExpr elseExpr =>
      collectIntrinsicUsesExpr thenExpr ++ collectIntrinsicUsesExpr elseExpr
  | .dynamicBytesEq _ _ =>
      []
  | _ => []

private partial def specializeForkExpr
    (targetFork : Verity.Core.Intrinsics.HardFork) : Expr → Expr
  | .mapping field key => .mapping field (specializeForkExpr targetFork key)
  | .mappingWord field key wordOffset => .mappingWord field (specializeForkExpr targetFork key) wordOffset
  | .mappingPackedWord field key wordOffset packed => .mappingPackedWord field (specializeForkExpr targetFork key) wordOffset packed
  | .mapping2 field key1 key2 => .mapping2 field (specializeForkExpr targetFork key1) (specializeForkExpr targetFork key2)
  | .mapping2Word field key1 key2 wordOffset => .mapping2Word field (specializeForkExpr targetFork key1) (specializeForkExpr targetFork key2) wordOffset
  | .mappingUint field key => .mappingUint field (specializeForkExpr targetFork key)
  | .mappingChain field keys => .mappingChain field (keys.map (specializeForkExpr targetFork))
  | .structMember field key memberName => .structMember field (specializeForkExpr targetFork key) memberName
  | .structMember2 field key1 key2 memberName => .structMember2 field (specializeForkExpr targetFork key1) (specializeForkExpr targetFork key2) memberName
  | .extcodesize addr => .extcodesize (specializeForkExpr targetFork addr)
  | .mload offset => .mload (specializeForkExpr targetFork offset)
  | .tload offset => .tload (specializeForkExpr targetFork offset)
  | .keccak256 offset size => .keccak256 (specializeForkExpr targetFork offset) (specializeForkExpr targetFork size)
  | .call gas target value inOffset inSize outOffset outSize =>
      .call (specializeForkExpr targetFork gas) (specializeForkExpr targetFork target)
        (specializeForkExpr targetFork value) (specializeForkExpr targetFork inOffset)
        (specializeForkExpr targetFork inSize) (specializeForkExpr targetFork outOffset)
        (specializeForkExpr targetFork outSize)
  | .staticcall gas target inOffset inSize outOffset outSize =>
      .staticcall (specializeForkExpr targetFork gas) (specializeForkExpr targetFork target)
        (specializeForkExpr targetFork inOffset) (specializeForkExpr targetFork inSize)
        (specializeForkExpr targetFork outOffset) (specializeForkExpr targetFork outSize)
  | .delegatecall gas target inOffset inSize outOffset outSize =>
      .delegatecall (specializeForkExpr targetFork gas) (specializeForkExpr targetFork target)
        (specializeForkExpr targetFork inOffset) (specializeForkExpr targetFork inSize)
        (specializeForkExpr targetFork outOffset) (specializeForkExpr targetFork outSize)
  | .calldataload offset => .calldataload (specializeForkExpr targetFork offset)
  | .returndataOptionalBoolAt outOffset => .returndataOptionalBoolAt (specializeForkExpr targetFork outOffset)
  | .externalCall name args => .externalCall name (args.map (specializeForkExpr targetFork))
  | .internalCall name args => .internalCall name (args.map (specializeForkExpr targetFork))
  | .arrayElement name index => .arrayElement name (specializeForkExpr targetFork index)
  | .memoryArrayElement name index => .memoryArrayElement name (specializeForkExpr targetFork index)
  | .arrayElementWord name index elementWords wordOffset => .arrayElementWord name (specializeForkExpr targetFork index) elementWords wordOffset
  | .arrayElementDynamicWord name index wordOffset => .arrayElementDynamicWord name (specializeForkExpr targetFork index) wordOffset
  | .arrayElementDynamicDataOffset name index => .arrayElementDynamicDataOffset name (specializeForkExpr targetFork index)
  | .paramDynamicMemberElement name wordOffset innerIndex => .paramDynamicMemberElement name wordOffset (specializeForkExpr targetFork innerIndex)
  | .arrayElementDynamicMemberLength name index wordOffset => .arrayElementDynamicMemberLength name (specializeForkExpr targetFork index) wordOffset
  | .arrayElementDynamicMemberDataOffset name index wordOffset => .arrayElementDynamicMemberDataOffset name (specializeForkExpr targetFork index) wordOffset
  | .arrayElementDynamicMemberElement name index wordOffset innerIndex =>
      .arrayElementDynamicMemberElement name (specializeForkExpr targetFork index) wordOffset (specializeForkExpr targetFork innerIndex)
  | .storageArrayElement field index => .storageArrayElement field (specializeForkExpr targetFork index)
  | .add a b => .add (specializeForkExpr targetFork a) (specializeForkExpr targetFork b)
  | .sub a b => .sub (specializeForkExpr targetFork a) (specializeForkExpr targetFork b)
  | .mul a b => .mul (specializeForkExpr targetFork a) (specializeForkExpr targetFork b)
  | .div a b => .div (specializeForkExpr targetFork a) (specializeForkExpr targetFork b)
  | .sdiv a b => .sdiv (specializeForkExpr targetFork a) (specializeForkExpr targetFork b)
  | .mod a b => .mod (specializeForkExpr targetFork a) (specializeForkExpr targetFork b)
  | .smod a b => .smod (specializeForkExpr targetFork a) (specializeForkExpr targetFork b)
  | .bitAnd a b => .bitAnd (specializeForkExpr targetFork a) (specializeForkExpr targetFork b)
  | .bitOr a b => .bitOr (specializeForkExpr targetFork a) (specializeForkExpr targetFork b)
  | .bitXor a b => .bitXor (specializeForkExpr targetFork a) (specializeForkExpr targetFork b)
  | .bitNot a => .bitNot (specializeForkExpr targetFork a)
  | .shl a b => .shl (specializeForkExpr targetFork a) (specializeForkExpr targetFork b)
  | .shr a b => .shr (specializeForkExpr targetFork a) (specializeForkExpr targetFork b)
  | .sar a b => .sar (specializeForkExpr targetFork a) (specializeForkExpr targetFork b)
  | .byte a b => .byte (specializeForkExpr targetFork a) (specializeForkExpr targetFork b)
  | .signextend a b => .signextend (specializeForkExpr targetFork a) (specializeForkExpr targetFork b)
  | .intrinsic name lowering minFork args => .intrinsic name lowering minFork (args.map (specializeForkExpr targetFork))
  | .forkIfAtLeast required thenExpr elseExpr =>
      specializeForkExpr targetFork
        (if Verity.Core.Intrinsics.HardFork.allows targetFork required then thenExpr else elseExpr)
  | .eq a b => .eq (specializeForkExpr targetFork a) (specializeForkExpr targetFork b)
  | .ge a b => .ge (specializeForkExpr targetFork a) (specializeForkExpr targetFork b)
  | .gt a b => .gt (specializeForkExpr targetFork a) (specializeForkExpr targetFork b)
  | .sgt a b => .sgt (specializeForkExpr targetFork a) (specializeForkExpr targetFork b)
  | .lt a b => .lt (specializeForkExpr targetFork a) (specializeForkExpr targetFork b)
  | .slt a b => .slt (specializeForkExpr targetFork a) (specializeForkExpr targetFork b)
  | .le a b => .le (specializeForkExpr targetFork a) (specializeForkExpr targetFork b)
  | .logicalAnd a b => .logicalAnd (specializeForkExpr targetFork a) (specializeForkExpr targetFork b)
  | .logicalOr a b => .logicalOr (specializeForkExpr targetFork a) (specializeForkExpr targetFork b)
  | .logicalNot a => .logicalNot (specializeForkExpr targetFork a)
  | .ceilDiv a b => .ceilDiv (specializeForkExpr targetFork a) (specializeForkExpr targetFork b)
  | .mulDivDown a b c => .mulDivDown (specializeForkExpr targetFork a) (specializeForkExpr targetFork b) (specializeForkExpr targetFork c)
  | .mulDivUp a b c => .mulDivUp (specializeForkExpr targetFork a) (specializeForkExpr targetFork b) (specializeForkExpr targetFork c)
  | .mulDiv512Down a b c => .mulDiv512Down (specializeForkExpr targetFork a) (specializeForkExpr targetFork b) (specializeForkExpr targetFork c)
  | .mulDiv512Up a b c => .mulDiv512Up (specializeForkExpr targetFork a) (specializeForkExpr targetFork b) (specializeForkExpr targetFork c)
  | .wMulDown a b => .wMulDown (specializeForkExpr targetFork a) (specializeForkExpr targetFork b)
  | .wDivUp a b => .wDivUp (specializeForkExpr targetFork a) (specializeForkExpr targetFork b)
  | .min a b => .min (specializeForkExpr targetFork a) (specializeForkExpr targetFork b)
  | .max a b => .max (specializeForkExpr targetFork a) (specializeForkExpr targetFork b)
  | .ite a b c => .ite (specializeForkExpr targetFork a) (specializeForkExpr targetFork b) (specializeForkExpr targetFork c)
  | .adtConstruct adt variant args => .adtConstruct adt variant (args.map (specializeForkExpr targetFork))
  | other => other

private partial def specializeForkStmt
    (targetFork : Verity.Core.Intrinsics.HardFork) : Stmt → Stmt
  | .letVar name value => .letVar name (specializeForkExpr targetFork value)
  | .assignVar name value => .assignVar name (specializeForkExpr targetFork value)
  | .setStorage field value => .setStorage field (specializeForkExpr targetFork value)
  | .setStorageAddr field value => .setStorageAddr field (specializeForkExpr targetFork value)
  | .setStorageWord field wordOffset value => .setStorageWord field wordOffset (specializeForkExpr targetFork value)
  | .storageArrayPush field value => .storageArrayPush field (specializeForkExpr targetFork value)
  | .setStorageArrayElement field index value => .setStorageArrayElement field (specializeForkExpr targetFork index) (specializeForkExpr targetFork value)
  | .setMapping field key value => .setMapping field (specializeForkExpr targetFork key) (specializeForkExpr targetFork value)
  | .setMappingWord field key wordOffset value => .setMappingWord field (specializeForkExpr targetFork key) wordOffset (specializeForkExpr targetFork value)
  | .setMappingPackedWord field key wordOffset packed value => .setMappingPackedWord field (specializeForkExpr targetFork key) wordOffset packed (specializeForkExpr targetFork value)
  | .setMapping2 field key1 key2 value => .setMapping2 field (specializeForkExpr targetFork key1) (specializeForkExpr targetFork key2) (specializeForkExpr targetFork value)
  | .setMapping2Word field key1 key2 wordOffset value => .setMapping2Word field (specializeForkExpr targetFork key1) (specializeForkExpr targetFork key2) wordOffset (specializeForkExpr targetFork value)
  | .setMappingUint field key value => .setMappingUint field (specializeForkExpr targetFork key) (specializeForkExpr targetFork value)
  | .setMappingChain field keys value => .setMappingChain field (keys.map (specializeForkExpr targetFork)) (specializeForkExpr targetFork value)
  | .setStructMember field key memberName value => .setStructMember field (specializeForkExpr targetFork key) memberName (specializeForkExpr targetFork value)
  | .setStructMember2 field key1 key2 memberName value => .setStructMember2 field (specializeForkExpr targetFork key1) (specializeForkExpr targetFork key2) memberName (specializeForkExpr targetFork value)
  | .require cond message => .require (specializeForkExpr targetFork cond) message
  | .requireError cond errorName args => .requireError (specializeForkExpr targetFork cond) errorName (args.map (specializeForkExpr targetFork))
  | .revertError errorName args => .revertError errorName (args.map (specializeForkExpr targetFork))
  | .return value => .return (specializeForkExpr targetFork value)
  | .returnValues values => .returnValues (values.map (specializeForkExpr targetFork))
  | .returnCodeData pointer => .returnCodeData (specializeForkExpr targetFork pointer)
  | .mstore offset value => .mstore (specializeForkExpr targetFork offset) (specializeForkExpr targetFork value)
  | .tstore offset value => .tstore (specializeForkExpr targetFork offset) (specializeForkExpr targetFork value)
  | .calldatacopy dest source size => .calldatacopy (specializeForkExpr targetFork dest) (specializeForkExpr targetFork source) (specializeForkExpr targetFork size)
  | .returndataCopy dest source size => .returndataCopy (specializeForkExpr targetFork dest) (specializeForkExpr targetFork source) (specializeForkExpr targetFork size)
  | .ite cond thenBranch elseBranch => .ite (specializeForkExpr targetFork cond) (thenBranch.map (specializeForkStmt targetFork)) (elseBranch.map (specializeForkStmt targetFork))
  | .forEach varName count body => .forEach varName (specializeForkExpr targetFork count) (body.map (specializeForkStmt targetFork))
  | .forEachSetBit varName bitmap body => .forEachSetBit varName (specializeForkExpr targetFork bitmap) (body.map (specializeForkStmt targetFork))
  | .emit eventName args => .emit eventName (args.map (specializeForkExpr targetFork))
  | .internalCall functionName args => .internalCall functionName (args.map (specializeForkExpr targetFork))
  | .internalCallAssign names functionName args => .internalCallAssign names functionName (args.map (specializeForkExpr targetFork))
  | .rawLog topics dataOffset dataSize => .rawLog (topics.map (specializeForkExpr targetFork)) (specializeForkExpr targetFork dataOffset) (specializeForkExpr targetFork dataSize)
  | .externalCallBind resultVars externalName args => .externalCallBind resultVars externalName (args.map (specializeForkExpr targetFork))
  | .tryExternalCallBind successVar resultVars externalName args => .tryExternalCallBind successVar resultVars externalName (args.map (specializeForkExpr targetFork))
  | .ecm mod args => .ecm mod (args.map (specializeForkExpr targetFork))
  | .unsafeBlock reason body => .unsafeBlock reason (body.map (specializeForkStmt targetFork))
  | .matchAdt adtName scrutinee branches =>
      .matchAdt adtName (specializeForkExpr targetFork scrutinee)
        (branches.map fun (variantName, boundVarNames, body) =>
          (variantName, boundVarNames, body.map (specializeForkStmt targetFork)))
  | other => other

private def specializeForkConstructor
    (targetFork : Verity.Core.Intrinsics.HardFork)
    (ctor : ConstructorSpec) : ConstructorSpec :=
  { ctor with body := ctor.body.map (specializeForkStmt targetFork) }

private def specializeForkFunction
    (targetFork : Verity.Core.Intrinsics.HardFork)
    (fn : FunctionSpec) : FunctionSpec :=
  { fn with body := fn.body.map (specializeForkStmt targetFork) }

private def specializeForkSpec
    (targetFork : Verity.Core.Intrinsics.HardFork)
    (spec : CompilationModel) : CompilationModel :=
  { spec with
    «constructor» := spec.constructor.map (specializeForkConstructor targetFork)
    functions := spec.functions.map (specializeForkFunction targetFork) }

private partial def collectIntrinsicUsesStmt : Stmt → List IntrinsicUse
  | .letVar _ value | .assignVar _ value | .setStorage _ value
  | .setStorageAddr _ value | .setStorageWord _ _ value
  | .storageArrayPush _ value | .return value | .require value _ =>
      collectIntrinsicUsesExpr value
  | .setStorageArrayElement _ index value
  | .setMapping _ index value | .setMappingWord _ index _ value
  | .setMappingPackedWord _ index _ _ value | .setMappingUint _ index value
  | .setStructMember _ index _ value
  | .mstore index value | .tstore index value =>
      collectIntrinsicUsesExpr index ++ collectIntrinsicUsesExpr value
  | .setMapping2 _ a b value | .setMapping2Word _ a b _ value
  | .setStructMember2 _ a b _ value =>
      collectIntrinsicUsesExpr a ++ collectIntrinsicUsesExpr b ++ collectIntrinsicUsesExpr value
  | .setMappingChain _ keys value =>
      keys.flatMap collectIntrinsicUsesExpr ++ collectIntrinsicUsesExpr value
  | .requireError cond _ args =>
      collectIntrinsicUsesExpr cond ++ args.flatMap collectIntrinsicUsesExpr
  | .revertError _ args | .returnValues args | .emit _ args
  | .internalCall _ args | .internalCallAssign _ _ args
  | .externalCallBind _ _ args | .tryExternalCallBind _ _ _ args
  | .ecm _ args =>
      args.flatMap collectIntrinsicUsesExpr
  | .returnCodeData pointer =>
      collectIntrinsicUsesExpr pointer
  | .calldatacopy destOffset sourceOffset size
  | .returndataCopy destOffset sourceOffset size =>
      [destOffset, sourceOffset, size].flatMap collectIntrinsicUsesExpr
  | .rawLog topics dataOffset dataSize =>
      topics.flatMap collectIntrinsicUsesExpr ++ collectIntrinsicUsesExpr dataOffset ++
        collectIntrinsicUsesExpr dataSize
  | .ite cond thenBranch elseBranch =>
      collectIntrinsicUsesExpr cond ++ thenBranch.flatMap collectIntrinsicUsesStmt ++
        elseBranch.flatMap collectIntrinsicUsesStmt
  | .forEach _ count body =>
      collectIntrinsicUsesExpr count ++ body.flatMap collectIntrinsicUsesStmt
  | .forEachSetBit _ bitmap body =>
      collectIntrinsicUsesExpr bitmap ++ body.flatMap collectIntrinsicUsesStmt
  | .unsafeBlock _ body =>
      body.flatMap collectIntrinsicUsesStmt
  | .matchAdt _ scrutinee branches =>
      collectIntrinsicUsesExpr scrutinee ++
        branches.flatMap fun (_, _, body) => body.flatMap collectIntrinsicUsesStmt
  | .storageArrayPop _ | .returnArray _ | .returnBytes _ | .returnStorageWords _
  | .revertReturndata | .stop =>
      []
  | .unsafeYul _ =>
      []

private def collectIntrinsicUsesSpec (spec : CompilationModel) : List IntrinsicUse :=
  let ctorUses :=
    match spec.constructor with
    | some ctor => ctor.body.flatMap collectIntrinsicUsesStmt
    | none => []
  ctorUses ++ spec.functions.flatMap fun fn => fn.body.flatMap collectIntrinsicUsesStmt

private def ensureIntrinsicForksAllowed
    (targetFork : Verity.Core.Intrinsics.HardFork)
    (specs : List CompilationModel) : IO Unit := do
  for spec in specs do
    for use in collectIntrinsicUsesSpec spec do
      unless Verity.Core.Intrinsics.HardFork.allows targetFork use.minFork do
        throw (IO.userError
          s!"Intrinsic '{use.name}' in {spec.name} requires min_fork={use.minFork}, but target_fork={targetFork}. Re-run with a newer --target-fork or --allow-future-fork-intrinsics.")

private def ensureNoUncheckedDependencies (specs : List CompilationModel) : IO Unit := do
  let uncheckedSites := emitUncheckedUsageSiteLines specs
  if !uncheckedSites.isEmpty then
    throw (IO.userError
      s!"Unchecked foreign dependencies remain:\n{String.intercalate "\n" uncheckedSites}")

private def ensureNoAssumedDependencies (specs : List CompilationModel) : IO Unit := do
  let assumedSites := emitAssumedUsageSiteLines specs
  if !assumedSites.isEmpty then
    throw (IO.userError
      s!"Assumed or unchecked foreign dependencies remain:\n{String.intercalate "\n" assumedSites}")

private def ensureNoAxiomatizedPrimitives (specs : List CompilationModel) : IO Unit := do
  let primitiveSites := emitAxiomatizedPrimitiveUsageSiteLines specs
  if !primitiveSites.isEmpty then
    throw (IO.userError
      s!"Axiomatized primitives remain:\n{String.intercalate "\n" primitiveSites}")

private def ensureNoLocalObligations (specs : List CompilationModel) : IO Unit := do
  let localObligationSites := emitLocalObligationUsageSiteLines specs
  if !localObligationSites.isEmpty then
    throw (IO.userError
      s!"Undischarged local obligations remain:\n{String.intercalate "\n" localObligationSites}")

private def ensureNoLinearMemoryMechanics (specs : List CompilationModel) : IO Unit := do
  let linearMemorySites := emitLinearMemoryUsageSiteLines specs
  if !linearMemorySites.isEmpty then
    throw (IO.userError
      s!"Partially modeled linear-memory mechanics remain:\n{String.intercalate "\n" linearMemorySites}")

private def ensureNoEventEmission (specs : List CompilationModel) : IO Unit := do
  let eventEmissionSites := emitEventEmissionUsageSiteLines specs
  if !eventEmissionSites.isEmpty then
    throw (IO.userError
      s!"Not-modeled event emission remains:\n{String.intercalate "\n" eventEmissionSites}")

private def ensureNoProxyUpgradeability (specs : List CompilationModel) : IO Unit := do
  let proxySites := emitProxyUpgradeabilityUsageSiteLines specs
  if !proxySites.isEmpty then
    throw (IO.userError
      s!"Not-modeled proxy / upgradeability mechanics remain:\n{String.intercalate "\n" proxySites}")

private def ensureNoRuntimeIntrospection (specs : List CompilationModel) : IO Unit := do
  let runtimeIntrospectionSites := emitRuntimeIntrospectionUsageSiteLines specs
  if !runtimeIntrospectionSites.isEmpty then
    throw (IO.userError
      s!"Partially modeled runtime-introspection mechanics remain:\n{String.intercalate "\n" runtimeIntrospectionSites}")

private def ensureNoLowLevelMechanics (specs : List CompilationModel) : IO Unit := do
  let lowLevelSites := emitLowLevelMechanicsUsageSiteLines specs
  if !lowLevelSites.isEmpty then
    throw (IO.userError
      s!"Low-level mechanics remain:\n{String.intercalate "\n" lowLevelSites}")

private def ensureNoUnsafeBlocks (specs : List CompilationModel) : IO Unit := do
  let unsafeSites := emitUnsafeBlockUsageSiteLines specs
  if !unsafeSites.isEmpty then
    throw (IO.userError
      s!"Unsafe blocks remain:\n{String.intercalate "\n" unsafeSites}")

private def ensureLayoutCompatible (specs : List CompilationModel) : IO Unit := do
  let (baseline, candidate) ← requireLayoutCompatibilityPair specs
  let incompatibilities := emitIncompatibleLayoutChangeLines baseline candidate
  if !incompatibilities.isEmpty then
    throw (IO.userError
      s!"Layout incompatibilities remain:\n{String.intercalate "\n" incompatibilities}")

private def writeContract
    (backend : CodegenBackend)
    (spec : CompilationModel)
    (outDir : String)
    (contract : IRContract)
    (libraryPaths : List String)
    (verbose : Bool)
    (options : YulEmitOptions) : IO Yul.PatchPassReport := do
  let (baseYulObj, patchReport) := backend.emitYulWithOptionsReport contract options
  let linkModeComments :=
    spec.externals.map fun ext =>
      YulStmt.comment s!"verity linked external {ext.name} linkMode={ext.linkMode.toJsonString}"
  let yulObj :=
    { baseYulObj with
      runtimeCode := linkModeComments ++ baseYulObj.runtimeCode }

  let libraries ← libraryPaths.mapM fun path => do
    if verbose then
      IO.println s!"  Loading library: {path}"
    loadLibrary path

  let allLibFunctions := libraries.flatten
  if !allLibFunctions.isEmpty then
    orThrow (validateNoDuplicateNames allLibFunctions)
    orThrow (validateNoNameCollisions yulObj allLibFunctions)
  orThrow (validateExternalReferences yulObj allLibFunctions)
  if !allLibFunctions.isEmpty then
    orThrow (validateCallArity yulObj allLibFunctions)

  let text ←
    if allLibFunctions.isEmpty then
      pure (Yul.render yulObj)
    else
      match renderWithLibraries yulObj allLibFunctions with
      | .error err => throw (IO.userError err)
      | .ok rendered => pure rendered

  let path := s!"{outDir}/{contract.name}.yul"
  IO.FS.writeFile path text
  pure patchReport

def compileSpecsWithOptions
    (backend : CodegenBackend)
    (specs : List CompilationModel)
    (outDir : String)
    (verbose : Bool)
    (libraryPaths : List String)
    (options : YulEmitOptions)
    (patchReportPath : Option String)
    (trustReportPath : Option String)
    (assumptionReportPath : Option String)
    (abiOutDir : Option String)
    (denyUncheckedDependencies : Bool := false)
    (denyAssumedDependencies : Bool := false)
    (denyAxiomatizedPrimitives : Bool := false)
    (denyLocalObligations : Bool := false)
    (denyLinearMemoryMechanics : Bool := false)
    (denyEventEmission : Bool := false)
    (denyLowLevelMechanics : Bool := false)
    (denyRuntimeIntrospection : Bool := false)
    (denyProxyUpgradeability : Bool := false)
    (layoutReportPath : Option String := none)
    (layoutCompatibilityReportPath : Option String := none)
    (denyLayoutIncompatibility : Bool := false)
    (denyUnsafe : Bool := false) : IO Unit := do
  IO.FS.createDirAll outDir
  match abiOutDir with
  | some dir => IO.FS.createDirAll dir
  | none => pure ()

  let specs := specs.map (specializeForkSpec options.targetFork)

  unless options.allowFutureForkIntrinsics do
    ensureIntrinsicForksAllowed options.targetFork specs

  if !libraryPaths.isEmpty then
    if verbose then
      IO.println s!"Loading {libraryPaths.length} external libraries..."

  let mut patchRows : List (String × Yul.PatchPassReport) := []
  for spec in specs do
    let selectors ← computeSelectors spec
    match compile spec selectors options.targetFork with
    | .ok contract =>
        let contractLibs := if spec.externals.isEmpty then [] else libraryPaths
        let patchReport ← writeContract backend spec outDir contract contractLibs verbose options
        match abiOutDir with
        | some dir =>
            Compiler.ABI.writeContractABIFile dir spec
            Compiler.ABI.writeContractStorageLayoutFile dir spec
            if verbose then
              IO.println s!"✓ Wrote ABI {dir}/{spec.name}.abi.json"
              IO.println s!"✓ Wrote storage layout {dir}/{spec.name}.storage.json"
        | none => pure ()
        patchRows := (contract.name, patchReport) :: patchRows
        if verbose then
          IO.println s!"✓ Compiled {contract.name}"
    | .error err =>
        throw (IO.userError err)
  match patchReportPath with
  | some path =>
      writePatchReport path patchRows.reverse
      if verbose then
        IO.println s!"✓ Wrote patch report: {path}"
  | none => pure ()
  match trustReportPath with
  | some path =>
      writeTrustReport path specs
      if verbose then
        IO.println s!"✓ Wrote trust report: {path}"
  | none => pure ()
  match assumptionReportPath with
  | some path =>
      writeAssumptionReport path specs
      if verbose then
        IO.println s!"✓ Wrote assumption report: {path}"
  | none => pure ()
  match layoutReportPath with
  | some path =>
      writeLayoutReport path specs
      if verbose then
        IO.println s!"✓ Wrote layout report: {path}"
  | none => pure ()
  match layoutCompatibilityReportPath with
  | some path =>
      writeLayoutCompatibilityReport path specs
      if verbose then
        IO.println s!"✓ Wrote layout compatibility report: {path}"
  | none => pure ()
  if denyLocalObligations then
    ensureNoLocalObligations specs
  if denyAxiomatizedPrimitives then
    ensureNoAxiomatizedPrimitives specs
  if denyLinearMemoryMechanics then
    ensureNoLinearMemoryMechanics specs
  if denyEventEmission then
    ensureNoEventEmission specs
  if denyLowLevelMechanics then
    ensureNoLowLevelMechanics specs
  if denyRuntimeIntrospection then
    ensureNoRuntimeIntrospection specs
  if denyProxyUpgradeability then
    ensureNoProxyUpgradeability specs
  if denyLayoutIncompatibility then
    ensureLayoutCompatible specs
  if denyAssumedDependencies then
    ensureNoAssumedDependencies specs
  if denyUncheckedDependencies then
    ensureNoUncheckedDependencies specs
  if denyUnsafe then
    ensureNoUnsafeBlocks specs
  if verbose then
    IO.println ""
    IO.println "Linear memory mechanics report:"
    let mut anyLinearMemory := false
    for spec in specs do
      let mechanics := collectLinearMemoryMechanics spec
      if !mechanics.isEmpty then
        anyLinearMemory := true
        IO.println s!"  {spec.name}: {String.intercalate ", " mechanics}"
    if !anyLinearMemory then
      IO.println "  (no partially modeled linear-memory primitives used)"
    IO.println "  Proof boundary: these mechanics rely on linear memory / ABI movement that is still only partially modeled by current proof interpreters."
    IO.println ""
    IO.println "Event-emission report:"
    let mut anyEventEmission := false
    for spec in specs do
      let mechanics := collectEventEmissionMechanics spec
      if !mechanics.isEmpty then
        anyEventEmission := true
        IO.println s!"  {spec.name}: {String.intercalate ", " mechanics}"
    if !anyEventEmission then
      IO.println "  (no raw event-emission primitives used)"
    IO.println "  Proof boundary: raw LOG-style event emission is compiler-supported, but current proof interpreters still treat `rawLog` as a not-modeled feature."
    IO.println ""
    IO.println "Proxy / upgradeability report:"
    let mut anyProxyUpgradeability := false
    for spec in specs do
      let mechanics := collectProxyUpgradeabilityMechanics spec
      if !mechanics.isEmpty then
        anyProxyUpgradeability := true
        IO.println s!"  {spec.name}: {String.intercalate ", " mechanics}"
    if !anyProxyUpgradeability then
      IO.println "  (no proxy / upgradeability mechanics used)"
    IO.println "  Proof boundary: `delegatecall` still lacks native proxy / upgradeability semantics in the proof interpreters; treat these sites as explicit trust boundaries tracked under issue #1420."
    IO.println ""
    IO.println "Runtime introspection report:"
    let mut anyRuntimeIntrospection := false
    for spec in specs do
      let mechanics := collectRuntimeIntrospectionMechanics spec
      if !mechanics.isEmpty then
        anyRuntimeIntrospection := true
        IO.println s!"  {spec.name}: {String.intercalate ", " mechanics}"
    if !anyRuntimeIntrospection then
      IO.println "  (no partially modeled runtime-introspection primitives used)"
    IO.println "  Proof boundary: these context-sensitive primitives are compiler-supported, but current proof interpreters still model them only partially."
    IO.println ""
    IO.println "Low-level mechanics report:"
    let mut anyMechanics := false
    for spec in specs do
      let mechanics := collectLowLevelMechanics spec
      if !mechanics.isEmpty then
        anyMechanics := true
        IO.println s!"  {spec.name}: {String.intercalate ", " mechanics}"
    if !anyMechanics then
      IO.println "  (no first-class low-level call or returndata primitives used)"
    IO.println "  Proof boundary: mechanics are lowered natively by the compiler; current proof interpreters do not model these primitives, and callee behavior remains assumption-backed unless discharged separately."
    IO.println ""
    IO.println "Axiomatized primitive report:"
    let mut anyAxiomatized := false
    for spec in specs do
      let primitives := collectAxiomatizedPrimitives spec
      if !primitives.isEmpty then
        anyAxiomatized := true
        IO.println s!"  {spec.name}: {String.intercalate ", " primitives}"
    if !anyAxiomatized then
      IO.println "  (no axiomatized primitives used)"
    IO.println "  Proof boundary: these primitives compile through explicit trusted boundaries (for example, keccak-backed hashing) and should be audited alongside AXIOMS.md/TRUST_ASSUMPTIONS.md."
    IO.println ""
    IO.println "Local obligation report:"
    let mut anyLocalObligations := false
    for spec in specs do
      let obligations := collectLocalObligations spec
      if !obligations.isEmpty then
        anyLocalObligations := true
        IO.println s!"  {spec.name}:"
        for obligation in obligations do
          IO.println s!"    [{obligation.proofStatus.toJsonString}] {obligation.name}: {obligation.obligation}"
    if !anyLocalObligations then
      IO.println "  (no local unsafe/refinement obligations declared)"
    IO.println "  Proof boundary: local obligations isolate unsafe/assembly-shaped trust boundaries to one usage site and can later be discharged from `assumed`/`unchecked` to `proved`."
    IO.println ""
    IO.println "Unsafe block report:"
    let mut anyUnsafeBlocks := false
    for spec in specs do
      let unsafeReasons := collectUnsafeBlockReasons spec
      if !unsafeReasons.isEmpty then
        anyUnsafeBlocks := true
        IO.println s!"  {spec.name}:"
        for reason in unsafeReasons do
          IO.println s!"    [unsafe] \"{reason}\""
    if !anyUnsafeBlocks then
      IO.println "  (no unsafe blocks used)"
    IO.println "  Trust boundary: each `unsafe \"reason\" do` block suppresses restricted-operation gating for its body. Use `--deny-unsafe` to reject all unsafe blocks."
    IO.println ""
    IO.println "Proof-status summary:"
    let mut anyForeignStatus := false
    let mut anyUncheckedStatus := false
    for spec in specs do
      let primitives := collectAxiomatizedPrimitives spec
      let provedLocalObligations :=
        (collectLocalObligations spec).foldl
          (fun acc obligation => if obligation.proofStatus == .proved then acc ++ [obligation.name] else acc) []
      let assumedLocalObligations :=
        (collectLocalObligations spec).foldl
          (fun acc obligation => if obligation.proofStatus == .assumed then acc ++ [obligation.name] else acc) []
      let uncheckedLocalObligations :=
        (collectLocalObligations spec).foldl
          (fun acc obligation => if obligation.proofStatus == .unchecked then acc ++ [obligation.name] else acc) []
      let provedExternals :=
        (collectUsedExternalAssumptions spec).foldl
          (fun acc ext => if ext.proofStatus == .proved then acc ++ [ext.name] else acc) []
      let assumedExternals :=
        (collectUsedExternalAssumptions spec).foldl
          (fun acc ext => if ext.proofStatus == .assumed then acc ++ [ext.name] else acc) []
      let uncheckedExternals :=
        (collectUsedExternalAssumptions spec).foldl
          (fun acc ext => if ext.proofStatus == .unchecked then acc ++ [ext.name] else acc) []
      let usedModules := collectUsedEcmModules spec
      let provedModules := usedModules.foldl
        (fun acc mod => if mod.proofStatus == .proved then acc ++ [mod.name] else acc) []
      let assumedModules := usedModules.foldl
        (fun acc mod => if mod.proofStatus == .assumed then acc ++ [mod.name] else acc) []
      let uncheckedModules := usedModules.foldl
        (fun acc mod => if mod.proofStatus == .unchecked then acc ++ [mod.name] else acc) []
      if !primitives.isEmpty || !provedLocalObligations.isEmpty || !assumedLocalObligations.isEmpty ||
          !uncheckedLocalObligations.isEmpty || !provedExternals.isEmpty || !assumedExternals.isEmpty ||
          !uncheckedExternals.isEmpty || !provedModules.isEmpty || !assumedModules.isEmpty ||
          !uncheckedModules.isEmpty then
        anyForeignStatus := true
        IO.println s!"  {spec.name}:"
        if !primitives.isEmpty then
          IO.println s!"    assumed primitives: {String.intercalate ", " primitives}"
        if !provedLocalObligations.isEmpty then
          IO.println s!"    proved local obligations: {String.intercalate ", " provedLocalObligations}"
        if !assumedLocalObligations.isEmpty then
          IO.println s!"    assumed local obligations: {String.intercalate ", " assumedLocalObligations}"
        if !uncheckedLocalObligations.isEmpty then
          anyUncheckedStatus := true
          IO.println s!"    unchecked local obligations: {String.intercalate ", " uncheckedLocalObligations}"
        if !provedExternals.isEmpty then
          IO.println s!"    proved linked externals: {String.intercalate ", " provedExternals}"
        if !assumedExternals.isEmpty then
          IO.println s!"    assumed linked externals: {String.intercalate ", " assumedExternals}"
        if !uncheckedExternals.isEmpty then
          anyUncheckedStatus := true
          IO.println s!"    unchecked linked externals: {String.intercalate ", " uncheckedExternals}"
        if !provedModules.isEmpty then
          IO.println s!"    proved ECM modules: {String.intercalate ", " provedModules}"
        if !assumedModules.isEmpty then
          IO.println s!"    assumed ECM modules: {String.intercalate ", " assumedModules}"
        if !uncheckedModules.isEmpty then
          anyUncheckedStatus := true
          IO.println s!"    unchecked ECM modules: {String.intercalate ", " uncheckedModules}"
    if !anyForeignStatus then
      IO.println "  proved: none"
      IO.println "  assumed: none"
      IO.println "  unchecked: none"
    else if !anyUncheckedStatus then
      IO.println "  unchecked: none reported"
    else
      IO.println "  warning: unchecked foreign dependencies are present; exclude these contracts from full-verification claims"
    IO.println ""
    IO.println "Usage-site trust report:"
    let usageSiteLines := emitVerboseUsageSiteLines specs
    if usageSiteLines.isEmpty then
      IO.println "  (no localized trust surfaces)"
    else
      for line in usageSiteLines do
        IO.println line
    IO.println ""
    IO.println "External assumption report:"
    let mut anyExternalAssumptions := false
    for spec in specs do
      let primitiveAssumptions := collectAxiomatizedPrimitives spec
      let externals := collectUsedExternalAssumptions spec
      let ecmAxioms := collectEcmAxioms spec
      if !primitiveAssumptions.isEmpty || !externals.isEmpty || !ecmAxioms.isEmpty then
        anyExternalAssumptions := true
        IO.println s!"  {spec.name}:"
        if !primitiveAssumptions.isEmpty then
          for primitive in primitiveAssumptions do
            IO.println
              s!"    [primitive:{primitive}][assumed] {primitiveAssumptionName primitive}"
        if !externals.isEmpty then
          for ext in externals do
            let renderedAxioms :=
              if ext.axiomNames.isEmpty then "(no declared axioms)"
              else String.intercalate ", " ext.axiomNames
            IO.println s!"    [linked:{ext.name}][{ext.proofStatus.toJsonString}] {renderedAxioms}"
        if !ecmAxioms.isEmpty then
          for (modName, assumption) in ecmAxioms do
            IO.println s!"    [ecm:{modName}] {assumption}"
    if !anyExternalAssumptions then
      IO.println "  (no primitive assumptions, linked external assumptions, or ECM axioms)"
    IO.println ""
    IO.println "ECM axiom report:"
    let mut anyAxioms := false
    for spec in specs do
      let axioms := collectEcmAxioms spec
      if !axioms.isEmpty then
        anyAxioms := true
        IO.println s!"  {spec.name}:"
        for (modName, assumption) in axioms do
          IO.println s!"    [{modName}] {assumption}"
    if !anyAxioms then
      IO.println "  (no ECM axioms — no external call modules used)"
    IO.println ""
    IO.println "Compilation complete!"
    IO.println s!"Generated {specs.length} contracts in {outDir}"

unsafe def compileModulesWithOptions
    (backend : CodegenBackend)
    (outDir : String)
    (modules : List String)
    (verbose : Bool := false)
    (libraryPaths : List String := [])
    (options : YulEmitOptions := {})
    (patchReportPath : Option String := none)
    (trustReportPath : Option String := none)
    (assumptionReportPath : Option String := none)
    (abiOutDir : Option String := none)
    (denyUncheckedDependencies : Bool := false)
    (denyAssumedDependencies : Bool := false)
    (denyAxiomatizedPrimitives : Bool := false)
    (denyLocalObligations : Bool := false)
    (denyLinearMemoryMechanics : Bool := false)
    (denyEventEmission : Bool := false)
    (denyLowLevelMechanics : Bool := false)
    (denyRuntimeIntrospection : Bool := false)
    (denyProxyUpgradeability : Bool := false)
    (layoutReportPath : Option String := none)
    (layoutCompatibilityReportPath : Option String := none)
    (denyLayoutIncompatibility : Bool := false)
    (denyUnsafe : Bool := false) : IO Unit := do
  let specs ←
    match ← Compiler.ModuleInput.loadSpecsFromRawModules modules with
    | .ok specs => pure specs
    | .error err => throw (IO.userError err)
  compileSpecsWithOptions
    backend specs outDir verbose libraryPaths options patchReportPath trustReportPath assumptionReportPath abiOutDir
    denyUncheckedDependencies denyAssumedDependencies denyAxiomatizedPrimitives denyLocalObligations denyLinearMemoryMechanics
    denyEventEmission denyLowLevelMechanics denyRuntimeIntrospection denyProxyUpgradeability layoutReportPath
    layoutCompatibilityReportPath denyLayoutIncompatibility denyUnsafe

end Compiler.CompileDriverCommon

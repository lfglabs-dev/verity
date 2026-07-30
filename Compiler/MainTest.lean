import Contracts
import Contracts.LocalObligationMacroSmoke.LocalObligationMacroSmoke
import Contracts.LocalObligationTrustSurface
import Contracts.ProxyUpgradeabilityLayoutCompatibleSmoke
import Contracts.ProxyUpgradeabilityLayoutIncompatibleSmoke
import Contracts.ProxyUpgradeabilityMacroSmoke
import Contracts.RawLogTrustSurface
import Compiler.MainDriver
import Compiler.ParityPacks
import Compiler.Linker
import Compiler.TestModules

namespace Compiler.MainTest

private def contains (haystack needle : String) : Bool :=
  if needle.isEmpty then true
  else
    let parts := haystack.splitOn needle
    parts.length > 1

private unsafe def expectErrorContains (label : String) (args : List String) (needle : String) : IO Unit := do
  try
    Compiler.Main.run args
    throw (IO.userError s!"✗ {label}: expected failure, command succeeded")
  catch e =>
    let msg := e.toString
    if !contains msg needle then
      throw (IO.userError s!"✗ {label}: expected '{needle}', got:\n{msg}")
    IO.println s!"✓ {label}"

private def expectTrue (label : String) (ok : Bool) : IO Unit := do
  if !ok then
    throw (IO.userError s!"✗ {label}")
  IO.println s!"✓ {label}"

private def fileExists (path : String) : IO Bool := do
  try
    let _ ← IO.FS.readFile path
    pure true
  catch _ =>
    pure false

private def moduleArgs (modules : List String) : List String :=
  modules.foldr (fun moduleName acc => "--module" :: moduleName :: acc) []

private def contractArtifactPath (outDir : String) (moduleName : String) : String :=
  s!"{outDir}/{contractNameOfModule moduleName}.yul"

/-! #2214: the regression suite compiles contracts through the Lean interpreter
many times over. Running every case in one process accumulated interpreter and
environment memory to ~56 GB under Lean 4.31 and got OOM-killed on the 64 GB
build runner. The suite is therefore split into self-contained phases; CI runs
each phase in a fresh process so peak memory is one phase, not the sum. -/

set_option maxRecDepth 100000 in
unsafe def runFlagAndUnitTests : IO Unit := do
  let tempRoot := (← IO.getEnv "TMPDIR").getD "/tmp"
  let tempPath (name : String) : String := s!"{tempRoot}/{name}"
  expectErrorContains "missing --link value" ["--link"] "Missing value for --link"
  expectErrorContains "missing --output value" ["--output"] "Missing value for --output"
  expectErrorContains "missing -o value" ["-o"] "Missing value for --output"
  expectErrorContains "missing --abi-output value" ["--abi-output"] "Missing value for --abi-output"
  expectErrorContains "removed --input flag is rejected" ["--input", "edsl"] "Unknown argument: --input"
  expectErrorContains "missing --manifest value" ["--manifest"] "Missing value for --manifest"
  expectErrorContains "missing --module value" ["--module"] "Missing value for --module"
  expectErrorContains
    "duplicate --module value"
    (["--module", "Contracts.Counter.Counter", "--module", "Contracts.Counter.Counter"] ++ ["--output", tempPath "verity-main-test-dup"])
    "Duplicate module input: Contracts.Counter.Counter"
  expectErrorContains
    "empty compiler input is rejected"
    ["--output", tempPath "verity-main-test-empty"]
    "No compiler input provided. Use --manifest and/or --module."
  expectErrorContains
    "invalid module name is rejected"
    ["--module", "Contracts..Counter", "--output", tempPath "verity-main-test-invalid"]
    "Invalid module name: Contracts..Counter"
  expectErrorContains
    "missing manifest file is rejected"
    ["--manifest", tempPath "definitely-missing-verty-manifest", "--output", tempPath "verity-main-test-missing-manifest"]
    "Failed to read manifest"
  expectErrorContains "bare --patch-report errors missing value" ["--patch-report"] "Missing value for --patch-report"
  expectErrorContains "missing --assumption-report value" ["--assumption-report"] "Missing value for --assumption-report"
  expectErrorContains "missing --layout-report value" ["--layout-report"] "Missing value for --layout-report"
  expectErrorContains "missing --layout-compat-report value" ["--layout-compat-report"] "Missing value for --layout-compat-report"
  expectErrorContains "bare --patch-max-iterations errors missing value" ["--patch-max-iterations"] "Missing value for --patch-max-iterations"
  expectErrorContains "missing --backend-profile value" ["--backend-profile"] "Missing value for --backend-profile"
  expectErrorContains "invalid --backend-profile value" ["--backend-profile", "invalid-profile"] "expected semantic, solidity-parity-ordering, or solidity-parity"
  expectErrorContains "solidity-parity backend profile accepted; errors no input" ["--backend-profile", "solidity-parity"] "No compiler input provided"
  expectErrorContains "bare --parity-pack errors missing value" ["--parity-pack"] "Missing value for --parity-pack"
  expectErrorContains "invalid parity pack id is rejected" ["--parity-pack", "invalid-pack"] "Invalid value for --parity-pack"
  expectErrorContains "unknown parity pack id is rejected" ["--parity-pack", "solc-0.8.33-o200-viair-false-evm-shanghai", "--parity-pack", "solc-0.8.28-o999999-viair-true-evm-paris"] "Invalid value for --parity-pack"
  expectErrorContains "backend-profile + parity-pack conflict is rejected (profile first)" ["--backend-profile", "semantic", "--parity-pack", "solc-0.8.33-o200-viair-false-evm-shanghai"] "Cannot combine --parity-pack with --backend-profile"
  expectErrorContains "unknown parity pack id rejected before backend-profile conflict check" ["--parity-pack", "solc-0.8.33-o200-viair-false-evm-shanghai", "--backend-profile", "semantic"] "Invalid value for --parity-pack"
  expectErrorContains "missing --mapping-slot-scratch-base value" ["--mapping-slot-scratch-base"] "Missing value for --mapping-slot-scratch-base"
  expectErrorContains "invalid --mapping-slot-scratch-base value" ["--mapping-slot-scratch-base", "not-a-number"] "Invalid value for --mapping-slot-scratch-base: not-a-number"
  expectErrorContains "removed --ast flag is rejected" ["--ast"] "Unknown argument: --ast"
  expectErrorContains "unknown argument still reported" ["--definitely-unknown-flag"] "Unknown argument: --definitely-unknown-flag"
  expectTrue "shipped parity packs have proof composition metadata"
    Compiler.allParityPacksProofCompositionValid
  let invalidPack : Compiler.ParityPack :=
    { id := "invalid-proof-pack"
      compat := {
        solcVersion := "0.8.28"
        solcCommit := "7893614a"
        optimizerRuns := 200
        viaIR := false
        evmVersion := "shanghai"
        metadataMode := "default"
      }
      backendProfile := .solidityParity
      forcePatches := true
      defaultPatchMaxIterations := 2
      rewriteBundleId := Compiler.Yul.foundationRewriteBundleId
      compositionProofRef := .anonymous
      requiredProofRefs := [] }
  expectTrue "parity pack proof composition rejects empty metadata" (!invalidPack.proofCompositionValid)
  let missingBundlePack := { invalidPack with
    compositionProofRef := Compiler.Yul.proofRefName "Compiler.Proofs.YulGeneration.PatchRulesProofs.foundation_patch_pack_obligations"
    requiredProofRefs := Compiler.Yul.foundationProofAllowlist
    rewriteBundleId := "missing-rewrite-bundle" }
  expectTrue "parity pack proof composition rejects unknown rewrite bundle IDs"
    (!missingBundlePack.proofCompositionValid)

  let libWithCommentAndStringBraces :=
    "{\n" ++
    "function PoseidonT3_hash(a, b) -> result {\n" ++
    "  // } stray brace in comment\n" ++
    "  result := add(a, b)\n" ++
    "}\n\n" ++
    "function PoseidonT4_hash(a, b, c) -> result {\n" ++
    "  let marker := \"} in string\"\n" ++
    "  result := add(add(a, b), c)\n" ++
    "}\n" ++
    "}\n"

  let parsed := Compiler.Linker.parseLibrary libWithCommentAndStringBraces
  expectTrue "linker parses two functions when braces appear in comments/strings" (parsed.length == 2)
  expectTrue "linker keeps first function boundary intact" ((parsed.getD 0 {name := "", arity := 0, body := []}).name == "PoseidonT3_hash")
  expectTrue "linker keeps second function boundary intact" ((parsed.getD 1 {name := "", arity := 0, body := []}).name == "PoseidonT4_hash")
  let firstBody := String.intercalate "\n" ((parsed.getD 0 {name := "", arity := 0, body := []}).body)
  expectTrue "first function body does not swallow next function" (!contains firstBody "function PoseidonT4_hash")

set_option maxRecDepth 100000 in
unsafe def runCompileModeTests : IO Unit := do
  let tempRoot := (← IO.getEnv "TMPDIR").getD "/tmp"
  let tempPath (name : String) : String := s!"{tempRoot}/{name}"
  let nonce ← IO.monoMsNow
  let nonce ← IO.monoMsNow
  let allOutDir := tempPath s!"verity-main-test-{nonce}-all-out"
  IO.FS.createDirAll allOutDir
  Compiler.Main.run (moduleArgs canonicalModules ++ ["--output", allOutDir])
  let allArtifactsPresent ←
    canonicalModules.allM (fun moduleName => fileExists (contractArtifactPath allOutDir moduleName))
  expectTrue "module input mode compiles every requested artifact" allArtifactsPresent

  let singleOutDir := tempPath s!"verity-main-test-{nonce}-single-out"
  IO.FS.createDirAll singleOutDir
  Compiler.Main.run (["--module", "Contracts.Counter.Counter", "--output", singleOutDir])
  let selectedCounterArtifact ← fileExists s!"{singleOutDir}/Counter.yul"
  expectTrue "module input mode compiles explicitly selected contract" selectedCounterArtifact
  let nonSelectedArtifactFlags ←
    (canonicalModules.filter (· != "Contracts.Counter.Counter")).mapM
      (fun moduleName => fileExists (contractArtifactPath singleOutDir moduleName))
  let nonSelectedArtifactsAbsent := nonSelectedArtifactFlags.all (fun isPresent => !isPresent)
  expectTrue "selected module mode does not emit non-selected artifacts" nonSelectedArtifactsAbsent

set_option maxRecDepth 100000 in
unsafe def runStrictGateTests : IO Unit := do
  let tempRoot := (← IO.getEnv "TMPDIR").getD "/tmp"
  let tempPath (name : String) : String := s!"{tempRoot}/{name}"
  let nonce ← IO.monoMsNow
  let strictOutDir := tempPath s!"verity-main-test-{nonce}-strict-out"
  IO.FS.createDirAll strictOutDir
  Compiler.Main.run (["--module", "Contracts.Counter.Counter", "--deny-unchecked-dependencies", "--output", strictOutDir])
  let strictCounterArtifact ← fileExists s!"{strictOutDir}/Counter.yul"
  expectTrue "strict unchecked-dependency gate accepts proved local modules" strictCounterArtifact
  let proofStrictOutDir := tempPath s!"verity-main-test-{nonce}-proof-strict-out"
  IO.FS.createDirAll proofStrictOutDir
  Compiler.Main.run (["--module", "Contracts.Counter.Counter", "--deny-assumed-dependencies", "--output", proofStrictOutDir])
  let proofStrictCounterArtifact ← fileExists s!"{proofStrictOutDir}/Counter.yul"
  expectTrue "strict assumed-dependency gate accepts proved local modules" proofStrictCounterArtifact
  let primitiveStrictOutDir := tempPath s!"verity-main-test-{nonce}-primitive-strict-out"
  IO.FS.createDirAll primitiveStrictOutDir
  Compiler.Main.run (["--module", "Contracts.SimpleStorage.SimpleStorage", "--deny-axiomatized-primitives", "--output", primitiveStrictOutDir])
  let primitiveStrictArtifact ← fileExists s!"{primitiveStrictOutDir}/SimpleStorage.yul"
  expectTrue "strict axiomatized-primitive gate accepts contracts without axiomatized primitives" primitiveStrictArtifact
  expectErrorContains
    "strict axiomatized-primitive gate rejects axiomatized primitives"
    ["--module", "Contracts.Counter.Counter", "--deny-axiomatized-primitives", "--output", tempPath s!"verity-main-test-{nonce}-primitive-fail-out"]
    "Counter [function:previewEnvOps]: keccak256"
  let localObligationStrictOutDir := tempPath s!"verity-main-test-{nonce}-local-obligation-strict-out"
  IO.FS.createDirAll localObligationStrictOutDir
  Compiler.Main.run (["--module", "Contracts.SimpleStorage.SimpleStorage", "--deny-local-obligations", "--output", localObligationStrictOutDir])
  let localObligationStrictArtifact ← fileExists s!"{localObligationStrictOutDir}/SimpleStorage.yul"
  expectTrue "strict local-obligation gate accepts contracts without local obligations" localObligationStrictArtifact
  expectErrorContains
    "strict local-obligation gate rejects undischarged local obligations"
    ["--module", "Contracts.LocalObligationTrustSurface", "--deny-local-obligations", "--output", tempPath s!"verity-main-test-{nonce}-local-obligation-fail-out"]
    "LocalObligationTrustSurface [function:unsafeEdge]: assumed local obligations: manual_delegatecall_refinement"
  expectErrorContains
    "strict local-obligation gate rejects direct unsafe-boundary annotations"
    ["--module", "Contracts.Counter.Counter", "--deny-local-obligations", "--output", tempPath s!"verity-main-test-{nonce}-counter-local-obligation-fail-out"]
    "Counter [function:previewEnvOps]: assumed local obligations: env_memory_refinement"
  let macroLocalObligationTrustReportPath := tempPath s!"verity-main-test-{nonce}-macro-local-obligation-trust-report.json"
  let macroLocalObligationAssumptionReportPath := tempPath s!"verity-main-test-{nonce}-macro-local-obligation-assumption-report.json"
  let macroLocalObligationOutDir := tempPath s!"verity-main-test-{nonce}-macro-local-obligation-out"
  IO.FS.createDirAll macroLocalObligationOutDir
  Compiler.Main.run
    [ "--module", "Contracts.LocalObligationMacroSmoke.LocalObligationMacroSmoke"
    , "--trust-report", macroLocalObligationTrustReportPath
    , "--assumption-report", macroLocalObligationAssumptionReportPath
    , "--output", macroLocalObligationOutDir
    ]
  let macroLocalObligationTrustReport ← IO.FS.readFile macroLocalObligationTrustReportPath
  let macroLocalObligationAssumptionReport ← IO.FS.readFile macroLocalObligationAssumptionReportPath
  expectTrue "macro local-obligation trust report includes constructor obligation"
    (contains macroLocalObligationTrustReport "\"name\":\"constructor_storage_layout\",\"status\":\"unchecked\"")
  expectTrue "macro local-obligation trust report includes assumed function obligation"
    (contains macroLocalObligationTrustReport "\"name\":\"manual_delegatecall_refinement\",\"status\":\"assumed\"")
  expectTrue "macro local-obligation trust report includes proved function obligation"
    (contains macroLocalObligationTrustReport "\"name\":\"checked_patch_pack\",\"status\":\"proved\"")
  expectTrue "macro local-obligation trust report localizes constructor usage"
    (contains macroLocalObligationTrustReport "\"kind\":\"constructor\",\"name\":\"constructor\"")
  expectTrue "macro local-obligation assumption report flattens constructor and function obligations"
    ((contains macroLocalObligationAssumptionReport "\"category\":\"localObligation\",\"siteKind\":\"constructor\",\"siteName\":\"constructor\",\"name\":\"constructor_storage_layout\",\"status\":\"unchecked\"") &&
      (contains macroLocalObligationAssumptionReport "\"category\":\"localObligation\",\"siteKind\":\"function\",\"siteName\":\"unsafeEdge\",\"name\":\"manual_delegatecall_refinement\",\"status\":\"assumed\"") &&
      (contains macroLocalObligationAssumptionReport "\"category\":\"localObligation\",\"siteKind\":\"function\",\"siteName\":\"dischargedEdge\",\"name\":\"checked_patch_pack\",\"status\":\"proved\""))
  expectTrue "macro local-obligation assumption report keeps undischarged entries separate"
    ((contains macroLocalObligationAssumptionReport "\"undischarged\":[") &&
      (contains macroLocalObligationAssumptionReport "\"name\":\"constructor_storage_layout\",\"status\":\"unchecked\"") &&
      (contains macroLocalObligationAssumptionReport "\"name\":\"manual_delegatecall_refinement\",\"status\":\"assumed\""))
  expectErrorContains
    "strict local-obligation gate rejects macro-declared undischarged obligations"
    ["--module", "Contracts.LocalObligationMacroSmoke.LocalObligationMacroSmoke", "--deny-local-obligations", "--output", tempPath s!"verity-main-test-{nonce}-macro-local-obligation-fail-out"]
    "LocalObligationMacroSmoke [constructor:constructor]: unchecked local obligations: constructor_storage_layout"

set_option maxRecDepth 100000 in
unsafe def runMechanicsAndProxyTests : IO Unit := do
  let tempRoot := (← IO.getEnv "TMPDIR").getD "/tmp"
  let tempPath (name : String) : String := s!"{tempRoot}/{name}"
  let nonce ← IO.monoMsNow
  let memoryStrictOutDir := tempPath s!"verity-main-test-{nonce}-memory-strict-out"
  IO.FS.createDirAll memoryStrictOutDir
  Compiler.Main.run (["--module", "Contracts.SimpleStorage.SimpleStorage", "--deny-linear-memory-mechanics", "--output", memoryStrictOutDir])
  let memoryStrictArtifact ← fileExists s!"{memoryStrictOutDir}/SimpleStorage.yul"
  expectTrue "strict linear-memory gate accepts contracts without partially modeled memory mechanics" memoryStrictArtifact
  expectErrorContains
    "strict linear-memory gate rejects partially modeled memory mechanics"
    ["--module", "Contracts.Counter.Counter", "--deny-linear-memory-mechanics", "--output", tempPath s!"verity-main-test-{nonce}-memory-fail-out"]
    "Counter [function:previewEnvOps]: mload"
  let eventStrictOutDir := tempPath s!"verity-main-test-{nonce}-event-strict-out"
  IO.FS.createDirAll eventStrictOutDir
  Compiler.Main.run (["--module", "Contracts.SimpleStorage.SimpleStorage", "--deny-event-emission", "--output", eventStrictOutDir])
  let eventStrictArtifact ← fileExists s!"{eventStrictOutDir}/SimpleStorage.yul"
  expectTrue "strict event-emission gate accepts contracts without raw event emission" eventStrictArtifact
  expectErrorContains
    "strict event-emission gate rejects raw event emission"
    ["--module", "Contracts.RawLogTrustSurface", "--deny-event-emission", "--output", tempPath s!"verity-main-test-{nonce}-event-fail-out"]
    "RawLogTrustSurface [function:emitTrace]: rawLog"
  let lowLevelStrictOutDir := tempPath s!"verity-main-test-{nonce}-low-level-strict-out"
  IO.FS.createDirAll lowLevelStrictOutDir
  Compiler.Main.run (["--module", "Contracts.SimpleStorage.SimpleStorage", "--deny-low-level-mechanics", "--output", lowLevelStrictOutDir])
  let lowLevelStrictArtifact ← fileExists s!"{lowLevelStrictOutDir}/SimpleStorage.yul"
  expectTrue "strict low-level gate accepts contracts without low-level mechanics" lowLevelStrictArtifact
  expectErrorContains
    "strict low-level gate rejects low-level mechanics"
    ["--module", "Contracts.Counter.Counter", "--deny-low-level-mechanics", "--output", tempPath s!"verity-main-test-{nonce}-low-level-fail-out"]
    "Counter [function:previewLowLevel]: call, staticcall, delegatecall, revertReturndata, returndataCopy, returndataSize"
  let runtimeStrictOutDir := tempPath s!"verity-main-test-{nonce}-runtime-strict-out"
  IO.FS.createDirAll runtimeStrictOutDir
  Compiler.Main.run (["--module", "Contracts.SimpleStorage.SimpleStorage", "--deny-runtime-introspection", "--output", runtimeStrictOutDir])
  let runtimeStrictArtifact ← fileExists s!"{runtimeStrictOutDir}/SimpleStorage.yul"
  expectTrue "strict runtime-introspection gate accepts contracts without partially modeled runtime introspection" runtimeStrictArtifact
  expectErrorContains
    "strict runtime-introspection gate rejects partially modeled runtime introspection"
    ["--module", "Contracts.Counter.Counter", "--deny-runtime-introspection", "--output", tempPath s!"verity-main-test-{nonce}-runtime-fail-out"]
    "Counter [function:previewEnvOps]: blockNumber, contractAddress, chainid"
  let proxyStrictOutDir := tempPath s!"verity-main-test-{nonce}-proxy-strict-out"
  IO.FS.createDirAll proxyStrictOutDir
  Compiler.Main.run (["--module", "Contracts.SimpleStorage.SimpleStorage", "--deny-proxy-upgradeability", "--output", proxyStrictOutDir])
  let proxyStrictArtifact ← fileExists s!"{proxyStrictOutDir}/SimpleStorage.yul"
  expectTrue "strict proxy-upgradeability gate accepts contracts without delegatecall" proxyStrictArtifact
  expectErrorContains
    "strict proxy-upgradeability gate rejects delegatecall mechanics"
    ["--module", "Contracts.Counter.Counter", "--deny-proxy-upgradeability", "--output", tempPath s!"verity-main-test-{nonce}-proxy-fail-out"]
    "Counter [function:previewLowLevel]: delegatecall"
  let proxyMacroTrustReportPath := tempPath s!"verity-main-test-{nonce}-proxy-macro-trust-report.json"
  let proxyMacroOutDir := tempPath s!"verity-main-test-{nonce}-proxy-macro-out"
  IO.FS.createDirAll proxyMacroOutDir
  Compiler.Main.run
    [ "--module", "Contracts.ProxyUpgradeabilityMacroSmoke"
    , "--trust-report", proxyMacroTrustReportPath
    , "--output", proxyMacroOutDir
    ]
  let proxyMacroTrustReport ← IO.FS.readFile proxyMacroTrustReportPath
  expectTrue "macro proxy trust report includes delegatecall proxy boundary"
    (contains proxyMacroTrustReport "\"notModeledProxyUpgradeability\":[\"delegatecall\"]")
  expectTrue "macro proxy trust report includes initializer proxy obligation"
    (contains proxyMacroTrustReport "\"name\":\"implementation_slot_discipline\",\"status\":\"assumed\"")
  expectTrue "macro proxy trust report includes upgrade obligations"
    ((contains proxyMacroTrustReport "\"name\":\"upgrade_authorization\",\"status\":\"assumed\"") &&
      (contains proxyMacroTrustReport "\"name\":\"storage_layout_compatibility\",\"status\":\"unchecked\""))
  expectTrue "macro proxy trust report localizes delegatecall usage"
    (contains proxyMacroTrustReport "\"kind\":\"function\",\"name\":\"forward\"")
  expectErrorContains
    "strict proxy-upgradeability gate rejects macro proxy delegatecall"
    ["--module", "Contracts.ProxyUpgradeabilityMacroSmoke", "--deny-proxy-upgradeability", "--output", tempPath s!"verity-main-test-{nonce}-proxy-macro-fail-out"]
    "ProxyUpgradeabilityMacroSmoke [function:forward]: delegatecall"
  expectErrorContains
    "strict local-obligation gate rejects macro proxy obligations"
    ["--module", "Contracts.ProxyUpgradeabilityMacroSmoke", "--deny-local-obligations", "--output", tempPath s!"verity-main-test-{nonce}-proxy-macro-local-fail-out"]
    "ProxyUpgradeabilityMacroSmoke [function:initProxy]: assumed local obligations: implementation_slot_discipline"
  let proxyMacroLayoutReportPath := tempPath s!"verity-main-test-{nonce}-proxy-macro-layout-report.json"
  let proxyMacroLayoutOutDir := tempPath s!"verity-main-test-{nonce}-proxy-macro-layout-out"
  IO.FS.createDirAll proxyMacroLayoutOutDir
  Compiler.Main.run
    [ "--module", "Contracts.ProxyUpgradeabilityMacroSmoke"
    , "--layout-report", proxyMacroLayoutReportPath
    , "--output", proxyMacroLayoutOutDir
    ]
  let proxyMacroLayoutReport ← IO.FS.readFile proxyMacroLayoutReportPath
  expectTrue "macro proxy layout report includes implementation slot"
    (contains proxyMacroLayoutReport "\"name\":\"implementation\",\"declaredSlot\":2,\"canonicalSlot\":2")
  expectTrue "macro proxy layout report includes initializer slot"
    (contains proxyMacroLayoutReport "\"name\":\"initializedVersion\",\"declaredSlot\":0,\"canonicalSlot\":0")
  expectTrue "macro proxy layout report keeps empty alias policies explicit"
    ((contains proxyMacroLayoutReport "\"reservedSlotRanges\":[]") &&
      (contains proxyMacroLayoutReport "\"slotAliasRanges\":[]"))
  let proxyLayoutCompatReportPath := tempPath s!"verity-main-test-{nonce}-proxy-layout-compat-report.json"
  let proxyLayoutCompatOutDir := tempPath s!"verity-main-test-{nonce}-proxy-layout-compat-out"
  IO.FS.createDirAll proxyLayoutCompatOutDir
  Compiler.Main.run
    [ "--module", "Contracts.ProxyUpgradeabilityMacroSmoke"
    , "--module", "Contracts.ProxyUpgradeabilityLayoutCompatibleSmoke"
    , "--layout-compat-report", proxyLayoutCompatReportPath
    , "--output", proxyLayoutCompatOutDir
    ]
  let proxyLayoutCompatReport ← IO.FS.readFile proxyLayoutCompatReportPath
  expectTrue "proxy layout compatibility report accepts preserved baseline slots"
    (contains proxyLayoutCompatReport "\"compatible\":true")
  expectTrue "proxy layout compatibility report surfaces trailing added field"
    (contains proxyLayoutCompatReport "\"addedFields\":[\"pendingImplementation\"]")
  expectErrorContains
    "strict layout-compatibility gate rejects proxy slot drift"
    [ "--module", "Contracts.ProxyUpgradeabilityMacroSmoke"
    , "--module", "Contracts.ProxyUpgradeabilityLayoutIncompatibleSmoke"
    , "--deny-layout-incompatibility"
    , "--output", tempPath s!"verity-main-test-{nonce}-proxy-layout-compat-fail-out"
    ]
    "field 'admin' moved slots: 1 -> 2"

/-- All phases in one process: local convenience entry point. CI invokes the
phases individually (see `runPhase`) to keep peak memory bounded. -/
unsafe def runTests : IO Unit := do
  runFlagAndUnitTests
  runCompileModeTests
  runStrictGateTests
  runMechanicsAndProxyTests

unsafe def runPhase (phase : String) : IO UInt32 := do
  match phase with
  | "flags" => runFlagAndUnitTests; pure 0
  | "compile" => runCompileModeTests; pure 0
  | "gates" => runStrictGateTests; pure 0
  | "mechanics" => runMechanicsAndProxyTests; pure 0
  | _ =>
    IO.eprintln s!"unknown phase '{phase}'; expected flags|compile|gates|mechanics"
    pure 2

end Compiler.MainTest


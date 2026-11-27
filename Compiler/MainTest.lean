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
  expectErrorContains "missing --max-stack-locals value" ["--max-stack-locals"] "Missing value for --max-stack-locals"
  expectErrorContains "invalid --max-stack-locals value" ["--max-stack-locals", "not-a-number"] "Invalid value for --max-stack-locals: not-a-number"
  expectErrorContains "--max-stack-locals accepted; errors no input" ["--max-stack-locals", "8"] "No compiler input provided"
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
  -- ECM `resultVars` must be bound by the Yul the module emits (else dangling identifiers).
  expectTrue "ECM binding all declared result variables is accepted"
    (Compiler.CompilationModel.firstEcmUnboundResultVar
      Contracts.Smoke.GenericECMTripleResultSmoke.spec == none)
  let unboundMod : Compiler.ECM.ExternalCallModule :=
    { Contracts.Smoke.genericECMTripleResultModule with
      compile := fun _ _ => pure [.let_ "first" (.lit 1)] }
  let unboundSpec : Compiler.CompilationModel.CompilationModel := {
    name := "EcmUnboundResultVar"
    fields := []
    «constructor» := none
    functions := [
      { name := "run", params := [], returnType := none,
        body := [Compiler.CompilationModel.Stmt.ecm unboundMod [],
          Compiler.CompilationModel.Stmt.stop] }
    ] }
  expectTrue "ECM leaving a declared result variable unbound is detected"
    (Compiler.CompilationModel.firstEcmUnboundResultVar unboundSpec ==
      some ("genericTripleResult", "second"))
  match Compiler.CompilationModel.compile unboundSpec [0x12345678] with
  | .ok _ => throw (IO.userError "✗ ECM with unbound result variable compiled")
  | .error err =>
      expectTrue "ECM with unbound result variable is a compile error"
        (contains err "does not bind it with a top-level `let`")

  let oneLineLib :=
    "function libA() -> r { r := 1 }\n" ++
    "function libB() { libC() }\n" ++
    "function libC() { sstore(0, 2) }\n"
  let oneLineParsed := Compiler.Linker.parseLibrary oneLineLib
  expectTrue "linker parses consecutive one-line functions separately"
    (oneLineParsed.map (·.name) == ["libA", "libB", "libC"])
  let linkObj : Compiler.Yul.YulObject := {
    name := "LinkSmoke"
    deployCode := [.let_ "x" (.call "libA" [])]
    runtimeCode := [.exprStmt (.call "libB" [])] }
  match Compiler.Linker.renderWithLibraries linkObj oneLineParsed with
  | .error e => throw (IO.userError s!"✗ linker renders creation-code library calls: {e}")
  | .ok rendered =>
      let creation := (rendered.splitOn "object \"runtime\"").headD ""
      let runtime := (rendered.splitOn "object \"runtime\"").getD 1 ""
      expectTrue "linker injects library functions called from creation code"
        (contains creation "function libA()")
      expectTrue "linker leaves unreferenced library functions out of creation code"
        (!contains creation "function libB()" && !contains creation "function libC()")
      expectTrue "linker injects every library function into runtime code"
        (contains runtime "function libA()" && contains runtime "function libB()" &&
          contains runtime "function libC()")

  -- Call detection is per identifier: a space or a line break may sit between the
  -- callee and `(`, and a longer identifier ending in a library name is not a call to it.
  let spacedLib :=
    "function libA() -> r {\n" ++
    "    r := libC (1)\n" ++
    "    r := add(r, libE\n" ++
    "        (r))\n" ++
    "}\n" ++
    "function libC(x) -> y { y := x }\n" ++
    "function libD() -> y { y := 4 }\n" ++
    "function libE(x) -> y { y := x }\n" ++
    "function xlibD() -> y { y := 5 }\n"
  let spacedParsed := Compiler.Linker.parseLibrary spacedLib
  let spacedObj : Compiler.Yul.YulObject := {
    name := "LinkSpacing"
    deployCode := [.let_ "a" (.call "libA" []), .let_ "b" (.call "xlibD" [])]
    runtimeCode := [.exprStmt (.call "pop" [.call "xlibD" []])] }
  match Compiler.Linker.renderWithLibraries spacedObj spacedParsed with
  | .error e => throw (IO.userError s!"✗ linker renders spaced library calls: {e}")
  | .ok rendered =>
      let creation := (rendered.splitOn "object \"runtime\"").headD ""
      expectTrue "linker injects a library function called as `name (`"
        (contains creation "function libC(")
      expectTrue "linker injects a library function whose `(` is on the next line"
        (contains creation "function libE(")
      expectTrue "linker does not treat `xname(` as a call to `name`"
        (contains creation "function xlibD(" && !contains creation "function libD(")
  let xRuntimeObj : Compiler.Yul.YulObject := { spacedObj with deployCode := [] }
  expectTrue "referenced-library closure does not treat `xname(` as a call to `name`"
    ((Compiler.Linker.selectDirectlyReferencedLibraries xRuntimeObj spacedParsed).map (·.name) ==
      ["xlibD"])
  let spacedRuntimeObj : Compiler.Yul.YulObject :=
    { xRuntimeObj with runtimeCode := [.exprStmt (.call "pop" [.call "libA" []])] }
  expectTrue "referenced-library closure follows spaced and line-split calls"
    ((Compiler.Linker.selectDirectlyReferencedLibraries spacedRuntimeObj spacedParsed).map
      (·.name) == ["libA", "libC", "libE"])
  -- `raiseFreePointerInit` (no longer on a compile path: raising the free pointer does not
  -- protect spill words from runtime-sized writes at fixed low addresses, so the compile paths
  -- spill only statically gated sections).
  let spillProbe : List Compiler.Yul.YulStmt :=
    [.exprStmt (.call "mstore" [.lit 64, .lit 128]),
     .block [.exprStmt (.call "mstore" [.lit 4128, .lit 7]),
       .let_ "x" (.call "mload" [.lit 4096])]]
  expectTrue "spill high-water mark is one past the highest spill slot"
    (Compiler.Yul.TempReuse.spillHighWaterStmts spillProbe == 4160)
  expectTrue "no spill slot means no high-water mark"
    (Compiler.Yul.TempReuse.spillHighWaterStmts [.exprStmt (.call "mstore" [.lit 64, .lit 128])] == 0)
  expectTrue "the free-pointer initialisation is raised above the spill slots"
    (Compiler.Yul.TempReuse.raiseFreePointerInit 4160 spillProbe ==
      [.exprStmt (.call "mstore" [.lit 64, .lit 4160])] ++ spillProbe.drop 1)
  -- `n` long-lived locals `p_i := calldataload(i)`, all read by one final `sstore` each.
  let longLived (p : String) (n : Nat) : List Compiler.Yul.YulStmt :=
    ((List.range n).map fun i => .let_ s!"{p}{i}" (.call "calldataload" [.lit (32 * i)])) ++
      (List.range n).map fun i => .exprStmt (.call "sstore" [.lit i, .ident s!"{p}{i}"])
  let topSpillSlots (stmts : List Compiler.Yul.YulStmt) : List Nat :=
    stmts.filterMap fun
      | .exprStmt (.call "mstore" [.lit offset, _]) =>
          if Compiler.Yul.TempReuse.defaultSpillBase ≤ offset then some offset else none
      | _ => none
  -- An outer block whose spilled locals stay live across a nested block that also spills:
  -- the outer slots must lie above every slot of the nested block (#2831).
  let outer := longLived "o" 14
  let nestedProbe : List Compiler.Yul.YulStmt :=
    outer.take 14 ++ [.block (longLived "i" 14)] ++ outer.drop 14
  let nestedOut := Compiler.Yul.TempReuse.reuseAndSpillTemps 12 [] true nestedProbe
  let innerOut := nestedOut.filterMap fun | .block b => some b | _ => none
  expectTrue "nested block and enclosing block both spill"
    (!(topSpillSlots nestedOut).isEmpty && !(innerOut.flatMap topSpillSlots).isEmpty)
  expectTrue "enclosing-block spill slots lie above the nested block's slots"
    ((topSpillSlots nestedOut).all fun offset =>
      Compiler.Yul.TempReuse.spillHighWaterStmts innerOut.flatten ≤ offset)
  -- Function bodies and `for` initialisers never spill to fixed slots (callers, recursion and
  -- loop bodies would share them); they only reuse dead stack temporaries.
  let funcOut := Compiler.Yul.TempReuse.reuseAndSpillTemps 12 [] true
    [.funcDef "f" [] [] (longLived "f" 14)]
  expectTrue "function bodies do not spill"
    (Compiler.Yul.TempReuse.spillHighWaterStmts funcOut == 0)
  let forOut := Compiler.Yul.TempReuse.reuseAndSpillTemps 12 [] true
    [.for_ (longLived "l" 14) (.lit 0) [] []]
  expectTrue "for initialisers do not spill"
    (Compiler.Yul.TempReuse.spillHighWaterStmts forOut == 0)
  -- A `for` initialiser variable that the rest of the initialiser no longer reads is still live
  -- in the condition, body and post block: it must never be reused as a dead temporary.
  let forInitLive : List Compiler.Yul.YulStmt :=
    .let_ "t" (.lit 5) ::
      (List.range 13).flatMap fun i =>
        [.let_ s!"l{i}" (.call "calldataload" [.lit (32 * i)]),
         .exprStmt (.call "sstore" [.lit i, .ident s!"l{i}"])]
  let forInitProbe : List Compiler.Yul.YulStmt :=
    [.for_ forInitLive (.call "lt" [.ident "t", .lit 6])
      [.assign "t" (.call "add" [.ident "t", .lit 1])]
      [.exprStmt (.call "sstore" [.lit 99, .ident "t"])]]
  expectTrue "a deep for initialiser keeps every variable it declares"
    (Compiler.Yul.TempReuse.reuseAndSpillTemps 12 [] true forInitProbe == forInitProbe)
  -- The compile paths spill a section only when its spill words are statically checked to be
  -- disjoint from every other memory access (literal addresses below the spill base, no `msize`, no
  -- call leaving the section); otherwise the section is returned unchanged.
  let staticDeep : List Compiler.Yul.YulStmt :=
    [.exprStmt (.call "mstore" [.lit 64, .lit 128])] ++ longLived "s" 14 ++
      [.exprStmt (.call "return" [.lit 0, .lit 32])]
  let staticOut := Compiler.Yul.TempReuse.reuseAndSpillTempsStaticSection 12 staticDeep
  expectTrue "a static-memory section is spilled and keeps its free-pointer initialisation"
    (staticOut != staticDeep && staticOut.head? == staticDeep.head?)
  let withAlloc := staticDeep ++
    [.let_ "ptr" (.call "mload" [.lit 64]), .exprStmt (.call "mstore" [.ident "ptr", .lit 1])]
  expectTrue "a section that writes runtime-allocated memory is not spilled"
    (Compiler.Yul.TempReuse.reuseAndSpillTempsStaticSection 12 withAlloc == withAlloc)
  let withDynamic := staticDeep ++
    [.exprStmt (.call "return" [.lit 0, .call "calldataload" [.lit 0]])]
  expectTrue "a section with a non-literal memory range is not spilled"
    (Compiler.Yul.TempReuse.reuseAndSpillTempsStaticSection 12 withDynamic == withDynamic)
  let withMsize := staticDeep ++ [.exprStmt (.call "pop" [.call "msize" []])]
  expectTrue "a section that reads msize is not spilled"
    (Compiler.Yul.TempReuse.reuseAndSpillTempsStaticSection 12 withMsize == withMsize)
  let withExternal := staticDeep ++ [.exprStmt (.call "linkedHelper" [])]
  expectTrue "a section that calls a function it does not define is not spilled"
    (Compiler.Yul.TempReuse.reuseAndSpillTempsStaticSection 12 withExternal == withExternal)
  let withHighLiteral := staticDeep ++ [.exprStmt (.call "mstore" [.lit 4096, .lit 1])]
  expectTrue "a section that touches memory at or above the spill base is not spilled"
    (Compiler.Yul.TempReuse.reuseAndSpillTempsStaticSection 12 withHighLiteral == withHighLiteral)
  -- Per-dispatch-case spilling (`reuseAndSpillTempsDispatchedSection` /
  -- `reuseAndSpillTempsDispatchedObject`, used by `Compiler.emitYulSpilled`).
  let revert00 : List Compiler.Yul.YulStmt :=
    [.exprStmt (.call "revert" [.lit 0, .lit 0])]
  let mkRuntimeDispatch (funcs : List Compiler.Yul.YulStmt)
      (noSelDefault : List Compiler.Yul.YulStmt)
      (cases : List (Nat × List Compiler.Yul.YulStmt))
      (swDefault : List Compiler.Yul.YulStmt) : List Compiler.Yul.YulStmt :=
    funcs ++ [
      .exprStmt (.call "mstore" [.lit 64, .lit 128]),
      .block [
        .let_ "__has_selector"
          (.call "iszero" [.call "lt" [.call "calldatasize" [], .lit 4]]),
        .if_ (.call "iszero" [.ident "__has_selector"]) noSelDefault,
        .if_ (.ident "__has_selector")
          [ .switch
              (.call "shr" [.lit 224, .call "calldataload" [.lit 0]])
              cases
              (some swDefault) ]
      ]
    ]
  let extractCase? (tag : Nat) (code : List Compiler.Yul.YulStmt) :
      Option (List Compiler.Yul.YulStmt) :=
    code.findSome? fun
      | .block [ _, _, .if_ _ [ .switch _ cases _ ] ] =>
          (cases.find? (·.1 == tag)).map Prod.snd
      | _ => none
  let checkedAlloc (base next : String) (sz : Compiler.Yul.YulExpr) :
      List Compiler.Yul.YulStmt :=
    [ .let_ base (.call "mload" [.lit 64]),
      .let_ next (.call "add" [.ident base, sz]),
      .if_ (.call "gt" [.ident next, .lit (2 ^ 64 - 1)]) revert00,
      .if_ (.call "lt" [.ident next, .ident base]) revert00,
      .exprStmt (.call "mstore" [.lit 64, .ident next]) ]
  -- Positive: heap-allocating case spills (with `mstore(64, highWater)` at case entry) next to an
  -- untouched dynamic-scratch case in the same runtime section.
  let posAllocCase : List Compiler.Yul.YulStmt :=
    longLived "a" 14 ++
      checkedAlloc "p" "pEnd" (.lit 64) ++
      [ .exprStmt (.call "mstore" [.ident "p", .lit 11]),
        .exprStmt (.call "mstore" [.call "add" [.ident "p", .lit 32], .lit 22]),
        .exprStmt (.call "mstore" [.lit 0, .call "keccak256" [.ident "p", .lit 64]]),
        .exprStmt (.call "return" [.lit 0, .lit 32]) ]
  let dynScratchCase : List Compiler.Yul.YulStmt :=
    longLived "d" 14 ++
      [ .let_ "len" (.call "calldataload" [.lit 4]),
        .exprStmt (.call "calldatacopy" [.lit 64, .lit 36, .ident "len"]),
        .exprStmt (.call "return" [.lit 0, .call "add" [.lit 64, .ident "len"]]) ]
  let mixedSection :=
    mkRuntimeDispatch [] revert00 [(1, posAllocCase), (2, dynScratchCase)] revert00
  let mixedOut := Compiler.Yul.TempReuse.reuseAndSpillTempsDispatchedSection 12 mixedSection
  let posAllocOut := (extractCase? 1 mixedOut).getD []
  let dynScratchOut := (extractCase? 2 mixedOut).getD []
  let posHw := Compiler.Yul.TempReuse.spillHighWaterStmts posAllocOut
  expectTrue "dispatched gate spills checked-allocation case and prepends mstore(64, highWater)"
    (posHw ≥ Compiler.Yul.TempReuse.defaultSpillBase + 32 &&
      posAllocOut.head? == some (.exprStmt (.call "mstore" [.lit 64, .lit posHw])))
  expectTrue "dispatched gate leaves sibling dynamic-scratch case unchanged"
    (dynScratchOut == dynScratchCase)
  -- Positive: `loadimmutable` and `clz` are memory-free builtins, so their case spills.
  let immClzCase : List Compiler.Yul.YulStmt :=
    longLived "im" 14 ++
      [ .let_ "iv" (.call "loadimmutable" [.str "immSlot"]),
        .let_ "lz" (.call "clz" [.ident "iv"]),
        .let_ "ep" (.call "mload" [.lit 64]),
        .exprStmt (.call "mstore" [.ident "ep", .ident "lz"]),
        .exprStmt (.call "mstore" [.lit 0, .call "keccak256" [.ident "ep", .lit 32]]),
        .exprStmt (.call "return" [.lit 0, .lit 32]) ]
  let immClzOut :=
    (extractCase? 1
      (Compiler.Yul.TempReuse.reuseAndSpillTempsDispatchedSection 12
        (mkRuntimeDispatch [] revert00 [(1, immClzCase)] revert00))).getD []
  expectTrue "dispatched gate spills loadimmutable and clz case"
    (Compiler.Yul.TempReuse.spillHighWaterStmts immClzOut > 0)
  -- Negative / Reproducer 1: in-case `mstore(64, 128)` is never rewritten to `highWater`, and a
  -- literal store overlapping `[64, 96)` marks `fpClean := false` so a subsequent `mload(64)`
  -- rejects spilling.
  let repro1TupleStore : List Compiler.Yul.YulStmt :=
    longLived "r1" 14 ++
      [ .let_ "p" (.call "mload" [.lit 64]),
        .exprStmt (.call "mstore" [.ident "p", .lit 1]),
        .exprStmt (.call "mstore" [.lit 0, .lit 136]),
        .exprStmt (.call "mstore" [.lit 32, .lit 99]),
        .exprStmt (.call "mstore" [.lit 64, .lit 128]),
        .exprStmt (.call "return" [.lit 0, .lit 96]) ]
  let repro1TupleOut :=
    (extractCase? 1
      (Compiler.Yul.TempReuse.reuseAndSpillTempsDispatchedSection 12
        (mkRuntimeDispatch [] revert00 [(1, repro1TupleStore)] revert00))).getD []
  expectTrue "reproducer 1: user mstore(64, 128) in a case body is never rewritten to highWater"
    (repro1TupleOut.contains (.exprStmt (.call "mstore" [.lit 64, .lit 128])))
  let repro1ResetThenAlloc : List Compiler.Yul.YulStmt :=
    longLived "r1b" 14 ++
      [ .exprStmt (.call "mstore" [.lit 64, .lit 128]),
        .let_ "p" (.call "mload" [.lit 64]),
        .exprStmt (.call "mstore" [.ident "p", .lit 1]),
        .exprStmt (.call "return" [.lit 0, .lit 32]) ]
  let repro1ResetOut :=
    (extractCase? 1
      (Compiler.Yul.TempReuse.reuseAndSpillTempsDispatchedSection 12
        (mkRuntimeDispatch [] revert00 [(1, repro1ResetThenAlloc)] revert00))).getD []
  expectTrue "reproducer 1b: mstore(64, 128) followed by mload(64) is not spilled"
    (repro1ResetOut == repro1ResetThenAlloc)
  -- Negative / Reproducer 2: 256-bit wraparound addends (`2^256 - 32`, `calldataload`) and
  -- unguarded or loop `mstore(64, next)` are rejected.
  let repro2WrapConst : List Compiler.Yul.YulStmt :=
    longLived "r2" 14 ++
      [ .let_ "p" (.call "mload" [.lit 64]),
        .exprStmt (.call "mstore" [.call "add" [.ident "p", .lit (2 ^ 256 - 32)], .lit 999999]),
        .exprStmt (.call "return" [.lit 0, .lit 32]) ]
  let repro2DynAdd : List Compiler.Yul.YulStmt :=
    longLived "r2d" 14 ++
      [ .let_ "p" (.call "mload" [.lit 64]),
        .exprStmt (.call "mstore" [.call "add" [.ident "p", .call "calldataload" [.lit 4]], .lit 1]),
        .exprStmt (.call "return" [.lit 0, .lit 32]) ]
  let repro2UnguardedBump : List Compiler.Yul.YulStmt :=
    longLived "r2u" 14 ++
      [ .let_ "p" (.call "mload" [.lit 64]),
        .exprStmt (.call "mstore" [.ident "p", .lit 1]),
        .exprStmt (.call "mstore" [.lit 64, .call "add" [.ident "p", .lit 32]]),
        .exprStmt (.call "return" [.lit 0, .lit 32]) ]
  let repro2LoopAlloc : List Compiler.Yul.YulStmt :=
    longLived "r2l" 14 ++
      [ .for_ [.let_ "i" (.lit 0)] (.call "lt" [.ident "i", .lit 4])
          [.assign "i" (.call "add" [.ident "i", .lit 1])]
          (checkedAlloc "lp" "lpEnd" (.lit 32) ++
            [.exprStmt (.call "mstore" [.ident "lp", .lit 1])]),
        .exprStmt (.call "return" [.lit 0, .lit 32]) ]
  let repro2Out :=
    Compiler.Yul.TempReuse.reuseAndSpillTempsDispatchedSection 12
      (mkRuntimeDispatch [] revert00
        [(1, repro2WrapConst), (2, repro2DynAdd), (3, repro2UnguardedBump), (4, repro2LoopAlloc)]
        revert00)
  expectTrue "reproducer 2: wrapping constant addend is not spilled"
    ((extractCase? 1 repro2Out).getD [] == repro2WrapConst)
  expectTrue "reproducer 2b: unbounded calldata addend is not spilled"
    ((extractCase? 2 repro2Out).getD [] == repro2DynAdd)
  expectTrue "reproducer 2c: unguarded mstore(64, add(p, 32)) is not spilled"
    ((extractCase? 3 repro2Out).getD [] == repro2UnguardedBump)
  expectTrue "reproducer 2d: allocation inside a for loop is not spilled"
    ((extractCase? 4 repro2Out).getD [] == repro2LoopAlloc)
  -- Negative / Reproducer 3: observable `mem[64]` via overlapping static reads, hex literal `0x40`,
  -- `mcopy`, or pointer values in non-address positions (`sstore`, `eq`).
  let repro3Return96 : List Compiler.Yul.YulStmt :=
    longLived "r3" 14 ++
      [ .if_ (.call "calldataload" [.lit 4])
          [ .let_ "p" (.call "mload" [.lit 64]),
            .exprStmt (.call "mstore" [.ident "p", .lit 1]) ],
        .exprStmt (.call "return" [.lit 0, .lit 96]) ]
  let repro3Hex40 : List Compiler.Yul.YulStmt :=
    longLived "r3h" 14 ++
      [ .let_ "p" (.call "mload" [.lit 64]),
        .exprStmt (.call "mstore" [.ident "p", .lit 1]),
        .exprStmt (.call "mstore" [.lit 0, .call "mload" [.hex 0x40]]),
        .exprStmt (.call "return" [.lit 0, .lit 32]) ]
  let repro3McopyFp : List Compiler.Yul.YulStmt :=
    longLived "r3m" 14 ++
      [ .let_ "p" (.call "mload" [.lit 64]),
        .exprStmt (.call "mstore" [.ident "p", .lit 1]),
        .exprStmt (.call "mcopy" [.lit 0, .lit 64, .lit 32]),
        .exprStmt (.call "return" [.lit 0, .lit 32]) ]
  let repro3PtrLeak : List Compiler.Yul.YulStmt :=
    longLived "r3p" 14 ++
      [ .let_ "p" (.call "mload" [.lit 64]),
        .exprStmt (.call "mstore" [.ident "p", .lit 1]),
        .exprStmt (.call "sstore" [.lit 0, .ident "p"]),
        .exprStmt (.call "return" [.lit 0, .lit 32]) ]
  let repro3Partial48 : List Compiler.Yul.YulStmt :=
    longLived "r3w" 14 ++
      [ .let_ "p" (.call "mload" [.lit 64]),
        .exprStmt (.call "mstore" [.ident "p", .lit 1]),
        .exprStmt (.call "mstore" [.lit 48, .lit 0]),
        .exprStmt (.call "return" [.lit 0, .lit 96]) ]
  let repro3Out :=
    Compiler.Yul.TempReuse.reuseAndSpillTempsDispatchedSection 12
      (mkRuntimeDispatch [] revert00
        [ (1, repro3Return96), (2, repro3Hex40), (3, repro3McopyFp),
          (4, repro3PtrLeak), (5, repro3Partial48) ]
        revert00)
  expectTrue "reproducer 3: return(0, 96) reading unoverwritten mem[64] is not spilled"
    ((extractCase? 1 repro3Out).getD [] == repro3Return96)
  expectTrue "reproducer 3b: mload(0x40) in value position is not spilled"
    ((extractCase? 2 repro3Out).getD [] == repro3Hex40)
  expectTrue "reproducer 3c: mcopy from [64, 96) is not spilled"
    ((extractCase? 3 repro3Out).getD [] == repro3McopyFp)
  expectTrue "reproducer 3d: sstore of free-pointer local is not spilled"
    ((extractCase? 4 repro3Out).getD [] == repro3PtrLeak)
  expectTrue "reproducer 3e: partial write mstore(48, 0) before return(0, 96) is not spilled"
    ((extractCase? 5 repro3Out).getD [] == repro3Partial48)
  -- Negative / Reproducer 4: inner `switch` inside fallback/default body, non-terminating cases,
  -- `[leave, revert]`, and non-`buildSwitch` section shapes are left unchanged.
  let repro4Fallback : List Compiler.Yul.YulStmt :=
    [ .let_ "buf" (.call "mload" [.lit 64]),
      .let_ "off" (.call "calldataload" [.lit 4]),
      .exprStmt (.call "mstore" [.call "add" [.ident "buf", .ident "off"], .lit 777]),
      .switch (.call "callvalue" []) [(0, longLived "fb" 14)] none,
      .exprStmt (.call "mstore" [.lit 0, .call "mload" [.call "add" [.ident "buf", .ident "off"]]]),
      .exprStmt (.call "return" [.lit 0, .lit 32]) ]
  let repro4Section := mkRuntimeDispatch [] repro4Fallback [(1, posAllocCase)] repro4Fallback
  let repro4Out := Compiler.Yul.TempReuse.reuseAndSpillTempsDispatchedSection 12 repro4Section
  expectTrue "reproducer 4: fallback with inner non-terminating switch is left unchanged"
    (repro4Out == mkRuntimeDispatch [] repro4Fallback [(1, posAllocOut)] repro4Fallback)
  let nonTerminatingCase : List Compiler.Yul.YulStmt :=
    longLived "nt" 14 ++
      [ .let_ "p" (.call "mload" [.lit 64]),
        .exprStmt (.call "mstore" [.ident "p", .lit 1]) ]
  let leaveBeforeRevertCase : List Compiler.Yul.YulStmt :=
    longLived "lv" 14 ++
      [ .let_ "p" (.call "mload" [.lit 64]),
        .exprStmt (.call "mstore" [.ident "p", .lit 1]),
        .leave,
        .exprStmt (.call "revert" [.lit 0, .lit 0]) ]
  let msizeCase : List Compiler.Yul.YulStmt :=
    longLived "ms" 14 ++
      [ .let_ "p" (.call "mload" [.lit 64]),
        .exprStmt (.call "mstore" [.ident "p", .call "msize" []]),
        .exprStmt (.call "return" [.lit 0, .lit 32]) ]
  let forInitFpLeakCase : List Compiler.Yul.YulStmt :=
    longLived "fi" 14 ++
      [ .for_ [.let_ "p" (.call "mload" [.lit 64])] (.lit 1) []
          [ .exprStmt (.call "mstore" [.ident "p", .lit 1]),
            .exprStmt (.call "mstore" [.lit 0, .ident "p"]),
            .exprStmt (.call "return" [.lit 0, .lit 32]) ],
        .exprStmt (.call "return" [.lit 0, .lit 32]) ]
  let termAndMsizeOut :=
    Compiler.Yul.TempReuse.reuseAndSpillTempsDispatchedSection 12
      (mkRuntimeDispatch [] revert00
        [ (1, nonTerminatingCase), (2, leaveBeforeRevertCase),
          (3, msizeCase), (4, forInitFpLeakCase) ]
        revert00)
  expectTrue "reproducer 4b: non-terminating dispatch case is not spilled"
    ((extractCase? 1 termAndMsizeOut).getD [] == nonTerminatingCase)
  expectTrue "reproducer 4c: [leave, revert] does not count as terminating"
    ((extractCase? 2 termAndMsizeOut).getD [] == leaveBeforeRevertCase)
  expectTrue "msize in a dispatch case is not spilled"
    ((extractCase? 3 termAndMsizeOut).getD [] == msizeCase)
  expectTrue "for-init mload(64) pointer leak is not spilled"
    ((extractCase? 4 termAndMsizeOut).getD [] == forInitFpLeakCase)
  let trailingStmtSection :=
    mixedSection ++ [.exprStmt (.call "stop" [])]
  expectTrue "runtime section with trailing statement after buildSwitch is left unchanged"
    (Compiler.Yul.TempReuse.reuseAndSpillTempsDispatchedSection 12 trailingStmtSection ==
      trailingStmtSection)
  -- Negative / Round-2 Reproducers 5 & 6: static access in `[128, 4096)` mixed with `mload(64)`
  -- (static-vs-heap aliasing at `128`), and checked allocations with unbounded or near-`2^64`
  -- reservation sizes (`maxFp + ub > 2^64 - 1`).
  let repro5Static128Alias : List Compiler.Yul.YulStmt :=
    longLived "r5" 14 ++
      [ .let_ "p" (.call "mload" [.lit 64]),
        .exprStmt (.call "mstore" [.ident "p", .lit 111]),
        .exprStmt (.call "mstore" [.lit 0, .call "mload" [.lit 128]]),
        .exprStmt (.call "return" [.lit 0, .lit 32]) ]
  let repro6DynSizeAlloc : List Compiler.Yul.YulStmt :=
    longLived "r6d" 14 ++
      checkedAlloc "p" "pEnd" (.call "calldataload" [.lit 4]) ++
      [ .exprStmt (.call "mstore" [.ident "p", .lit 1]),
        .exprStmt (.call "return" [.lit 0, .lit 32]) ]
  let repro6NearU64Alloc : List Compiler.Yul.YulStmt :=
    longLived "r6c" 14 ++
      checkedAlloc "p" "pEnd" (.lit (2 ^ 64 - 200)) ++
      [ .exprStmt (.call "mstore" [.ident "p", .lit 1]),
        .exprStmt (.call "return" [.lit 0, .lit 32]) ]
  let repro6CumulativeAlloc : List Compiler.Yul.YulStmt :=
    longLived "r6s" 14 ++
      checkedAlloc "p1" "p1End" (.lit (2 ^ 63)) ++
      checkedAlloc "p2" "p2End" (.lit (2 ^ 63)) ++
      [ .exprStmt (.call "mstore" [.ident "p1", .lit 1]),
        .exprStmt (.call "return" [.lit 0, .lit 32]) ]
  let r2RoundOut :=
    Compiler.Yul.TempReuse.reuseAndSpillTempsDispatchedSection 12
      (mkRuntimeDispatch [] revert00
        [ (1, repro5Static128Alias), (2, repro6DynSizeAlloc),
          (3, repro6NearU64Alloc), (4, repro6CumulativeAlloc) ]
        revert00)
  expectTrue "reproducer 5: static mload(128) mixed with mload(64) heap is not spilled"
    ((extractCase? 1 r2RoundOut).getD [] == repro5Static128Alias)
  expectTrue "reproducer 6a: checked allocation with unbounded calldata size is not spilled"
    ((extractCase? 2 r2RoundOut).getD [] == repro6DynSizeAlloc)
  expectTrue "reproducer 6b: checked allocation with near-2^64 constant size is not spilled"
    ((extractCase? 3 r2RoundOut).getD [] == repro6NearU64Alloc)
  expectTrue "reproducer 6c: cumulative checked allocations exceeding 2^64 - 1 are not spilled"
    ((extractCase? 4 r2RoundOut).getD [] == repro6CumulativeAlloc)
  -- Negative / Round-3 Reproducer 7: Yul `break` / `continue` / `.exprStmt (.ident "leave")`
  -- inside loops or blocks must fail closed and never count as `stmtsAlwaysTerminate`.
  let repro7BreakCase : List Compiler.Yul.YulStmt :=
    longLived "r7b" 14 ++
      [ .for_ [.let_ "i" (.lit 0)] (.call "lt" [.ident "i", .lit 1])
          [.assign "i" (.call "add" [.ident "i", .lit 1])]
          [ .exprStmt (.call "mstore" [.lit 64, .lit 0]),
            .if_ (.call "calldataload" [.lit 4]) [.exprStmt (.ident "break")],
            .exprStmt (.call "revert" [.lit 0, .lit 0]) ],
        .let_ "p" (.call "mload" [.lit 64]),
        .exprStmt (.call "mstore" [.call "add" [.ident "p", .lit 4096], .lit 999999]),
        .exprStmt (.call "return" [.lit 0, .lit 32]) ]
  let repro7ContinueCase : List Compiler.Yul.YulStmt :=
    longLived "r7c" 14 ++
      [ .for_ [.let_ "i" (.lit 0)] (.call "lt" [.ident "i", .lit 2])
          [.assign "i" (.call "add" [.ident "i", .lit 1])]
          [ .if_ (.call "eq" [.ident "i", .lit 0])
              [ .exprStmt (.call "mstore" [.lit 64, .lit 0]),
                .if_ (.call "calldataload" [.lit 4]) [.exprStmt (.ident "continue")],
                .exprStmt (.call "revert" [.lit 0, .lit 0]) ] ],
        .let_ "p" (.call "mload" [.lit 64]),
        .exprStmt (.call "mstore" [.call "add" [.ident "p", .lit 4096], .lit 999999]),
        .exprStmt (.call "return" [.lit 0, .lit 32]) ]
  let repro7IdentLeaveCase : List Compiler.Yul.YulStmt :=
    longLived "r7l" 14 ++
      [ .exprStmt (.call "mstore" [.lit 0, .lit 1]),
        .exprStmt (.ident "leave"),
        .exprStmt (.call "revert" [.lit 0, .lit 0]) ]
  let r3RoundOut :=
    Compiler.Yul.TempReuse.reuseAndSpillTempsDispatchedSection 12
      (mkRuntimeDispatch [] revert00
        [(1, repro7BreakCase), (2, repro7ContinueCase), (3, repro7IdentLeaveCase)]
        revert00)
  expectTrue "reproducer 7a: loop break before revert does not mask mstore(64, 0) or spill"
    ((extractCase? 1 r3RoundOut).getD [] == repro7BreakCase)
  expectTrue "reproducer 7b: loop continue before revert does not mask mstore(64, 0) or spill"
    ((extractCase? 2 r3RoundOut).getD [] == repro7ContinueCase)
  expectTrue "reproducer 7c: .exprStmt (.ident \"leave\") before revert does not count as terminating"
    ((extractCase? 3 r3RoundOut).getD [] == repro7IdentLeaveCase)

set_option maxRecDepth 100000 in
unsafe def runCompileModeTests : IO Unit := do
  let tempRoot := (← IO.getEnv "TMPDIR").getD "/tmp"
  let tempPath (name : String) : String := s!"{tempRoot}/{name}"
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


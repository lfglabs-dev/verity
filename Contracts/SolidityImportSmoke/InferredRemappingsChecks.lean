import Compiler.SolidityImport.Import

/-!
Imports through Foundry's remappings (issue #2835), on the actual importer. Each fixture's
expected source is the one `forge build` (forge 1.5.0) compiled for the same files, read from
its build-info. Where two candidate files exist, they define different library members and
`Entry` calls the one only the expected file has, so a successful import shows which file
was used. `remappingScan` shows how far the importer read the libraries.

* `inferred-remappings/`: `libs = ["deps"]` and no written remapping for `deps/dep`:
  `dep/DepMath.sol` resolves through the inferred `dep/=deps/dep/src/`, its `./Bounds.sol`
  relatively, and `local/Scale.sol` through the written `local/=src/local/`. Full scan.
* `remappings-written-only/`: a written remapping ending in `/` and a relative import under
  `src/`: only library configurations are read.
* `remappings-inference-off/`: `auto_detect_remappings = false`: nothing is read, and
  `dep/Val.sol` is the project file, as in `forge build`.
* `remappings-config-into-src/`: a library's own `remappings.txt` maps `src/sub/` (inside the
  project's `src/`) to its `src/`; `forge build` compiles the library's file.
* `remappings-nested-written/`: of `a/` and the nested `a/b/`, `forge build` keeps `a/`.
* `remappings-config-context/`: a library's context remapping `src:@oz/=…` overrides the
  written `@oz/` for files under `src/` in `forge build`; the importer refuses.
* `inferred-remappings-unknown/`: a library whose `foundry.toml` the importer cannot check
  (Foundry would skip it, with whatever remappings it holds): every import is refused.
* Generated under `.lake/remapping-fixtures/` (symlinks are not committed):
  `symlink-unrelated/` (an unrelated symlink under `deps/`; `src/foo/Bar.sol` as written,
  configurations only), `symlink-written-noslash/` (the same with `oz=deps/oz`, importing
  `oz/A.sol`), and `symlink-supplies-name/` (`deps/pkg` is a symlink, so Foundry infers `pkg/`
  through it and compiles `deps/pkg/src/P.sol` although the project has `pkg/P.sol`: refused),
  and `symlink-config-file/` (a library's `remappings.txt` is a symlink; `forge build` reads
  it and compiles `deps/dep/alt/Bar.sol` for `src/foo/Bar.sol`; the importer does not follow
  it: refused), and `symlink-root-config/` (the project's own `foundry.toml` is a symlink,
  read through as Foundry does), and `nonconfig-toml/` (test-fixture `foundry.toml` files
  with `libs = [".."]` deep in a library: the scan stays bounded).
-/
namespace SolidityImportSmoke.InferredRemappingsChecks
open Compiler.CompilationModel.SolidityImport

solidity_profile remapProfile where
  evmVersion := "osaka"
  viaIR := true
  optimizerRuns := some 466
  bytecodeHash := "none"

private def has (text needle : String) : Bool := (text.splitOn needle).length > 1

solidity_import inferred from "Contracts/SolidityImportSmoke/inferred-remappings"
  entry "src/Entry.sol" using remapProfile contract Entry
  function combined(uint256)

#guard inferred.report.inferredRemappings == ["dep/=deps/dep/src/"]
#guard has inferred.report.settingsJson "\"remappings\":[\"local/=src/local/\",\"dep/=deps/dep/src/\"]"
#guard has inferred.report.toText "\ninferred remapping dep/=deps/dep/src/\n"
#guard inferred.report.remappingScan == "full"

solidity_import writtenOnly from "Contracts/SolidityImportSmoke/remappings-written-only"
  entry "src/Entry.sol" using remapProfile contract Entry
  function value()

#guard writtenOnly.report.inferredRemappings == []
#guard writtenOnly.report.remappingScan == "configs"

solidity_import inferenceOff from "Contracts/SolidityImportSmoke/remappings-inference-off"
  entry "src/Entry.sol" using remapProfile contract Entry
  function value()

#guard inferenceOff.report.remappingScan == "none"

solidity_import configIntoSrc from "Contracts/SolidityImportSmoke/remappings-config-into-src"
  entry "src/Entry.sol" using remapProfile contract Entry
  function value()

#guard configIntoSrc.report.inferredRemappings == ["src/sub/=deps/dep/src/"]
#guard configIntoSrc.report.remappingScan == "full"

solidity_import nestedWritten from "Contracts/SolidityImportSmoke/remappings-nested-written"
  entry "src/Entry.sol" using remapProfile contract Entry
  function value()

#guard has nestedWritten.report.settingsJson "\"remappings\":[\"a/=deps/A/\"]"
#guard nestedWritten.report.remappingScan == "none"

/--
error: src/Entry.sol: import @oz/A.sol in src/Entry.sol can take the context remapping src:@oz/, which the importer does not model
-/
#guard_msgs in
solidity_import configContext from "Contracts/SolidityImportSmoke/remappings-config-context"
  entry "src/Entry.sol" using remapProfile contract Entry
  function value()

/--
error: src/Entry.sol: import dep/DepMath.sol: Foundry's remappings are unknown here (deps/bad/foundry.toml line 2 is not TOML this reader checks), so any import may resolve differently; remove the cause, or set auto_detect_remappings = false if the written remappings suffice
-/
#guard_msgs in
solidity_import unknown from "Contracts/SolidityImportSmoke/inferred-remappings-unknown"
  entry "src/Entry.sol" using remapProfile contract Entry
  function twice(uint256)

/-- A library whose member `fn` returns `v`. -/
private def library (name fn : String) (v : Nat) : String :=
  s!"// SPDX-License-Identifier: MIT\npragma solidity ^0.8.0;\n\nlibrary {name} \{\n    \
    function {fn}() internal pure returns (uint256) \{\n        return {v};\n    }\n}\n"

/-- An `Entry` contract importing `{name}` from `path` and returning `name.fn()`. -/
private def entry (name path fn : String) : String :=
  s!"// SPDX-License-Identifier: MIT\npragma solidity ^0.8.0;\n\nimport \{{name}} from \"{path}\";\n\n\
    contract Entry \{\n    function value() external pure returns (uint256) \{\n        \
    return {name}.{fn}();\n    }\n}\n"

/-- Write a fixture project at `.lake/remapping-fixtures/<name>` (replacing an earlier copy):
its files, then its symlinks (`ln -s target link`). -/
private def writeFixture (name : String) (files : List (String × String))
    (links : List (String × String)) : IO Unit := do
  let root := (← IO.currentDir) / ".lake" / "remapping-fixtures" / name
  if ← root.pathExists then IO.FS.removeDirAll root
  for (p, c) in files do
    let f := root / p
    if let some d := f.parent then IO.FS.createDirAll d
    IO.FS.writeFile f c
  for (link, target) in links do
    let l := root / link
    if let some d := l.parent then IO.FS.createDirAll d
    let out ← IO.Process.output { cmd := "ln", args := #["-s", target, l.toString] }
    unless out.exitCode == 0 do throw (IO.userError s!"ln -s {target} {l}: {out.stderr}")

private def unrelatedLink : List (String × String) := [("deps/other/link", "../../vendor/real")]
private def withUnrelatedLink : List (String × String) :=
  [("foundry.toml", "[profile.default]\nlibs = [\"deps\"]\n"),
   ("deps/dep/src/D.sol", library "D" "dValue" 3), ("vendor/real/src/R.sol", library "R" "rValue" 4)]

run_meta (writeFixture "symlink-unrelated"
  (withUnrelatedLink ++ [("src/foo/Bar.sol", library "Bar" "barValue" 1),
    ("src/Entry.sol", entry "Bar" "src/foo/Bar.sol" "barValue")]) unrelatedLink)
run_meta (writeFixture "symlink-written-noslash"
  (withUnrelatedLink ++ [("remappings.txt", "oz=deps/oz\n"), ("deps/oz/A.sol", library "A" "ozValue" 1),
    ("src/Entry.sol", entry "A" "oz/A.sol" "ozValue")]) unrelatedLink)
run_meta (writeFixture "symlink-supplies-name"
  [("foundry.toml", "[profile.default]\nlibs = [\"deps\"]\n"),
   ("pkg/P.sol", library "P" "projectValue" 1), ("vendor/pkg/src/P.sol", library "P" "vendorValue" 2),
   ("src/Entry.sol", entry "P" "pkg/P.sol" "projectValue")] [("deps/pkg", "../vendor/pkg")])
run_meta (writeFixture "symlink-config-file"
  [("foundry.toml", "[profile.default]\nlibs = [\"deps\"]\n"),
   ("deps/dep/foundry.toml", "[profile.default]\n"), ("elsewhere.txt", "src/foo/=alt/\n"),
   ("deps/dep/alt/Bar.sol", library "Bar" "barValue" 2), ("deps/dep/src/D.sol", library "D" "dValue" 3),
   ("src/foo/Bar.sol", library "Bar" "barValue" 1),
   ("src/Entry.sol", entry "Bar" "src/foo/Bar.sol" "barValue")]
  [("deps/dep/remappings.txt", "../../elsewhere.txt")])

solidity_import symlinkUnrelated from ".lake/remapping-fixtures/symlink-unrelated"
  entry "src/Entry.sol" using remapProfile contract Entry
  function value()

#guard symlinkUnrelated.report.remappingScan == "configs"

solidity_import symlinkNoSlash from ".lake/remapping-fixtures/symlink-written-noslash"
  entry "src/Entry.sol" using remapProfile contract Entry
  function value()

#guard symlinkNoSlash.report.remappingScan == "configs"

/--
error: src/Entry.sol: import pkg/P.sol could take a remapping Foundry infers, but the inferred set is unknown here (symlink in deps); write the remapping in remappings.txt
-/
#guard_msgs in
solidity_import symlinkName from ".lake/remapping-fixtures/symlink-supplies-name"
  entry "src/Entry.sol" using remapProfile contract Entry
  function value()

-- `foundry.toml` files Foundry does not read as library configurations (test fixtures deep
-- in a library), with `libs = [".."]` or a hidden entry: the full scan stays bounded and
-- inside the project; `forge build` compiled `deps/dep/src/D.sol`.
run_meta (writeFixture "nonconfig-toml"
  [("foundry.toml", "[profile.default]\nlibs = [\"deps\"]\n"),
   ("deps/dep/src/D.sol", library "D" "dValue" 3),
   ("deps/dep/test/fixtures/foundry.toml", "[profile.default]\nlibs = [\"..\"]\n"),
   ("deps/dep/test/fx2/foundry.toml", "[profile.default]\nlibs = [\"..\"]\n"),
   ("deps/dep/test/foundry.toml", "[profile.default]\nlibs = [\".hidden\"]\n"),
   ("deps/dep/test/.hidden/x/X.sol", library "X" "xValue" 4),
   ("src/Entry.sol", entry "D" "dep/D.sol" "dValue")] [])

solidity_import nonconfigToml from ".lake/remapping-fixtures/nonconfig-toml"
  entry "src/Entry.sol" using remapProfile contract Entry
  function value()

#guard nonconfigToml.report.inferredRemappings == ["dep/=deps/dep/src/"]
#guard nonconfigToml.report.remappingScan == "full"

-- The project's own `foundry.toml` may be a symlink (read through, as Foundry does): the
-- library configuration's `src/sub/` remapping still applies, and `forge build` compiled
-- `deps/dep/src/Shared.sol` here too.
run_meta (writeFixture "symlink-root-config"
  [("cfg/foundry.toml", "[profile.default]\nlibs = [\"deps\"]\n"),
   ("deps/dep/foundry.toml", "[profile.default]\n"), ("deps/dep/remappings.txt", "src/sub/=src/\n"),
   ("deps/dep/src/Shared.sol", library "Shared" "depValue" 2),
   ("src/sub/Shared.sol", library "Shared" "projectValue" 1),
   ("src/Entry.sol", entry "Shared" "src/sub/Shared.sol" "depValue")]
  [("foundry.toml", "cfg/foundry.toml")])

solidity_import symlinkRootConfig from ".lake/remapping-fixtures/symlink-root-config"
  entry "src/Entry.sol" using remapProfile contract Entry
  function value()

#guard symlinkRootConfig.report.inferredRemappings == ["src/sub/=deps/dep/src/"]

/--
error: src/Entry.sol: import src/foo/Bar.sol: Foundry's remappings are unknown here (deps/dep: a configuration file is a symlink or unreadable), so any import may resolve differently; remove the cause, or set auto_detect_remappings = false if the written remappings suffice
-/
#guard_msgs in
solidity_import symlinkConfig from ".lake/remapping-fixtures/symlink-config-file"
  entry "src/Entry.sol" using remapProfile contract Entry
  function value()

end SolidityImportSmoke.InferredRemappingsChecks

import Lean

/-!
# Importer sources hashed into `sourceDigest`

`sourceDigest` must identify the importer that produced a model. The hashed
files are computed, not listed by hand, so a new or moved module is covered
without an edit here:

* every module in the import closure of `Compiler.SolidityImport.Import` whose
  source file lies under the importer's source root. That closure includes the
  execution semantics the model is interpreted by (`Verity.Core.Model.Denote`
  and its imports) and `Compiler.CompilationModel`. Lean core, Std and other
  packages' modules have no file under the source root and are not hashed;
* every `.lean` file under `Compiler/SolidityImport/`, whether or not `Import`
  imports it, except test sources (`isImporterTestSource`).

Each file is hashed with the host's SHA-256 tool, the one that already checks
the pinned solc binary; the importer frames the relative paths and their
digests as JSON.
-/

namespace Compiler.CompilationModel.SolidityImport

open Lean System

/-- The module whose import closure is hashed. -/
def importerRootModule : Name := `Compiler.SolidityImport.Import

/-- The importer's directory, relative to the source root. -/
def importerDirectory : String := "Compiler/SolidityImport"

/-- Test sources in the importer's directory are not digest inputs: a file
whose name ends in `Test.lean` or `Tests.lean`. -/
def isImporterTestSource (rel : String) : Bool :=
  rel.endsWith "Test.lean" || rel.endsWith "Tests.lean"

/-- `Compiler.SolidityImport.Import` ↦ `Compiler/SolidityImport/Import.lean`. -/
def moduleSourcePath (mod : Name) : String :=
  "/".intercalate (mod.components.map (·.toString (escape := false))) ++ ".lean"

/-- `root` and every module it imports, directly or transitively, read from the
module data of `env`. Sorted by name. -/
def importClosure (env : Environment) (root : Name) : Except String (Array Name) := do
  let mut seen : NameSet := {}
  let mut stack := #[root]
  while !stack.isEmpty do
    let mod := stack.back!
    stack := stack.pop
    unless seen.contains mod do
      seen := seen.insert mod
      let some idx := env.getModuleIdx? mod
        | throw s!"module {mod} is not imported by this file"
      let some data := env.header.moduleData[idx.toNat]?
        | throw s!"no module data for {mod}"
      for imp in data.imports do
        unless seen.contains imp.module do stack := stack.push imp.module
  return (seen.toArray.qsort Name.lt)

/-- The `.lean` files under `sourceRoot/Compiler/SolidityImport/`, test sources
excluded, relative to `sourceRoot`. -/
def importerDirectorySources (sourceRoot : FilePath) : IO (Array String) := do
  let dir := sourceRoot / importerDirectory
  unless ← dir.isDir do throw (IO.userError s!"importer source missing: {dir}")
  let prefixLen := dir.toString.length + 1
  let mut out : Array String := #[]
  for path in ← dir.walkDir do
    if path.extension == some "lean" && !(← path.isDir) then
      let rel := importerDirectory ++ "/" ++ (path.toString.drop prefixLen).toString
      unless isImporterTestSource rel do out := out.push rel
  return out

/-- Every digest input relative to `sourceRoot`, sorted and without duplicates:
the import closure of `importerRootModule` in `env` restricted to files under
`sourceRoot`, and `importerDirectorySources`. -/
def importerDigestSources (env : Environment) (sourceRoot : FilePath) : IO (Array String) := do
  let closure ← match importClosure env importerRootModule with
    | .ok mods => pure mods
    | .error e => throw (IO.userError s!"importer digest: {e}")
  let mut rels : Array String := #[]
  for mod in closure do
    let rel := moduleSourcePath mod
    if ← (sourceRoot / rel).pathExists then rels := rels.push rel
  rels := rels ++ (← importerDirectorySources sourceRoot)
  let sorted := rels.qsort (· < ·)
  return sorted.foldl (init := #[]) fun acc r => if acc.back? == some r then acc else acc.push r

/-- Lowercase hex SHA-256 of each file, in order, from one run of the host's
SHA-256 tool (`sha256sum`, or `shasum -a 256` on macOS). -/
def sha256Files (paths : Array FilePath) : IO (Array String) := do
  if paths.isEmpty then return #[]
  let (cmd, pre) :=
    if System.Platform.isOSX then ("/usr/bin/shasum", #["-a", "256"])
    else ("/usr/bin/sha256sum", #[])
  let out ← IO.Process.output { cmd, args := pre ++ #["--"] ++ paths.map (·.toString) }
  unless out.exitCode == 0 do
    throw (IO.userError s!"{cmd} failed (exit code {out.exitCode}): {out.stderr}")
  let lines := (out.stdout.splitOn "\n").filter (!·.isEmpty) |>.toArray
  unless lines.size == paths.size do
    throw (IO.userError s!"{cmd} printed {lines.size} digests for {paths.size} files")
  lines.mapM fun line => do
    -- A file name that needs escaping makes the tool prefix the line with `\`.
    let line := if line.startsWith "\\" then (line.drop 1).toString else line
    let hex := (line.take 64).toString
    unless hex.length == 64 && hex.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')) do
      throw (IO.userError s!"{cmd}: unexpected output line {line}")
    pure hex

/-- The `importerSources` member of the digest input: each input's path
relative to the source root, mapped to the SHA-256 of its bytes. -/
def importerSourcesJson (env : Environment) (sourceRoot : FilePath) : IO Json := do
  let rels ← importerDigestSources env sourceRoot
  let hashes ← sha256Files (rels.map fun (rel : String) => sourceRoot / rel)
  return Json.mkObj ((rels.zip hashes).toList.map fun (rel, h) => (rel, Json.str h))

end Compiler.CompilationModel.SolidityImport

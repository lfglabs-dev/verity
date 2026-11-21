import Compiler.SolidityImport.Import

/-!
Coverage of `sourceDigest`'s importer inputs (#2829).

1. Every module the importer imports, directly or transitively, with a source
   file in this checkout is a digest input. The closure is recomputed here from
   the `import` lines of the source files, independently of the module data
   `importerDigestSources` reads.
2. Every non-test `.lean` file in `Compiler/SolidityImport/` is a digest input;
   test files are not.
3. In a scratch source root, editing one importer file changes its entry in the
   digest input and leaves the others unchanged; hidden entries are skipped.
4. `Import.lean` puts that input into the digest.

The checks assert membership and differences only, never a full list or a
digest of this checkout, so they do not change when a module is added.
-/

namespace Compiler.CompilationModel.SolidityImport.SourceDigestTest

open Lean Meta Compiler.CompilationModel.SolidityImport

/-- Module names on the `import` lines of a Lean source. Tokens that are not
module names (prose that happens to start with `import `) resolve to no file
and are dropped by the caller. -/
private def importedNames (text : String) : Array Name :=
  (text.splitOn "\n").foldl (init := #[]) fun acc line =>
    if line.startsWith "import " then
      ((line.drop 7).toString.splitOn " ").foldl (init := acc) fun acc tok =>
        if tok.isEmpty then acc else acc.push tok.toName
    else acc

-- 1. The importer's import closure, from the source text.
run_meta do
  let root ← IO.currentDir
  let inputs ← importerDigestSources (← getEnv) root
  let mut seen : NameSet := {}
  let mut stack := #[importerRootModule]
  let mut localCount : Nat := 0
  while !stack.isEmpty do
    let mod := stack.back!
    stack := stack.pop
    if seen.contains mod then continue
    seen := seen.insert mod
    let rel := moduleSourcePath mod
    if ← (root / rel).pathExists then
      localCount := localCount + 1
      unless inputs.contains rel do
        throwError "{rel} is in the importer's import closure but not a sourceDigest input"
      for imp in importedNames (← IO.FS.readFile (root / rel)) do
        stack := stack.push imp
  -- The closure reaches the model semantics and the compilation model.
  unless localCount ≥ 20 do
    throwError "import closure suspiciously small: {localCount} local modules"
  for rel in ["Compiler/SolidityImport/Import.lean", "Verity/Core/Model/Denote.lean",
      "Compiler/CompilationModel.lean"] do
    unless inputs.contains rel do throwError "{rel} is not a sourceDigest input"

-- 2. Every non-test file of the importer directory, read with `readDir`.
run_meta do
  let root ← IO.currentDir
  let inputs ← importerDigestSources (← getEnv) root
  let mut files : Nat := 0
  for entry in ← (root / importerDirectory).readDir do
    if entry.fileName.endsWith ".lean" then
      let rel := importerDirectory ++ "/" ++ entry.fileName
      if isImporterTestSource rel then
        if inputs.contains rel then throwError "test source {rel} is a sourceDigest input"
      else
        files := files + 1
        unless inputs.contains rel do throwError "{rel} is not a sourceDigest input"
  unless files ≥ 20 do throwError "importer directory suspiciously small: {files} files"
  unless !inputs.contains "Compiler/SolidityImport/SourceDigestTest.lean" do
    throwError "this test file must not be a sourceDigest input"

-- 3. Editing one file changes its entry and only its entry.
run_meta do
  IO.FS.withTempDir fun tmp => do
    let dir := tmp / importerDirectory
    IO.FS.createDirAll (dir / "Nested")
    IO.FS.writeFile (dir / "A.lean") "abc"
    IO.FS.writeFile (dir / "Nested" / "B.lean") "def"
    IO.FS.writeFile (dir / "ATest.lean") "test"
    IO.FS.writeFile (dir / "README.md") "notes"
    IO.FS.writeFile (dir / ".#A.lean") "editor lock"
    let rels := (← importerDirectorySources tmp).qsort (· < ·)
    unless rels == #["Compiler/SolidityImport/A.lean", "Compiler/SolidityImport/Nested/B.lean"] do
      throwError "unexpected directory sources {rels}"
    let hashes ← sha256Files (rels.map fun (rel : String) => tmp / rel)
    -- FIPS 180-2 test vector: SHA-256("abc").
    unless hashes[0]? == some "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad" do
      throwError "unexpected SHA-256 of \"abc\": {hashes}"
    -- The real environment's closure has no file under `tmp`, so only the
    -- directory files are inputs here.
    let before ← importerSourcesJson (← getEnv) tmp
    IO.FS.writeFile (dir / "Nested" / "B.lean") "deg"
    let after ← importerSourcesJson (← getEnv) tmp
    let entry (j : Json) (k : String) := (j.getObjValAs? String k).toOption
    let a := "Compiler/SolidityImport/A.lean"
    unless entry before a == entry after a && (entry before a).isSome do
      throwError "an unedited file's entry changed: {before.compress} / {after.compress}"
    unless entry before "Compiler/SolidityImport/Nested/B.lean" !=
        entry after "Compiler/SolidityImport/Nested/B.lean" do
      throwError "editing a file left the digest input unchanged: {after.compress}"

-- 4. `importSlice` frames `importerSourcesJson` as the digest's `importerSources`,
-- not a hand-written file list. Read from the source because `importSlice` is
-- private and needs solc.
run_meta do
  let text ← IO.FS.readFile ((← IO.currentDir) / "Compiler/SolidityImport/Import.lean")
  let has (needle : String) := (text.splitOn needle).length > 1
  unless has "let importerSources ← importerSourcesJson (← getEnv) sourceRoot" &&
      has "(\"importerSources\", importerSources)" do
    throwError "Import.lean no longer frames importerSourcesJson as importerSources"
  if has "moduleText sourceRoot" then
    throwError "Import.lean reads importer sources by hand again (moduleText)"

end Compiler.CompilationModel.SolidityImport.SourceDigestTest

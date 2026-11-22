import Compiler.SolidityImport.FoundryRemappings

/-!
Foundry's inferred remappings (`inferFoundryRemappings`) and the staged resolution
(`resolveImportStaged`: which stage, hence which library read, each import needs). Each layout's expected list is the `remappings` of `forge config --json`
(forge 1.5.0, commit 1c57854; what `forge build` gives solc) for the same files, minus the
written lines. `order dependent` gave a different value for `a/` when the same files were
listed in reverse order.
-/

namespace Compiler.CompilationModel.SolidityImport.FoundryRemappingsTest

open Compiler.CompilationModel.SolidityImport

/-- Insert a file at `path` (components) into `d`. -/
private partial def insertFile (d : RemapDir) : List String → String → RemapDir
  | [], _ => d
  | [file], content =>
    if file.endsWith ".sol" then { d with hasSol := true }
    else if file == "foundry.toml" then { d with foundryToml := some content }
    else if file == "remappings.txt" then { d with remappingsTxt := some content }
    else d
  | dir :: rest, content =>
    let child := (d.child? dir).getD { name := dir, hidden := dir.startsWith "." }
    let others := d.children.filter (·.name != dir)
    { d with children := (others.push (insertFile child rest content)).qsort (·.name < ·.name) }

/-- A project root holding `files` (path, content). -/
private def layout (files : List (String × String)) : RemapDir :=
  files.foldl (fun d (p, c) => insertFile d ((p.splitOn "/").filter (· != "")) c) { name := "" }

private def explicitOf (files : List (String × String)) : Array (String × String) :=
  match files.find? (·.1 == "remappings.txt") with
  | none => #[]
  | some (_, text) => (text.splitOn "\n").toArray.filterMap fun l =>
      match l.splitOn "=" with
      | [a, b] => some (a, b)
      | _ => none

private def infer (files : List (String × String)) : InferredRemappings :=
  inferFoundryRemappings (layout files) (explicitOf files)

private def lines (files : List (String × String)) : List String :=
  (infer files).remappings.toList.map fun r => s!"{r.name}={r.path}"

private def clean (files : List (String × String)) : Bool :=
  (infer files).globalIssue.isNone && (infer files).remappings.all (·.issue.isNone)

/-- Resolve `spec` imported from `origin` in a project tree with written remappings
`explicit`, every stage at hand: the target, the inferred entry used, and the deepest stage
needed (0: no library read, 1: library configurations, 2: full scan); `none` on an error. -/
private def resolveTree (d : RemapDir) (explicit : Array (String × String))
    (origin spec : String) : Option (String × Option String × Nat) :=
  (resolveImportStaged origin spec (remapStage0 d explicit) (remapConfigPool d)
    (inferFoundryRemappings d explicit)).toOption.map fun (t, r, n) => (t, r.map (·.name), n)

/-- The error `resolveTree` drops. -/
private def errorTree (d : RemapDir) (explicit : Array (String × String))
    (origin spec : String) : String :=
  match resolveImportStaged origin spec (remapStage0 d explicit) (remapConfigPool d)
      (inferFoundryRemappings d explicit) with
  | .error e => e
  | .ok _ => ""

/-- `resolveTree` in the project `files`, from `origin`. -/
private def resolveFrom (files : List (String × String)) (origin spec : String) :
    Option (String × Option String × Nat) :=
  resolveTree (layout files) (explicitOf files) origin spec

/-- The target and inferred entry of `name` imported from `src/E.sol` in `files`. -/
private def resolve (files : List (String × String)) (name : String) :
    Option (String × Option String) :=
  (resolveFrom files "src/E.sol" name).map fun (t, r, _) => (t, r)

/-- The stage `name`, imported from `src/E.sol` in `files`, needs. -/
private def stageOf (files : List (String × String)) (name : String) : Option Nat :=
  (resolveFrom files "src/E.sol" name).map (·.2.2)

private def errorOf (files : List (String × String)) (name : String) : String :=
  errorTree (layout files) (explicitOf files) "src/E.sol" name

-- Dapptools layout: `<dep>/` → `lib/<dep>/src/`, nested `lib/` opens a new window, `test/` is
-- not searched.
private def dapptools : List (String × String) :=
  [("lib/dep/src/A.sol", ""), ("lib/dep/lib/inner/src/B.sol", ""), ("lib/dep/test/T.sol", "")]
#guard lines dapptools == ["dep/=lib/dep/src/", "inner/=lib/dep/lib/inner/src/"]
#guard clean dapptools

-- Hardhat layout under `node_modules`: sibling packages unify to their scope.
#guard lines [("node_modules/@grp/a/contracts/X.sol", ""), ("node_modules/@grp/b/contracts/Y.sol", "")] ==
  ["@grp/=node_modules/@grp/"]

-- `auto_detect_remappings = false` turns inference off.
#guard lines [("foundry.toml", "[profile.default]\nauto_detect_remappings = false\n"),
  ("lib/dep/src/A.sol", "")] == []

-- Precedence: an inferred remapping whose name nests with an explicit one, either way, is
-- dropped; the others stay.
private def explicitSame : List (String × String) :=
  [("remappings.txt", "dep/=vendor/dep/\n"), ("lib/dep/src/A.sol", ""), ("lib/other/src/O.sol", "")]
#guard lines explicitSame == ["other/=lib/other/src/"]
#guard resolve explicitSame "dep/A.sol" == some ("vendor/dep/A.sol", none)
#guard resolve explicitSame "other/O.sol" == some ("lib/other/src/O.sol", some "other/")

private def explicitNested : List (String × String) :=
  [("remappings.txt", "dep/sub/=vendor/sub/\n"), ("lib/dep/src/A.sol", "")]
#guard lines explicitNested == []
#guard resolve explicitNested "dep/sub/X.sol" == some ("vendor/sub/X.sol", none)
-- Foundry has no `dep/` here, so the path stays as written.
#guard resolve explicitNested "dep/A.sol" == some ("dep/A.sol", none)

-- Longest prefix first, across explicit and inferred: `oz` (written without `/`) does not
-- nest with `ozx/`, so both stay and `ozx/` wins on `ozx/…`.
private def explicitNoSlash : List (String × String) :=
  [("remappings.txt", "oz=vendor/oz/\n"), ("lib/ozx/src/A.sol", "")]
#guard lines explicitNoSlash == ["ozx/=lib/ozx/src/"]
#guard resolve explicitNoSlash "ozx/A.sol" == some ("lib/ozx/src/A.sol", some "ozx/")

-- A library with its own `foundry.toml`: its `remappings.txt` is rebased onto it, its `src`
-- gets a remapping, and a nested remapping that nests with its parent's is dropped.
private def nestedConfig : List (String × String) :=
  [("lib/core/foundry.toml", "[profile.default]\n"),
   ("lib/core/remappings.txt", "@scope/=lib/scope-lib/\n"), ("lib/core/src/C.sol", ""),
   ("lib/core/lib/scope-lib/contracts/D.sol", ""),
   ("lib/core/lib/scope-lib/remappings.txt", "@scope/lib/=contracts/\n"),
   ("lib/core/lib/scope-lib/foundry.toml", "[profile.default]\nsrc = 'contracts'\n"),
   ("lib/tool/src/E.sol", "")]
#guard lines nestedConfig == ["@scope/=lib/core/lib/scope-lib/", "core/=lib/core/src/",
  "scope-lib/=lib/core/lib/scope-lib/contracts/", "tool/=lib/tool/src/"]
#guard clean nestedConfig

-- A consumer importing `@vendor/…` and `<dep>/…` through its dependencies' own configs
-- resolves with no change to its `remappings.txt`.
private def consumerShape : List (String × String) :=
  [("remappings.txt", "@scope/core/=lib/core/\n"), ("src/Manager.sol", ""),
   ("lib/core/foundry.toml", "[profile.default]\n"),
   ("lib/core/remappings.txt", "@vendor/=lib/vendor-lib/\nauth-lib/=lib/auth-lib/\n"),
   ("lib/core/src/Pool.sol", ""),
   ("lib/core/lib/vendor-lib/foundry.toml", "[profile.default]\nsrc = 'contracts'\n"),
   ("lib/core/lib/vendor-lib/remappings.txt", "@vendor/contracts/=contracts/\n"),
   ("lib/core/lib/vendor-lib/contracts/token/Token.sol", ""),
   ("lib/core/lib/auth-lib/src/Auth.sol", ""),
   ("lib/approvals/foundry.toml", "[profile.default]\n"), ("lib/approvals/src/Approve.sol", ""),
   ("lib/approvals/lib/auth-lib/src/Auth.sol", "")]
#guard lines consumerShape == ["@vendor/=lib/core/lib/vendor-lib/", "approvals/=lib/approvals/src/",
  "auth-lib/=lib/core/lib/auth-lib/", "core/=lib/core/src/",
  "vendor-lib/=lib/core/lib/vendor-lib/contracts/"]
#guard clean consumerShape
#guard resolve consumerShape "@vendor/contracts/token/Token.sol" ==
  some ("lib/core/lib/vendor-lib/contracts/token/Token.sol", some "@vendor/")
#guard resolve consumerShape "approvals/Approve.sol" ==
  some ("lib/approvals/src/Approve.sol", some "approvals/")
#guard resolve consumerShape "@scope/core/src/Pool.sol" == some ("lib/core/src/Pool.sol", none)

-- `forge build` protects the project's `src`, `test` and `script` names (ASCII case
-- ignored): a library's `src/=src/` is dropped, so `src/…` and relative imports stay in the
-- project. `forge remappings` still prints the dropped entry; `forge config` does not.
private def projectPathLib : List (String × String) :=
  [("src/E.sol", ""), ("src/B.sol", ""), ("lib/dep/foundry.toml", "[profile.default]\n"),
   ("lib/dep/remappings.txt", "src/=src/\n"), ("lib/dep/src/B.sol", "")]
#guard lines projectPathLib == ["dep/=lib/dep/src/"]
#guard resolve projectPathLib "src/B.sol" == some ("src/B.sol", none)
#guard (resolveFrom projectPathLib "src/E.sol" "./B.sol").map (·.1) == some "src/B.sol"
-- The same holds for written remappings.
#guard (infer [("src/E.sol", ""), ("remappings.txt", "src/=lib/dep/src/\nTest/=x/\n")]).explicit == #[]

-- `forge build` also drops a written remapping nested under an earlier written one.
private def nestedExplicit : List (String × String) :=
  [("src/E.sol", ""), ("remappings.txt", "@oz/=lib/oz/\n@oz/up/=lib/ozup/\n")]
#guard (infer nestedExplicit).explicit == #[("@oz/", "lib/oz/")]
#guard resolve nestedExplicit "@oz/up/X.sol" == some ("lib/oz/up/X.sol", none)

-- A hidden library directory is not scanned for sources, but its `foundry.toml` counts.
#guard lines [("lib/.cfg/foundry.toml", "[profile.default]\nremappings = ['dep/=foo/']\n"),
  ("lib/dep/src/A.sol", "")] == [".cfg/=lib/.cfg/src/", "dep/=lib/.cfg/foo/"]

-- A nested `foundry.toml` this reader cannot check: Foundry would skip that library's config,
-- so its remappings (context ones included) are unknown and every import is refused.
private def badToml : List (String × String) :=
  [("lib/core/foundry.toml", "[profile.default]\nthis is not toml\n"),
   ("lib/core/remappings.txt", "@oz/=lib/oz/\n"), ("lib/core/src/A.sol", "")]
#guard (infer badToml).globalIssue.isSome
#guard resolve badToml "@oz/T.sol" == none
#guard resolve badToml "src/A.sol" == none

-- Relative imports resolve first, then remap, as in solc (`./x` from `a/B.sol` is `a/x`).
private def relative (origin spec : String) (explicit : Array (String × String)) :
    Option String :=
  (resolveTree { name := "" } explicit origin spec).map (·.1)
#guard relative "a/B.sol" "./C.sol" #[("a/", "x/")] == some "x/C.sol"
#guard relative "a/b/B.sol" "../C.sol" #[] == some "a/C.sol"
#guard relative "a/B.sol" "../../C.sol" #[] == none

-- Order dependent: `lib/a/` and `lib/b/lib/a/src/` both claim `a/`, and each replaces the
-- other, so Foundry keeps whichever it lists last. The entry is kept (it still drops
-- conflicting names) but using it is an error.
private def orderDependent : List (String × String) :=
  [("lib/a/A.sol", ""), ("lib/b/lib/a/src/A.sol", "")]
#guard (infer orderDependent).remappings.toList.map (·.name) == ["a/"]
#guard (infer orderDependent).remappings.all (·.issue.isSome)
#guard resolve orderDependent "a/A.sol" == none
#guard (errorOf orderDependent "a/A.sol" |>.splitOn "depends on directory listing order").length > 1

-- Foundry's `last_nested_source_dir` can climb above the project root and stop at a
-- directory named `src` there: `forge remappings` printed `c/=<abs>/src/` for this layout
-- under `…/src/proj`, and `c/=lib/x/lib/` under a parent with no such name.
private def climb : List (String × String) := [("lib/x/src/X.sol", ""), ("lib/x/lib/c/k/C.sol", "")]
#guard lines climb == ["c/=lib/x/lib/", "x/=lib/x/src/"]
#guard clean climb
#guard (inferFoundryRemappings { layout climb with aboveRootSource := true } #[]).globalIssue.isSome

-- An ambiguous candidate feeding a later merge leaves the key set itself unknown: listed in
-- one order Foundry keeps `c/` and `@s/`, in the other only `@s/`.
#guard (infer [("lib/src/F.sol", ""), ("lib/src/node_modules/c/C.sol", ""),
  ("lib/src/node_modules/@s/x/S.sol", "")]).globalIssue.isSome

-- An entry with an issue may really win its slot, so the issue carries over to the winner.
-- Listed in one order Foundry printed `x/=lib/x/src/`, in the other `x/=lib/x/`.
#guard (infer [("lib/x/foundry.toml", "[profile.default]\n"), ("lib/x/a/c/contracts/F.sol", ""),
  ("lib/a/lib/x/c/src/F.sol", "")]).remappings.any fun r => r.name == "x/" && r.issue.isSome
-- An absolute target (an issue) competing with a clean auto-detected entry.
#guard (infer [("lib/n/foundry.toml", "[profile.default]\nremappings = [\"z/=/abs/zz/\"]\n"),
  ("lib/z/src/Z.sol", "")]).remappings.any fun r => r.name == "z/" && r.issue.isSome

-- A hidden directory in a library's `libs` is scanned by Foundry like any other (the readers
-- read it too).
#guard lines [("lib/x/foundry.toml", "[profile.default]\nlibs = ['.deps']\n"),
  ("lib/x/.deps/foo/src/F.sol", ""), ("lib/y/lib/foo/src/F.sol", "")] ==
  ["foo/=lib/x/.deps/foo/src/", "x/=lib/x/src/"]

-- A symlink in a scanned library leaves the names Foundry finds by scanning unknown, but
-- such a name is a single directory name (`<dir>/`). With an unrelated symlink under `lib/`
-- (`forge build` compiled `src/foo/Bar.sol` as written), a path whose first directory is
-- protected (`src`, `lib`, `contracts`, the project's `test`, `script`) still resolves after
-- reading only the library configurations; so does a written match ending in `/`, or a
-- written `E` without `/` when the path continues with `E/` (F3x: `forge build` compiled
-- `deps/oz/A.sol` for `oz=deps/oz`). A path such a name could reach is refused.
private def withSymlink : RemapDir :=
  let d := layout dapptools
  let lib := (d.child? "lib").get!
  { d with children := #[{ lib with hasSymlink := true }] }
#guard (inferFoundryRemappings withSymlink #[]).globalIssue.isSome
#guard resolveTree withSymlink #[("x/", "y/")] "src/E.sol" "src/foo/Bar.sol" ==
  some ("src/foo/Bar.sol", none, 1)
#guard resolveTree withSymlink #[("x/", "y/")] "src/E.sol" "./A.sol" == some ("src/A.sol", none, 1)
#guard resolveTree withSymlink #[("x/", "y/")] "src/E.sol" "x/A.sol" == some ("y/A.sol", none, 1)
#guard resolveTree withSymlink #[("oz", "deps/oz")] "src/E.sol" "oz/A.sol" ==
  some ("deps/oz/A.sol", none, 1)
#guard resolveTree withSymlink #[("x/", "y/")] "src/E.sol" "dep/A.sol" == none
#guard (errorTree withSymlink #[] "src/E.sol" "dep/A.sol" |>.splitOn "symlink in lib").length > 1
#guard resolveTree withSymlink #[("oz", "deps/oz/")] "src/E.sol" "ozx/A.sol" == none
-- The symlink itself can supply the name: with `lib/pkg` a symlink to a package, `forge build`
-- compiled `lib/pkg/src/P.sol` for `pkg/P.sol` although `pkg/P.sol` exists in the project.
-- Resolving as written would take another file, so the import is refused.
#guard resolveTree { layout [("src/E.sol", ""), ("pkg/P.sol", "")] with
    children := #[{ name := "lib", hasSymlink := true }, { name := "pkg", hasSol := true }] }
  #[] "src/E.sol" "pkg/P.sol" == none

-- A library's configuration can remap a path in the project's own `src/`: `forge build`
-- compiled `lib/dep/src/X.sol` for the project's `src/sub/X.sol` here.
private def configIntoSrc : List (String × String) :=
  [("src/E.sol", ""), ("src/sub/X.sol", ""), ("lib/dep/foundry.toml", "[profile.default]\n"),
   ("lib/dep/remappings.txt", "src/sub/=src/\n"), ("lib/dep/src/X.sol", "")]
#guard resolveFrom configIntoSrc "src/E.sol" "src/sub/X.sol" ==
  some ("lib/dep/src/X.sol", some "src/sub/", 2)

-- A context remapping in a library's configuration reaches solc verbatim and overrides a
-- written remapping for files under its context: `forge build` compiled `lib/dep/lib/alt/A.sol`
-- for `@oz/A.sol` in `src/E.sol` despite `@oz/=lib/oz/`. The importer refuses there, and
-- resolves the written remapping in files outside the context.
private def configContext : List (String × String) :=
  [("remappings.txt", "@oz/=lib/oz/\n"), ("src/E.sol", ""), ("lib/oz/A.sol", ""),
   ("lib/dep/foundry.toml", "[profile.default]\n"), ("lib/dep/remappings.txt", "src:@oz/=lib/alt/\n"),
   ("lib/dep/src/D.sol", ""), ("lib/dep/lib/alt/A.sol", "")]
#guard resolveFrom configContext "src/E.sol" "@oz/A.sol" == none
#guard (errorOf configContext "@oz/A.sol" |>.splitOn "context remapping src:@oz/").length > 1
#guard resolveFrom configContext "test/T.sol" "@oz/A.sol" == some ("lib/oz/A.sol", none, 1)
-- A written context remapping is refused the same way.
#guard resolveFrom [("remappings.txt", "src:@oz/=x/\n")] "src/E.sol" "@oz/A.sol" == none

-- Library reads happen only when a decision needs them. No library directory, or
-- `auto_detect_remappings = false`: nothing is read (`forge build` compiled the project's
-- `dep/V.sol` with inference off). Written remappings and protected paths: configurations only.
#guard stageOf [("remappings.txt", "x/=y/\n"), ("src/E.sol", "")] "x/A.sol" == some 0
#guard resolveFrom [("foundry.toml", "[profile.default]\nlibs = ['deps']\nauto_detect_remappings = false\n"),
  ("dep/V.sol", ""), ("deps/dep/src/V.sol", "")] "src/E.sol" "dep/V.sol" == some ("dep/V.sol", none, 0)
private def writtenOnly : List (String × String) :=
  [("remappings.txt", "dep/=lib/dep/src/\n"), ("src/E.sol", ""), ("src/B.sol", ""),
   ("lib/dep/src/D.sol", "")]
#guard stageOf writtenOnly "dep/D.sol" == some 1
#guard (resolveFrom writtenOnly "src/E.sol" "./B.sol").map (·.2.2) == some 1
#guard stageOf explicitSame "other/O.sol" == some 2
-- F1a: of two nested written remappings `forge build` keeps the first; it compiled
-- `deps/A/b/X.sol` for `a/b/X.sol`.
#guard resolveFrom [("remappings.txt", "a/=deps/A/\na/b/=deps/B/\n")] "src/E.sol" "a/b/X.sol" ==
  some ("deps/A/b/X.sol", none, 0)

-- Written names and targets reach solc with a trailing `/`, as `forge build` passes them:
-- `oz/=deps/oz` compiles `deps/oz/A.sol` (not `deps/ozA.sol`), and `oz=deps/oz/` does not
-- match `ozx/A.sol`.
#guard (remapStage0 { name := "" } #[("oz/", "deps/oz"), ("w", "x.sol")]).explicit ==
  #[("oz/", "deps/oz/"), ("w/", "x.sol")]
#guard resolveFrom [("remappings.txt", "oz/=deps/oz\n")] "src/E.sol" "oz/A.sol" ==
  some ("deps/oz/A.sol", none, 0)
#guard resolveFrom [("remappings.txt", "oz=deps/oz/\n")] "src/E.sol" "ozx/A.sol" ==
  some ("ozx/A.sol", none, 0)

-- A library's file remapping is never dropped for nesting, so it can beat a written match:
-- `forge build` compiled `lib/dep/alt/A.sol` for `oz/A.sol` despite `oz/=deps/oz/`. The written
-- shortcut does not apply, and the full scan refuses the file remapping.
private def configFileRemap : List (String × String) :=
  [("remappings.txt", "oz/=deps/oz/\n"), ("src/E.sol", ""), ("deps/oz/A.sol", ""),
   ("lib/dep/foundry.toml", "[profile.default]\n"), ("lib/dep/remappings.txt", "oz/A.sol=alt/A.sol\n"),
   ("lib/dep/alt/A.sol", ""), ("lib/dep/src/D.sol", "")]
#guard resolve configFileRemap "oz/A.sol" == none
#guard (errorOf configFileRemap "oz/A.sol" |>.splitOn "file remapping").length > 1
#guard resolve configFileRemap "oz/B.sol" == some ("deps/oz/B.sol", none)

-- A `libs` entry the importer does not read (outside the project, as a hoisted
-- `../../node_modules`): irrelevant with auto-detection off, refused when Foundry infers.
private def hoisted (auto : String) : List (String × String) :=
  [("foundry.toml", s!"[profile.default]\nlibs = [\"node_modules\", \"../../node_modules\"]\n{auto}"),
   ("remappings.txt", "@oz/=deps/oz/\n")]
#guard resolveFrom (hoisted "auto_detect_remappings = false\n") "src/E.sol" "@oz/A.sol" ==
  some ("deps/oz/A.sol", none, 0)
#guard resolveFrom (hoisted "") "src/E.sol" "@oz/A.sol" == none
#guard (errorTree (layout (hoisted "")) (explicitOf (hoisted "")) "src/E.sol" "@oz/A.sol"
  |>.splitOn "outside the project").length > 1

-- `foundry.toml` reading: only `[profile.default]` counts; other profiles are ignored; a
-- modeled key outside any profile, or an unreadable value, is an issue.
#guard (FoundryRemap.parseFoundryToml
  "[profile.default]\nsrc = \"contracts\" # c\nlibs = [\n  'lib',\n  \"node_modules\",\n]\n[profile.ci]\nsrc = 'x'\n").src ==
  some "contracts"
#guard (FoundryRemap.parseFoundryToml "[profile.default]\nlibs = [\n  'lib',\n  \"node_modules\",\n]\n").libs ==
  some ["lib", "node_modules"]
#guard (FoundryRemap.parseFoundryToml "src = 'x'\n").issue.isSome
#guard (FoundryRemap.parseFoundryToml "[profile.default]\nremappings = [x]\n").issue.isSome
-- Other keys pass when they are well-formed TOML lines, including multi-line inline tables.
#guard (FoundryRemap.parseFoundryToml
  "[profile.default]\nfs_permissions = [\n  { access = \"read\", path = \"./a\" },\n]\nruns = 10_000\n[fuzz]\nseed = '0x1'\n").issue.isNone
-- Multi-line strings are skipped; an unterminated one is an issue.
#guard (FoundryRemap.parseFoundryToml "[profile.default]\nkey = \"\"\"\nx = [\n\"\"\"\nsrc = 'c'\n").src ==
  some "c"
#guard (FoundryRemap.parseFoundryToml "[profile.default]\nkey = \"\"\"\nx\n").issue.isSome
-- Keys are matched as Foundry reads them: snake case, dotted paths into `profile.default`.
#guard (FoundryRemap.parseFoundryToml "[profile.default]\nLibs = ['deps']\n").libs == some ["deps"]
#guard (FoundryRemap.parseFoundryToml "profile.default.libs = ['deps']\n").libs == some ["deps"]
#guard (FoundryRemap.parseFoundryToml "[profile]\ndefault.src = 'x'\n").src == some "x"
#guard (FoundryRemap.parseFoundryToml "[profile.default]\nauto-detect-remappings = false\n").autoDetect ==
  some false
#guard (FoundryRemap.parseFoundryToml "[profile.default]\nautoDetectRemappings = false\n").autoDetect ==
  some false
#guard (FoundryRemap.parseFoundryToml "[default]\nlibs = ['deps']\n").libs == some ["deps"]
#guard (FoundryRemap.parseFoundryToml "[other]\nlibs = ['deps']\n").issue.isSome
#guard (FoundryRemap.parseFoundryToml "[profile.ci]\nlibs = ['deps']\n").issue.isNone
-- `extends` and inline tables holding the default profile could set these keys elsewhere.
#guard (FoundryRemap.parseFoundryToml "[profile.default]\nextends = 'base.toml'\n").issue.isSome
#guard (FoundryRemap.parseFoundryToml "[profile]\ndefault = { src = 'contracts' }\n").issue.isSome
#guard (FoundryRemap.parseFoundryToml "profile = { default = { libs = ['deps'] } }\n" (strict := false)).issue.isSome
#guard (FoundryRemap.parseFoundryToml "[profile.ci]\nextends = 'base.toml'\n").issue.isNone
-- The project's own `foundry.toml` is read leniently: Foundry could not build the project at
-- all if it rejected the file, so a line this reader does not check is no issue there.
#guard (FoundryRemap.parseFoundryToml "[profile.default]\nnot toml\n" (strict := false)).issue.isNone
#guard (inferFoundryRemappings (layout [("foundry.toml", "[profile.default]\nnot toml\n"),
  ("src/A.sol", "")]) #[]).globalIssue.isNone

end Compiler.CompilationModel.SolidityImport.FoundryRemappingsTest

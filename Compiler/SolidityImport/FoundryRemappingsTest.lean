import Compiler.SolidityImport.FoundryRemappings

/-!
Foundry's inferred remappings (`inferFoundryRemappings`) and the resolution order
(`remapImportPath`). Each layout's expected list is what `forge remappings` (forge 1.5.0,
commit 1c57854) printed for the same files, minus the explicit lines. `order dependent`
printed a different value for `a/` when the same files were listed in reverse order.
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
    let child := (d.child? dir).getD { name := dir }
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

/-- Resolve `name` against `explicit` and `inferred`: the target and the inferred entry
used, or `none` on an error. -/
private def resolveWith (explicit : Array (String × String)) (inferred : InferredRemappings)
    (name : String) : Option (String × Option String) :=
  (remapImportPath name explicit inferred).toOption.map fun (t, r) => (t, r.map (·.name))

/-- Resolve `name` in the project `files`. -/
private def resolve (files : List (String × String)) (name : String) :
    Option (String × Option String) :=
  resolveWith (explicitOf files) (infer files) name

private def errorOf (files : List (String × String)) (name : String) : String :=
  match remapImportPath name (explicitOf files) (infer files) with
  | .error e => e
  | .ok _ => ""

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
#guard resolve explicitNoSlash "oz/B.sol" == some ("vendor/oz//B.sol", none)

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

-- The shape of #2835 (a periphery project importing `@openzeppelin/…` and `<dep>/src/…`
-- through its dependencies' configs) resolves with no change to `remappings.txt`.
private def peripheryShape : List (String × String) :=
  [("remappings.txt", "@uniswap/core/=lib/core/\n"), ("src/Manager.sol", ""),
   ("lib/core/foundry.toml", "[profile.default]\n"),
   ("lib/core/remappings.txt", "@openzeppelin/=lib/openzeppelin-contracts/\nsolmate/=lib/solmate/\n"),
   ("lib/core/src/Pool.sol", ""),
   ("lib/core/lib/openzeppelin-contracts/foundry.toml", "[profile.default]\nsrc = 'contracts'\n"),
   ("lib/core/lib/openzeppelin-contracts/remappings.txt", "@openzeppelin/contracts/=contracts/\n"),
   ("lib/core/lib/openzeppelin-contracts/contracts/token/Token.sol", ""),
   ("lib/core/lib/solmate/src/Auth.sol", ""),
   ("lib/permit/foundry.toml", "[profile.default]\n"), ("lib/permit/src/Permit.sol", ""),
   ("lib/permit/lib/solmate/src/Auth.sol", "")]
#guard lines peripheryShape == ["@openzeppelin/=lib/core/lib/openzeppelin-contracts/",
  "core/=lib/core/src/", "openzeppelin-contracts/=lib/core/lib/openzeppelin-contracts/contracts/",
  "permit/=lib/permit/src/", "solmate/=lib/core/lib/solmate/"]
#guard clean peripheryShape
#guard resolve peripheryShape "@openzeppelin/contracts/token/Token.sol" ==
  some ("lib/core/lib/openzeppelin-contracts/contracts/token/Token.sol", some "@openzeppelin/")
#guard resolve peripheryShape "permit/Permit.sol" == some ("lib/permit/src/Permit.sol", some "permit/")
#guard resolve peripheryShape "@uniswap/core/src/Pool.sol" == some ("lib/core/src/Pool.sol", none)

-- Order dependent: `lib/a/` and `lib/b/lib/a/src/` both claim `a/`, and each replaces the
-- other, so Foundry keeps whichever it lists last. The entry is kept (it still drops
-- conflicting names) but using it is an error.
private def orderDependent : List (String × String) :=
  [("lib/a/A.sol", ""), ("lib/b/lib/a/src/A.sol", "")]
#guard (infer orderDependent).remappings.toList.map (·.name) == ["a/"]
#guard (infer orderDependent).remappings.all (·.issue.isSome)
#guard resolve orderDependent "a/A.sol" == none
#guard (errorOf orderDependent "a/A.sol" |>.splitOn "depends on directory listing order").length > 1

-- A symlink anywhere in a scanned library leaves the inferred set unknown: an import that
-- needs an inferred remapping fails, explicit and plain paths resolve as before.
private def withSymlink : InferredRemappings :=
  let d := layout dapptools
  let lib := (d.child? "lib").get!
  inferFoundryRemappings { d with children := #[{ lib with hasSymlink := true }] } #[("x/", "y/")]
#guard withSymlink.globalIssue.isSome
#guard resolveWith #[("x/", "y/")] withSymlink "dep/A.sol" == none
#guard match remapImportPath "dep/A.sol" #[("x/", "y/")] withSymlink with
  | .error e => (e.splitOn "symlink in lib").length > 1
  | .ok _ => false
#guard resolveWith #[("x/", "y/")] withSymlink "x/A.sol" == some ("y/A.sol", none)
#guard resolveWith #[("x/", "y/")] withSymlink "src/A.sol" == some ("src/A.sol", none)

-- `foundry.toml` reading: only `[profile.default]` counts; other profiles are ignored; a
-- modeled key outside any profile, or an unreadable value, is an issue.
#guard (FoundryRemap.parseFoundryToml
  "[profile.default]\nsrc = \"contracts\" # c\nlibs = [\n  'lib',\n  \"node_modules\",\n]\n[profile.ci]\nsrc = 'x'\n").src ==
  some "contracts"
#guard (FoundryRemap.parseFoundryToml "[profile.default]\nlibs = [\n  'lib',\n  \"node_modules\",\n]\n").libs ==
  some ["lib", "node_modules"]
#guard (FoundryRemap.parseFoundryToml "src = 'x'\n").issue.isSome
#guard (FoundryRemap.parseFoundryToml "[profile.default]\nremappings = [x]\n").issue.isSome

end Compiler.CompilationModel.SolidityImport.FoundryRemappingsTest

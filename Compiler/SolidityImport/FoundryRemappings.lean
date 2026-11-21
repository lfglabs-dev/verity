/-!
Foundry's inferred remappings (forge 1.5.0: `foundry-config` `RemappingsProvider` and
`foundry-compilers` 0.19.6 `Remapping::find_many`).

When a project writes no remapping for a library, Foundry derives one from the directories
under its `libs` (`lib/` by default) and from the `remappings.txt` / `foundry.toml` of every
library that has its own `foundry.toml`, recursively. This module ports those rules over an
in-memory directory tree (`RemapDir`), so the rules are testable without a file system, plus
one IO function that reads the tree. Nothing is executed and nothing is fetched.

Foundry's own result depends on directory listing order in a few places (parallel scans whose
first hit wins). Each such place is computed for every order: an entry whose value can differ
is marked ambiguous. A layout this port does not model (a symlink, a context remapping, a
`foundry.toml` value it cannot read) sets `globalIssue`. The importer refuses to use an
ambiguous entry, and refuses any inferred resolution while `globalIssue` is set.
-/

namespace Compiler.CompilationModel.SolidityImport

/-- A directory, as far as Foundry's remapping rules look at it. Children are the
non-hidden subdirectories, sorted by name. -/
structure RemapDir where
  name : String
  /-- A hidden directory. Only kept when it holds a `foundry.toml`: Foundry's library scan
  skips hidden entries, but its search for nested configs does not. -/
  hidden : Bool := false
  /-- A non-hidden `*.sol` file lies directly in this directory. -/
  hasSol : Bool := false
  /-- Some non-hidden entry directly in this directory is a symlink (not followed). -/
  hasSymlink : Bool := false
  /-- The directory could not be listed. -/
  unreadable : Bool := false
  foundryToml : Option String := none
  remappingsTxt : Option String := none
  children : Array RemapDir := #[]
  /-- On the project root: some directory on its absolute path (itself included) is named
  `src` or `contracts`, where Foundry's `last_nested_source_dir` climb can stop. -/
  aboveRootSource : Bool := false
  deriving Inhabited, Repr

/-- A remapping Foundry would add on its own, relative to the project root. -/
structure InferredRemapping where
  name : String
  /-- Target, relative to the project root, ending in `/`. -/
  path : String
  /-- Why the importer must not use this entry (ambiguous order, absolute path, …). -/
  issue : Option String := none
  deriving Inhabited, Repr, BEq

/-- Foundry's inferred remappings for a project, in Foundry's order. -/
structure InferredRemappings where
  remappings : Array InferredRemapping := #[]
  /-- Set when the layout leaves Foundry's inferred set itself unknown. -/
  globalIssue : Option String := none
  deriving Inhabited, Repr

/-- The child directory named `name`. -/
def RemapDir.child? (d : RemapDir) (name : String) : Option RemapDir :=
  d.children.find? (·.name == name)

namespace FoundryRemap

/-- An absolute path, as components below the project root. -/
abbrev Path := List String

/-- The last component of a path (Rust `Path::file_name`). -/
def lastName (p : Path) : Option String := p.getLast?

/-- `is_source_dir`: the directory is named `src` or `contracts`. -/
def isSourceDir (p : Path) : Bool := lastName p == some "src" || lastName p == some "contracts"
/-- `is_lib_dir`: the directory is named `lib` or `node_modules`. -/
def isLibDir (p : Path) : Bool := lastName p == some "lib" || lastName p == some "node_modules"
/-- Rust `path.ends_with("src")`. -/
def endsWithSrc (p : Path) : Bool := lastName p == some "src"
/-- `no_recurse`: directories the candidate search does not enter. -/
def noRecurse (name : String) : Bool := name == "tests" || name == "test" || name == "demo"

/-- Rust `Path::ends_with` against `contracts` or `contracts/src`. -/
def endsWithJsSource (p : Path) : Bool :=
  lastName p == some "contracts" ||
    (p.length ≥ 2 && p.drop (p.length - 2) == ["contracts", "src"])

/-- `dir_distance(root, current)`. -/
def dirDistance (root current : Path) : Nat :=
  if root == current then 0
  else if root.isPrefixOf current then current.length - root.length else 0

/-- `next_nested_window(root, current)`: inside a `lib` window, the dependency directory. -/
def nextNestedWindow (root current : Path) : Path :=
  if !isLibDir root || root == current then root
  else if root.isPrefixOf current && current.length > root.length then
    root ++ [current[root.length]!]
  else root

/-- `last_nested_source_dir(root, dir)`, and whether the climb left the project: Foundry then
continues through the project root's absolute ancestors (the project root first), stopping at
one named `src` or `contracts`, and returns `root` only if none is. -/
def lastNestedSourceDir (root dir : Path) : Path × Bool := Id.run do
  if isSourceDir dir then return (dir, false)
  let mut p := dir
  while !p.isEmpty do
    let parent := p.dropLast
    if parent == root then return (root, false)
    if isSourceDir parent then return (parent, false)
    p := parent
  return (root, true)

/-- A remapping candidate of `find_remapping_candidates`. -/
structure Candidate where
  windowStart : Path
  sourceDir : Path
  level : Nat
  ambiguous : Bool := false
  deriving Inhabited, Repr, BEq

/-- `Candidate::merge_on_same_level`. Also returns whether the outcome is uncertain: the
single-`src` test reads every candidate's `sourceDir`, and an ambiguous one's real value may
differ, which can drop or keep whole candidates (keys). -/
def mergeOnSameLevel (cands : List Candidate) (current : Path) (level : Nat)
    (windowStart : Path) (insideNodeModules : Bool) : List Candidate × Bool :=
  let uncertain := cands.any (·.ambiguous)
  match cands.filter (endsWithSrc ·.sourceDir) with
  | [c] => ([c], uncertain)
  | _ =>
    let kept := cands.filter (·.level != level)
    let sourceDir := if insideNodeModules then windowStart else current
    if level > 0 && sourceDir == windowStart && (isSourceDir sourceDir || isLibDir sourceDir) then
      (kept, uncertain)
    else
      (kept ++ [{ windowStart, sourceDir, level }], uncertain)

/-- The `else` branch of `find_remapping_candidates`: Foundry adjusts the *first* candidate
of the current level, in directory listing order. With one such candidate that is exact.
With several, every candidate the adjustment would change is marked ambiguous. Also returns
whether an adjustment climbs above the project root while a directory there could stop it
(`aboveRootSource`): its value is then outside the project. -/
def adjustSingleNested (cands : List Candidate) (open_ windowStart : Path) (level : Nat)
    (aboveRootSource : Bool) : List Candidate × Bool :=
  let adjust (c : Candidate) : Candidate × Bool :=
    if dirDistance c.windowStart c.sourceDir > 1 && endsWithJsSource c.sourceDir then
      ({ c with sourceDir := windowStart }, false)
    else if !isSourceDir c.sourceDir && c.sourceDir != c.windowStart then
      let (p, escaped) := lastNestedSourceDir open_ c.sourceDir
      ({ c with sourceDir := p }, escaped)
    else (c, false)
  let atLevel := cands.filter (·.level == level)
  let escapes := aboveRootSource && atLevel.any (adjust · |>.2)
  if atLevel.length == 1 then
    (cands.map fun c => if c.level == level then (adjust c).1 else c, escapes)
  else
    (cands.map fun c =>
      if c.level == level && (adjust c).1 != c then { c with ambiguous := true } else c, escapes)

/-- `find_remapping_candidates`, and whether its outcome is uncertain (see
`mergeOnSameLevel`, `adjustSingleNested`). Symlinks never reach here: they set the global
issue. -/
partial def findCandidates (d : RemapDir) (current open_ : Path) (level : Nat)
    (insideNodeModules aboveRootSource : Bool) : List Candidate × Bool :=
  let search := d.children.toList.filter fun c => !c.hidden && !noRecurse c.name
  let subs := search.map fun c =>
    let sub := current ++ [c.name]
    if isLibDir sub then findCandidates c sub sub (level + 1) insideNodeModules aboveRootSource
    else findCandidates c sub open_ level insideNodeModules aboveRootSource
  let cands := subs.flatMap (·.1)
  let uncertain := subs.any (·.2)
  let windowStart := nextNestedWindow open_ current
  let sameWindow := cands.filter fun c => c.level == level && c.windowStart == windowStart
  let (out, u) := if d.hasSol || sameWindow.length > 1 then
      mergeOnSameLevel cands current level windowStart insideNodeModules
    else
      adjustSingleNested cands open_ windowStart level aboveRootSource
  (out, uncertain || u)

/-- Among values inserted in an unknown order into one map slot, where `replace old new`
decides whether `new` overwrites `old`: the value that wins in every order, or an
arbitrary one marked ambiguous. -/
def orderIndependentWinner {α : Type} [BEq α] (replace : α → α → Bool) (xs : List α) :
    Option (α × Bool) :=
  let uniq := xs.eraseDups
  match uniq with
  | [] => none
  | first :: _ =>
    match uniq.find? fun d => uniq.all fun e => e == d || (!replace d e && replace e d) with
    | some d => some (d, false)
    | none => some (first, true)

/-- `Remapping::find_many` over the library directory `lib` (at `libPath`): the keys with
their value and whether it is ambiguous, and whether the key set itself is uncertain. -/
def findMany (lib : RemapDir) (libPath : Path) (aboveRootSource : Bool) :
    List (String × Path × Bool) × Bool :=
  let insideNodeModules := lastName libPath == some "node_modules"
  let subs := (lib.children.toList.filter (!·.hidden)).map fun c =>
    let p := libPath ++ [c.name]
    findCandidates c p p 0 insideNodeModules aboveRootSource
  let cands := subs.flatMap (·.1)
  let keyOf (c : Candidate) := (lastName c.windowStart).map (· ++ "/")
  let keys := (cands.filterMap keyOf).eraseDups.toArray.qsort (· < ·)
  let replace (old new : Path) : Bool :=
    old.length > new.length || (endsWithSrc new && !endsWithSrc old)
  (keys.toList.filterMap fun k =>
    let group := cands.filter (keyOf · == some k)
    let ambiguousInput := group.any (·.ambiguous)
    (orderIndependentWinner replace (group.map (·.sourceDir))).map fun (p, amb) =>
      (k, p, amb || ambiguousInput), subs.any (·.2))

/-! ### Remapping strings and `foundry.toml` -/

/-- A remapping inside Foundry's provider: `context:name=path`, `path` absolute
(components below the project root) once rebased. -/
structure Remap where
  context : Option String
  name : String
  /-- Absolute target, as components below the project root. -/
  path : Path
  /-- Whether the written target ended in `/` (Foundry keeps file remappings as written). -/
  pathText : String
  issue : Option String := none
  /-- Added by inference (library scan or nested config), not written by the user. -/
  lib : Bool := false
  deriving Inhabited, Repr, BEq

/-- The issue of an entry whose value depends on directory listing order. -/
def orderIssue (name : String) : Option String :=
  some s!"Foundry's value for {name} depends on directory listing order"

/-- Rust `Path::components().count()` for a path built by joining relative pieces:
`.` components vanish, everything else counts. -/
def componentCount (p : Path) : Nat := (p.filter (· != ".")).length

/-- `Remapping::from_str`: `none` on a line Foundry rejects. -/
def parseRemapping (s : String) : Option (Option String × String × String) :=
  match s.splitOn "=" with
  | [] | [_] => none
  | lhs :: rest =>
    let rhs := String.intercalate "=" rest
    let (ctx, name) := match lhs.splitOn ":" with
      | [n] => (none, n)
      | c :: ns => (if c.trimAscii.toString.isEmpty then none else some c, String.intercalate ":" ns)
      | [] => (none, lhs)
    if name.trimAscii.toString.isEmpty || rhs.trimAscii.toString.isEmpty then none
    else some (ctx, name, rhs)

/-- `needs_trailing_slash`. -/
def needsTrailingSlash (s : String) : Bool := !s.endsWith "/" && !s.endsWith ".sol"

/-- Append `/` unless the name or path already ends in `/` or `.sol`. -/
def withSlash (s : String) : String := if needsTrailingSlash s then s ++ "/" else s

/-- Rebase a written target onto `root`, as `RelativeRemappingPathBuf::relative` does,
noting the targets this port refuses to use. -/
def rebase (root : Path) (target : String) : Path × Option String :=
  let parts := (target.splitOn "/").filter (· != "")
  if target.startsWith "/" then
    (parts, some s!"absolute remapping target {target}")
  else if parts.any (fun p => p == "." || p == "..") then
    (root ++ parts, some s!"remapping target {target} has a . or .. component")
  else (root ++ parts, none)

/-- Parse a written remapping and rebase its target onto `root`. -/
def remapOfText (root : Path) (text : String) : Option Remap :=
  (parseRemapping text).map fun (ctx, name, rhs) =>
    let (path, issue) := rebase root rhs
    let issue := if name.endsWith ".sol" then some s!"file remapping {text}" else issue
    { context := ctx, name, path, pathText := rhs, issue }

/-- `remappings_from_newline`: every non-blank line must parse, or the config fails. -/
def parseRemappingsTxt (root : Path) (text : String) : Option (List Remap) :=
  (text.splitOn "\n").map (·.trimAscii.toString) |>.filter (!·.isEmpty) |>.mapM (remapOfText root)

/-- Quoted strings of a TOML array body. -/
def quotedStrings (s : String) : Option (List String) := Id.run do
  let mut out : Array String := #[]
  let mut inQuote : Option Char := none
  let mut cur := ""
  for c in s.toList do
    match inQuote with
    | none =>
      if c == '"' || c == '\'' then
        inQuote := some c
        cur := ""
      else if !(c.isWhitespace || c == ',' || c == '[' || c == ']') then
        return none
    | some q =>
      if c == q then
        out := out.push cur
        inQuote := none
      else cur := cur.push c
  if inQuote.isSome then return none
  return some out.toList

/-- The `[profile.default]` keys that steer remapping inference. -/
structure TomlKeys where
  remappings : Option (List String) := none
  src : Option String := none
  libs : Option (List String) := none
  autoDetect : Option Bool := none
  issue : Option String := none
  deriving Inhabited, Repr

/-- Strip a `#` comment that is not inside a quoted string. -/
def stripComment (line : String) : String := Id.run do
  let mut out := ""
  let mut inQuote : Option Char := none
  for c in line.toList do
    match inQuote with
    | none =>
      if c == '#' then return out
      if c == '"' || c == '\'' then inQuote := some c
      out := out.push c
    | some q =>
      if c == q then inQuote := none
      out := out.push c
  return out

/-- The `foundry.toml` keys that steer remapping inference. -/
def modeledKeys : List String := ["remappings", "src", "libs", "auto_detect_remappings"]

/-- Net `[`/`{` nesting a TOML line opens, outside quoted strings. -/
def bracketDepth (s : String) : Int := Id.run do
  let mut depth : Int := 0
  let mut inQuote : Option Char := none
  for c in s.toList do
    match inQuote with
    | none =>
      if c == '"' || c == '\'' then inQuote := some c
      else if c == '[' || c == '{' then depth := depth + 1
      else if c == ']' || c == '}' then depth := depth - 1
    | some q => if c == q then inQuote := none
  return depth

/-- A bare or quoted TOML key, possibly dotted. -/
def isTomlKey (k : String) : Bool :=
  !k.isEmpty && (k.startsWith "\"" || k.startsWith "'" ||
    k.all fun c => c.isAlphanum || c == '_' || c == '-' || c == '.')

/-- The parts of a dotted TOML key or table name, quotes removed. -/
def tomlKeyParts (k : String) : List String := Id.run do
  let mut out : Array String := #[]
  let mut cur := ""
  let mut inQuote : Option Char := none
  for c in k.toList do
    match inQuote with
    | none =>
      if c == '"' || c == '\'' then inQuote := some c
      else if c == '.' then
        out := out.push cur.trimAscii.toString
        cur := ""
      else cur := cur.push c
    | some q => if c == q then inQuote := none else cur := cur.push c
  return (out.push cur.trimAscii.toString).toList

/-- Foundry's `ForcedSnakeCaseData`: `autoDetectRemappings`, `auto-detect-remappings` and
`Libs` name the keys `auto_detect_remappings` and `libs`. -/
def snakeCase (k : String) : String := Id.run do
  let mut out := ""
  let mut prevLowerOrDigit := false
  for c in k.toList do
    if c.isUpper then
      if prevLowerOrDigit then out := out.push '_'
      out := out.push c.toLower
      prevLowerOrDigit := false
    else if c == '-' then
      out := out.push '_'
      prevLowerOrDigit := false
    else
      out := out.push c
      prevLowerOrDigit := c.isLower || c.isDigit
  return out

/-- Record one `key = value` under table `sect` (its parts), when the full key path ends in
a key that steers inference. `profile.default.<key>` is read; `profile.<other>.<key>` is
another profile; a deeper path is a subtable. Any other place for such a key (top level,
`[default]`, …) is an issue, and so are `extends` and an inline table holding the default
profile, which could set such a key where this reader does not look. -/
def TomlKeys.record (keys : TomlKeys) (sect : List String) (key value : String) : TomlKeys :=
  let path := (sect ++ tomlKeyParts key).map snakeCase
  -- forge 1.5.0 still reads the deprecated `[default]` table as the default profile.
  let path := if path.head? == some "default" then "profile" :: path else path
  match path.getLast? with
  | none => keys
  | some leaf =>
    -- `profile = { default = { … } }` and `[profile] default = { … }` set modeled keys
    -- through an inline table; `extends` pulls them from another file. Neither is read here.
    if path == ["profile"] || path == ["profile", "default"] then
      { keys with issue := some s!"foundry.toml sets {String.intercalate "." path} as a value" }
    else if leaf == "extends" && path.length ≤ 3 &&
        !(path.length == 3 && path.head? == some "profile" && path[1]? != some "default") then
      { keys with issue := some "foundry.toml extends another file" }
    else if !modeledKeys.contains leaf then keys
    else if path.length > 3 then keys
    else if path.length == 3 && path.head? == some "profile" then
      if path[1]? != some "default" then keys
      else if leaf == "src" then
        match quotedStrings value with
        | some [v] => { keys with src := some v }
        | _ => { keys with issue := some "cannot read foundry.toml key src" }
      else if leaf == "auto_detect_remappings" then
        if value == "true" then { keys with autoDetect := some true }
        else if value == "false" then { keys with autoDetect := some false }
        else { keys with issue := some "cannot read foundry.toml key auto_detect_remappings" }
      else
        match quotedStrings value with
        | none => { keys with issue := some s!"cannot read foundry.toml key {leaf}" }
        | some xs => if leaf == "remappings" then { keys with remappings := some xs }
          else { keys with libs := some xs }
    else { keys with issue := some s!"foundry.toml sets {leaf} outside [profile.default]" }

/-- Read the modeled keys of `[profile.default]`. A modeled key this reader cannot place, or
whose value it cannot read, is an issue. With `strict` (a library's `foundry.toml`), so is a
line that is not a table header, a `key = value`, or the continuation of a bracketed value
or multi-line string: Foundry would fail to load such a file and skip the library's
remappings, which this reader cannot rule out. -/
def parseFoundryToml (text : String) (strict : Bool := true) : TomlKeys := Id.run do
  let mut keys : TomlKeys := {}
  let mut sect : List String := []
  -- An open value: key, text so far, bracket depth, and the closing delimiter of an open
  -- multi-line string.
  let mut pending : Option (String × String × Int × Option String) := none
  let mut lineNo := 0
  for raw in text.splitOn "\n" do
    lineNo := lineNo + 1
    if let some (key, buf, depth, closer) := pending then
      if let some q := closer then
        if (raw.splitOn q).length > 1 then
          pending := none
          keys := keys.record sect key (buf ++ " " ++ raw)
        else pending := some (key, buf ++ " " ++ raw, depth, closer)
        continue
      let line := (stripComment raw).trimAscii.toString
      let buf := buf ++ " " ++ line
      let depth := depth + bracketDepth line
      if depth > 0 then
        pending := some (key, buf, depth, none)
      else
        pending := none
        keys := keys.record sect key buf
      continue
    let line := (stripComment raw).trimAscii.toString
    if line.isEmpty then continue
    if line.startsWith "[" then
      if strict && !line.endsWith "]" then
        keys := { keys with issue := some s!"foundry.toml line {lineNo} is not a table header" }
      sect := tomlKeyParts ((line.dropWhile (· == '[')).takeWhile (· != ']')).toString
      continue
    let parts := line.splitOn "="
    let key := (parts.headD "").trimAscii.toString
    let value := (String.intercalate "=" (parts.drop 1)).trimAscii.toString
    if parts.length < 2 || !isTomlKey key || value.isEmpty then
      if strict then
        keys := { keys with issue := some s!"foundry.toml line {lineNo} is not TOML this reader checks" }
      continue
    let tripleQuote := ["\"\"\"", "'''"].find? (value.startsWith ·)
    if let some q := tripleQuote then
      -- A multi-line string ends at the next occurrence of its delimiter.
      if ((value.drop 3).toString.splitOn q).length > 1 then keys := keys.record sect key value
      else pending := some (key, value, 0, some q)
      continue
    let depth := bracketDepth value
    if depth > 0 then pending := some (key, value, depth, none)
    else keys := keys.record sect key value
  if pending.isSome && strict then
    keys := { keys with issue := some "unterminated value in foundry.toml" }
  return keys

/-! ### The provider -/

/-- `Remappings::push`: a library remapping is dropped when its name nests with an earlier
remapping of the same context, in either direction. -/
def pushFiltered (existing : Array Remap) (r : Remap) : Array Remap :=
  if r.name.endsWith ".sol" && !r.pathText.endsWith ".sol" then existing
  else if existing.any (fun e =>
      e.context == r.context &&
        (if r.name.endsWith ".sol" then e.name == r.name && e.path == r.path
         else
           let en := if e.name.endsWith "/" then e.name else e.name ++ "/"
           r.name.startsWith en || e.name.startsWith r.name)) then existing
  else existing.push r

/-- `Remappings::into_inner`: the first remapping of each `context ++ name` wins. -/
def dedupByKey (rs : Array Remap) : Array Remap := Id.run do
  let mut seen : Array String := #[]
  let mut out : Array Remap := #[]
  for r in rs do
    let k := r.context.getD "" ++ r.name
    unless seen.contains k do
      seen := seen.push k
      out := out.push r
  return out

/-- A library remapping inside `insert_closest`, tagged with where it came from. -/
structure LibEntry where
  remap : Remap
  /-- `some i`: from the `i`-th nested `foundry.toml` directory (listing order unknown);
  `none`: auto-detected (sequence order known). -/
  nestedDir : Option Nat
  deriving Inhabited

/-- `insert_closest` for one `(context, name)` slot. Nested entries come first in an unknown
directory order; within one directory, and among auto-detected entries, order is known.
The fewest components win; on a tie the first inserted stays. -/
def insertClosest (entries : List LibEntry) : Option LibEntry := do
  let first ← entries.head?
  let best := entries.foldl (fun m e => min m (componentCount e.remap.path))
    (componentCount first.remap.path)
  let atMin := entries.filter (componentCount ·.remap.path == best)
  let nestedAtMin := atMin.filter (·.nestedDir.isSome)
  if nestedAtMin.isEmpty then
    atMin.head?
  else
    let dirs := (nestedAtMin.filterMap (·.nestedDir)).eraseDups
    let firsts := dirs.filterMap fun i => nestedAtMin.find? (·.nestedDir == some i)
    let pick ← firsts.head?
    let paths := (firsts.map (·.remap.path)).eraseDups
    let issues := (firsts.map (·.remap.issue)).eraseDups
    if paths.length > 1 || issues.length > 1 then
      return { pick with remap := { pick.remap with issue := orderIssue pick.remap.name } }
    return pick

/-- The output of the remappings provider for one project root. -/
structure Provided where
  remaps : Array Remap
  globalIssue : Option String := none
  deriving Inhabited

/-- The first of two issues. -/
def mergeIssue (a b : Option String) : Option String := a <|> b

/-- Library directories from `libs`, or Foundry's default (`DappHardhatDirProvider`). -/
def libsOf (d : RemapDir) (keys : TomlKeys) : List String × Option String :=
  match keys.libs with
  | some ls =>
    if ls.any (fun l => l.startsWith "/" || ((l.splitOn "/").filter (· != "")).length != 1) then
      (ls, some s!"unsupported libs entry in {ls}")
    else (ls.map fun l => ((l.splitOn "/").filter (· != "")).headD l, none)
  | none =>
    if (d.child? "node_modules").isSome then
      ((if (d.child? "lib").isSome then ["lib"] else []) ++ ["node_modules"], none)
    else (["lib"], none)

/-- Symlinks or unreadable directories anywhere below `d`. -/
partial def treeIssue (d : RemapDir) (p : Path) : Option String :=
  if d.hasSymlink then some s!"symlink in {String.intercalate "/" p}"
  else if d.unreadable then some s!"cannot list {String.intercalate "/" p}"
  else d.children.toList.findSome? fun c => treeIssue c (p ++ [c.name])

mutual
/-- `RemappingsProvider::get_remappings` for the project at `root` (`d`), seeded with its
user remappings. Returns the provider's remappings, rebased onto the project root.
`above` is the top project root's `aboveRootSource`. -/
partial def provide (d : RemapDir) (root : Path) (keys : TomlKeys) (user : Array Remap)
    (above : Bool) : Provided := Id.run do
  let mut all := user
  let mut issue := keys.issue
  if keys.autoDetect.getD true then
    let (libs, libIssue) := libsOf d keys
    issue := mergeIssue issue libIssue
    let mut entries : Array LibEntry := #[]
    let mut dirIdx := 0
    -- `find_nested_foundry_remappings`: each lib directory itself, then its children.
    for lib in libs do
      let some libDir := d.child? lib | continue
      issue := mergeIssue issue (treeIssue libDir (root ++ [lib]))
      let tomlDirs := (if libDir.foundryToml.isSome then [(libDir, root ++ [lib])] else []) ++
        (libDir.children.toList.filter (·.foundryToml.isSome)).map fun c => (c, root ++ [lib, c.name])
      for (nd, np) in tomlDirs do
        let sub := nestedRemappings nd np above
        issue := mergeIssue issue sub.globalIssue
        for r in sub.remaps do
          entries := entries.push { remap := r, nestedDir := some dirIdx }
        dirIdx := dirIdx + 1
    -- `auto_detect_remappings`.
    for lib in libs do
      let some libDir := d.child? lib | continue
      let (found, uncertain) := findMany libDir (root ++ [lib]) above
      if uncertain then
        issue := mergeIssue issue (some s!"Foundry's scan of {String.intercalate "/" (root ++ [lib])} \
          depends on directory listing order or on directories above the project root")
      for (name, path, amb) in found do
        if ["lib/", "src/", "contracts/"].contains name then continue
        let text := String.intercalate "/" path ++ "/"
        entries := entries.push
          { remap := { context := none, name, path, pathText := text,
                       issue := if amb then orderIssue name else none },
            nestedDir := none }
    let slotKey (e : LibEntry) := (e.remap.context, e.remap.name)
    let slots := (entries.toList.map slotKey).eraseDups.toArray.qsort fun a b =>
      match a.1, b.1 with
      | none, some _ => true
      | some _, none => false
      | some x, some y => x < y || (x == y && a.2 < b.2)
      | none, none => a.2 < b.2
    for slot in slots do
      let some e := insertClosest (entries.toList.filter (slotKey · == slot)) | continue
      if e.remap.context.isSome then
        issue := mergeIssue issue (some s!"context remapping {e.remap.name}")
      all := pushFiltered all { e.remap with lib := true }
  return { remaps := dedupByKey all, globalIssue := issue }

/-- `nested_foundry_remappings(lib)`: `Config::load_with_root(lib).sanitized().remappings`
plus the library's `src` remapping. A config Foundry fails to load contributes nothing. -/
partial def nestedRemappings (d : RemapDir) (root : Path) (above : Bool) : Provided := Id.run do
  let keys := parseFoundryToml (d.foundryToml.getD "")
  let keys := { keys with issue := keys.issue.map (s!"{String.intercalate "/" root}/" ++ ·) }
  let txt ← match d.remappingsTxt with
    | none => pure (some [])
    | some t => pure (parseRemappingsTxt root t)
  let toml := (keys.remappings.getD []).mapM (remapOfText root)
  let (some txt, some toml) := (txt, toml) | return { remaps := #[] }
  let p := provide d root keys (txt ++ toml).toArray above
  -- Round trip through `RelativeRemapping`: names and targets gain a trailing `/`.
  let mut out := p.remaps.map fun r =>
    { r with name := withSlash r.name, pathText := withSlash r.pathText, lib := false }
  -- After `sanitized()` the configured `src` is absolute, so Foundry always adds it.
  let srcText := keys.src.getD
    (if (d.child? "src").isSome then "src" else if (d.child? "contracts").isSome then "contracts"
     else "src")
  let srcParts := (srcText.splitOn "/").filter (· != "")
  let srcPath := root ++ srcParts.filter (· != ".")
  let srcIssue :=
    if srcText.startsWith "/" || srcParts.any (· == "..") ||
        (srcParts.any (· == ".") && srcParts != ["."]) then
      some s!"unsupported src {srcText}" else none
  if let some name := lastName root then
    out := out.push { context := none, name := name ++ "/", path := srcPath,
                      pathText := String.intercalate "/" srcPath ++ "/", issue := srcIssue }
  return { p with remaps := out }
end

/-- Output form of a provider remapping: target relative to the project root. -/
def Remap.toInferred (r : Remap) : InferredRemapping :=
  let path := if r.pathText.startsWith "/" then withSlash r.pathText
    else withSlash (String.intercalate "/" r.path)
  { name := r.name, path, issue := r.issue }

end FoundryRemap

open FoundryRemap in
/-- The remappings Foundry infers for the project `root` beyond its `explicit` ones
(`remappings.txt`, then `foundry.toml`), in Foundry's order. -/
def inferFoundryRemappings (root : RemapDir) (explicit : Array (String × String)) :
    InferredRemappings :=
  let keys := parseFoundryToml (root.foundryToml.getD "") (strict := false)
  let user := explicit.map fun (n, t) =>
    match parseRemapping s!"{n}={t}" with
    | some (ctx, name, _) => { context := ctx, name, path := [], pathText := t }
    | none => { context := none, name := n, path := [], pathText := t }
  let p := provide root [] keys user root.aboveRootSource
  let inferred := (p.remaps.filter (·.lib)).map (·.toInferred)
  { remappings := inferred, globalIssue := p.globalIssue }

/-- solc's remapping of the import path `name` (after relative resolution): the longest
matching prefix among the `explicit` remappings (the first on a tie) and Foundry's inferred
ones. Foundry drops every inferred remapping whose name nests with an explicit one, so an
inferred entry can only win where no explicit prefix matches. Returns the remapped path and
the inferred entry used, if any. Using an entry with an issue, or any inferred entry while
the inferred set is unknown, is an error. -/
def remapImportPath (name : String) (explicit : Array (String × String))
    (inferred : InferredRemappings) (relative : Bool := false) :
    Except String (String × Option InferredRemapping) := do
  let mut best : Option (String × String) := none
  for pair in explicit do
    if name.startsWith pair.1 then
      best := match best with
        | none => some pair
        | some prev => if pair.1.length > prev.1.length then some pair else some prev
  let mut inf : Option InferredRemapping := none
  for r in inferred.remappings do
    if name.startsWith r.name && best.all (r.name.length > ·.1.length) &&
        inf.all (r.name.length > ·.name.length) then
      inf := some r
  match inf, best with
  | some r, _ =>
    if let some g := inferred.globalIssue then
      throw s!"import {name} needs Foundry's inferred remapping {r.name}={r.path}, but the \
        inferred set is unknown here ({g}); write the remapping in remappings.txt"
    if let some i := r.issue then
      throw s!"import {name} needs Foundry's inferred remapping {r.name}={r.path}, but {i}; \
        write the remapping in remappings.txt"
    return (r.path ++ (name.drop r.name.length).toString, some r)
  | none, some (pre, tgt) =>
    -- A written name without a trailing `/` does not drop a longer inferred name it is a
    -- prefix of (`oz` keeps `ozx/`), so an unknown inferred set could hold a longer match.
    if let some g := inferred.globalIssue then
      if !pre.endsWith "/" then
        throw s!"import {name} matches the remapping {pre}={tgt}, written without a trailing \
          /, but Foundry's inferred remappings are unknown here ({g}); end the name with /"
    return (tgt ++ (name.drop pre.length).toString, none)
  | none, none =>
    -- Foundry might hold an inferred remapping for this path that the port cannot see.
    -- A written non-relative path is refused; a relative one, already inside the project
    -- tree, resolves as written.
    if let some g := inferred.globalIssue then
      if !relative then
        throw s!"import {name} matches no remapping, but Foundry's inferred remappings are \
          unknown here ({g}); write the remapping in remappings.txt"
    return (name, none)

/-- Normalize a `/`-separated source unit name: drop `.` and empty parts, apply `..`. -/
def normalizeSourcePath (path : String) : Except String String := Id.run do
  let mut out : Array String := #[]
  for part in path.splitOn "/" do
    if part == "" || part == "." then
      pure ()
    else if part == ".." then
      if out.isEmpty then return .error s!"path escapes the project: {path}"
      out := out.pop
    else
      out := out.push part
  return .ok (String.intercalate "/" out.toList)

/-- The source unit that `spec`, imported from `origin`, names, as solc resolves it: a
relative path is joined to `origin`'s directory first, then remappings apply to every import
path. Also returns the inferred remapping used, if any. -/
def resolveImport (origin spec : String) (explicit : Array (String × String))
    (inferred : InferredRemappings) : Except String (String × Option InferredRemapping) := do
  let relative := spec.startsWith "."
  let path ← if relative then
      let parent := String.intercalate "/" (origin.splitOn "/").dropLast
      normalizeSourcePath (parent ++ "/" ++ spec)
    else pure spec
  let (target, used) ← remapImportPath path explicit inferred relative
  return (← normalizeSourcePath target, used)

/-- Read the parts of `dir` that remapping inference looks at. Hidden entries are skipped,
symlinks are recorded and not followed, children are sorted. -/
partial def readRemapDir (dir : System.FilePath) (name : String) : IO RemapDir := do
  let entries ← try dir.readDir catch _ => return { name, unreadable := true }
  let entries := entries.qsort (·.fileName < ·.fileName)
  let mut d : RemapDir := { name }
  for e in entries do
    let md ← try e.path.symlinkMetadata catch _ => return { d with unreadable := true }
    if e.fileName.startsWith "." then
      -- Only a hidden directory holding a `foundry.toml` can matter (a nested config).
      if md.type == .dir && (← (e.path / "foundry.toml").pathExists) then
        let child ← readRemapDir e.path e.fileName
        d := { d with children := d.children.push { child with hidden := true } }
      continue
    match md.type with
    | .symlink => d := { d with hasSymlink := true }
    | .dir => d := { d with children := d.children.push (← readRemapDir e.path e.fileName) }
    | .file =>
      if e.fileName.endsWith ".sol" then d := { d with hasSol := true }
      if e.fileName == "foundry.toml" || e.fileName == "remappings.txt" then
        let text ← try IO.FS.readFile e.path catch _ => return { d with unreadable := true }
        d := if e.fileName == "foundry.toml" then { d with foundryToml := some text }
          else { d with remappingsTxt := some text }
    | .other => pure ()
  return d

/-- The project root as inference sees it: its `foundry.toml`, and its library directories
read in full (the only part of the tree Foundry scans). -/
def readRemapRoot (root : System.FilePath) : IO RemapDir := do
  let toml ← if ← (root / "foundry.toml").pathExists then
      some <$> IO.FS.readFile (root / "foundry.toml") else pure none
  let keys := FoundryRemap.parseFoundryToml (toml.getD "") (strict := false)
  let present ← ["lib", "node_modules"].filterM fun (n : String) => (root / n).isDir
  let shallow : RemapDir :=
    { name := "", foundryToml := toml, children := present.toArray.map fun n => { name := n } }
  let (libs, _) := FoundryRemap.libsOf shallow keys
  let mut children := shallow.children.filter (!libs.contains ·.name)
  for lib in libs do
    if ← (root / lib).isDir then
      let md ← (root / lib).symlinkMetadata
      if md.type == .symlink then
        children := children.push { name := lib, hasSymlink := true }
      else
        children := children.push (← readRemapDir (root / lib) lib)
  let real ← try IO.FS.realPath root catch _ => pure root
  let aboveRootSource := real.components.any (fun c => c == "src" || c == "contracts")
  return { shallow with children, aboveRootSource }

end Compiler.CompilationModel.SolidityImport

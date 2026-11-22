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
  /-- This directory is itself a symlink and was not read. -/
  isSymlink : Bool := false
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
  /-- The written remappings `forge build` keeps, in order (see `inferFoundryRemappings`). -/
  explicit : Array (String × String) := #[]
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
their value, whether it is ambiguous, and its possible values when they are known (a pure
listing-order tie), and whether the key set itself is uncertain. -/
def findMany (lib : RemapDir) (libPath : Path) (aboveRootSource : Bool) :
    List (String × Path × Bool × Option (List Path)) × Bool :=
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
    let values := group.map (·.sourceDir)
    (orderIndependentWinner replace values).map fun (p, amb) =>
      let alts := if amb && !ambiguousInput then some values.eraseDups else none
      (k, p, amb || ambiguousInput, alts), subs.any (·.2))

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
  /-- `[profile.default]` `test` and `script` (the project paths `forge build` protects). -/
  test : Option String := none
  script : Option String := none
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
    else if path == ["profile", "default", "test"] || path == ["profile", "default", "script"] then
      match quotedStrings value with
      | some [v] => if leaf == "test" then { keys with test := some v } else { keys with script := some v }
      | _ => keys
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
  /-- For an entry with an issue: every value it may really have, when known. -/
  alts : Option (List Path) := none
  deriving Inhabited

/-- `insert_closest` for one `(context, name)` slot. Nested entries come first in an unknown
directory order; within one directory, and among auto-detected entries, order is known.
The fewest components win; on a tie the first inserted stays. -/
def insertClosestValue (entries : List LibEntry) : Option LibEntry := do
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

/-- `insertClosestValue`, carrying over the issue of an entry in the slot whose real value
the port does not know for sure (a listing-order alternative, an absolute target counted on
another basis) when that value may win: fewer components than the winner, or as many with
a different path. -/
def insertClosest (entries : List LibEntry) : Option LibEntry := do
  let winner ← insertClosestValue entries
  if winner.remap.issue.isSome then return winner
  let n := componentCount winner.remap.path
  let mayWin (p : Path) : Bool :=
    componentCount p < n || (componentCount p == n && p != winner.remap.path)
  match entries.find? fun e => e.remap.issue.isSome && (e.alts.map (·.any mayWin)).getD true with
  | some e => return { winner with remap := { winner.remap with issue := e.remap.issue } }
  | none => return winner

/-- The output of the remappings provider for one project root. -/
structure Provided where
  remaps : Array Remap
  globalIssue : Option String := none
  deriving Inhabited

/-- The first of two issues. -/
def mergeIssue (a b : Option String) : Option String := a <|> b

/-- The directory a `libs` entry names, when it is one directory of the project (`lib`,
`./lib`, `lib/`): Foundry joins the entry to the root, so `.` parts do not matter. -/
def libName? (l : String) : Option String :=
  match (l.splitOn "/").filter (fun p => p != "" && p != ".") with
  | [n] => if l.startsWith "/" || n == ".." then none else some n
  | _ => none

/-- Library directories from `libs`, or Foundry's default (`DappHardhatDirProvider`). -/
def libsOf (d : RemapDir) (keys : TomlKeys) : List String × Option String :=
  match keys.libs with
  | some ls =>
    match ls.mapM libName? with
    | some names => (names, none)
    | none => (ls, some s!"libs entry outside the project or with several components in {ls}; \
        the importer does not read there")
  | none =>
    if (d.child? "node_modules").isSome then
      ((if (d.child? "lib").isSome then ["lib"] else []) ++ ["node_modules"], none)
    else (["lib"], none)

/-- Symlinks or unreadable directories anywhere below `d`. -/
partial def treeIssue (d : RemapDir) (p : Path) : Option String :=
  if d.hasSymlink || d.isSymlink then some s!"symlink in {String.intercalate "/" p}"
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
      for (name, path, amb, alts) in found do
        if ["lib/", "src/", "contracts/"].contains name then continue
        let text := String.intercalate "/" path ++ "/"
        entries := entries.push
          { remap := { context := none, name, path, pathText := text,
                       issue := if amb then orderIssue name else none },
            nestedDir := none, alts }
    let slotKey (e : LibEntry) := (e.remap.context, e.remap.name)
    let slots := (entries.toList.map slotKey).eraseDups.toArray.qsort fun a b =>
      match a.1, b.1 with
      | none, some _ => true
      | some _, none => false
      | some x, some y => x < y || (x == y && a.2 < b.2)
      | none, none => a.2 < b.2
    for slot in slots do
      let some e := insertClosest (entries.toList.filter (slotKey · == slot)) | continue
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

/-! ### Library configurations only (no source scan) -/

/-- The remappings Foundry may take from library configurations, without scanning any
library for sources: for every nested `foundry.toml` directory (recursively), its written
remappings, rebased and slash-normalized as Foundry does, and its `src` remapping. Context
remappings are included with their context. Names Foundry derives by scanning sources are
single directory names (`<dir>/`), so they are left out here. `issue`: a configuration whose
remappings this reader cannot know (see `parseFoundryToml`), a symlinked or unreadable
library directory. -/
structure ConfigPool where
  entries : Array Remap := #[]
  issue : Option String := none
  deriving Inhabited

mutual
/-- `ConfigPool` of the libraries of the project or library `d` at `root`. -/
partial def configPool (d : RemapDir) (root : Path) (keys : TomlKeys) : ConfigPool := Id.run do
  if !(keys.autoDetect.getD true) then return {}
  let (libs, libIssue) := libsOf d keys
  let mut out : ConfigPool := { issue := libIssue }
  for lib in libs do
    let some libDir := d.child? lib | continue
    let path := root ++ [lib]
    if libDir.isSymlink || libDir.unreadable then
      -- Foundry reads nested configurations through a symlinked library directory.
      let why := s!"library directory {String.intercalate "/" path} is a symlink or unreadable"
      out := { out with issue := mergeIssue out.issue (some why) }
      continue
    if let some c := libDir.children.find? (·.unreadable) then
      let why := s!"{String.intercalate "/" (path ++ [c.name])}: a configuration file is a \
        symlink or unreadable"
      out := { out with issue := mergeIssue out.issue (some why) }
    let tomlDirs := (if libDir.foundryToml.isSome then [(libDir, path)] else []) ++
      (libDir.children.toList.filter (·.foundryToml.isSome)).map fun c => (c, path ++ [c.name])
    for (nd, np) in tomlDirs do
      let sub := nestedConfigPool nd np
      out := { entries := out.entries ++ sub.entries, issue := mergeIssue out.issue sub.issue }
  return out

/-- `ConfigPool` contribution of the library configuration `d` at `root`. -/
partial def nestedConfigPool (d : RemapDir) (root : Path) : ConfigPool := Id.run do
  let keys := parseFoundryToml (d.foundryToml.getD "")
  let issue := keys.issue.map (s!"{String.intercalate "/" root}/" ++ ·)
  let txt := match d.remappingsTxt with
    | none => some []
    | some t => parseRemappingsTxt root t
  let toml := (keys.remappings.getD []).mapM (remapOfText root)
  -- A configuration Foundry fails to load contributes nothing.
  let (some txt, some toml) := (txt, toml) | return { issue }
  let written := (txt ++ toml).toArray.map fun r =>
    { r with name := withSlash r.name, pathText := withSlash r.pathText }
  let srcName := (lastName root).map (· ++ "/")
  let src : Array Remap := match srcName with
    | some n => #[{ context := none, name := n, path := [], pathText := "" }]
    | none => #[]
  let sub := configPool d root keys
  return { entries := written ++ src ++ sub.entries, issue := mergeIssue issue sub.issue }
end

end FoundryRemap

open FoundryRemap in
/-- The project paths `forge build` protects: `src` (configured, else `src` or `contracts`
as present), `test` and `script`, each with a trailing `/`. -/
def projectPathsOf (root : RemapDir) (keys : TomlKeys) : List String :=
  let src := keys.src.getD (if (root.child? "src").isSome then "src"
    else if (root.child? "contracts").isSome then "contracts" else "src")
  [src, keys.test.getD "test", keys.script.getD "script"].map (· ++ "/")

open FoundryRemap in
/-- Written remappings as Foundry parses them (`context:name=target`). -/
def userRemaps (explicit : Array (String × String)) : Array Remap :=
  explicit.map fun (n, t) =>
    match parseRemapping s!"{n}={t}" with
    | some (ctx, name, _) => { context := ctx, name, path := [], pathText := t }
    | none => { context := none, name := n, path := [], pathText := t }

open FoundryRemap in
/-- `forge build`'s last pass (`BuildOpts` in forge's CLI; `forge remappings` prints the list
before it): the provider's list, written then inferred, pushed once more through
`Remappings::push` with the project paths as protected names. It drops a remapping named
after a project path (ASCII case ignored) and a written remapping nested under an earlier
one. Returns the kept written pairs as solc gets them (context ones included, in order; name
and target with a trailing `/` unless they end in `/` or `.sol`), the kept inferred
remappings, and the kept written context remappings. -/
def buildPass (projectPaths : List String) (explicit : Array (String × String))
    (inferred : Array Remap) : Array (String × String) × Array Remap × Array Remap := Id.run do
  let isProjectPath (n : String) : Bool := projectPaths.any (·.toLower == n.toLower)
  let mut kept : Array Remap := #[]
  let mut keptExplicit : Array (String × String) := #[]
  let mut contexts : Array Remap := #[]
  for (pair, r) in explicit.zip (userRemaps explicit) do
    if isProjectPath r.name then continue
    let next := pushFiltered kept r
    if next.size > kept.size then
      -- solc gets them with a trailing `/` on name and target (`Remapping::from`).
      let name := match r.context with
        | some c => s!"{c}:{withSlash r.name}"
        | none => withSlash pair.1
      keptExplicit := keptExplicit.push (name, withSlash pair.2)
      if r.context.isSome then contexts := contexts.push { r with name := withSlash r.name }
    kept := next
  let mut keptInferred : Array Remap := #[]
  for r in inferred do
    if isProjectPath r.name then continue
    let next := pushFiltered kept r
    if next.size > kept.size then keptInferred := keptInferred.push r
    kept := next
  return (keptExplicit, keptInferred, contexts)

open FoundryRemap in
/-- The remappings `forge build` gives solc for the project `root` (read in full) with the
written remappings `explicit` (`remappings.txt`, then `foundry.toml`): the provider's list
after `buildPass`. Context remappings are left out of `remappings` (the importer refuses an
import a context remapping could reach before it gets here; see `remapDecideA`). -/
def inferFoundryRemappings (root : RemapDir) (explicit : Array (String × String)) :
    InferredRemappings :=
  let keys := parseFoundryToml (root.foundryToml.getD "") (strict := false)
  let p := provide root [] keys (userRemaps explicit) root.aboveRootSource
  let (keptExplicit, keptInferred, _) :=
    buildPass (projectPathsOf root keys) explicit (p.remaps.filter (·.lib))
  { remappings := (keptInferred.filter (·.context.isNone)).map (·.toInferred),
    explicit := keptExplicit, globalIssue := p.globalIssue }

/-- What the importer knows before reading inside any library directory (only the root's
`foundry.toml` and which directories exist): the written remappings `forge build` keeps, its
written context remappings, the project paths, and whether Foundry infers anything at all
(auto-detection on and some library directory present). `issue`: the root configuration
leaves even the written remappings unknown (`extends`, an inline default profile, …). -/
structure RemapStage0 where
  explicit : Array (String × String) := #[]
  contexts : Array FoundryRemap.Remap := #[]
  projectPaths : List String := []
  inference : Bool := false
  issue : Option String := none
  deriving Inhabited

open FoundryRemap in
/-- `RemapStage0` of the project `root` (a shallow read suffices). -/
def remapStage0 (root : RemapDir) (explicit : Array (String × String)) : RemapStage0 :=
  let keys := parseFoundryToml (root.foundryToml.getD "") (strict := false)
  let projectPaths := projectPathsOf root keys
  let (keptExplicit, _, contexts) := buildPass projectPaths explicit #[]
  let (libs, libIssue) := libsOf root keys
  let present := libs.any fun l => (root.child? l).isSome
  -- An unsupported `libs` entry only matters when Foundry infers (`remapDecideA`).
  let inference := keys.autoDetect.getD true && (present || libIssue.isSome)
  { explicit := keptExplicit, contexts, projectPaths, inference, issue := keys.issue }

open FoundryRemap in
/-- The `ConfigPool` of the project `root` (read with `readRemapConfigs`, or in full). -/
def remapConfigPool (root : RemapDir) : ConfigPool :=
  if root.unreadable then { issue := some "the project's configuration files are unreadable" }
  else configPool root [] (parseFoundryToml (root.foundryToml.getD "") (strict := false))

/-- One step of the staged resolution: a result, or the next read it needs. -/
inductive RemapStep where
  | done (target : String) (used : Option InferredRemapping)
  | needConfigs
  | needScan
  deriving Inhabited

/-- The longest written remapping without a context whose name is a prefix of `path` (the
first on a tie). -/
def bestExplicit (explicit : Array (String × String)) (path : String) :
    Option (String × String) := Id.run do
  let mut best : Option (String × String) := none
  for pair in explicit do
    let contextual := (FoundryRemap.parseRemapping s!"{pair.1}={pair.2}").any (·.1.isSome)
    if path.startsWith pair.1 && !contextual then
      best := match best with
        | none => some pair
        | some prev => if pair.1.length > prev.1.length then some pair else some prev
  return best

/-- `path` remapped by `best`, or as written. -/
def applyRemapping (path : String) : Option (String × String) → String
  | some (pre, tgt) => tgt ++ (path.drop pre.length).toString
  | none => path

/-- solc's remapping of the import path `name` (after relative resolution) by the written
remappings `explicit` and Foundry's inferred ones: the longest matching prefix (the first on a
tie among written ones). Foundry drops every inferred remapping whose name nests with a
written one, so an inferred entry only wins where no written prefix of it matches. Returns
the remapped path and the inferred entry used, if any. Using an entry with an issue is an
error. -/
def remapImportPath (name : String) (explicit : Array (String × String))
    (inferred : InferredRemappings) : Except String (String × Option InferredRemapping) := do
  let best := bestExplicit explicit name
  let mut inf : Option InferredRemapping := none
  for r in inferred.remappings do
    if name.startsWith r.name && best.all (r.name.length > ·.1.length) &&
        inf.all (r.name.length > ·.name.length) then
      inf := some r
  match inf with
  | some r =>
    if let some i := r.issue then
      -- A file remapping is never dropped for nesting, so writing one does not help.
      let advice := if r.name.endsWith ".sol" then
          "set auto_detect_remappings = false if the written remappings suffice"
        else "write the remapping in remappings.txt"
      throw s!"import {name} needs Foundry's inferred remapping {r.name}={r.path}, but {i}; \
        {advice}"
    return (r.path ++ (name.drop r.name.length).toString, some r)
  | none => return (applyRemapping name best, none)

open FoundryRemap in
/-- A context remapping that can reach `path` imported from `origin`: solc applies
`context:name=target` to imports in files whose source unit name starts with `context`, and
`forge build` passes such remappings from library configurations verbatim. The importer does
not model contexts, so it refuses. -/
def contextRefusal (origin path : String) (rs : Array Remap) : Option String :=
  rs.findSome? fun r => match r.context with
    | some c =>
      if origin.startsWith c && path.startsWith r.name then
        some s!"import {path} in {origin} can take the context remapping {c}:{r.name}, \
          which the importer does not model"
      else none
    | none => none

/-- Stage 0 (no library read): refusal on an unknown root configuration or a written context
remapping; the written result when Foundry infers nothing; otherwise `needConfigs`. -/
def remapDecide0 (s : RemapStage0) (origin path : String) : Except String RemapStep := do
  if let some i := s.issue then
    throw s!"import {path}: the project's remappings are unknown ({i})"
  if let some m := contextRefusal origin path s.contexts then throw m
  if !s.inference then return .done (applyRemapping path (bestExplicit s.explicit path)) none
  return .needConfigs

/-- Stage 1 (library configurations read, no source scan). Decides `path` when no inferred
remapping can reach it, whatever a scan would find:
- a written match ending in `/` (Foundry drops every inferred name nesting with it), or a
  written match `E` without `/` where `path` continues with `E/` (any longer name matching
  `path` starts with `E/` and nests with it), unless a configuration's file remapping
  (`….sol`, never dropped for nesting) matches `path`;
- no written match, or a shorter one, where no configuration name is a prefix of `path` and
  the first component `c` of `path` is protected: a name found by scanning sources is a single
  directory name, so only `c/` could match, and Foundry skips `lib/`, `src/`, `contracts/`
  found that way and drops a project path (`src`, `test`, `script` as configured).
Context remappings that can reach `path` are refused. Otherwise `needScan`. -/
def remapDecideA (s : RemapStage0) (pool : FoundryRemap.ConfigPool) (origin path : String) :
    Except String RemapStep := do
  if let some i := pool.issue then
    throw s!"import {path}: Foundry's remappings are unknown here ({i}), so any import may \
      resolve differently; remove the cause, or set auto_detect_remappings = false if the \
      written remappings suffice"
  if let some m := contextRefusal origin path pool.entries then throw m
  let best := bestExplicit s.explicit path
  -- `Remappings::push` drops no file remapping (`….sol`) for nesting, so a configuration's
  -- file remapping matching `path` can win over any written match.
  let fileHit := pool.entries.any fun r => r.context.isNone && r.name.endsWith ".sol" &&
    path.startsWith r.name
  if let some (pre, _) := best then
    if !fileHit && (pre.endsWith "/" || path.startsWith (pre ++ "/")) then
      return .done (applyRemapping path best) none
  let c := ((path.splitOn "/").headD "") ++ "/"
  let projectPath := s.projectPaths.any (·.toLower == c.toLower)
  let protected_ := path.length > c.length && path.startsWith c &&
    (["lib/", "src/", "contracts/"].contains c || projectPath)
  let poolHit := pool.entries.any fun r =>
    r.context.isNone && path.startsWith r.name && !(projectPath && r.name.toLower == c.toLower)
  if protected_ && !poolHit then return .done (applyRemapping path best) none
  return .needScan

/-- Stage 2 (libraries scanned in full): the exact result, or a refusal when Foundry's inferred
set is unknown (`globalIssue`) or the matching inferred entry has an issue. -/
def remapDecideB (s : RemapStage0) (full : InferredRemappings) (path : String) :
    Except String (String × Option InferredRemapping) := do
  if let some g := full.globalIssue then
    throw s!"import {path} could take a remapping Foundry infers, but the inferred set is \
      unknown here ({g}); write the remapping in remappings.txt"
  remapImportPath path s.explicit full

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

/-- The import path of `spec` in `origin` before remapping: a relative `spec` joined to
`origin`'s directory and normalized, as solc does first. -/
def importPath (origin spec : String) : Except String String :=
  if spec.startsWith "." then
    normalizeSourcePath (String.intercalate "/" (origin.splitOn "/").dropLast ++ "/" ++ spec)
  else pure spec

/-- The source unit that `spec`, imported from `origin`, names, as solc resolves it with the
remappings `forge build` passes, with every stage at hand: the source unit, the inferred
remapping used, and the deepest stage the decision needed (0: none, 1: library
configurations, 2: full library scan). The importer runs the same stages but reads each one
only when a decision needs it. -/
def resolveImportStaged (origin spec : String) (s : RemapStage0)
    (pool : FoundryRemap.ConfigPool) (full : InferredRemappings) :
    Except String (String × Option InferredRemapping × Nat) := do
  let path ← importPath origin spec
  match ← remapDecide0 s origin path with
  | .done t u => return (← normalizeSourcePath t, u, 0)
  | _ =>
    match ← remapDecideA s pool origin path with
    | .done t u => return (← normalizeSourcePath t, u, 1)
    | _ =>
      let (t, u) ← remapDecideB s full path
      return (← normalizeSourcePath t, u, 2)

/-- Read a configuration file that may be absent: `none` if absent, `.error` if unreadable,
or if it is a symlink and `follow` is off (a library's configuration file is never followed;
the project's own is, as `readRemappings` and `readRemapRootShallow` read it). -/
def readOptional (path : System.FilePath) (follow : Bool := false) :
    IO (Except Unit (Option String)) := do
  let md ← try path.symlinkMetadata catch _ => return .ok none
  if md.type == .symlink && !follow then return .error ()
  try return .ok (some (← IO.FS.readFile path)) catch _ => return .error ()

/-- Shallow entries of `dir` for the directories named `names` that exist there: a symlink
is recorded (`isSymlink`) and not followed. -/
def shallowDirs (dir : System.FilePath) (names : List String) : IO (Array RemapDir) := do
  let mut out : Array RemapDir := #[]
  for n in names.eraseDups do
    if n.isEmpty || n.startsWith "/" || n.contains '/' then continue
    let p := dir / n
    let md ← try p.symlinkMetadata catch _ => continue
    if md.type == .symlink then
      if ← p.isDir then out := out.push { name := n, isSymlink := true }
    else if md.type == .dir then out := out.push { name := n }
  return out

/-- Read the parts of `dir` that remapping inference looks at. Hidden entries are skipped,
except a hidden directory holding a `foundry.toml` and the hidden library directories a
`foundry.toml` here names. Symlinks are recorded and not followed. Children are sorted. -/
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
  if let some toml := d.foundryToml then
    -- A library's own hidden `libs` directory is scanned by Foundry like any other.
    -- Only entries naming one directory here (`libName?`): never `.` or `..`.
    let (libs, libIssue) := FoundryRemap.libsOf d (FoundryRemap.parseFoundryToml toml)
    for lib in if libIssue.isSome then [] else libs do
      if lib.startsWith "." && (d.child? lib).isNone then
        for c in ← shallowDirs dir [lib] do
          let child ← if c.isSymlink then pure c else readRemapDir (dir / lib) lib
          d := { d with children := d.children.push { child with hidden := true } }
  return d

/-- The project root without reading inside any directory: its `foundry.toml`, and shallow
entries for `src`, `contracts`, `lib`, `node_modules` and the configured `libs`. Enough for
`remapStage0`. -/
def readRemapRootShallow (root : System.FilePath) : IO RemapDir := do
  let toml ← if ← (root / "foundry.toml").pathExists then
      some <$> IO.FS.readFile (root / "foundry.toml") else pure none
  let keys := FoundryRemap.parseFoundryToml (toml.getD "") (strict := false)
  let children ← shallowDirs root
    (["contracts", "lib", "node_modules", "src"] ++ (keys.libs.getD []).filterMap FoundryRemap.libName?)
  let real ← try IO.FS.realPath root catch _ => pure root
  let aboveRootSource := real.components.any (fun c => c == "src" || c == "contracts")
  return { name := "", foundryToml := toml, children, aboveRootSource }

mutual
/-- `dir` read for `remapConfigPool`: its configuration files, shallow entries for its
default directories, and its library directories (`readRemapLibConfigs`). `follow`: read
symlinked configuration files (the project root only). -/
partial def readRemapConfigDir (dir : System.FilePath) (name : String) (follow : Bool := false) :
    IO RemapDir := do
  let some toml ← (do
      match ← readOptional (dir / "foundry.toml") follow with
      | .ok t => pure (some t)
      | .error () => pure none) | return { name, unreadable := true }
  let txt ← match ← readOptional (dir / "remappings.txt") follow with
    | .ok t => pure t
    | .error () => return { name, unreadable := true }
  let keys := FoundryRemap.parseFoundryToml (toml.getD "") (strict := false)
  let present ← shallowDirs dir
    (["contracts", "lib", "node_modules", "src"] ++ (keys.libs.getD []).filterMap FoundryRemap.libName?)
  let shallow : RemapDir := { name, foundryToml := toml, remappingsTxt := txt, children := present }
  let (libs, _) := FoundryRemap.libsOf shallow keys
  let mut children := present.filter (!libs.contains ·.name)
  for c in present.filter (libs.contains ·.name) do
    children := children.push (← if c.isSymlink then pure c else readRemapLibConfigs (dir / c.name) c.name)
  return { shallow with children }

/-- A library directory read for `remapConfigPool`: listed one level deep; it and every child
holding a `foundry.toml` are read with `readRemapConfigDir`. Symlinked children are not
followed (Foundry's search for nested configurations does not follow them either). -/
partial def readRemapLibConfigs (dir : System.FilePath) (name : String) : IO RemapDir := do
  let entries ← try dir.readDir catch _ => return { name, unreadable := true }
  let hasToml := (← (dir / "foundry.toml").symlinkMetadata.toBaseIO).toBool
  let mut d : RemapDir := { name }
  if hasToml then d ← readRemapConfigDir dir name
  for e in entries.qsort (·.fileName < ·.fileName) do
    let md ← try e.path.symlinkMetadata catch _ => return { d with unreadable := true }
    if md.type != .dir || (d.child? e.fileName).isSome then continue
    -- `symlinkMetadata`: a symlinked `foundry.toml` is found (and refused) too.
    if (← (e.path / "foundry.toml").symlinkMetadata.toBaseIO).toBool then
      let child ← readRemapConfigDir e.path e.fileName
      d := { d with children := d.children.push { child with hidden := e.fileName.startsWith "." } }
  return d
end

/-- The project root read for `remapConfigPool`. -/
def readRemapConfigs (root : System.FilePath) : IO RemapDir := do
  let d ← readRemapConfigDir root "" (follow := true)
  return { d with aboveRootSource := (← readRemapRootShallow root).aboveRootSource }

/-- The project root read in full for `inferFoundryRemappings`: its `foundry.toml`, and its
library directories read entirely (the only part of the tree Foundry scans). -/
def readRemapRoot (root : System.FilePath) : IO RemapDir := do
  let shallow ← readRemapRootShallow root
  let keys := FoundryRemap.parseFoundryToml (shallow.foundryToml.getD "") (strict := false)
  let (libs, _) := FoundryRemap.libsOf shallow keys
  let mut children := shallow.children.filter (!libs.contains ·.name)
  for c in shallow.children.filter (libs.contains ·.name) do
    children := children.push (← if c.isSymlink then pure c else readRemapDir (root / c.name) c.name)
  return { shallow with children }

end Compiler.CompilationModel.SolidityImport

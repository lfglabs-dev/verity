import Lean

namespace Verity.Compiler.FromSolidity

open Lean Elab Command

/-!
# `#fromSolidity` Lean entry point — scaffold

Today the Verity compiler runs out-of-band via the `verity-cli`
command-line tool: a developer manually invokes
`verity-cli compile path/to/Foo.sol --emit lean` and copies the
generated Lean term into the benchmark.

This module is the **scaffold** for surfacing that pipeline as a Lean
elaborator-level command, so that a benchmark file can declare:

```
#fromSolidity "vendor/account-abstraction/EntryPoint.sol"
```

and obtain a proof-checked `verity_contract` term as if it had been
hand-written.

## Status

This scaffold lands the public API surface (`#fromSolidity` command,
options, error type) and a stub elaborator that defers to the CLI via
`IO.Process.run`. The full machine translation requires hooking
`Compiler/CompilationModel.lean`'s Solidity-IR pipeline directly into
Lean's elaborator, which is a multi-week project tracked separately
(see `docs/ROADMAP.md` "machine fromSolidity").

The scaffold exists so:

* The API contract is fixed (the command name and option shape will not
  change underneath downstream benchmarks).
* The CLI integration point is documented as a single function
  (`runVerityCliCompile`) that the next PR replaces with an in-process
  call.
* Benchmarks that today write `verity_contract` blocks by hand can
  switch to `#fromSolidity` once the CLI shells out cleanly, without
  changing their proof files.

## Trust boundary today vs. after full implementation

Today (`fromSolidity` shells out to `verity-cli`):
* Trust the CLI binary on disk.
* Trust the file-system path is consistent with what the developer
  proved against.

After full implementation (in-process):
* No CLI binary trust — translation runs inside Lean.
* The same kernel checks the resulting term that checks every Lean
  proof.

The headline difference: the post-implementation form makes
*translation faithfulness* part of the proof-checked trust base.
-/

/-- Options for `#fromSolidity`. -/
structure Options where
  /-- Path to the Solidity source. Resolved relative to the workspace root. -/
  path : System.FilePath
  /-- Optional contract name selector (defaults to the only contract in the file). -/
  contractName : Option String := none
  /-- Verity CLI binary to invoke. Defaults to `verity-cli` on PATH. -/
  cliBinary : String := "verity-cli"
  deriving Repr

/-- Result of running the CLI translation step. -/
inductive Result where
  | ok (lean : String)
  | error (msg : String)
  deriving Repr

/-- Locate the Lake workspace root containing the current process, if any. -/
partial def findWorkspaceRoot? (dir : System.FilePath) : IO (Option System.FilePath) := do
  if ← (dir / "lakefile.lean").pathExists then
    pure (some dir)
  else if ← (dir / "lakefile.toml").pathExists then
    pure (some dir)
  else
    match dir.parent with
    | some parent =>
        if parent == dir then
          pure none
        else
          findWorkspaceRoot? parent
    | none => pure none

/-- Resolve `path` according to the `Options.path` contract.

Absolute paths are preserved. Relative paths are anchored at the Lake workspace
root containing the current process, falling back to the process working
directory when the command is run outside a Lake workspace. -/
def resolveSourcePath (path : System.FilePath) : IO System.FilePath := do
  if path.isAbsolute then
    pure path.normalize
  else
    let cwd ← IO.currentDir
    let root ← findWorkspaceRoot? cwd
    pure (((root.getD cwd) / path).normalize)

/-- Invoke `verity-cli compile path --emit lean`. Returns the emitted
    Lean source on stdout or an error message. -/
def runVerityCliCompile (opts : Options) : IO Result := do
  let sourcePath ← resolveSourcePath opts.path
  let args := match opts.contractName with
    | some c =>
        #["compile", sourcePath.toString, "--contract", c, "--emit", "lean"]
    | none =>
        #["compile", sourcePath.toString, "--emit", "lean"]
  try
    let out ← IO.Process.run { cmd := opts.cliBinary, args }
    return .ok out
  catch e =>
    return .error s!"verity-cli failed: {e.toString}"

/-- `#fromSolidity "path"` command. Currently emits a placeholder
    `axiom` whose name documents the pending translation; replace with a
    proper elaborator emission once the in-process translator lands. -/
syntax (name := fromSolidityCmd) "#fromSolidity " str (" contract " str)? : command

@[command_elab fromSolidityCmd]
def elabFromSolidity : CommandElab := fun stx => do
  let pathLit := stx[1]
  let path : System.FilePath := pathLit.isStrLit?.get!
  let contractOpt : Option String :=
    if stx[2].getNumArgs > 0 then some stx[2][1].isStrLit?.get! else none
  let opts : Options := { path := path, contractName := contractOpt }
  let result : Result ← (runVerityCliCompile opts).toIO
    (fun e => IO.userError s!"fromSolidity IO failure: {e.toString}")
  match result with
  | .ok _emitted =>
      let sourcePath ← (resolveSourcePath opts.path).toIO
        (fun e => IO.userError s!"fromSolidity path resolution failure: {e.toString}")
      logInfo m!"fromSolidity scaffold: would elaborate {sourcePath}; in-process translator pending"
  | .error msg =>
      throwError m!"fromSolidity: {msg}. Falling back: declare the verity_contract block by hand for now."

end Verity.Compiler.FromSolidity

import Compiler.SolidityImport.Coverage
import Compiler.SolidityImport.Report
import Compiler.CompilationModel
import Compiler.Codegen
import Compiler.Yul.PrettyPrint
import Compiler.Keccak.Sponge
import Compiler.Hex
import Lean.Data.Json

/-! Test-only runner for an arbitrary covered Solidity slice. The execution path
is the same `Denote.execStmtList` used by proofs. JSON/IO and the concrete hash
implementation are harness code, not additional proof assumptions. -/
namespace Compiler.CompilationModel.SolidityImport.Differential
open Lean Compiler.CompilationModel.Denote Verity.Core

private def word (j : Json) : Except String Nat := do
  let s ← j.getStr?
  let some n := s.toNat? | throw "expected an unsigned decimal word"
  unless n < 2^256 do throw "word exceeds uint256"
  return n

private def words (j : Json) : Except String (List Nat) := do
  (← j.getArr?).toList.mapM word

private def pairs (j : Json) : Except String (List (Nat × Nat)) := do
  (← j.getArr?).toList.mapM fun row => do
    let xs ← words row
    match xs with
    | [slot, value] => return (slot, value)
    | _ => throw "storage row must contain slot and value"

private def mappingSlot (base key : Nat) : Nat :=
  let bytes := fun n : Nat => ByteArray.mk ((List.range 32).toArray.map fun i =>
    UInt8.ofNat (n / 2^(8*(31-i)) % 256))
  (KeccakEngine.keccak256 (bytes key ++ bytes base)).data.foldl
    (fun n b => n * 256 + b.toNat) 0

/-- Concrete hash oracle for word-chunk memory slices used by the adapter.
Custom-error signatures populate this temporary buffer explicitly. -/
def oracle : DenoteOracle :=
  { mappingSlot, keccakMemorySlice := fun memory offset size =>
      let bytes := (List.range size).toArray.map fun index =>
        UInt8.ofNat ((memory (offset + index / 32 * 32)).val /
          2^(8*(31-index % 32)) % 256)
      (KeccakEngine.keccak256 (ByteArray.mk bytes)).data.foldl
        (fun value byte => value * 256 + byte.toNat) 0 }

private def jsonWords (xs : List Nat) : Json := toJson (xs.map toString)

private def jsonBytes (bytes : List UInt8) : Json :=
  toJson ("0x" ++ String.ofList (bytes.flatMap fun byte =>
    [Compiler.Hex.hexDigit (byte.toNat / 16), Compiler.Hex.hexDigit (byte.toNat % 16)]))

private def execute (model : CompilationModel) (fn : FunctionSpec) (j : Json) : Except String Json := do
  let ident ← j.getObjValAs? String "id"
  let args ← words (← j.getObjVal? "args")
  unless args.length == fn.params.length do throw "model argument count mismatch"
  let storage ← pairs (← j.getObjVal? "storage")
  let slots ← words (← j.getObjVal? "observe")
  unless (storage.map Prod.fst).eraseDups.length == storage.length do
    throw "duplicate initial storage slot"
  let timestamp ← word (← j.getObjVal? "timestamp")
  let world := Verity.defaultState.withStorageWords fun slot =>
    match slot with
    | .slot n => Uint256.ofNat ((storage.find? (fun p => p.1 == n)).map Prod.snd |>.getD 0)
    | _ => Verity.defaultState.storageWords slot
  let initial : DenoteState :=
    { world := { world with blockTimestamp := Uint256.ofNat timestamp }
      bindings := fn.params.map (·.name) |>.zip args
      errors := model.errors }
  let result := execStmtList oracle model.fields initial fn.body
  let (status, output, data, finalWorld) ← match result with
    | .stop final => match final.observedReturnWords with
      | some xs => pure ("ok", xs, xs.flatMap wordBytes, final.world)
      | none => throw "covered slice stopped without return words"
    | .revertWithData bytes => pure ("revert", [], bytes, initial.world)
    | .revert => throw "Denote failure has no exact revert observation"
    | _ => throw "covered slice did not return or revert"
  return Json.mkObj [("id", toJson ident), ("status", toJson status),
    ("words", jsonWords output), ("data", jsonBytes data),
    ("storage", jsonWords (slots.map fun slot => (finalWorld.storageWords (.slot slot)).val))]

/-- Compile one root on its own with the ordinary Verity compiler, behind a
placeholder selector. Success means the compiler accepts the function; it says
nothing about agreement with Denote or solc (that is what `run` samples). -/
def compileRoot (model : CompilationModel) (fn : FunctionSpec) :=
  Compiler.CompilationModel.compile { model with functions := [fn] } [0x12345678] .osaka

/-- The four statuses of every root, one block per root. `importable` holds for
every listed root; `denoteCovered` and `compilerProofCovered` come from the
import report; `compilable` is this compile attempt. -/
def statusText (model : CompilationModel) (report : ImportReport) : String := Id.run do
  let mut lines := #[]
  for fn in model.functions do
    let some st := report.functions.find? (·.function == fn.name)
      | lines := lines.push s!"function {fn.name}\n  missing from the import report"
    let compilable := match compileRoot model fn with
      | .ok _ => "true"
      | .error reason => s!"false ({reason.replace "\n" " "})"
    lines := lines.push (String.intercalate "\n"
      [s!"function {fn.name}", "  importable true", s!"  denoteCovered {st.denoteCovered}",
       s!"  compilable {compilable}", s!"  compilerProofCovered {st.compilerProof.toText}"])
  return String.intercalate "\n" lines.toList ++ "\n"

private def selectRoot (model : CompilationModel) (name : String) : IO FunctionSpec := do
  let some fn := model.functions.find? (·.name == name)
    | throw (IO.userError s!"no imported root {name}; roots: {model.functions.map (·.name)}")
  return fn

/-- The driver imports the model, then invokes this shared entrypoint.
`describe` also attempts the ordinary Verity compiler; a failure is explicit. -/
def run (model : CompilationModel) (report : ImportReport) (args : List String) : IO UInt32 := do
  unless modelImportCovered model do throw (IO.userError "unsupported Denote slice")
  match args with
  | ["status", output] => IO.FS.writeFile output (statusText model report)
  | ["describe", name, output, yulPath] =>
    let fn ← selectRoot model name
    let (compilable, reason) ← match compileRoot model fn with
      | .ok ir =>
        IO.FS.writeFile yulPath (Compiler.Yul.render (Compiler.emitYul ir))
        pure (true, "")
      | .error reason => pure (false, reason)
    let projections := (report.projections.filter (·.function == name)).map fun p => Json.mkObj
      [("parameter", toJson p.parameter), ("member", toJson p.member), ("modelParam", toJson p.modelParam)]
    IO.FS.writeFile output (Json.compress (Json.mkObj
      [("function", toJson name), ("params", toJson (fn.params.map (·.name))),
       ("projections", toJson projections),
       ("digest", toJson report.sourceDigest), ("settings", toJson report.settingsJson),
       ("compilable", toJson compilable), ("compileError", toJson reason),
       ("panicPayloadObserved", toJson report.observesPanicPayload)]))
  | ["run", name, input, output, digest] =>
    let fn ← selectRoot model name
    unless digest == report.sourceDigest do throw (IO.userError "source/importer digest changed; rebuild the campaign")
    let parsed ← IO.ofExcept (Json.parse (← IO.FS.readFile input))
    let results ← IO.ofExcept do
      (← parsed.getArr?).toList.mapM (execute model fn)
    IO.FS.writeFile output (Json.compress (toJson results))
  | _ => throw (IO.userError "expected status OUTPUT, describe FUNCTION OUTPUT YUL, or run FUNCTION INPUT OUTPUT DIGEST")
  return 0

end Compiler.CompilationModel.SolidityImport.Differential

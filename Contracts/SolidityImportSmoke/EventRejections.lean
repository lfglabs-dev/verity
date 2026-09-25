import Compiler.SolidityImport.SequenceRunner

namespace SolidityImportSmoke.EventRejections
open Compiler.CompilationModel Compiler.CompilationModel.Denote
open Compiler.CompilationModel.SolidityImport

private def oracle : DenoteOracle := ⟨fun _ _ => 0, fun _ _ _ => 0⟩
private def definition : EventDef :=
  { name := "Changed", params := [
    { name := "previous", ty := .uint256, kind := .indexed },
    { name := "next", ty := .uint256, kind := .unindexed }] }
private def model (events : List EventDef) (values : List Expr) : CompilationModel :=
  { name := "EventRejections", fields := [], constructor := none, events, functions := [
    { name := "f", params := [], returnType := none, body := [.emit "Changed" values, .returnValues []] }] }
private def input : String :=
  "{\"account\":\"1\",\"storage\":[],\"transactions\":[{\"id\":\"0\",\"function\":\"f\",\"args\":[],\"sender\":\"2\",\"target\":\"1\",\"value\":\"0\",\"timestamp\":\"100\",\"blockNumber\":\"2\",\"observe\":[]}]}"

def runChecks : IO Unit := do
  let request ← IO.ofExcept (Lean.Json.parse input)
  let values := [.literal 7, .literal 9]
  let observed ← IO.ofExcept (SequenceRunner.execute (model [definition] values) oracle request)
  let rows ← IO.ofExcept observed.getArr?
  let events ← IO.ofExcept ((← IO.ofExcept (rows[0]!.getObjVal? "events")).getArr?)
  unless events.size == 1 do throw (IO.userError "positive event control missing")
  let reject := fun (label : String) (candidate : CompilationModel) (diagnostic : String) => do
    match SequenceRunner.execute candidate oracle request with
    | .error error =>
        unless error == diagnostic do
          throw (IO.userError s!"{label}: unexpected rejection: {error}")
    | .ok _ => throw (IO.userError s!"{label}: unsupported event accepted")
  reject "unknown" (model [] values) "observed event must resolve uniquely: Changed"
  reject "ambiguous" (model [definition, definition] values)
    "observed event must resolve uniquely: Changed"
  reject "missing argument" (model [definition] [.literal 7]) "event argument count differs"
  reject "extra argument" (model [definition] (values ++ [.literal 10])) "event argument count differs"
  let unsupported := { definition with params := [
    { name := "previous", ty := .address, kind := .indexed },
    { name := "next", ty := .uint256, kind := .unindexed }] }
  reject "unsupported type" (model [unsupported] values)
    "event observation currently requires uint256 parameters"
  let excess := { definition with params := List.replicate 4 ({ name := "topic", ty := .uint256, kind := .indexed } : EventParam) }
  reject "too many topics" (model [excess] (List.replicate 4 (.literal 1)))
    "event has more than three indexed parameters"
  IO.println "Event positive control and six exact-diagnostic near-miss rejections passed"
end SolidityImportSmoke.EventRejections

def main : IO Unit := SolidityImportSmoke.EventRejections.runChecks

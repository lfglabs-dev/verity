import Compiler.CompilationModel.Types

namespace Compiler.CompilationModel

/-- Collect all unique (moduleName, axiom) pairs from ECM statements in a spec.
    Used for axiom aggregation reports. -/
def collectEcmAxioms (spec : CompilationModel) : List (String × String) :=
  let stmtsFromFn (fn : FunctionSpec) := fn.body
  let stmtsFromCtor : List Stmt := match spec.constructor with
    | some ctor => ctor.body
    | none => []
  let allStmts := stmtsFromCtor ++ spec.functions.flatMap stmtsFromFn
  let pairs := Stmt.foldList
    (fun acc stmt _ =>
      match stmt with
      | .ecm mod _ => acc ++ mod.axioms.map (fun a => (mod.name, a))
      | _ => acc)
    [] allStmts
  pairs.foldl (fun acc p => if acc.contains p then acc else acc ++ [p]) []

end Compiler.CompilationModel

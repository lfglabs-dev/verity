import Compiler.Proofs.IRGeneration.SourceSemantics

namespace Compiler.Proofs.IRGeneration.SourceCustomErrorBytes
open Compiler.CompilationModel

def hash (name : String) (types : List String) : Nat :=
  let bytes := (name ++ "(" ++ String.intercalate "," types ++ ")").toUTF8.data.toList
  SourceSemantics.keccakMemorySlice (Denote.signatureMemory bytes) 0 bytes.length

/-- The actual declaration lookup, scalar validity guards and argument
evaluation determine the bytes; no uninterpreted payload oracle is assumed. -/
theorem evaluated_payload (fields : List Field) (runtime : SourceSemantics.RuntimeState)
    (name : String) (args : List Expr) (values : List Nat) (definition : ErrorDef)
    (types : List String)
    (evaluated : SourceSemantics.evalExprList fields runtime args = some values)
    (resolved : runtime.errors.filter (·.name == name) = [definition])
    (arity : definition.params.length = values.length)
    (canonical : (definition.params.zip values).all
      (fun pair => Denote.errorScalarValueValid pair.1 pair.2) = true)
    (scalarTypes : definition.params.mapM Denote.errorScalarType = some types) :
    SourceSemantics.typedErrorRevertResult fields runtime name args =
      .revertWithData ((Denote.wordBytes (hash name types)).take 4 ++
        values.flatMap Denote.wordBytes) := by
  simp [SourceSemantics.typedErrorRevertResult, evaluated, Denote.customErrorBytes,
    resolved, arity, canonical, scalarTypes, hash]

end Compiler.Proofs.IRGeneration.SourceCustomErrorBytes

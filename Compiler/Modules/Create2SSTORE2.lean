/-
  Compiler.Modules.Create2SSTORE2: CREATE2 and SSTORE2-style code-as-data helpers.

  These ECMs expose the low-level source surface needed by code-as-data
  contracts without requiring downstream projects to patch generated Yul.
-/

import Compiler.ECM
import Compiler.CompilationModel

namespace Compiler.Modules.Create2SSTORE2

open Compiler.Yul
open Compiler.ECM

/-- Deploy already-prepared initcode with `create2(value, offset, size, salt)` and
    bind the deployed address word. The caller owns initcode layout and salt
    semantics; this module only lowers the EVM mechanic. -/
def deployModule (resultVar : String) : ExternalCallModule where
  name := "create2Deploy"
  numArgs := 4
  resultVars := [resultVar]
  writesState := true
  readsState := false
  axioms := ["create2_initcode_layout", "create2_address_derivation"]
  compile := fun _ctx args => do
    match args with
    | [value, offset, size, salt] =>
        pure [YulStmt.let_ resultVar (YulExpr.call "create2" [value, offset, size, salt])]
    | _ =>
        throw s!"create2Deploy expects 4 arguments, got {args.length}"

/-- Copy deployed bytecode into memory with `extcodecopy(pointer, dest, offset, size)`.
    This is the read half of SSTORE2-style code-as-data patterns. -/
def readCodeModule : ExternalCallModule where
  name := "sstore2ReadCode"
  numArgs := 4
  writesState := false
  readsState := true
  axioms := ["sstore2_pointer_code_layout"]
  compile := fun _ctx args => do
    match args with
    | [pointer, destOffset, codeOffset, size] =>
        pure [YulStmt.exprStmt (YulExpr.call "extcodecopy" [pointer, destOffset, codeOffset, size])]
    | _ =>
        throw s!"sstore2ReadCode expects 4 arguments, got {args.length}"

end Compiler.Modules.Create2SSTORE2

import Compiler.Codegen
import Compiler.CompilationModel
import Compiler.CompilationModel.TrustSurface
import Compiler.Modules.Calls
import Compiler.Yul.PrettyPrint

namespace Compiler.Modules.CallsTest

open Compiler
open Compiler.CompilationModel

private def contains (haystack needle : String) : Bool :=
  let h := haystack.toList
  let n := needle.toList
  if n.isEmpty then true
  else
    let rec go : List Char → Bool
      | [] => false
      | c :: cs =>
          if (c :: cs).take n.length == n then true
          else go cs
    go h

private def expectTrue (label : String) (ok : Bool) : IO Unit := do
  if !ok then
    throw (IO.userError s!"✗ {label}")
  IO.println s!"✓ {label}"

private def selectorsFor (spec : CompilationModel) : List Nat :=
  List.range (spec.functions.filter (fun fn =>
    !fn.isInternal && fn.name != "fallback" && fn.name != "receive")).length

private def expectCompileErrorContains (label : String)
    (spec : CompilationModel) (needle : String) : IO Unit := do
  match Compiler.CompilationModel.compile spec (selectorsFor spec) with
  | .ok _ => throw (IO.userError s!"✗ {label}: expected compile error containing '{needle}'")
  | .error err =>
      if !contains err needle then
        throw (IO.userError s!"✗ {label}: expected error containing '{needle}', got '{err}'")
      IO.println s!"✓ {label}"

private def expectCompileToYul (label : String) (spec : CompilationModel) : IO String := do
  match Compiler.CompilationModel.compile spec (selectorsFor spec) with
  | .ok ir =>
      IO.println s!"✓ {label}"
      pure (Compiler.Yul.render (Compiler.emitYul ir))
  | .error err =>
      throw (IO.userError s!"✗ {label}: compile failed: {err}")

private def selfDelegateMulticallBytesSmokeSpec : CompilationModel := {
  name := "SelfDelegateMulticallBytesSmoke"
  fields := []
  «constructor» := none
  functions := [
    { name := "multicall"
      params := [
        { name := "calls", ty := ParamType.array ParamType.bytes }
      ]
      returnType := none
      body := [
        Compiler.Modules.Calls.selfDelegateMulticallBytes "calls",
        Stmt.stop
      ]
    }
  ]
}

private def selfDelegateMulticallBytesBadAritySpec : CompilationModel := {
  name := "SelfDelegateMulticallBytesBadArity"
  fields := []
  «constructor» := none
  functions := [
    { name := "bad"
      params := [
        { name := "calls", ty := ParamType.array ParamType.bytes }
      ]
      returnType := none
      body := [
        Stmt.ecm (Compiler.Modules.Calls.selfDelegateMulticallBytesModule "calls")
          [Expr.arrayLength "calls"],
        Stmt.stop
      ]
    }
  ]
}

private def selfDelegateMulticallBytesEmptyParamSpec : CompilationModel := {
  name := "SelfDelegateMulticallBytesEmptyParam"
  fields := []
  «constructor» := none
  functions := [
    { name := "bad"
      params := [
        { name := "calls", ty := ParamType.array ParamType.bytes }
      ]
      returnType := none
      body := [
        Compiler.Modules.Calls.selfDelegateMulticallBytes "",
        Stmt.stop
      ]
    }
  ]
}

private def selfDelegateMulticallBytesViewRejectedSpec : CompilationModel := {
  name := "SelfDelegateMulticallBytesViewRejected"
  fields := []
  «constructor» := none
  functions := [
    { name := "multicall"
      params := [
        { name := "calls", ty := ParamType.array ParamType.bytes }
      ]
      returnType := none
      isView := true
      body := [
        Compiler.Modules.Calls.selfDelegateMulticallBytes "calls",
        Stmt.stop
      ]
    }
  ]
}

unsafe def runTests : IO Unit := do
  let yul ←
    expectCompileToYul "self-delegate multicall bytes smoke spec" selfDelegateMulticallBytesSmokeSpec
  expectTrue "self-delegate multicall walks bytes[] calldata offsets"
    (contains yul "for {" &&
      contains yul "let __mc_i := 0" &&
      contains yul "lt(__mc_i, calls_length)" &&
      contains yul "let __mc_rel_offset := calldataload(add(calls_data_offset, mul(__mc_i, 32)))" &&
      contains yul "if lt(__mc_rel_offset, mul(calls_length, 32)) {" &&
      contains yul "if gt(__mc_rel_offset, sub(not(0), calls_data_offset)) {" &&
      contains yul "let __mc_head_offset := add(calls_data_offset, __mc_rel_offset)" &&
      contains yul "let __mc_data_size := calldataload(__mc_head_offset)" &&
      contains yul "let __mc_data_offset := add(__mc_head_offset, 32)")
  expectTrue "self-delegate multicall copies each bytes payload and delegatecalls address()"
    (contains yul "calldatacopy(__mc_ptr, __mc_data_offset, __mc_data_size)" &&
      contains yul "delegatecall(gas(), address(), __mc_ptr, __mc_data_size, 0, 0)")
  expectTrue "self-delegate multicall forwards revert returndata exactly"
    (contains yul "let __mc_rds := returndatasize()" &&
      contains yul "returndatacopy(0, 0, __mc_rds)" &&
      contains yul "revert(0, __mc_rds)")
  expectCompileErrorContains
    "self-delegate multicall ECM rejects invalid argument counts"
    selfDelegateMulticallBytesBadAritySpec
    "uses ECM 'selfDelegateMulticallBytes' with 1 arguments but it expects 0"
  expectCompileErrorContains
    "self-delegate multicall rejects empty parameter names"
    selfDelegateMulticallBytesEmptyParamSpec
    "selfDelegateMulticallBytes: arrayParam must be non-empty"
  expectCompileErrorContains
    "self-delegate multicall remains rejected from view functions"
    selfDelegateMulticallBytesViewRejectedSpec
    "function 'multicall' is marked view but writes state"
  let report := emitTrustReportJson [selfDelegateMulticallBytesSmokeSpec]
  expectTrue "self-delegate multicall trust report surfaces scoped multicall assumption without proxy boundary"
    (contains report "\"module\":\"selfDelegateMulticallBytes\"" &&
      contains report "\"assumption\":\"self_delegate_multicall_bytes_revert_bubbling\"" &&
      contains report "\"boundaryClass\":\"abiBoundary\"" &&
      contains report "\"notModeledProxyUpgradeability\":[]" &&
      ! (contains report "\"delegatecall\""))

#eval! runTests

end Compiler.Modules.CallsTest

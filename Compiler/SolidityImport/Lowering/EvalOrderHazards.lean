import Lean
import Compiler.SolidityImport.ExprHelpers

/-!
# Evaluation-order hazards between sibling expressions

Moved unchanged from `Import.lean` (#2837): the analyses the importer uses to
decide whether the evaluation order of sibling expressions is observable, through
stateful calls (`statefulCallIn`) or through memory that one sibling may write and
the other reads (`memoryWriteOrderHazard`). solc's order differs between
pipelines, so the importer fails closed on such siblings.
-/

open Lean

namespace Compiler.CompilationModel.SolidityImport.Lowering

/-- Stateful calls in sibling expressions need an independently validated order.
    A non-view declaration is conservatively treated as stateful even when its
    current body happens not to write. Unknown calls retain their usual rejection. -/
partial def statefulCallIn (j : Json) (env : Env) : Bool :=
  match j with
  | .arr xs => xs.any (fun child => statefulCallIn child env)
  | .obj o =>
      let isStateful (fid : Nat) : Bool :=
        match env.funs.find? fid with
        | some fn => ![some "pure", some "view"].contains (optStr fn "stateMutability")
        | none => false
      let own := if optStr j "nodeType" == some "FunctionCall" &&
          optStr j "kind" == some "functionCall" then
        let callee := (field? j "expression").getD Json.null
        match (field? callee "referencedDeclaration").bind (·.getNat?.toOption) with
        | some id =>
          let ptrStateful : Bool :=
            match env.fnPtrs.find? id with
            | some (.direct fid) => isStateful fid
            | some (.branch _ tFid fFid) => isStateful tFid || isStateful fFid
            | none => false
          ptrStateful || ((effectCallTarget? env [] callee id).map isStateful).getD true
        | none => false
      else if optStr j "nodeType" == some "BinaryOperation" ||
          optStr j "nodeType" == some "UnaryOperation" then
        match (field? j "function").bind (fun id => id.getNat?.toOption) with
        | some id =>
          let targetId := resolveInContracts env env.linearizedBases.toList id |>.getD id
          isStateful targetId
        | none => false
      else false
      o.foldl (fun found _ child => found || statefulCallIn child env) own
  | _ => false

/-- `T[N] memory`, `T[] memory`, `bytes`/`string memory` and memory structs are
    passed to internal functions by reference (`typeIdentifier` `…_memory_ptr`). -/
def memoryReferenceNode (j : Json) : Bool :=
  ((field? j "typeDescriptions").bind (optStr · "typeIdentifier")).any (·.endsWith "_memory_ptr")

/-- Some subexpression of `j` is a by-reference memory value, so evaluating `j`
    can read memory that an internal callee receiving that reference may write. -/
partial def memoryReferenceIn (j : Json) : Bool :=
  match j with
  | .arr xs => xs.any memoryReferenceIn
  | .obj o => memoryReferenceNode j || o.foldl (fun found _ child => found || memoryReferenceIn child) false
  | _ => false

/-- Yul `j` may write memory: a memory-writing builtin (`mstore`, the `*copy`
    family, calls returning into memory). A missing Yul AST counts as writing. -/
partial def yulMemoryWriteIn (j : Json) : Bool :=
  match j with
  | .null => true
  | .arr xs => xs.any yulMemoryWriteIn
  | .obj o =>
      let own := optStr j "nodeType" == some "YulFunctionCall" &&
        (((field? j "functionName").bind (optStr · "name")).any fun name =>
          ["mstore", "mstore8", "mcopy", "calldatacopy", "codecopy", "extcodecopy",
            "returndatacopy", "call", "callcode", "delegatecall", "staticcall"].contains name)
      own || o.foldl (fun found _ child => found || (child matches .obj _ | .arr _) && yulMemoryWriteIn child) false
  | _ => false

/-- `j` may write memory visible outside the call it occurs in: an internal call
    with a by-reference memory argument or receiver whose callee (transitively)
    assigns, deletes or increments through a memory reference, writes memory
    in inline assembly (`yulMemoryWriteIn`), or has modifiers. `pure`/`view` callees count: `statefulCallIn`
    does not see these writes. Unresolved callees and function pointers count
    as writing; `seen` cuts recursion. -/
partial def memoryWriteIn (j : Json) (env : Env) (seen : List Nat := []) : Bool :=
  match j with
  | .arr xs => xs.any (memoryWriteIn · env seen)
  | .obj o =>
      let kind := optStr j "nodeType"
      let op := optStr j "operator" |>.getD ""
      let own :=
        if kind == some "InlineAssembly" then yulMemoryWriteIn ((field? j "AST").getD Json.null)
        else if kind == some "Assignment" then
          ((field? j "leftHandSide").map memoryReferenceIn).getD true
        else if kind == some "UnaryOperation" && ["++", "--", "delete"].contains op then
          ((field? j "subExpression").map memoryReferenceIn).getD true
        else if kind == some "FunctionCall" && optStr j "kind" == some "functionCall" then
          let callee := (field? j "expression").getD Json.null
          let internal := ((field? callee "typeDescriptions").bind (optStr · "typeIdentifier")).any
            (·.startsWith "t_function_internal_")
          let args := match field? j "arguments" with
            | some (.arr xs) => xs
            | _ => #[]
          let receiver := optStr callee "nodeType" == some "MemberAccess" &&
            ((field? callee "expression").map memoryReferenceNode).getD false
          if !internal || !(receiver || args.any memoryReferenceNode) then false
          else match (field? callee "referencedDeclaration").bind (·.getNat?.toOption) with
            | none => true
            | some id =>
              if env.fnPtrs.contains id then true
              else
                match effectCallTarget? env seen callee id with
                | none => true
                | some targetId =>
                  if seen.contains targetId then false
                  else match env.funs.find? targetId with
                    | none => true
                    | some fn =>
                      let hasModifiers := match field? fn "modifiers" with
                        | some (.arr ms) => !ms.isEmpty
                        | _ => false
                      hasModifiers ||
                        memoryWriteIn ((field? fn "body").getD Json.null) env (targetId :: seen)
        else false
      own || o.foldl (fun found _ child => found || memoryWriteIn child env seen) false
  | _ => false

/-- Evaluation order between sibling expressions `a` and `b` is observable
    through memory: one may write memory (`memoryWriteIn`) that the other reads.
    solc's order differs between pipelines for binary operands and the importer
    fixes one order, so such siblings fail closed. -/
def memoryWriteOrderHazard (a b : Json) (env : Env) : Bool :=
  (memoryWriteIn a env && memoryReferenceIn b) || (memoryWriteIn b env && memoryReferenceIn a)

end Compiler.CompilationModel.SolidityImport.Lowering

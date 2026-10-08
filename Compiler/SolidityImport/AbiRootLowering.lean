import Compiler.SolidityImport.AbiSchema
import Compiler.SolidityImport.AbiLowering

namespace Compiler.CompilationModel.SolidityImport.AbiRootLowering
open AbiSchema AbiLowering

/-- Every generated name must be reserved by the importer before lowering the
source body. The schema was checked separately; no type coercion occurs here. -/
structure Plan where
  calldataPointer : String
  memoryPointer : String
  names : List String
  body : List Stmt

/-- Materialize a schema-checked struct from a validated calldata pointer into
freshly allocated memory, returning the memory pointer, reserved binding names,
and statements. Matches solc's `convert_t_struct_calldata_ptr_to_t_struct_memory_ptr`. -/
def materializeFromCalldata (calldataPointer stem : String)
    (schema : List Member) : Plan := Id.run do
  let memoryPointer := stem ++ "_memory"
  let nextPointer := stem ++ "_next"
  let mut names := [memoryPointer, nextPointer]
  let mut body : List Stmt := [
    .letVar memoryPointer (.mload (.literal 64)),
    .letVar nextPointer (.add (.localVar memoryPointer) (.literal (32*schema.length))),
    .ite (.le (.localVar nextPointer) (.literal (2^64-1))) [] [.panicCode (.literal 0x41)],
    .ite (.ge (.localVar nextPointer) (.localVar memoryPointer)) [] [.panicCode (.literal 0x41)],
    .mstore (.literal 64) (.localVar nextPointer)]
  for (member, i) in schema.zipIdx do
    let destination := Expr.add (.localVar memoryPointer) (.literal (32*i))
    match member with
    | .scalar field =>
      let value := Expr.calldataload (.add (.localVar calldataPointer) (.literal (32*i)))
      let bound := SolidityAbi.scalarBound field.kind
      if bound < 2^256 then body := body ++ [guard (.lt value (.literal bound))]
      body := body ++ [.mstore destination value]
    | .scalarArray field =>
      let memberStem := stem ++ "_array" ++ toString i
      let arrayPointer := memberStem ++ "_memory"
      let header := memberStem ++ "_header"
      let length := memberStem ++ "_length"
      let data := memberStem ++ "_data"
      let next := memberStem ++ "_next"
      let elementStem := memberStem ++ "_element"
      names := names ++ [arrayPointer, header, length, data, next, elementStem ++ "_index"]
      body := body ++ [.letVar arrayPointer (.mload (.literal 64))] ++
        memoryStaticArrayHead (.localVar calldataPointer) (.localVar arrayPointer) i 1
          header length data next ++
        materializeStaticScalarArray (.localVar data) (.localVar length)
          (.localVar arrayPointer) (.localVar next) elementStem field.kind ++
        [.mstore destination (.localVar arrayPointer)]
    | .structArray _ fields =>
      let memberStem := stem ++ "_array" ++ toString i
      let arrayPointer := memberStem ++ "_memory"
      let header := memberStem ++ "_header"
      let length := memberStem ++ "_length"
      let data := memberStem ++ "_data"
      let next := memberStem ++ "_next"
      let elementStem := memberStem ++ "_element"
      names := names ++ [arrayPointer, header, length, data, next,
        elementStem ++ "_index", elementStem ++ "_element",
        elementStem ++ "_next", elementStem ++ "_source"]
      body := body ++ [.letVar arrayPointer (.mload (.literal 64))] ++
        memoryStaticArrayHead (.localVar calldataPointer) (.localVar arrayPointer) i fields.length
          header length data next ++
        materializeStaticStructArray (.localVar data) (.localVar length)
          (.localVar arrayPointer) (.localVar next) elementStem (fields.map (·.kind)) ++
        [.mstore destination (.localVar arrayPointer)]
  return { calldataPointer, memoryPointer, names, body }

/-- Materialize a single flat static struct element from a calldata pointer
expression into freshly allocated memory, returning the memory pointer,
reserved binding names, and statements. -/
def materializeElementFromCalldata (source : Expr) (stem : String)
    (fields : List ScalarField) : String × List String × List Stmt := Id.run do
  let sourceBinding := stem ++ "_source"
  let memoryPointer := stem ++ "_memory"
  let nextPointer := stem ++ "_next"
  let names := [sourceBinding, memoryPointer, nextPointer]
  let mut body : List Stmt := [
    .letVar sourceBinding source,
    guard (.logicalNot (.slt (.sub .calldatasize (.localVar sourceBinding))
      (.literal (32*fields.length)))),
    .letVar memoryPointer (.mload (.literal 64)),
    .letVar nextPointer (.add (.localVar memoryPointer) (.literal (32*fields.length))),
    .ite (.le (.localVar nextPointer) (.literal (2^64-1))) [] [.panicCode (.literal 0x41)],
    .ite (.ge (.localVar nextPointer) (.localVar memoryPointer)) [] [.panicCode (.literal 0x41)],
    .mstore (.literal 64) (.localVar nextPointer)]
  for (field, i) in fields.zipIdx do
    let value := Expr.calldataload (.add (.localVar sourceBinding) (.literal (32*i)))
    let bound := SolidityAbi.scalarBound field.kind
    if bound < 2^256 then body := body ++ [guard (.lt value (.literal bound))]
    body := body ++ [.mstore (.add (.localVar memoryPointer) (.literal (32*i))) value]
  return (memoryPointer, names, body)

/-- Build the entry decoder in declaration order. Memory allocation begins at
the current free pointer, initialized once by the function prelude. Calldata
only validates the root head here; field checks remain at the actual reads. -/
def root (stem : String) (rootHeadWords parameterHeadWord : Nat)
    (schema : List Member) (inMemory : Bool) : Plan := Id.run do
  let calldataPointer := stem ++ "_calldata"
  let memoryPointer := stem ++ "_memory"
  let names := [calldataPointer]
  let body := tupleHead calldataPointer rootHeadWords parameterHeadWord schema.length
  if !inMemory then return { calldataPointer, memoryPointer, names, body }
  let mat := materializeFromCalldata calldataPointer stem schema
  return {
    calldataPointer
    memoryPointer := mat.memoryPointer
    names := names ++ mat.names
    body := body ++ mat.body
  }

/-- Scalar field reads preserve the eager-memory/lazy-calldata distinction.
The importer must first resolve a scalar member, rather than treating an array
pointer as a scalar. No fallback for an unsupported member is provided. -/
def scalarRead (plan : Plan) (inMemory : Bool) (index : Nat)
    (kind : SolidityAbi.ScalarKind) : List Stmt × Expr :=
  if inMemory then ([], .mload (.add (.localVar plan.memoryPointer) (.literal (32*index))))
  else
    let value := Expr.calldataload (.add (.localVar plan.calldataPointer) (.literal (32*index)))
    let bound := SolidityAbi.scalarBound kind
    (if bound < 2^256 then [guard (.lt value (.literal bound))] else [], value)

end Compiler.CompilationModel.SolidityImport.AbiRootLowering

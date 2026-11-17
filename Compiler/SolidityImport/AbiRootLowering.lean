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
  deriving Inhabited

/-- Materialize a schema-checked struct from a validated calldata pointer into
freshly allocated memory, returning the memory pointer, reserved binding names,
and statements. Matches solc's `convert_t_struct_calldata_ptr_to_t_struct_memory_ptr`. -/
def materializeFromCalldata (calldataPointer stem : String)
    (schema : List Member) (fuel : Nat := 16) : Plan :=
  match fuel with
  | 0 => { calldataPointer, memoryPointer := stem ++ "_memory", names := [], body := [] }
  | fuel + 1 => Id.run do
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
      | .bytesField _ _ =>
        let memberStem := stem ++ "_bytes" ++ toString i
        let bytesPointer := memberStem ++ "_memory"
        let header := memberStem ++ "_header"
        let length := memberStem ++ "_length"
        let data := memberStem ++ "_data"
        let next := memberStem ++ "_next"
        let copyIndex := memberStem ++ "_index"
        names := names ++ [bytesPointer, header, length, data, next, copyIndex]
        body := body ++
          memoryBytesField (.localVar calldataPointer) i
            bytesPointer header length data next copyIndex ++
          [.mstore destination (.localVar bytesPointer)]
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
      | .bytesArray _ =>
        -- `abi_decode_t_array$_t_bytes_memory_ptr_$dyn_memory_ptr`: the
        -- pointer array, then each element's eager `bytes` copy.
        let memberStem := stem ++ "_array" ++ toString i
        let arrayPointer := memberStem ++ "_memory"
        let header := memberStem ++ "_header"
        let length := memberStem ++ "_length"
        let data := memberStem ++ "_data"
        let next := memberStem ++ "_next"
        let index := memberStem ++ "_index"
        let elementStem := memberStem ++ "_bytes"
        let element := elementStem ++ "_memory"
        let elementNames := [element, elementStem ++ "_header", elementStem ++ "_length",
          elementStem ++ "_data", elementStem ++ "_next", elementStem ++ "_index"]
        names := names ++ [arrayPointer, header, length, data, next, index] ++ elementNames
        let slot := Expr.add (.localVar data) (.mul (.localVar index) (.literal 32))
        body := body ++ [.letVar arrayPointer (.mload (.literal 64))] ++
          memoryStaticArrayHead (.localVar calldataPointer) (.localVar arrayPointer) i 1
            header length data next ++
          [.mstore (.localVar arrayPointer) (.localVar length),
           .mstore (.literal 64) (.localVar next),
           .forEach index (.localVar length) (
             memoryBytesAt (.localVar data) slot element (elementStem ++ "_header")
               (elementStem ++ "_length") (elementStem ++ "_data") (elementStem ++ "_next")
               (elementStem ++ "_index") ++
             [.mstore (.add (.add (.localVar arrayPointer) (.literal 32))
               (.mul (.localVar index) (.literal 32))) (.localVar element)]),
           .mstore destination (.localVar arrayPointer)]
      | .nestedStruct _ _ _ _ subSchema =>
        let memberStem := stem ++ "_struct" ++ toString i
        let subCalldata := memberStem ++ "_calldata"
        let subMat := materializeFromCalldata subCalldata memberStem subSchema fuel
        names := names ++ [subCalldata] ++ subMat.names
        body := body ++
          memoryNestedStructHead (.localVar calldataPointer) i subSchema.length subCalldata ++
          subMat.body ++
          [.mstore destination (.localVar subMat.memoryPointer)]
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

/-- Unread head word standing for a root parameter before a `rootArray` view. -/
def rootArrayPlaceholder : Member := .scalar ⟨"", .uint ⟨31, by decide⟩⟩

/-- `w` placeholders, then `member`: the root argument tuple seen as a struct
whose word `w` is the root array parameter `member`. -/
def rootArraySchema (word : Nat) (member : Member) : List Member :=
  List.replicate word rootArrayPlaceholder ++ [member]

/-- Entry decoder of a root `S[]` parameter viewed as the last member of
`schema` (see `rootArraySchema`) in the root argument tuple, whose pointer is
4 and against which ABI offsets are relative. solc decodes root arrays
eagerly: calldata gets the full array-head checks of `abi_decode_t_array_*_calldata_ptr`
at entry (element reads re-check lazily), memory the same eager copy as a
struct-array member (`memoryStaticArrayHead` + `materializeStaticStructArray`). -/
def rootArray (stem : String) (rootHeadWords : Nat) (schema : List Member)
    (inMemory : Bool) : Plan :=
  let calldataPointer := stem ++ "_calldata"
  let tuple := Stmt.letVar calldataPointer (.literal 4)
  if inMemory then
    let mat := materializeFromCalldata calldataPointer stem schema
    { calldataPointer
      memoryPointer := mat.memoryPointer
      names := calldataPointer :: mat.names
      body := [guard (.logicalNot (.slt (.sub .calldatasize (.literal 4))
          (.literal (32*rootHeadWords)))), tuple] ++ mat.body }
  else
    let word := schema.length - 1
    let elementWords := match schema.getLast? with
      | some (.structArray _ fields) => fields.length
      | _ => 1
    let offset := stem ++ "_offset"
    let header := stem ++ "_header"
    let length := stem ++ "_length"
    let data := stem ++ "_data"
    { calldataPointer
      memoryPointer := stem ++ "_memory"
      names := [calldataPointer, offset, header, length, data]
      body := scalarArrayCalldataHead offset header length data rootHeadWords (4 + 32*word)
          elementWords ++ [tuple] }

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

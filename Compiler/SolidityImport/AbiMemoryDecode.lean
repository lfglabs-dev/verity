import Compiler.SolidityImport.AbiSchema
import Compiler.SolidityImport.AbiLowering

namespace Compiler.CompilationModel.SolidityImport.AbiMemoryDecode
open AbiSchema AbiLowering

/-!
`abi.decode(data, (S))` of a schema-checked dynamic struct from a `bytes memory`
buffer, as executable model code matching solc's `abi_decode_*_fromMemory`
functions: signed remaining-size checks against the buffer end, 64-bit offset
bounds, eager allocation (`Panic(0x41)` on length or free-pointer overflow)
before the payload-truncation check, and a zero-byte revert for every other
malformation. The struct is materialized in solc's memory layout, so the
importer's memory readers and ABI encoder apply unchanged.
-/

/-- Members decoded here: unsigned/enum scalars, dynamic `bytes`, and dynamic
arrays of unsigned scalars or of flat scalar structs. -/
def supportedMember : Member → Bool
  | .scalar _ | .bytesField _ false | .scalarArray _ | .structArray _ _ => true
  | .bytesField _ true | .nestedStruct _ _ _ _ _ | .bytesArray _ => false

/-- Every generated name and statement. Names must be reserved by the importer. -/
structure Plan where
  memoryPointer : String
  names : List String
  body : List Stmt
  deriving Inhabited

private def allocationGuard (condition : Expr) : Stmt :=
  .ite condition [] [.panicCode (.literal 0x41)]

/-- solc's `allocate_memory(size)` for a word-multiple `size`. -/
def allocate (pointer next : String) (size : Expr) : List Stmt :=
  [ .letVar pointer (.mload (.literal 64))
  , .letVar next (.add (.localVar pointer) size)
  , allocationGuard (.le (.localVar next) (.literal (2^64-1)))
  , allocationGuard (.ge (.localVar next) (.localVar pointer))
  , .mstore (.literal 64) (.localVar next) ]

/-- `validator_revert_t_<scalar>`: a non-canonical word reverts with no data. -/
def scalarChecks (kind : SolidityAbi.ScalarKind) (value : Expr) : List Stmt :=
  let bound := SolidityAbi.scalarBound kind
  if bound < 2^256 then [guard (.lt value (.literal bound))] else []

/-- `abi_decode_t_struct_fromMemory` of a flat static struct at `head`: the
remaining-size check, a fresh allocation bound to `pointer`, and every field
validated and stored in declaration order. -/
def flatStruct (head dataEnd : Expr) (pointer next : String)
    (fields : List SolidityAbi.ScalarKind) : List Stmt :=
  [guard (.logicalNot (.slt (.sub dataEnd head) (.literal (32*fields.length))))] ++
  allocate pointer next (.literal (32*fields.length)) ++
  fields.zipIdx.flatMap fun (kind, i) =>
    let value := Expr.mload (.add head (.literal (32*i)))
    scalarChecks kind value ++ [.mstore (.add (.localVar pointer) (.literal (32*i))) value]

/-- Names bound by `array` for the member stem `stem`. -/
def arrayNames (stem : String) : List String :=
  [stem ++ "_offset", stem ++ "_header", stem ++ "_length", stem ++ "_memory",
   stem ++ "_next", stem ++ "_data", stem ++ "_index", stem ++ "_source",
   stem ++ "_element", stem ++ "_element_next"]

/-- `abi_decode_t_array_fromMemory` of the dynamic array whose offset is the
member word `memberWord` of the struct at `head`. `fields` is `none` for a
scalar array of `kind` and the element fields for an array of flat structs,
whose payload holds pointers to separately allocated elements. -/
def array (head dataEnd : Expr) (memberWord : Nat) (stem : String)
    (kind : SolidityAbi.ScalarKind) (fields : Option (List SolidityAbi.ScalarKind)) :
    List Stmt :=
  let offset := Expr.localVar (stem ++ "_offset")
  let header := Expr.localVar (stem ++ "_header")
  let length := Expr.localVar (stem ++ "_length")
  let arrayPointer := Expr.localVar (stem ++ "_memory")
  let data := Expr.localVar (stem ++ "_data")
  let index := Expr.localVar (stem ++ "_index")
  let elementWords := match fields with
    | some fields => fields.length
    | none => 1
  let slot := Expr.add (.add arrayPointer (.literal 32)) (.mul index (.literal 32))
  let body : List Stmt := match fields with
    | none =>
        let value := Expr.mload (.add data (.mul index (.literal 32)))
        scalarChecks kind value ++ [.mstore slot value]
    | some fields =>
        [.letVar (stem ++ "_source") (.add data (.mul index (.literal (32*fields.length))))] ++
        flatStruct (.localVar (stem ++ "_source")) dataEnd (stem ++ "_element")
          (stem ++ "_element_next") fields ++
        [.mstore slot (.localVar (stem ++ "_element"))]
  [ .letVar (stem ++ "_offset") (.mload (.add head (.literal (32*memberWord))))
  , guard (.le offset (.literal (2^64-1)))
  , .letVar (stem ++ "_header") (.add head offset)
  , guard (.slt (.add header (.literal 31)) dataEnd)
  , .letVar (stem ++ "_length") (.mload header)
  , allocationGuard (.le length (.literal (2^64-1))) ] ++
  allocate (stem ++ "_memory") (stem ++ "_next") (.add (.mul length (.literal 32)) (.literal 32)) ++
  [ .mstore arrayPointer length
  , .letVar (stem ++ "_data") (.add header (.literal 32))
  , guard (.logicalNot (.gt (.add data (.mul length (.literal (32*elementWords)))) dataEnd))
  , .forEach (stem ++ "_index") length body ]

/-- Names bound by `bytes` for the member stem `stem`. -/
def bytesNames (stem : String) : List String :=
  [stem ++ "_offset", stem ++ "_header", stem ++ "_length", stem ++ "_memory",
   stem ++ "_next", stem ++ "_data", stem ++ "_index"]

/-- `abi_decode_t_bytes_memory_ptr` (from memory or calldata) for the `bytes`
member at word `memberWord` of the struct at `head`: 64-bit offset check,
signed length-word availability, eager allocation (`Panic(0x41)` on length or
free-pointer overflow), payload truncation check, word copy, and trailing zero
cleanup. -/
def bytes (head dataEnd : Expr) (memberWord : Nat) (stem : String)
    (fromCalldata : Bool := false) : List Stmt :=
  let load (addr : Expr) : Expr := if fromCalldata then .calldataload addr else .mload addr
  let offset := Expr.localVar (stem ++ "_offset")
  let header := Expr.localVar (stem ++ "_header")
  let length := Expr.localVar (stem ++ "_length")
  let bytesPointer := Expr.localVar (stem ++ "_memory")
  let data := Expr.localVar (stem ++ "_data")
  let index := Expr.localVar (stem ++ "_index")
  let alignedSize := Expr.bitAnd
    (.add (.add length (.literal 32)) (.literal 31))
    (.bitNot (.literal 31))
  let wordCount := Expr.div (.add length (.literal 31)) (.literal 32)
  [ .letVar (stem ++ "_offset") (load (.add head (.literal (32*memberWord))))
  , guard (.le offset (.literal (2^64-1)))
  , .letVar (stem ++ "_header") (.add head offset)
  , guard (.slt (.add header (.literal 31)) dataEnd)
  , .letVar (stem ++ "_length") (load header)
  , allocationGuard (.le length (.literal (2^64-1))) ] ++
  allocate (stem ++ "_memory") (stem ++ "_next") alignedSize ++
  [ .letVar (stem ++ "_data") (.add header (.literal 32))
  , guard (.logicalNot (.gt (.add data length) dataEnd))
  , .mstore bytesPointer length
  , .forEach (stem ++ "_index") wordCount
      [.mstore (.add (.add bytesPointer (.literal 32)) (.mul index (.literal 32)))
        (load (.add data (.mul index (.literal 32))))]
  , .mstore (.add (.add bytesPointer (.literal 32)) length) (.literal 0) ]

/-- `abi_decode_tuple_t_struct_fromMemory(base, dataEnd)` for a buffer already
checked to hold one head word: the struct offset, the struct's head size, a
fresh allocation bound to `stem_memory`, and every member in declaration order.
Only `supportedMember`s are decoded; the importer rejects every other schema. -/
def materialize (base dataEnd : Expr) (stem : String) (schema : List Member) : Plan :=
  let offset := stem ++ "_offset"
  let head := stem ++ "_head"
  let memoryPointer := stem ++ "_memory"
  let next := stem ++ "_next"
  let prefixStmts : List Stmt :=
    [ .letVar offset (.mload base)
    , guard (.le (.localVar offset) (.literal (2^64-1)))
    , .letVar head (.add base (.localVar offset))
    , guard (.logicalNot (.slt (.sub dataEnd (.localVar head)) (.literal (32*schema.length)))) ] ++
    allocate memoryPointer next (.literal (32*schema.length))
  let members : List (List String × List Stmt) := schema.zipIdx.map fun (member, i) =>
    let destination := Expr.add (.localVar memoryPointer) (.literal (32*i))
    let memberStem := stem ++ "_array" ++ toString i
    let bytesStem := stem ++ "_bytes" ++ toString i
    match member with
    | .scalar field =>
        let value := Expr.mload (.add (.localVar head) (.literal (32*i)))
        ([], scalarChecks field.kind value ++ [.mstore destination value])
    | .bytesField _ false =>
        (bytesNames bytesStem,
          bytes (.localVar head) dataEnd i bytesStem false ++
            [.mstore destination (.localVar (bytesStem ++ "_memory"))])
    | .scalarArray field =>
        (arrayNames memberStem,
          array (.localVar head) dataEnd i memberStem field.kind none ++
            [.mstore destination (.localVar (memberStem ++ "_memory"))])
    | .structArray _ fields =>
        (arrayNames memberStem,
          array (.localVar head) dataEnd i memberStem .bool (some (fields.map (·.kind))) ++
            [.mstore destination (.localVar (memberStem ++ "_memory"))])
    | .bytesField _ true | .nestedStruct _ _ _ _ _ | .bytesArray _ => ([], [])
  { memoryPointer
    names := [offset, head, memoryPointer, next] ++ members.flatMap (·.1)
    body := prefixStmts ++ members.flatMap (·.2) }

/-- `abi_decode_tuple_t_struct(base, dataEnd)` from a `bytes calldata` slice
already checked to hold one head word, materializing a `bytes`-member struct
into freshly allocated memory with the same `names` layout as `materialize`. -/
def materializeFromCalldata (base dataEnd : Expr) (stem : String) (schema : List Member) : Plan :=
  let offset := stem ++ "_offset"
  let head := stem ++ "_head"
  let memoryPointer := stem ++ "_memory"
  let next := stem ++ "_next"
  let headSize := 32 * schema.length
  let prefixStmts : List Stmt :=
    [ .letVar offset (.calldataload base)
    , guard (.le (.localVar offset) (.literal (2^64-1)))
    , .letVar head (.add base (.localVar offset))
    , guard (.le (.add (.localVar head) (.literal headSize)) dataEnd) ] ++
    allocate memoryPointer next (.literal headSize)
  let members : List (List String × List Stmt) := schema.zipIdx.map fun (member, i) =>
    let destination := Expr.add (.localVar memoryPointer) (.literal (32*i))
    let bytesStem := stem ++ "_bytes" ++ toString i
    match member with
    | .scalar field =>
        let rawVal := Expr.calldataload (.add (.localVar head) (.literal (32*i)))
        ([], scalarChecks field.kind rawVal ++ [.mstore destination rawVal])
    | .bytesField _ false =>
        (bytesNames bytesStem,
          bytes (.localVar head) dataEnd i bytesStem true ++
            [.mstore destination (.localVar (bytesStem ++ "_memory"))])
    | _ => ([], [])
  { memoryPointer
    names := [offset, head, memoryPointer, next] ++ members.flatMap (·.1)
    body := prefixStmts ++ members.flatMap (·.2) }

end Compiler.CompilationModel.SolidityImport.AbiMemoryDecode

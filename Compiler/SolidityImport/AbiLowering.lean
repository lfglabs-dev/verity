import Compiler.CompilationModel
import Compiler.SolidityImport.SolidityAbi

namespace Compiler.CompilationModel.SolidityImport.AbiLowering

/-- ABI failure is an empty revert at external entry, where EIP-211 guarantees
an empty return-data buffer. Callers must retain the explicit local obligation
for these low-level operations, and may not move them after an external call. -/
def guard (condition : Expr) : Stmt := .ite condition [] [.revertReturndata]

/-- Source-compatible calldata tuple-head checks as executable model code.
The caller supplies a fresh binding name and a schema-checked head size/index.
This is a building block; generic parameter loading must not run a conflicting
decoder before this prelude when it is connected to imported entry points. -/
def tupleHead (binding : String) (rootHeadWords parameterIndex tupleHeadWords : Nat) : List Stmt :=
  let rawOffset := Expr.calldataload (.literal (4 + 32*parameterIndex))
  [ guard (.logicalNot (.slt (.sub .calldatasize (.literal 4)) (.literal (32*rootHeadWords))))
  , guard (.le rawOffset (.literal (2^64-1)))
  , .letVar binding (.add (.literal 4) rawOffset)
  , guard (.logicalNot (.slt (.sub .calldatasize (.localVar binding)) (.literal (32*tupleHeadWords)))) ]

/-- Source-compatible `bytes calldata` root parameter checks as executable model
code, matching `solc`'s `abi_decode_tuple` and `abi_decode_t_bytes_calldata_ptr`. -/
def bytesCalldataHead (offsetBinding headerBinding lengthBinding dataBinding : String)
    (rootHeadWords headOffset : Nat) : List Stmt :=
  [ guard (.logicalNot (.slt (.sub .calldatasize (.literal 4)) (.literal (32*rootHeadWords))))
  , .letVar offsetBinding (.calldataload (.literal headOffset))
  , guard (.le (.localVar offsetBinding) (.literal (2^64-1)))
  , .letVar headerBinding (.add (.literal 4) (.localVar offsetBinding))
  , guard (.slt (.add (.localVar headerBinding) (.literal 31)) .calldatasize)
  , .letVar lengthBinding (.calldataload (.localVar headerBinding))
  , guard (.le (.localVar lengthBinding) (.literal (2^64-1)))
  , .letVar dataBinding (.add (.localVar headerBinding) (.literal 32))
  , guard (.le (.add (.localVar dataBinding) (.localVar lengthBinding)) .calldatasize) ]

/-- Lazy calldata array header for statically sized elements. Invoke at the
source access, not at entry: source guards may precede malformed-array errors.
All three output names must be fresh and distinct. The schema must establish
positive `elementWords`; index bounds and scalar canonicality are separate.
Signed offset bounds deliberately permit backwards offsets, matching solc. -/
def staticArrayHead (tuplePointer : Expr) (memberWord elementWords : Nat)
    (addressBinding lengthBinding dataBinding : String) : List Stmt :=
  let relative := Expr.calldataload (.add tuplePointer (.literal (32*memberWord)))
  let available := Expr.sub (.sub .calldatasize tuplePointer) (.literal 31)
  [ guard (.slt relative available)
  , .letVar addressBinding (.add tuplePointer relative)
  , .letVar lengthBinding (.calldataload (.localVar addressBinding))
  , guard (.le (.localVar lengthBinding) (.literal (2^64-1)))
  , .letVar dataBinding (.add (.localVar addressBinding) (.literal 32))
  , guard (.logicalNot (.sgt (.localVar dataBinding)
      (.sub .calldatasize (.mul (.literal (32*elementWords)) (.localVar lengthBinding))))) ]

/-- Eager memory-array header checks. Unlike the calldata rule, allocation
failure produces Panic(0x41), before payload truncation is considered. This
returns the next free pointer in a fresh binding; materializing the array and
its static-struct elements remains separate. Names must be fresh and distinct. -/
def memoryStaticArrayHead (tuplePointer freePointer : Expr)
    (memberWord elementWords : Nat)
    (addressBinding lengthBinding dataBinding nextFreeBinding : String) : List Stmt :=
  let relative := Expr.calldataload (.add tuplePointer (.literal (32*memberWord)))
  let allocationGuard := fun condition =>
    Stmt.ite condition [] [.panicCode (.literal 0x41)]
  [ guard (.le relative (.literal (2^64-1)))
  , .letVar addressBinding (.add tuplePointer relative)
  , guard (.slt (.add (.localVar addressBinding) (.literal 31)) .calldatasize)
  , .letVar lengthBinding (.calldataload (.localVar addressBinding))
  , allocationGuard (.le (.localVar lengthBinding) (.literal (2^64-1)))
  , .letVar nextFreeBinding
      (.add freePointer (.mul (.literal 32) (.add (.localVar lengthBinding) (.literal 1))))
  , allocationGuard (.le (.localVar nextFreeBinding) (.literal (2^64-1)))
  , allocationGuard (.ge (.localVar nextFreeBinding) freePointer)
  , .letVar dataBinding (.add (.localVar addressBinding) (.literal 32))
  , guard (.le (.add (.localVar dataBinding)
      (.mul (.literal (32*elementWords)) (.localVar lengthBinding))) .calldatasize) ]

/-- Materialize an already validated array of flat static structs. Header
validation/allocation must have run first. The array contains pointers to
separately allocated structs, not inline struct words. The prefix must be fresh
against all source/parameter names; fields must come from a checked AST schema.
This helper owns the free-memory pointer at byte64 after the header allocation. -/
def materializeStaticStructArray (data length arrayPointer nextFree : Expr)
    (namePrefix : String) (fields : List SolidityAbi.ScalarKind) : List Stmt :=
  let index := namePrefix ++ "_index"
  let element := namePrefix ++ "_element"
  let next := namePrefix ++ "_next"
  let source := namePrefix ++ "_source"
  let allocationGuard := fun condition =>
    Stmt.ite condition [] [.panicCode (.literal 0x41)]
  let fieldStores := fields.zipIdx.flatMap fun (kind, i) =>
    let value := Expr.calldataload (.add (.localVar source) (.literal (32*i)))
    let bound := SolidityAbi.scalarBound kind
    let checks := if bound = 2^256 then [] else [guard (.lt value (.literal bound))]
    checks ++ [.mstore (.add (.localVar element) (.literal (32*i))) value]
  [ .mstore arrayPointer length
  , .mstore (.literal 64) nextFree
  , .forEach index length (
      [ .letVar source (.add data (.mul (.localVar index) (.literal (32*fields.length))))
      , guard (.logicalNot (.slt (.sub .calldatasize (.localVar source))
          (.literal (32*fields.length))))
      , .letVar element (.mload (.literal 64))
      , .letVar next (.add (.localVar element) (.literal (32*fields.length)))
      , allocationGuard (.le (.localVar next) (.literal (2^64-1)))
      , allocationGuard (.ge (.localVar next) (.localVar element))
      , .mstore (.literal 64) (.localVar next)
      , .mstore (.add (.add arrayPointer (.literal 32))
          (.mul (.localVar index) (.literal 32))) (.localVar element)
      ] ++ fieldStores) ]

/-- Fill a validated scalar-array allocation. Unlike an array of structs,
scalar elements occupy the array payload directly, without element pointers. -/
def materializeStaticScalarArray (data length arrayPointer nextFree : Expr)
    (namePrefix : String) (kind : SolidityAbi.ScalarKind) : List Stmt :=
  let index := namePrefix ++ "_index"
  let value := Expr.calldataload (.add data (.mul (.localVar index) (.literal 32)))
  let bound := SolidityAbi.scalarBound kind
  let checks := if bound = 2^256 then [] else [guard (.lt value (.literal bound))]
  [.mstore arrayPointer length,
   .mstore (.literal 64) nextFree,
   .forEach index length (checks ++
     [.mstore (.add (.add arrayPointer (.literal 32))
       (.mul (.localVar index) (.literal 32))) value])]

/-- Source-compatible `T[] calldata` root parameter checks as executable model
code, matching `solc`'s `abi_decode_tuple` and `abi_decode_t_array_*_calldata_ptr`. -/
def scalarArrayCalldataHead (offsetBinding headerBinding lengthBinding dataBinding : String)
    (rootHeadWords headOffset : Nat) : List Stmt :=
  [ guard (.logicalNot (.slt (.sub .calldatasize (.literal 4)) (.literal (32*rootHeadWords))))
  , .letVar offsetBinding (.calldataload (.literal headOffset))
  , guard (.le (.localVar offsetBinding) (.literal (2^64-1)))
  , .letVar headerBinding (.add (.literal 4) (.localVar offsetBinding))
  , guard (.slt (.add (.localVar headerBinding) (.literal 31)) .calldatasize)
  , .letVar lengthBinding (.calldataload (.localVar headerBinding))
  , guard (.le (.localVar lengthBinding) (.literal (2^64-1)))
  , .letVar dataBinding (.add (.localVar headerBinding) (.literal 32))
  , guard (.le (.add (.localVar dataBinding) (.mul (.localVar lengthBinding) (.literal 32))) .calldatasize) ]

/-- Source-compatible `T[] memory` root parameter header checks and materialization,
matching `solc`'s `abi_decode_t_array_*_memory_ptr`. -/
def scalarArrayMemoryHead
    (memoryPointer offsetBinding headerBinding lengthBinding dataBinding nextFreeBinding namePrefix : String)
    (rootHeadWords headOffset : Nat) (kind : SolidityAbi.ScalarKind) : List Stmt :=
  let freePointer := Expr.localVar memoryPointer
  let allocationGuard := fun condition =>
    Stmt.ite condition [] [.panicCode (.literal 0x41)]
  [ guard (.logicalNot (.slt (.sub .calldatasize (.literal 4)) (.literal (32*rootHeadWords))))
  , .letVar offsetBinding (.calldataload (.literal headOffset))
  , guard (.le (.localVar offsetBinding) (.literal (2^64-1)))
  , .letVar headerBinding (.add (.literal 4) (.localVar offsetBinding))
  , guard (.slt (.add (.localVar headerBinding) (.literal 31)) .calldatasize)
  , .letVar lengthBinding (.calldataload (.localVar headerBinding))
  , allocationGuard (.le (.localVar lengthBinding) (.literal (2^64-1)))
  , .letVar memoryPointer (.mload (.literal 64))
  , .letVar nextFreeBinding
      (.add freePointer (.mul (.literal 32) (.add (.localVar lengthBinding) (.literal 1))))
  , allocationGuard (.le (.localVar nextFreeBinding) (.literal (2^64-1)))
  , allocationGuard (.ge (.localVar nextFreeBinding) freePointer)
  , .letVar dataBinding (.add (.localVar headerBinding) (.literal 32))
  , guard (.le (.add (.localVar dataBinding) (.mul (.localVar lengthBinding) (.literal 32))) .calldatasize) ] ++
  materializeStaticScalarArray (.localVar dataBinding) (.localVar lengthBinding)
    freePointer (.localVar nextFreeBinding) namePrefix kind

/-- Source-compatible `bytes memory` / `string memory` root parameter checks as
executable model code, matching `solc`'s `abi_decode_t_bytes_memory_ptr`. -/
def bytesMemoryHead
    (memoryPointer offsetBinding headerBinding lengthBinding dataBinding nextFreeBinding copyIndexBinding : String)
    (rootHeadWords headOffset : Nat) : List Stmt :=
  let freePointer := Expr.localVar memoryPointer
  let allocationGuard := fun condition =>
    Stmt.ite condition [] [.panicCode (.literal 0x41)]
  let alignedSize := Expr.bitAnd
    (.add (.add (.localVar lengthBinding) (.literal 32)) (.literal 31))
    (.bitNot (.literal 31))
  let wordCount := Expr.div (.add (.localVar lengthBinding) (.literal 31)) (.literal 32)
  [ guard (.logicalNot (.slt (.sub .calldatasize (.literal 4)) (.literal (32*rootHeadWords))))
  , .letVar offsetBinding (.calldataload (.literal headOffset))
  , guard (.le (.localVar offsetBinding) (.literal (2^64-1)))
  , .letVar headerBinding (.add (.literal 4) (.localVar offsetBinding))
  , guard (.slt (.add (.localVar headerBinding) (.literal 31)) .calldatasize)
  , .letVar lengthBinding (.calldataload (.localVar headerBinding))
  , allocationGuard (.le (.localVar lengthBinding) (.literal (2^64-1)))
  , .letVar memoryPointer (.mload (.literal 64))
  , .letVar nextFreeBinding (.add freePointer alignedSize)
  , allocationGuard (.le (.localVar nextFreeBinding) (.literal (2^64-1)))
  , allocationGuard (.ge (.localVar nextFreeBinding) freePointer)
  , .letVar dataBinding (.add (.localVar headerBinding) (.literal 32))
  , guard (.le (.add (.localVar dataBinding) (.localVar lengthBinding)) .calldatasize)
  , .mstore freePointer (.localVar lengthBinding)
  , .mstore (.literal 64) (.localVar nextFreeBinding)
  , .forEach copyIndexBinding wordCount
      [.mstore (.add (.add freePointer (.literal 32)) (.mul (.localVar copyIndexBinding) (.literal 32)))
        (.calldataload (.add (.localVar dataBinding) (.mul (.localVar copyIndexBinding) (.literal 32))))] ]

/-- Allocate and materialize a validated calldata scalar array into memory when
passed to a `T[] memory` helper parameter. -/
def materializeCalldataScalarArray (data length : Expr)
    (arrayPointerBinding nextFreeBinding namePrefix : String)
    (kind : SolidityAbi.ScalarKind) : List Stmt :=
  let allocationGuard := fun condition =>
    Stmt.ite condition [] [.panicCode (.literal 0x41)]
  [ .letVar arrayPointerBinding (.mload (.literal 64))
  , allocationGuard (.le length (.literal (2^64-1)))
  , .letVar nextFreeBinding
      (.add (.localVar arrayPointerBinding) (.mul (.literal 32) (.add length (.literal 1))))
  , allocationGuard (.le (.localVar nextFreeBinding) (.literal (2^64-1)))
  , allocationGuard (.ge (.localVar nextFreeBinding) (.localVar arrayPointerBinding)) ] ++
  materializeStaticScalarArray data length (.localVar arrayPointerBinding) (.localVar nextFreeBinding) namePrefix kind

end Compiler.CompilationModel.SolidityImport.AbiLowering

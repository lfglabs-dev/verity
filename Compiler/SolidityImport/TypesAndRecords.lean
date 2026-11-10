import Compiler.CompilationModel
import Compiler.SolidityImport.SolidityAbi
import Compiler.SolidityImport.AbiSchema

set_option autoImplicit false

/-!
# Core Lowering Types & Descriptor Records (`Compiler.SolidityImport.TypesAndRecords`)

Construct-generic core data structures used across the Solidity importer (`Import.lean`):
* Lowered expression bundles (`Val`, `EncodedBytes`) and storage access paths (`SPath`)
* Storage struct layout descriptors (`StructFixedArrayInfo`, `StructMappingInfo`,
  `StructDynamicArrayInfo`, `RawStructSubStructInfo`, `RawStructMemberInfo`, `RawStructInfo`)
* Local and reference descriptors (`FlatStructLocal`, `Ref`, `AbiElementLocal`,
  `CalldataBytesParam`, `ScalarArrayParam`, `MemParam`, `FnPtr`, `CallArg`)
* Contract-level metadata records (`FieldInfo`, `FnRec`, `ProjRec`, `OpaqRec`, `SrcParam`)
* ABI decode schema/value descriptors (`AbiDecodeTypeItem`, `AbiDecodedValue`)
-/

namespace Compiler.CompilationModel.SolidityImport

open Compiler.CompilationModel

/-- A lowered expression and the statements that must run before it. -/
structure Val where
  pre : Array Stmt
  expr : Expr

structure EncodedBytes where
  pre : Array Stmt
  pointer : Expr
  size : Expr

inductive SPath where
  | zero (field : String)
  | one (field : String) (key : Expr)
  | two (field : String) (k1 k2 : Expr)
  | outer (field : String) (k1 : Expr)
  | rawSlot (structId : Nat) (slot : Expr)
  | bytesSlot (target : String × Expr) (isString : Bool)

structure StructFixedArrayInfo where
  member : String
  solcType : String
  wordOffset : Nat
  byteOffset : Nat
  length : Nat
  elementWidth : Nat
  arrayType : String

structure StructMappingInfo where
  member : String
  solcType : String
  wordOffset : Nat
  keyType : MappingKeyType
  valueWidth : Nat
  booleanValue : Bool := false
  valueStructId : Option Nat := none
  /-- For `mapping(K1 => mapping(K2 => V))`, the key type of the inner mapping: indexing the
  member once yields the inner mapping, whose slot is that of a member at offset 0. -/
  innerKeyType : Option MappingKeyType := none

structure StructDynamicArrayInfo where
  member : String
  solcType : String
  wordOffset : Nat
  elemType : String
  modelElemType : ParamType
  abiKind : SolidityAbi.ScalarKind
  elemStructId : Option Nat := none

structure RawStructSubStructInfo where
  member : String
  structId : Nat
  wordOffset : Nat

structure RawStructMemberInfo where
  member : String
  ty : String
  wordOffset : Nat
  byteOffset : Nat
  bitWidth : Nat
  isBool : Bool := false

structure RawStructInfo where
  structId : Nat
  structName : String
  scalars : Array RawStructMemberInfo
  mappings : Array StructMappingInfo
  dynamicArrays : Array StructDynamicArrayInfo := #[]
  subStructs : Array RawStructSubStructInfo := #[]
  wordCount : Nat := 0
  /-- Members whose storage type is outside this slice. Each keeps the slot solc assigns it,
  so later members are placed correctly, and any access to it is rejected. -/
  opaqueMemberNames : Array String := #[]

structure FlatStructLocal where
  structId : Nat
  structName : String
  members : Array (String × String × String)

inductive Ref where
  | expr (v : Val)
  | path (pre : Array Stmt) (p : SPath)
  | fixedElement (pre : Array Stmt) (path : SPath) (index : Expr)
  | structFixedArray (pre : Array Stmt) (path : SPath) (info : StructFixedArrayInfo)
  | structFixedElement (pre : Array Stmt) (path : SPath) (info : StructFixedArrayInfo) (index : Expr)
  | structMapping (pre : Array Stmt) (path : SPath) (info : StructMappingInfo)
  | structMappingElement (pre : Array Stmt) (path : SPath) (info : StructMappingInfo) (key : Expr)
  | structDynamicArray (pre : Array Stmt) (path : SPath) (info : StructDynamicArrayInfo)
  | structDynamicElement (pre : Array Stmt) (path : SPath) (info : StructDynamicArrayInfo) (index : Expr)
  | storageDynamicElement (pre : Array Stmt) (fieldName : String) (slotExpr : Expr) (elemTy : String) (index : Expr)
  | snapshot (elements : Array Expr)
  | mem (id : Nat) (pre : Array Stmt)
  | flatStruct (id : Nat)
  | abiArray (id memberIndex : Nat) (pre : Array Stmt)
  | abiBytesField (id memberIndex : Nat) (pre : Array Stmt)
  | abiElement (id memberIndex : Nat) (pointer : Expr) (inMemory : Bool) (pre : Array Stmt)
  | calldataBytes (id : Nat) (pre : Array Stmt)
  | scalarArray (id : Nat) (pre : Array Stmt)
  | state (name : String) (pre : Array Stmt)

structure AbiElementLocal where
  rootId : Nat
  memberIndex : Nat
  pointer : Expr
  inMemory : Bool

structure CalldataBytesParam where
  param : String
  offsetBinding : String
  headerBinding : String
  lengthBinding : String
  dataBinding : String
  isString : Bool := false
  inMemory : Bool := false
  memoryPointer : String := ""
  nextFreeBinding : String := ""
  copyIndexBinding : String := ""

structure ScalarArrayParam where
  param : String
  elementType : String
  modelElementType : ParamType
  abiKind : SolidityAbi.ScalarKind
  inMemory : Bool
  offsetBinding : String := ""
  headerBinding : String := ""
  lengthBinding : String
  dataBinding : String := ""
  memoryPointer : String := ""
  nextFreeBinding : String := ""
  namePrefix : String := ""

structure MemParam where
  structId : Nat
  param : String
  structName : String
  members : Array (String × String)
  staticTypes : Option (List ParamType) := none
  calldataLocation : Bool := false
  headBinding : String := ""
  schema : Option (List AbiSchema.Member) := none
  abiStem : String := ""

inductive FnPtr where
  | direct (fnId : Nat)
  | branch (cond : Expr) (trueFnId : Nat) (falseFnId : Nat)

inductive CallArg where
  | scalar (value : Val)
  | memory (descriptor : MemParam) (pre : Array Stmt)
  | abiElement (bound : AbiElementLocal) (pre : Array Stmt)
  | scalarArray (descriptor : ScalarArrayParam) (pre : Array Stmt)
  | byteBuffer (buffer : EncodedBytes)
  | stringBuffer (buffer : EncodedBytes)
  | calldataBytes (descriptor : CalldataBytesParam) (pre : Array Stmt)
  | storagePath (structId : Nat) (path : SPath) (pre : Array Stmt)
  | flatStruct (structId : Nat) (structName : String) (members : Array (String × String × Expr)) (pre : Array Stmt)
  | storageBytes (target : String × Expr × Array Stmt) (isString : Bool)
  | storageDynamicArray (fieldName : String) (slotExpr : Expr) (elemTy : String) (elemStructId : Option Nat) (pre : Array Stmt)
  | fnPtr (ptr : FnPtr) (pre : Array Stmt)

structure FieldInfo where
  slot : Nat
  field : Field
  keyCount : Nat
  memberNames : Array String
  opaqueNames : Array String
  booleanMembers : Array String := #[]
  structFixedArrays : Array StructFixedArrayInfo := #[]
  structMappings : Array StructMappingInfo := #[]
  structDynamicArrays : Array StructDynamicArrayInfo := #[]
  subStructs : Array (String × Nat) := #[]
  structMembers : Array StructMember := #[]
  booleanScalar : Bool := false
  scalarMapping : Bool := false
  booleanMapping : Bool := false
  bytesStorage : Bool := false
  stringStorage : Bool := false
  dynamicArrayElemType : Option (String × ParamType × SolidityAbi.ScalarKind) := none
  dynamicArrayStructId : Option Nat := none
  thirdKeyMapping : Option StructMappingInfo := none
  fixedArrayLength : Option Nat := none
  fixedArrayType : String := ""

structure FnRec where
  contract : String
  name : String
  declId : Nat
  paramTypes : Array String

structure ProjRec where
  parameter : String
  member : String
  structName : String
  headWord : Nat
  modelParam : String

structure OpaqRec where
  field : String
  name : String
  solcType : String
  wordOffset : Nat
  byteOffset : Nat

structure SrcParam where
  name : String
  id : Nat

inductive AbiDecodeTypeItem where
  | scalar (ty : String) (pty : ParamType) (enumBound? : Option Nat)
  | flatStruct (sid : Nat) (sName : String) (members : Array (String × String))
  | scalarArray (elemStr : String) (elemPty : ParamType) (abiKind : SolidityAbi.ScalarKind)
  | dynamicBytes (isString : Bool)
  /-- A struct with dynamic array members, decoded from memory by `AbiMemoryDecode`. -/
  | dynamicStruct (sid : Nat) (sName : String) (members : Array (String × String))
      (schema : List AbiSchema.Member)

instance : Inhabited AbiDecodeTypeItem := ⟨.dynamicBytes false⟩

inductive AbiDecodedValue where
  | scalar (ty : String) (pty : ParamType) (expr : Expr)
  | flatStruct (sid : Nat) (sName : String) (members : Array (String × String × Expr))
  | scalarArray (elemStr : String) (elemPty : ParamType) (abiKind : SolidityAbi.ScalarKind) (desc : ScalarArrayParam)
  | dynamicBytes (isString : Bool) (buf : EncodedBytes)
  /-- A memory struct materialized in solc's layout, with its complete schema. -/
  | dynamicStruct (descriptor : MemParam)

instance : Inhabited AbiDecodedValue := ⟨.scalar "" .uint256 (.literal 0)⟩

end Compiler.CompilationModel.SolidityImport

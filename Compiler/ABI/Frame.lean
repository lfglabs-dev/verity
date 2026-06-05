import Compiler.CompilationModel.AbiTypeLayout
import Compiler.Yul.Ast

namespace Compiler.ABI.Frame

open Compiler.CompilationModel
open Compiler.Yul

inductive FrameSource
  | calldata
  | memory
  | code
  | storage
  deriving Repr, BEq

inductive FramePassMode
  | inlineWords
  | pointer
  deriving Repr, BEq

structure FrameField where
  name : String
  ty : ParamType
  source : FrameSource
  sourceBase : String := ""
  sourceOffset : Nat := 0
  tailBytes : Nat := 0
  deriving Repr, BEq

structure FrameLayout where
  fields : List FrameField
  headWords : Nat
  hasDynamic : Bool
  mode : FramePassMode
  deriving Repr, BEq

def spillThresholdWords : Nat := 4

def fieldHeadWords (field : FrameField) : Nat :=
  paramParentHeadWords field.ty

def fieldsHeadWords (fields : List FrameField) : Nat :=
  fields.foldl (fun acc field => acc + fieldHeadWords field) 0

def fieldsHaveDynamic (fields : List FrameField) : Bool :=
  fields.any (fun field => isDynamicParamType field.ty)

def shouldPassByPointer (fields : List FrameField) : Bool :=
  fields.any (fun field => field.source == .code) ||
    fieldsHaveDynamic fields || spillThresholdWords < fieldsHeadWords fields

def layout (fields : List FrameField) : FrameLayout :=
  let headWords := fieldsHeadWords fields
  let hasDynamic := fieldsHaveDynamic fields
  { fields
    headWords
    hasDynamic
    mode := if shouldPassByPointer fields then .pointer else .inlineWords }

def fieldSourceSupported (field : FrameField) : Bool :=
  match field.source with
  | .memory | .code | .storage => true
  | .calldata => true

def layoutSourcesSupported (l : FrameLayout) : Bool :=
  l.fields.all fieldSourceSupported

def frameSizeBytes (l : FrameLayout) : Nat :=
  l.fields.foldl (fun acc field => acc + fieldHeadWords field * 32 +
    (if isDynamicParamType field.ty then field.tailBytes else 0)) 0

def fieldPayloadWords (field : FrameField) : Nat :=
  fieldHeadWords field + if isDynamicParamType field.ty then (field.tailBytes + 31) / 32 else 0

def frameAllocBytes (l : FrameLayout) : Nat :=
  l.fields.foldl (fun acc field => acc + fieldPayloadWords field * 32) 0

def ptrName (base : String) : String :=
  "__abi_frame_" ++ base

def fieldWordName (base : String) (field : FrameField) (idx : Nat) : String :=
  ptrName base ++ "_" ++ field.name ++ "_" ++ toString idx

def allocateFrame (base : String) (l : FrameLayout) : List YulStmt :=
  [ YulStmt.let_ (ptrName base) (YulExpr.call "mload" [YulExpr.lit 64])
  , YulStmt.expr (YulExpr.call "mstore"
      [ YulExpr.lit 64
      , YulExpr.call "add" [YulExpr.ident (ptrName base), YulExpr.lit (frameAllocBytes l)] ])]

def sourceBaseName (field : FrameField) : String :=
  if field.sourceBase.isEmpty then field.name else field.sourceBase

private def sourceByteOffset (field : FrameField) (idx : Nat) : YulExpr :=
  let byteOffset := field.sourceOffset + idx * 32
  if byteOffset == 0 then
    YulExpr.ident (sourceBaseName field)
  else
    YulExpr.call "add" [YulExpr.ident (sourceBaseName field), YulExpr.lit byteOffset]

private def sourceCodeOffset (field : FrameField) (idx : Nat) : YulExpr :=
  YulExpr.lit (field.sourceOffset + idx * 32)

private def sourceStorageSlot (field : FrameField) (idx : Nat) : YulExpr :=
  if idx == 0 then
    YulExpr.ident (sourceBaseName field)
  else
    YulExpr.call "add" [YulExpr.ident (sourceBaseName field), YulExpr.lit idx]

private def dynamicTailByteOffset (field : FrameField) (idx : Nat) : YulExpr :=
  let wordOffset := YulExpr.lit (idx * 32)
  match field.source with
  | .calldata =>
      let base := YulExpr.ident (sourceBaseName field)
      YulExpr.call "add" [YulExpr.call "add" [base, YulExpr.call "calldataload" [base]], wordOffset]
  | .memory =>
      if field.sourceOffset + idx * 32 == 0 then
        YulExpr.ident (sourceBaseName field)
      else
        YulExpr.call "add" [YulExpr.ident (sourceBaseName field), YulExpr.lit (field.sourceOffset + idx * 32)]
  | .code => YulExpr.lit (field.sourceOffset + idx * 32)
  | .storage => sourceStorageSlot field idx

private def materializeSourceWord (field : FrameField) (idx : Nat) : YulExpr :=
  match field.source with
  | .calldata => YulExpr.call "calldataload" [sourceByteOffset field idx]
  | .memory => YulExpr.call "mload" [sourceByteOffset field idx]
  | .code => YulExpr.call "mload" [YulExpr.lit 0]
  | .storage => YulExpr.call "sload" [sourceStorageSlot field idx]

private def spillCodeWord (field : FrameField) (dest offset : YulExpr) : YulStmt :=
  YulStmt.expr (YulExpr.call "extcodecopy"
    [ YulExpr.ident (sourceBaseName field), dest, offset, YulExpr.lit 32 ])

private def spillStaticField (base : String) (headOffsetWords : Nat) (field : FrameField) : List YulStmt :=
  (List.range (fieldHeadWords field)).map fun idx =>
    let dest := YulExpr.call "add" [YulExpr.ident (ptrName base), YulExpr.lit ((headOffsetWords + idx) * 32)]
    match field.source with
    | .code => spillCodeWord field dest (sourceCodeOffset field idx)
    | _ =>
        YulStmt.expr (YulExpr.call "mstore"
          [dest, materializeSourceWord field idx])

private def spillDynamicField (base : String) (headOffsetWords tailOffsetWords : Nat) (field : FrameField) : List YulStmt :=
  let tailOffsetBytes := tailOffsetWords * 32
  let headDest := YulExpr.call "add" [YulExpr.ident (ptrName base), YulExpr.lit (headOffsetWords * 32)]
  let head := [YulStmt.expr (YulExpr.call "mstore" [headDest, YulExpr.lit tailOffsetBytes])]
  let tailWords := (field.tailBytes + 31) / 32
  head ++ (List.range tailWords).map fun idx =>
    let dest := YulExpr.call "add" [YulExpr.ident (ptrName base), YulExpr.lit ((tailOffsetWords + idx) * 32)]
    match field.source with
    | .code => spillCodeWord field dest (dynamicTailByteOffset field idx)
    | .storage =>
        YulStmt.expr (YulExpr.call "mstore"
          [dest, YulExpr.call "sload" [dynamicTailByteOffset field idx]])
    | .calldata =>
        YulStmt.expr (YulExpr.call "mstore"
          [dest, YulExpr.call "calldataload" [dynamicTailByteOffset field idx]])
    | .memory =>
        YulStmt.expr (YulExpr.call "mstore"
          [dest, YulExpr.call "mload" [dynamicTailByteOffset field idx]])

partial def spillFieldsAbi (base : String) (headOffsetWords tailOffsetWords : Nat) : List FrameField → List YulStmt
  | [] => []
  | field :: rest =>
      let headWords := fieldHeadWords field
      if isDynamicParamType field.ty then
        spillDynamicField base headOffsetWords tailOffsetWords field ++
          spillFieldsAbi base (headOffsetWords + headWords) (tailOffsetWords + (field.tailBytes + 31) / 32) rest
      else
        spillStaticField base headOffsetWords field ++
          spillFieldsAbi base (headOffsetWords + headWords) tailOffsetWords rest

/-- Materialize a typed ABI frame into memory before lowering calls/logs/returns.
    Large or dynamic payloads are then passed as `(ptr, size)` instead of as a
    long list of Yul values. -/
def spillPayloadToMemory (base : String) (l : FrameLayout) : List YulStmt :=
  allocateFrame base l ++ spillFieldsAbi base 0 l.headWords l.fields

def pointerArgs (base : String) (l : FrameLayout) : List YulExpr :=
  [YulExpr.ident (ptrName base), YulExpr.lit (frameSizeBytes l)]

def inlinePayloadToScratch (words : List YulExpr) : List YulStmt :=
  words.zipIdx.map fun (word, idx) =>
    YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit (idx * 32), word])

private partial def inlineArgsFrom : List FrameField → List YulExpr
  | [] => []
  | field :: rest =>
      (List.range (fieldHeadWords field)).map (fun wordIdx =>
        materializeSourceWord field wordIdx) ++
      inlineArgsFrom rest

def inlineArgs (l : FrameLayout) : List YulExpr :=
  inlineArgsFrom l.fields

def loweredArgs (base : String) (l : FrameLayout) : List YulExpr :=
  match l.mode with
  | .pointer => pointerArgs base l
  | .inlineWords => inlineArgs l

def materializePayloadToMemory (base : String) (l : FrameLayout) : List YulStmt × List YulExpr :=
  match l.mode with
  | .pointer =>
      (spillPayloadToMemory base l, pointerArgs base l)
  | .inlineWords =>
      (inlinePayloadToScratch (inlineArgs l), [YulExpr.lit 0, YulExpr.lit (frameSizeBytes l)])

def containsDynamicArrayOrBytes (l : FrameLayout) : Bool :=
  l.fields.any fun field =>
    match field.ty with
    | .array _ | .bytes | .string => true
    | _ => isDynamicParamType field.ty

def supportsNestedStructs (l : FrameLayout) : Bool :=
  l.fields.any fun field =>
    match field.ty with
    | .tuple elems => elems.any (fun ty => match ty with | .tuple _ => true | _ => false)
    | _ => false

end Compiler.ABI.Frame

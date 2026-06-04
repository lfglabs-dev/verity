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
  fieldsHaveDynamic fields || spillThresholdWords < fieldsHeadWords fields

def layout (fields : List FrameField) : FrameLayout :=
  let headWords := fieldsHeadWords fields
  let hasDynamic := fieldsHaveDynamic fields
  { fields
    headWords
    hasDynamic
    mode := if hasDynamic || spillThresholdWords < headWords then .pointer else .inlineWords }

def sourceCanMaterializeEarly : FrameSource → Bool
  | .calldata | .memory | .code | .storage => true

def layoutSourcesSupported (l : FrameLayout) : Bool :=
  l.fields.all (fun field => sourceCanMaterializeEarly field.source)

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
  if idx == 0 then
    YulExpr.ident (sourceBaseName field)
  else
    YulExpr.call "add" [YulExpr.ident (sourceBaseName field), YulExpr.lit (idx * 32)]

private def sourceStorageSlot (field : FrameField) (idx : Nat) : YulExpr :=
  if idx == 0 then
    YulExpr.ident (sourceBaseName field)
  else
    YulExpr.call "add" [YulExpr.ident (sourceBaseName field), YulExpr.lit idx]

private def materializeSourceWord (field : FrameField) (idx : Nat) : YulExpr :=
  match field.source with
  | .calldata => YulExpr.call "calldataload" [sourceByteOffset field idx]
  | .memory => YulExpr.call "mload" [sourceByteOffset field idx]
  | .code => YulExpr.call "mload" [sourceByteOffset field idx]
  | .storage => YulExpr.call "sload" [sourceStorageSlot field idx]

partial def spillField (base : String) (offsetWords : Nat) (field : FrameField) : List YulStmt :=
  (List.range (fieldPayloadWords field)).map fun idx =>
    YulStmt.expr (YulExpr.call "mstore"
      [ YulExpr.call "add" [YulExpr.ident (ptrName base), YulExpr.lit ((offsetWords + idx) * 32)]
      , materializeSourceWord field idx ])

partial def spillFields (base : String) (offsetWords : Nat) : List FrameField → List YulStmt
  | [] => []
  | field :: rest => spillField base offsetWords field ++ spillFields base (offsetWords + fieldPayloadWords field) rest

/-- Materialize a typed ABI frame into memory before lowering calls/logs/returns.
    Large or dynamic payloads are then passed as `(ptr, size)` instead of as a
    long list of Yul values. -/
def spillPayloadToMemory (base : String) (l : FrameLayout) : List YulStmt :=
  allocateFrame base l ++ spillFields base 0 l.fields

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

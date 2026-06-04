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
  l.headWords * 32

def ptrName (base : String) : String :=
  "__abi_frame_" ++ base

def fieldWordName (base : String) (field : FrameField) (idx : Nat) : String :=
  ptrName base ++ "_" ++ field.name ++ "_" ++ toString idx

def allocateFrame (base : String) (l : FrameLayout) : List YulStmt :=
  [ YulStmt.let_ (ptrName base) (YulExpr.call "mload" [YulExpr.lit 64])
  , YulStmt.expr (YulExpr.call "mstore"
      [ YulExpr.lit 64
      , YulExpr.call "add" [YulExpr.ident (ptrName base), YulExpr.lit (frameSizeBytes l)] ])]

private def materializeSourceWord (field : FrameField) (idx : Nat) : YulExpr :=
  let name := fieldWordName "src" field idx
  match field.source with
  | .calldata => YulExpr.call "calldataload" [YulExpr.ident name]
  | .memory => YulExpr.call "mload" [YulExpr.ident name]
  | .code => YulExpr.call "mload" [YulExpr.ident name]
  | .storage => YulExpr.call "sload" [YulExpr.ident name]

partial def spillField (base : String) (offsetWords : Nat) (field : FrameField) : List YulStmt :=
  (List.range (fieldHeadWords field)).map fun idx =>
    YulStmt.expr (YulExpr.call "mstore"
      [ YulExpr.call "add" [YulExpr.ident (ptrName base), YulExpr.lit ((offsetWords + idx) * 32)]
      , materializeSourceWord field idx ])

partial def spillFields (base : String) (offsetWords : Nat) : List FrameField → List YulStmt
  | [] => []
  | field :: rest => spillField base offsetWords field ++ spillFields base (offsetWords + fieldHeadWords field) rest

/-- Materialize a typed ABI frame into memory before lowering calls/logs/returns.
    Large or dynamic payloads are then passed as `(ptr, size)` instead of as a
    long list of Yul values. -/
def spillPayloadToMemory (base : String) (l : FrameLayout) : List YulStmt :=
  allocateFrame base l ++ spillFields base 0 l.fields

def pointerArgs (base : String) (l : FrameLayout) : List YulExpr :=
  [YulExpr.ident (ptrName base), YulExpr.lit (frameSizeBytes l)]

private partial def inlineArgsFrom (idx : Nat) : List FrameField → List YulExpr
  | [] => []
  | field :: rest =>
      (List.range (fieldHeadWords field)).map (fun wordIdx =>
        materializeSourceWord field (idx + wordIdx)) ++
      inlineArgsFrom (idx + 1) rest

def inlineArgs (l : FrameLayout) : List YulExpr :=
  inlineArgsFrom 0 l.fields

def loweredArgs (base : String) (l : FrameLayout) : List YulExpr :=
  match l.mode with
  | .pointer => pointerArgs base l
  | .inlineWords => inlineArgs l

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

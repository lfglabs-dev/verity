import Compiler.ABI.Frame
import Compiler.Modules.Create2SSTORE2

namespace Compiler.Modules.CodeData

open Compiler.ABI.Frame
open Compiler.CompilationModel
open Compiler.ECM
open Compiler.Yul

structure CodeDataWrite where
  salt : YulExpr
  value : YulExpr := YulExpr.lit 0
  payload : FrameLayout
  deriving Repr

structure CodeDataRead where
  pointer : YulExpr
  destOffset : YulExpr
  codeOffset : YulExpr
  size : YulExpr
  payload : FrameLayout
  deriving Repr

def trustSurface : List String :=
  [ "CREATE2 address derivation is trusted at the EVM boundary"
  , "SSTORE2 pointer code layout is trusted as code-as-data"
  , "extcodecopy reads immutable deployed code bytes into caller-owned memory"
  , "ABI frame layout is typed by Compiler.ABI.Frame before write/read lowering"
  , "single dynamic bytes/string CodeData payloads use ABI head/length/padded-tail layout" ]

def isBytesLikeParamType : ParamType → Bool
  | .bytes | .string => true
  | .newtypeOf _ baseType => isBytesLikeParamType baseType
  | _ => false

def fieldCodeDataDynamicSupported (field : FrameField) : Bool :=
  isBytesLikeParamType field.ty &&
    (field.source == .calldata || field.source == .memory)

def layoutCodeDataDynamicSupported (l : FrameLayout) : Bool :=
  match l.fields with
  | [field] => fieldCodeDataDynamicSupported field
  | _ => false

def layoutCodeDataSupported (l : FrameLayout) : Bool :=
  layoutSourcesSupported l || layoutCodeDataDynamicSupported l

def codeDataBytesHeadOffset : Nat := 32
def codeDataBytesLengthOffset : Nat := 32
def codeDataBytesDataOffset : Nat := 64

def codeDataBytesPaddedDataBytes (len : Nat) : Nat :=
  ((len + 31) / 32) * 32

def codeDataBytesPayloadBytes (len : Nat) : Nat :=
  codeDataBytesDataOffset + codeDataBytesPaddedDataBytes len

theorem codeDataBytesAbiRoundtripSound (len : Nat) :
    codeDataBytesLengthOffset = codeDataBytesHeadOffset ∧
    codeDataBytesDataOffset = codeDataBytesHeadOffset + 32 ∧
    codeDataBytesPayloadBytes len =
      codeDataBytesDataOffset + codeDataBytesPaddedDataBytes len := by
  simp [codeDataBytesLengthOffset, codeDataBytesHeadOffset,
    codeDataBytesDataOffset, codeDataBytesPayloadBytes]

private def lengthName (field : FrameField) : String :=
  sourceBaseName field ++ "_length"

private def dataOffsetName (field : FrameField) : String :=
  sourceBaseName field ++ "_data_offset"

private def dynamicSourceHead (field : FrameField) : YulExpr :=
  let byteOffset := field.sourceOffset
  if byteOffset == 0 then
    YulExpr.ident (sourceBaseName field)
  else
    YulExpr.call "add" [YulExpr.ident (sourceBaseName field), YulExpr.lit byteOffset]

private def dynamicSourceOffsetAndLength (field : FrameField) : List YulStmt × YulExpr × YulExpr :=
  if field.sourceBase.isEmpty then
    ([], YulExpr.ident (dataOffsetName field), YulExpr.ident (lengthName field))
  else
    let head := dynamicSourceHead field
    let base := YulExpr.ident (sourceBaseName field)
    let relName := "__codedata_bytes_rel"
    let lenName := "__codedata_bytes_len"
    let tailName := "__codedata_bytes_tail"
    let loadWord :=
      match field.source with
      | .calldata => "calldataload"
      | .memory => "mload"
      | .code | .storage => "mload"
    ( [ YulStmt.let_ relName (YulExpr.call loadWord [head])
      , YulStmt.let_ lenName (YulExpr.call loadWord [
          YulExpr.call "add" [base, YulExpr.ident relName]
        ])
      , YulStmt.let_ tailName (YulExpr.call "add" [
          YulExpr.call "add" [base, YulExpr.ident relName],
          YulExpr.lit 32
        ])]
    , YulExpr.ident tailName
    , YulExpr.ident lenName )

private def copyDynamicBytes (field : FrameField) (dest src len : YulExpr) : List YulStmt :=
  let clearPartialWord :=
    YulStmt.if_ (YulExpr.call "mod" [len, YulExpr.lit 32])
      [YulStmt.expr (YulExpr.call "mstore" [
        YulExpr.call "add" [dest, YulExpr.call "and" [len, YulExpr.call "not" [YulExpr.lit 31]]],
        YulExpr.lit 0
      ])]
  let copyStmt :=
    match field.source with
    | .calldata => YulStmt.expr (YulExpr.call "calldatacopy" [dest, src, len])
    | .memory => YulStmt.expr (YulExpr.call "mcopy" [dest, src, len])
    | .code | .storage => YulStmt.expr (YulExpr.call "mcopy" [dest, src, len])
  [clearPartialWord, copyStmt]

private def materializeDynamicBytesPayloadToMemory
    (base : String) (field : FrameField) : List YulStmt × List YulExpr :=
  let (sourcePrelude, sourceOffset, sourceLen) := dynamicSourceOffsetAndLength field
  let paddedName := "__codedata_bytes_padded"
  let sizeName := "__codedata_bytes_size"
  let dataDestName := "__codedata_bytes_data_dest"
  let allocPrelude :=
    [ YulStmt.let_ (ptrName base) (YulExpr.call "mload" [YulExpr.lit 64])
    , YulStmt.let_ paddedName (YulExpr.call "and" [
        YulExpr.call "add" [sourceLen, YulExpr.lit 31],
        YulExpr.call "not" [YulExpr.lit 31]
      ])
    , YulStmt.let_ sizeName (YulExpr.call "add" [YulExpr.lit codeDataBytesDataOffset, YulExpr.ident paddedName])
    , YulStmt.expr (YulExpr.call "mstore" [
        YulExpr.lit 64,
        YulExpr.call "add" [YulExpr.ident (ptrName base), YulExpr.ident sizeName]
      ])
    , YulStmt.expr (YulExpr.call "mstore" [
        YulExpr.ident (ptrName base),
        YulExpr.lit codeDataBytesHeadOffset
      ])
    , YulStmt.expr (YulExpr.call "mstore" [
        YulExpr.call "add" [YulExpr.ident (ptrName base), YulExpr.lit codeDataBytesLengthOffset],
        sourceLen
      ])
    , YulStmt.let_ dataDestName
        (YulExpr.call "add" [YulExpr.ident (ptrName base), YulExpr.lit codeDataBytesDataOffset]) ]
  ( sourcePrelude ++ allocPrelude ++
      copyDynamicBytes field (YulExpr.ident dataDestName) sourceOffset sourceLen
  , [YulExpr.ident (ptrName base), YulExpr.ident sizeName] )

private def materializeCodeDataPayloadToMemory
    (base : String) (l : FrameLayout) : Except String (List YulStmt × List YulExpr) := do
  if layoutSourcesSupported l then
    pure (materializePayloadToMemory base l)
  else
    match l.fields with
    | [field] =>
        if fieldCodeDataDynamicSupported field then
          pure (materializeDynamicBytesPayloadToMemory base field)
        else
          throw "CodeData payload supports only static layouts or one calldata/memory bytes/string field"
    | _ =>
        throw "CodeData payload supports only static layouts or one calldata/memory bytes/string field"

def writeTyped (resultVar base : String) (write : CodeDataWrite) : Except String (List YulStmt) := do
  if !layoutCodeDataSupported write.payload then
    throw "CodeData write payload has unsupported frame source or dynamic shape"
  let (prelude, payloadArgs) ← materializeCodeDataPayloadToMemory base write.payload
  let initcodeOffset ←
    match payloadArgs with
    | [offset, _size] => pure offset
    | _ => throw "CodeData write expected a memory payload pointer and size"
  let initcodeSize ←
    match payloadArgs with
    | [_offset, size] => pure size
    | _ => throw "CodeData write expected a memory payload pointer and size"
  let deploy ← (Compiler.Modules.Create2SSTORE2.deployModule resultVar).compile {}
    [write.value, initcodeOffset, initcodeSize, write.salt]
  pure (prelude ++ deploy)

def readTyped (read : CodeDataRead) : Except String (List YulStmt) := do
  if !layoutCodeDataSupported read.payload then
    throw "CodeData read payload has unsupported frame source or dynamic shape"
  (Compiler.Modules.Create2SSTORE2.readCodeModule).compile {}
    [read.pointer, read.destOffset, read.codeOffset, read.size]

def roundtripShape (resultVar base : String) (write : CodeDataWrite) (read : CodeDataRead) :
    Except String (List YulStmt) := do
  let w ← writeTyped resultVar base write
  let r ← readTyped read
  pure (w ++ r)

def hasCreate2AndExtcodecopy (stmts : List YulStmt) : Bool :=
  let hasCreate2 := stmts.any fun
    | .let_ _ (.call "create2" _) => true
    | _ => false
  let hasExtcodecopy := stmts.any fun
    | .expr (.call "extcodecopy" _) => true
    | _ => false
  hasCreate2 && hasExtcodecopy

end Compiler.Modules.CodeData

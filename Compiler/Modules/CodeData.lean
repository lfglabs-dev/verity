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
  , "Runtime-sized dynamic ABI payload copies preserve the caller-provided byte extent"
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

def sstore2PrefixBytes : Nat := 1

def sstore2PrefixOffset : YulExpr := YulExpr.lit sstore2PrefixBytes

def sstore2RuntimeSize (payloadSize : YulExpr) : YulExpr :=
  YulExpr.call "add" [sstore2PrefixOffset, payloadSize]

theorem sstore2PrefixBytes_eq : sstore2PrefixBytes = 1 := rfl

theorem sstore2PrefixOffset_eq : sstore2PrefixOffset = YulExpr.lit 1 := rfl

theorem sstore2RuntimeSize_adds_prefix (payloadSize : YulExpr) :
    sstore2RuntimeSize payloadSize =
      YulExpr.call "add" [YulExpr.lit 1, payloadSize] :=
  rfl

def codeDataPayloadSupported (payload : FrameLayout) : Bool :=
  if layoutHasRuntimeSize payload then
    layoutRuntimeSourcesSupported payload
  else
    (!payload.hasDynamic && layoutSourcesSupported payload) ||
      layoutCodeDataDynamicSupported payload

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
      [YulStmt.exprStmt (YulExpr.call "mstore" [
        YulExpr.call "add" [dest, YulExpr.call "and" [len, YulExpr.call "not" [YulExpr.lit 31]]],
        YulExpr.lit 0
      ])]
  let copyStmt :=
    match field.source with
    | .calldata => YulStmt.exprStmt (YulExpr.call "calldatacopy" [dest, src, len])
    | .memory => YulStmt.exprStmt (YulExpr.call "mcopy" [dest, src, len])
    | .code | .storage => YulStmt.exprStmt (YulExpr.call "mcopy" [dest, src, len])
  [clearPartialWord, copyStmt]

private def copyMemorySlice (dest src size : YulExpr) : List YulStmt :=
  [ YulStmt.for_
      [YulStmt.let_ "__codedata_copy_i" (YulExpr.lit 0)]
      (YulExpr.call "lt" [YulExpr.ident "__codedata_copy_i", size])
      [YulStmt.assign "__codedata_copy_i"
        (YulExpr.call "add" [YulExpr.ident "__codedata_copy_i", YulExpr.lit 32])]
      [YulStmt.exprStmt (YulExpr.call "mstore"
        [ YulExpr.call "add" [dest, YulExpr.ident "__codedata_copy_i"]
        , YulExpr.call "mload" [YulExpr.call "add" [src, YulExpr.ident "__codedata_copy_i"]] ])] ]

private def materializeStaticSstore2Payload (base : String) (payload : FrameLayout) :
    Except String (List YulStmt × List YulExpr) := do
  let (payloadPrelude, payloadArgs) := materializePayloadToMemory (base ++ "_payload") payload
  let payloadOffset ←
    match payloadArgs with
    | [offset, _size] => pure offset
    | _ => throw "CodeData write expected a memory payload pointer and size"
  let payloadSize ←
    match payloadArgs with
    | [_offset, size] => pure size
    | _ => throw "CodeData write expected a memory payload pointer and size"
  let ptr := YulExpr.ident (ptrName base)
  let dest := YulExpr.call "add" [ptr, sstore2PrefixOffset]
  pure
    ( payloadPrelude ++
      [ YulStmt.let_ (ptrName base) (YulExpr.call "mload" [YulExpr.lit 64])
      , YulStmt.exprStmt (YulExpr.call "mstore"
          [ YulExpr.lit 64
          , YulExpr.call "add" [ptr, sstore2RuntimeSize payloadSize] ])
      , YulStmt.exprStmt (YulExpr.call "mstore8" [ptr, YulExpr.lit 0]) ] ++
      copyMemorySlice dest payloadOffset payloadSize
    , [ptr, sstore2RuntimeSize payloadSize] )

private def materializeDynamicSstore2Payload (base : String) (payload : FrameLayout) :
    Except String (List YulStmt × List YulExpr) := do
  let (prelude, args) ← materializeRuntimePayloadToMemoryWithPrefix base sstore2PrefixBytes payload
  pure
    ( prelude ++
      [YulStmt.exprStmt (YulExpr.call "mstore8" [YulExpr.ident (ptrName base), YulExpr.lit 0])]
    , args )

private def materializeDynamicBytesSstore2Payload
    (base : String) (field : FrameField) : List YulStmt × List YulExpr :=
  let (sourcePrelude, sourceOffset, sourceLen) := dynamicSourceOffsetAndLength field
  let paddedName := "__codedata_bytes_padded"
  let sizeName := "__codedata_bytes_size"
  let totalSizeName := "__codedata_bytes_total_size"
  let dataDestName := "__codedata_bytes_data_dest"
  let payloadBase :=
    YulExpr.call "add" [YulExpr.ident (ptrName base), YulExpr.lit sstore2PrefixBytes]
  let allocPrelude :=
    [ YulStmt.let_ (ptrName base) (YulExpr.call "mload" [YulExpr.lit 64])
    , YulStmt.let_ paddedName (YulExpr.call "and" [
        YulExpr.call "add" [sourceLen, YulExpr.lit 31],
        YulExpr.call "not" [YulExpr.lit 31]
      ])
    , YulStmt.let_ sizeName (YulExpr.call "add" [YulExpr.lit codeDataBytesDataOffset, YulExpr.ident paddedName])
    , YulStmt.let_ totalSizeName (sstore2RuntimeSize (YulExpr.ident sizeName))
    , YulStmt.exprStmt (YulExpr.call "mstore" [
        YulExpr.lit 64,
        YulExpr.call "add" [YulExpr.ident (ptrName base), YulExpr.ident totalSizeName]
      ])
    , YulStmt.exprStmt (YulExpr.call "mstore8" [YulExpr.ident (ptrName base), YulExpr.lit 0])
    , YulStmt.exprStmt (YulExpr.call "mstore" [
        payloadBase,
        YulExpr.lit codeDataBytesHeadOffset
      ])
    , YulStmt.exprStmt (YulExpr.call "mstore" [
        YulExpr.call "add" [payloadBase, YulExpr.lit codeDataBytesLengthOffset],
        sourceLen
      ])
    , YulStmt.let_ dataDestName
        (YulExpr.call "add" [payloadBase, YulExpr.lit codeDataBytesDataOffset]) ]
  ( sourcePrelude ++ allocPrelude ++
      copyDynamicBytes field (YulExpr.ident dataDestName) sourceOffset sourceLen
  , [YulExpr.ident (ptrName base), YulExpr.ident totalSizeName] )

def materializeSstore2Payload (base : String) (payload : FrameLayout) :
    Except String (List YulStmt × List YulExpr) :=
  if layoutHasRuntimeSize payload then
    materializeDynamicSstore2Payload base payload
  else
    match payload.fields with
    | [field] =>
        if payload.hasDynamic && fieldCodeDataDynamicSupported field then
          pure (materializeDynamicBytesSstore2Payload base field)
        else
          materializeStaticSstore2Payload base payload
    | _ =>
        materializeStaticSstore2Payload base payload

def writeTyped (resultVar base : String) (write : CodeDataWrite) : Except String (List YulStmt) := do
  if !codeDataPayloadSupported write.payload then
    throw "CodeData write payload has unsupported frame source or dynamic shape"
  let (prelude, payloadArgs) ← materializeSstore2Payload base write.payload
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
  if !codeDataPayloadSupported read.payload then
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
    | .exprStmt (.call "extcodecopy" _) => true
    | _ => false
  hasCreate2 && hasExtcodecopy

end Compiler.Modules.CodeData

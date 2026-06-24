import Compiler.CompilationModel.ParamLoading

namespace Compiler.CompilationModel

namespace DynamicAbiDecoder

/-- A decoded ABI value. Dynamic values keep offsets in calldata-word units so
tests and proof code can inspect the shape without committing to a byte array
model for payload contents. -/
inductive DecodedValue where
  | word (value : Nat)
  | bytes (length dataOffset : Nat)
  | string (length dataOffset : Nat)
  | array (length dataOffset : Nat) (elems : List DecodedValue)
  | tuple (elems : List DecodedValue)
  deriving Repr, BEq

def wordNormalize (n : Nat) : Nat :=
  n % Compiler.Constants.evmModulus

def uint8Modulus : Nat := 2 ^ 8
def uint16Modulus : Nat := 2 ^ 16

def selectorWord (selector : Nat) : Nat :=
  (selector % Compiler.Constants.selectorModulus) * (2 ^ Compiler.Constants.selectorShift)

/-- EVM-style `calldataload` over selector-prefixed external calldata represented
as ABI words after the 4-byte selector. Unaligned reads bridge adjacent words. -/
def calldataloadWord (selector : Nat) (calldata : List Nat) (offset : Nat) : Nat :=
  if offset = 0 then
    selectorWord selector
  else if offset < 4 then
    0
  else
    let p := offset - 4
    let q := p / 32
    let r := p % 32
    if r = 0 then
      calldata.getD q 0 % Compiler.Constants.evmModulus
    else
      let hi := calldata.getD q 0 % Compiler.Constants.evmModulus
      let lo := calldata.getD (q + 1) 0 % Compiler.Constants.evmModulus
      ((hi % (2 ^ (8 * (32 - r)))) * (2 ^ (8 * r)) +
          lo / (2 ^ (8 * (32 - r)))) %
        Compiler.Constants.evmModulus

def externalCalldataSize (calldata : List Nat) : Nat :=
  4 + 32 * calldata.length

def externalWordAt? (selector : Nat) (calldata : List Nat) (byteOffset : Nat) :
    Option Nat :=
  if 4 ≤ byteOffset ∧ byteOffset + 32 ≤ externalCalldataSize calldata then
    some (calldataloadWord selector calldata byteOffset)
  else
    none

def decodeScalarWord? (ty : ParamType) (word : Nat) : Option Nat :=
  let word := wordNormalize word
  match ty with
  | .uint256 | .int256 | .bytes32 => some word
  | .uint8 => some (word % uint8Modulus)
  | .uint16 => some (word % uint16Modulus)
  | .address => some (word % Compiler.Constants.addressModulus)
  | .bool => some (if word = 0 then 0 else 1)
  | _ => none

def staticElementStrideWords (elemTy : ParamType) : Nat :=
  if isDynamicParamType elemTy then
    1
  else
    Nat.max 1 (paramHeadSize elemTy / 32)

def dynamicArrayPayloadBytes (elemTy : ParamType) (length : Nat) : Nat :=
  length * 32 * staticElementStrideWords elemTy

structure DynamicHead where
  relativeOffset : Nat
  absoluteOffset : Nat
  deriving Repr, BEq

def decodeDynamicHead? (selector : Nat) (calldata : List Nat)
    (headSize baseOffset headOffset : Nat) : Option DynamicHead := do
  let relativeOffset ← externalWordAt? selector calldata headOffset
  if relativeOffset < headSize then
    none
  else
    let absoluteOffset := baseOffset + relativeOffset
    if absoluteOffset + 32 ≤ externalCalldataSize calldata then
      some { relativeOffset, absoluteOffset }
    else
      none

structure LengthPrefixed where
  relativeOffset : Nat
  absoluteOffset : Nat
  length : Nat
  dataOffset : Nat
  deriving Repr, BEq

def decodeLengthPrefixed? (selector : Nat) (calldata : List Nat)
    (headSize baseOffset headOffset payloadBytes : Nat) : Option LengthPrefixed := do
  let head ← decodeDynamicHead? selector calldata headSize baseOffset headOffset
  let length ← externalWordAt? selector calldata head.absoluteOffset
  let dataOffset := head.absoluteOffset + 32
  if dataOffset + payloadBytes ≤ externalCalldataSize calldata then
    some
      { relativeOffset := head.relativeOffset
        absoluteOffset := head.absoluteOffset
        length
        dataOffset }
  else
    none

mutual
  partial def decodeDynamicBodyAt? (selector : Nat) (calldata : List Nat)
      (ty : ParamType) (baseOffset bodyOffset : Nat) : Option DecodedValue :=
    match ty with
    | .bytes => do
        let length ← externalWordAt? selector calldata bodyOffset
        let dataOffset := bodyOffset + 32
        if dataOffset + length ≤ externalCalldataSize calldata then
          some (.bytes length dataOffset)
        else
          none
    | .string => do
        let length ← externalWordAt? selector calldata bodyOffset
        let dataOffset := bodyOffset + 32
        if dataOffset + length ≤ externalCalldataSize calldata then
          some (.string length dataOffset)
        else
          none
    | .array elemTy => do
        let length ← externalWordAt? selector calldata bodyOffset
        let dataOffset := bodyOffset + 32
        let payloadBytes := dynamicArrayPayloadBytes elemTy length
        if dataOffset + payloadBytes ≤ externalCalldataSize calldata then
          let elems ← decodeArrayElements? selector calldata elemTy dataOffset length
          some (.array length dataOffset elems)
        else
          none
    | .tuple elemTys => do
        let elems ← decodeTupleElements? selector calldata elemTys
          (paramHeadSizeList elemTys) bodyOffset bodyOffset
        some (.tuple elems)
    | .fixedArray elemTy n => do
        let elems ← decodeFixedArrayElements? selector calldata elemTy n
          (n * paramHeadSize elemTy) baseOffset bodyOffset
        some (.array n bodyOffset elems)
    | .newtypeOf _ baseTy =>
        decodeDynamicBodyAt? selector calldata baseTy baseOffset bodyOffset
    | _ =>
        decodeValueAt? selector calldata ty 32 baseOffset bodyOffset

  partial def decodeValueAt? (selector : Nat) (calldata : List Nat)
      (ty : ParamType) (headSize baseOffset headOffset : Nat) :
      Option DecodedValue :=
    match ty with
    | .uint256 | .int256 | .uint8 | .uint16 | .address | .bool | .bytes32 => do
        let word ← externalWordAt? selector calldata headOffset
        let value ← decodeScalarWord? ty word
        some (.word value)
    | .bytes => do
        let head ← decodeDynamicHead? selector calldata headSize baseOffset headOffset
        decodeDynamicBodyAt? selector calldata ty baseOffset head.absoluteOffset
    | .string => do
        let head ← decodeDynamicHead? selector calldata headSize baseOffset headOffset
        decodeDynamicBodyAt? selector calldata ty baseOffset head.absoluteOffset
    | .array elemTy => do
        let head ← decodeDynamicHead? selector calldata headSize baseOffset headOffset
        decodeDynamicBodyAt? selector calldata (.array elemTy) baseOffset head.absoluteOffset
    | .tuple elemTys =>
        if isDynamicParamTypeList elemTys then do
          let head ← decodeDynamicHead? selector calldata headSize baseOffset headOffset
          decodeDynamicBodyAt? selector calldata ty baseOffset head.absoluteOffset
        else do
          let elems ← decodeTupleElements? selector calldata elemTys
            (paramHeadSizeList elemTys) baseOffset headOffset
          some (.tuple elems)
    | .fixedArray elemTy n => do
        let elems ← decodeFixedArrayElements? selector calldata elemTy n headSize baseOffset headOffset
        some (.array n headOffset elems)
    | .newtypeOf _ baseTy =>
        decodeValueAt? selector calldata baseTy headSize baseOffset headOffset
    | .adt _ _ => none

  partial def decodeTupleElements? (selector : Nat) (calldata : List Nat)
      (tys : List ParamType) (headSize baseOffset headOffset : Nat) :
      Option (List DecodedValue) :=
    match tys with
    | [] => some []
    | ty :: rest => do
        let here ← decodeValueAt? selector calldata ty headSize baseOffset headOffset
        let tail ← decodeTupleElements? selector calldata rest headSize baseOffset
          (headOffset + paramHeadSize ty)
        some (here :: tail)

  partial def decodeFixedArrayElements? (selector : Nat) (calldata : List Nat)
      (elemTy : ParamType) (remaining headSize baseOffset headOffset : Nat) :
      Option (List DecodedValue) :=
    match remaining with
    | 0 => some []
    | n + 1 => do
        let here ← decodeValueAt? selector calldata elemTy headSize baseOffset headOffset
        let tail ← decodeFixedArrayElements? selector calldata elemTy n headSize baseOffset
          (headOffset + paramHeadSize elemTy)
        some (here :: tail)

  partial def decodeArrayElements? (selector : Nat) (calldata : List Nat)
      (elemTy : ParamType) (dataOffset length : Nat) : Option (List DecodedValue) :=
    let rec go (idx remaining : Nat) : Option (List DecodedValue) :=
      match remaining with
      | 0 => some []
      | n + 1 => do
          let here ←
            if isDynamicParamType elemTy then
              let relOffset ← externalWordAt? selector calldata (dataOffset + idx * 32)
              let elemHeadOffset := dataOffset + relOffset
              decodeDynamicBodyAt? selector calldata elemTy dataOffset elemHeadOffset
            else
              let elemHeadOffset := dataOffset + idx * 32 * staticElementStrideWords elemTy
              decodeValueAt? selector calldata elemTy (length * 32) dataOffset elemHeadOffset
          let tail ← go (idx + 1) n
          some (here :: tail)
    go 0 length
end

def decodeCalldata (selector : Nat) (params : List Param) (calldata : List Nat) :
    Option (List (String × DecodedValue)) := do
  let headSize := paramHeadSizeList (params.map (·.ty))
  if externalCalldataSize calldata < 4 + headSize then
    none
  else
    let values ←
      decodeTupleElements? selector calldata (params.map (·.ty)) headSize 4 4
    some (params.map (·.name) |>.zip values)

def lookup? (name : String) (values : List (String × DecodedValue)) :
    Option DecodedValue :=
  values.find? (fun entry => entry.1 == name) |>.map Prod.snd

/-! ## ERC-4337 `handleOps` shape -/

namespace ERC4337

def handleOpsSelector : Nat := 0x765e827f

def packedUserOperationType : ParamType :=
  .tuple
    [ .address
    , .uint256
    , .bytes
    , .bytes
    , .bytes32
    , .uint256
    , .bytes32
    , .bytes ]

def handleOpsParams : List Param :=
  [ { name := "ops", ty := .array packedUserOperationType }
  , { name := "beneficiary", ty := .address } ]

structure BytesView where
  length : Nat
  dataOffset : Nat
  deriving Repr, BEq

structure PackedUserOperationView where
  sender : Nat
  nonce : Nat
  initCode : BytesView
  callData : BytesView
  accountGasLimits : Nat
  preVerificationGas : Nat
  gasFees : Nat
  paymasterAndData : BytesView
  deriving Repr, BEq

def bytesView? : DecodedValue → Option BytesView
  | .bytes length dataOffset => some { length, dataOffset }
  | _ => none

def wordView? : DecodedValue → Option Nat
  | .word value => some value
  | _ => none

def packedUserOperationView? : DecodedValue → Option PackedUserOperationView
  | .tuple
      [ sender
      , nonce
      , initCode
      , callData
      , accountGasLimits
      , preVerificationGas
      , gasFees
      , paymasterAndData ] => do
        some
          { sender := (← wordView? sender)
            nonce := (← wordView? nonce)
            initCode := (← bytesView? initCode)
            callData := (← bytesView? callData)
            accountGasLimits := (← wordView? accountGasLimits)
            preVerificationGas := (← wordView? preVerificationGas)
            gasFees := (← wordView? gasFees)
            paymasterAndData := (← bytesView? paymasterAndData) }
  | _ => none

structure HandleOpsView where
  opsLength : Nat
  opsDataOffset : Nat
  ops : List PackedUserOperationView
  beneficiary : Nat
  deriving Repr, BEq

def handleOpsView? (decoded : List (String × DecodedValue)) : Option HandleOpsView := do
  let opsValue ← lookup? "ops" decoded
  let beneficiaryValue ← lookup? "beneficiary" decoded
  match opsValue with
  | .array length dataOffset elems =>
      let ops ← elems.mapM packedUserOperationView?
      let beneficiary ← wordView? beneficiaryValue
      some { opsLength := length, opsDataOffset := dataOffset, ops, beneficiary }
  | _ => none

def decodeHandleOpsCalldata (calldata : List Nat) : Option HandleOpsView := do
  let decoded ← decodeCalldata handleOpsSelector handleOpsParams calldata
  handleOpsView? decoded

end ERC4337

end DynamicAbiDecoder

end Compiler.CompilationModel

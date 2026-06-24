import Compiler.CompilationModel.DynamicAbiDecoder

namespace Compiler.DynamicAbiDecoderTest

open Compiler.CompilationModel
open Compiler.CompilationModel.DynamicAbiDecoder

namespace ERC4337OneOp

def beneficiary : Nat := 0x1111111111111111111111111111111111111111
def sender : Nat := 0x2222222222222222222222222222222222222222
def nonce : Nat := 7
def accountGasLimits : Nat := 0xaaaa
def preVerificationGas : Nat := 50000
def gasFees : Nat := 0xbbbb

/-- ABI words after the 4-byte selector for:
`handleOps([PackedUserOperation(empty dynamic bytes fields)], beneficiary)`.

The `ops` array is dynamic. Its single element is a dynamic tuple, so the array
payload starts with one element offset word and that offset points directly to
the tuple head. The tuple's dynamic bytes fields then point to empty tails. -/
def calldata : List Nat :=
  [ 64
  , beneficiary
  , 1
  , 32
  , sender
  , nonce
  , 256
  , 288
  , accountGasLimits
  , preVerificationGas
  , gasFees
  , 320
  , 0
  , 0
  , 0 ]

def decoded : Option ERC4337.HandleOpsView :=
  ERC4337.decodeHandleOpsCalldata calldata

example : decoded.isSome = true := by
  native_decide

example :
    (decoded ==
      some
        { opsLength := 1
          opsDataOffset := 100
          ops :=
            [ { sender := sender
                nonce := nonce
                initCode := { length := 0, dataOffset := 420 }
                callData := { length := 0, dataOffset := 452 }
                accountGasLimits := accountGasLimits
                preVerificationGas := preVerificationGas
                gasFees := gasFees
                paymasterAndData := { length := 0, dataOffset := 484 } } ]
          beneficiary := beneficiary }) = true := by
  native_decide

end ERC4337OneOp

end Compiler.DynamicAbiDecoderTest

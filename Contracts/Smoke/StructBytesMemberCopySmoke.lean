import Contracts.Common

namespace Contracts.Smoke

open Verity hiding pure bind

/-! `copyBytes` and `bytesLength` on a `Bytes` member of a dynamically encoded struct
parameter lower through the checked dynamic-member helpers (`paramDynamicMemberDataOffset`
/ `paramDynamicMemberLength`), like `arrayLength s.field`. -/
verity_contract StructBytesMemberCopySmoke where
  storage

  struct Call where
    target : Address,
    data : Bytes,
    tag : Uint256

  function copyData (c : Call)
    local_obligations [scratch_copy := assumed "copies the member to memory at 0x80 and reads the first word back"]
    : Uint256 := do
    copyBytes c.data 128
    let w := mload 128
    return w

  function hashData (c : Call)
    local_obligations [scratch_hash := assumed "copies the member to memory at 0x80 and hashes the copied region"]
    : Uint256 := do
    copyBytes c.data 128
    let h := keccak256 128 (bytesLength c.data)
    return h

  function dataLength (c : Call) : Uint256 := do
    return bytesLength c.data

example :
    StructBytesMemberCopySmoke.copyData_modelBody =
      [ Compiler.CompilationModel.Stmt.calldatacopy
          (Compiler.CompilationModel.Expr.literal 128)
          (Compiler.CompilationModel.Expr.paramDynamicMemberDataOffset "c" 1)
          (Compiler.CompilationModel.Expr.paramDynamicMemberLength "c" 1)
      , Compiler.CompilationModel.Stmt.letVar "w"
          (Compiler.CompilationModel.Expr.mload (Compiler.CompilationModel.Expr.literal 128))
      , Compiler.CompilationModel.Stmt.return (Compiler.CompilationModel.Expr.localVar "w")
      ] := rfl

example :
    StructBytesMemberCopySmoke.dataLength_modelBody =
      [ Compiler.CompilationModel.Stmt.return
          (Compiler.CompilationModel.Expr.paramDynamicMemberLength "c" 1)
      ] := rfl

/-- Executable side: the whole copied region hashes as `keccak256(data)` (35 bytes, crossing a
word boundary; the digest is `cast keccak 0xdeadbeef00112233445566778899aabbccddeeff0102030405060708090a0b0c0d0e0f`). -/
example :
    let c : StructBytesMemberCopySmoke.Call :=
      { target := 0, data := ⟨#[0xde, 0xad, 0xbe, 0xef, 0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77,
          0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd, 0xee, 0xff, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,
          0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f]⟩, tag := 0 }
    ((StructBytesMemberCopySmoke.hashData c).run Verity.defaultState).getValue? =
      some 0x963a09f68cb830dd9336287d5146e65c3aa6a808af9e200ee5a1d52bd160cf48 := by
  native_decide

/-- Executable side: the member's bytes land in memory. -/
example :
    let c : StructBytesMemberCopySmoke.Call := { target := 0, data := ⟨#[0xab]⟩, tag := 0 }
    ((StructBytesMemberCopySmoke.copyData c).run Verity.defaultState).getValue? =
      some 0xab00000000000000000000000000000000000000000000000000000000000000 := by
  native_decide

example :
    let c : StructBytesMemberCopySmoke.Call := { target := 0, data := ⟨#[1, 2, 3]⟩, tag := 0 }
    ((StructBytesMemberCopySmoke.dataLength c).run Verity.defaultState).getValue? = some 3 := by
  native_decide

end Contracts.Smoke

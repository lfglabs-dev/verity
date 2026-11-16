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

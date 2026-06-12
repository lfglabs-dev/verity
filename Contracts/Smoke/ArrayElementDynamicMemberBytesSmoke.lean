import Contracts.Common

namespace Contracts.Smoke

open Verity hiding pure bind

-- Smoke test for `arrayLength` on `bytes`/`string` dynamic members (PR
-- verity#1991 follow-up). The model side already lowered these through
-- `Expr.paramDynamicMemberLength` / `Expr.arrayElementDynamicMemberLength`;
-- the executable side needs the `ArrayLength` instances for `ByteArray`
-- (Bytes) and `String` so the same source elaborates as a runnable
-- `Contract` function.
verity_contract ArrayElementDynamicMemberBytesSmoke where
  storage

  struct Operation where
    callData : Bytes,
    label : String

  function callDataLength (ops : Operation) : Uint256 := do
    return arrayLength ops.callData

  function labelLength (ops : Operation) : Uint256 := do
    return arrayLength ops.label

  function getElmLength (ops : Array Operation, idx : Uint256) : Uint256 := do
    return arrayLength (arrayElement ops idx).callData

example :
    ArrayElementDynamicMemberBytesSmoke.callDataLength_modelBody =
      [ Compiler.CompilationModel.Stmt.return
          (Compiler.CompilationModel.Expr.paramDynamicMemberLength "ops" 0)
      ] := rfl

example :
    ArrayElementDynamicMemberBytesSmoke.labelLength_modelBody =
      [ Compiler.CompilationModel.Stmt.return
          (Compiler.CompilationModel.Expr.paramDynamicMemberLength "ops" 1)
      ] := rfl

example :
    ArrayElementDynamicMemberBytesSmoke.getElmLength_modelBody =
      [ Compiler.CompilationModel.Stmt.return
          (Compiler.CompilationModel.Expr.arrayElementDynamicMemberLength
            "ops"
            (Compiler.CompilationModel.Expr.param "idx")
            0)
      ] := rfl

end Contracts.Smoke

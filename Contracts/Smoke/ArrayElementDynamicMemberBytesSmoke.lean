import Contracts.Common

namespace Contracts.Smoke

open Verity hiding pure bind

verity_contract ArrayElementDynamicMemberBytesSmoke where
  storage

  struct Operation where
    callData: Bytes

  function callDataLength(ops: Operation) : Uint256 := do
    return arrayLength ops.callData

  function getElmLength(ops: Array Operation, idx : Uint256) : Uint256 := do
    return arrayLength ( arrayElement ops idx).callData


example :
  ArrayElementDynamicMemberBytesSmoke.callDataLength_modelBody = [
    Compiler.CompilationModel.Stmt.return
      (Compiler.CompilationModel.Expr.paramDynamicMemberLength "ops" 0)
  ] := rfl

example :
 ArrayElementDynamicMemberBytesSmoke.getElmLength_modelBody = [ Compiler.CompilationModel.Stmt.return
          (Compiler.CompilationModel.Expr.arrayElementDynamicMemberLength
            "ops"
            (Compiler.CompilationModel.Expr.param "idx")
            0)
      ] := rfl
end Contracts.Smoke

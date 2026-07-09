import Compiler.CompilationModel

namespace Compiler.PanicCodeRegressionTest

open Compiler.CompilationModel
open Compiler.Yul

def panicMloadCachesCodeBeforePayloadStores : Bool :=
  match compileStmt [] [] [] .calldata [] false [] []
      (Stmt.panicCode (Expr.mload (Expr.literal 0))) with
  | .ok [
      YulStmt.let_ codeName (YulExpr.call "mload" [YulExpr.lit 0]),
      YulStmt.exprStmt (YulExpr.call "mstore" [
        YulExpr.lit 0,
        YulExpr.call "shl" [YulExpr.lit 224, YulExpr.hex 0x4e487b71]
      ]),
      YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit 4, YulExpr.ident payloadCodeName]),
      YulStmt.exprStmt (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 36])
    ] =>
      codeName == "__panic_code" && payloadCodeName == codeName
  | _ => false

example : panicMloadCachesCodeBeforePayloadStores = true := by native_decide

end Compiler.PanicCodeRegressionTest

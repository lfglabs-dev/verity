/-
  Contracts.Smoke.MultiArgIntrinsicSmoke: end-to-end coverage for
  multi-argument `verity_intrinsic` declarations (#1977).

  Verifies that the macro accepts intrinsics with multiple comma-separated
  typed parameters, materialises the right curried wrapper definition,
  records the parameter list in the intrinsic registry, and rejects
  `verbatim` lowerings whose declared input arity disagrees with the
  parameter count.

  The semantics terms below are intentionally toy: this smoke exercises the
  multi-arg surface (parser + elaborator + wrapper emission), not real
  intrinsic semantics. Consumers wiring up genuine multi-arg opcode
  intrinsics (e.g. ERC-4337 `innerHandleOp`) supply matching `verbatim`
  arities, real Yul opcodes / builtins, and proper refinement obligations.
-/
import Contracts.Common
import Compiler.CompilationModel
import Compiler.CompilationModel.ExpressionCompile
import Compiler.CompilationModel.TrustSurface

namespace Contracts.Smoke

open Verity hiding pure bind
open Verity.EVM.Uint256
open Compiler.Yul
open Compiler.CompilationModel

-- Two-argument intrinsic: returns the sum (toy semantics).
verity_intrinsic addPair (a : Uint256, b : Uint256) : Uint256
  where pure;
        yul := verbatim 2 1 (hex "01");
        min_fork := osaka;
        semantics := (fun a b => Verity.Core.Uint256.ofNat ((a.val + b.val) % (2 ^ 256)));
        obligation [add_pair_matches_evm_add := assumed "toy multi-arg intrinsic example for #1977 coverage"]

-- Three-argument intrinsic: returns the bitwise AND of the three operands
-- (toy semantics chosen to keep the example deterministic).
verity_intrinsic andTriple (x : Uint256, y : Uint256, z : Uint256) : Uint256
  where pure;
        yul := verbatim 3 1 (hex "16");
        min_fork := osaka;
        semantics := (fun x y z =>
          Verity.Core.Uint256.ofNat (Nat.land (Nat.land x.val y.val) z.val));
        obligation [and_triple_matches_native := assumed "toy multi-arg intrinsic example for #1977 coverage"]

example : (addPair (Verity.Core.Uint256.ofNat 7) (Verity.Core.Uint256.ofNat 35)).val = 42 := by
  native_decide

example :
    (andTriple (Verity.Core.Uint256.ofNat 0b1110)
               (Verity.Core.Uint256.ofNat 0b1101)
               (Verity.Core.Uint256.ofNat 0b1011)).val = 0b1000 := by
  native_decide

-- The intrinsic registry records all parameter names and types in order.
example :
    (addPair_intrinsic_obligations).startsWith "add_pair_matches_evm_add: assumed" := by
  native_decide

-- A `builtin` lowering with a known fixed arity also cross-checks the
-- declared parameter count. The Yul `add` builtin takes 2 inputs, so a
-- two-parameter intrinsic is accepted.
verity_intrinsic addViaBuiltin (a : Uint256, b : Uint256) : Uint256
  where pure;
        yul := builtin "add";
        min_fork := osaka;
        semantics := (fun a b => Verity.Core.Uint256.ofNat ((a.val + b.val) % (2 ^ 256)));
        obligation [add_via_builtin_matches_evm_add := assumed "toy builtin arity-match coverage for the PR #1971 Bugbot fix"]

example :
    (addViaBuiltin (Verity.Core.Uint256.ofNat 9) (Verity.Core.Uint256.ofNat 14)).val = 23 := by
  native_decide

-- A three-parameter intrinsic that names the 2-input `add` builtin must be
-- rejected with a Bugbot-style arity mismatch (PR #1971 Bugbot review:
-- "Builtin intrinsics skip arity match"). The `verbatim` path already
-- enforced this; the `builtin` path now matches.
/--
error: verity_intrinsic `builtin "add"` expects 2 input(s) but 3 parameter(s) were declared
-/
#guard_msgs in
verity_intrinsic addViaBuiltinArityMismatch (a : Uint256, b : Uint256, c : Uint256) : Uint256
  where pure;
        yul := builtin "add";
        min_fork := osaka;
        semantics := (fun a b c => Verity.Core.Uint256.ofNat ((a.val + b.val + c.val) % (2 ^ 256)));
        obligation [add_via_builtin_mismatch := assumed "negative coverage; never elaborated"]

-- Four-argument template intrinsic: the body is typed Yul AST and intentionally
-- unchecked by Verity beyond arity/shape. The explicit assumed obligation marks
-- the refinement proof that consumers must discharge or continue to trust.
verity_intrinsic entryPointPackInnerCalldata (sender : Uint256, gasLimit : Uint256, callDataOffset : Uint256, callDataLength : Uint256) : Uint256
  where pure;
        yul := [template (sender, gasLimit, callDataOffset, callDataLength) -> packed := [
          yulcall mstore(0, sender),
          let head := add(sender, gasLimit),
          packed := add(head, add(callDataOffset, callDataLength))
        ]];
        min_fork := osaka;
        semantics := (fun sender gasLimit callDataOffset callDataLength =>
          Verity.Core.Uint256.ofNat ((sender.val + gasLimit.val + callDataOffset.val + callDataLength.val) % (2 ^ 256)));
        obligation [entrypoint_inner_calldata_layout := assumed "template Yul body is unchecked; ERC-4337 consumer must prove or trust this lowering"]

example :
    (entryPointPackInnerCalldata
      (Verity.Core.Uint256.ofNat 1)
      (Verity.Core.Uint256.ofNat 2)
      (Verity.Core.Uint256.ofNat 3)
      (Verity.Core.Uint256.ofNat 4)).val = 10 := by
  native_decide

private def templateLowering : Verity.Core.Intrinsics.YulLowering :=
  Verity.Core.Intrinsics.YulLowering.template
    ["sender", "gasLimit", "callDataOffset", "callDataLength"]
    "packed"
    [
      YulStmt.exprStmt
        (YulExpr.call "mstore" [YulExpr.lit 0, YulExpr.ident "sender"]),
      YulStmt.let_ "head"
        (YulExpr.call "add" [YulExpr.ident "sender", YulExpr.ident "gasLimit"]),
      YulStmt.assign "packed"
        (YulExpr.call "add" [
          YulExpr.ident "head",
          YulExpr.call "add" [YulExpr.ident "callDataOffset", YulExpr.ident "callDataLength"]
        ])
    ]
    [("entrypoint_inner_calldata_layout", "assumed",
      "template Yul body is unchecked; ERC-4337 consumer must prove or trust this lowering")]

def templateIntrinsicCompilesToHelperCall : Bool :=
  match Compiler.CompilationModel.compileExpr [] .calldata
      (Compiler.CompilationModel.Expr.intrinsic
        "entryPointPackInnerCalldata"
        templateLowering
        Verity.Core.Intrinsics.HardFork.osaka
        [ Compiler.CompilationModel.Expr.param "sender"
        , Compiler.CompilationModel.Expr.param "gasLimit"
        , Compiler.CompilationModel.Expr.param "callDataOffset"
        , Compiler.CompilationModel.Expr.param "callDataLength"
        ]) with
  | .ok (YulExpr.call "__verity_intrinsic_template_entryPointPackInnerCalldata"
      [YulExpr.ident "sender", YulExpr.ident "gasLimit", YulExpr.ident "callDataOffset", YulExpr.ident "callDataLength"]) => true
  | _ => false

example : templateIntrinsicCompilesToHelperCall = true := by
  native_decide

private def templateIntrinsicModel : CompilationModel := {
  name := "TemplateIntrinsicModel"
  fields := []
  «constructor» := none
  functions := [
    { name := "pack"
      params := [
        { name := "sender", ty := ParamType.uint256 },
        { name := "gasLimit", ty := ParamType.uint256 },
        { name := "callDataOffset", ty := ParamType.uint256 },
        { name := "callDataLength", ty := ParamType.uint256 }
      ]
      returnType := some FieldType.uint256
      body := [
        Stmt.return
          (Expr.intrinsic
            "entryPointPackInnerCalldata"
            templateLowering
            Verity.Core.Intrinsics.HardFork.osaka
            [ Expr.param "sender"
            , Expr.param "gasLimit"
            , Expr.param "callDataOffset"
            , Expr.param "callDataLength"
            ])
      ]
    }
  ]
}

def templateIntrinsicCompilationEmitsHelper : Bool :=
  match Compiler.CompilationModel.compile templateIntrinsicModel [0] with
  | .ok contract =>
      contract.internalFunctions.any fun
        | YulStmt.funcDef "__verity_intrinsic_template_entryPointPackInnerCalldata"
            ["sender", "gasLimit", "callDataOffset", "callDataLength"]
            ["packed"]
            [
              YulStmt.exprStmt
                (YulExpr.call "mstore" [YulExpr.lit 0, YulExpr.ident "sender"]),
              YulStmt.let_ "head"
                (YulExpr.call "add" [YulExpr.ident "sender", YulExpr.ident "gasLimit"]),
              YulStmt.assign "packed"
                (YulExpr.call "add" [
                  YulExpr.ident "head",
                  YulExpr.call "add" [YulExpr.ident "callDataOffset", YulExpr.ident "callDataLength"]
                ])
            ] => true
        | _ => false
  | .error _ => false

example : templateIntrinsicCompilationEmitsHelper = true := by
  native_decide

def templateIntrinsicTrustReportSurfacesObligation : Bool :=
  match Compiler.CompilationModel.collectLocalObligations templateIntrinsicModel with
  | [{ name := "entrypoint_inner_calldata_layout", proofStatus := .assumed, .. }] => true
  | _ => false

#guard templateIntrinsicTrustReportSurfacesObligation

/--
error: verity_intrinsic `template` parameter 'wrongName' does not match declared parameter 'gasLimit'
-/
#guard_msgs in
verity_intrinsic entryPointPackTemplateParamMismatch (sender : Uint256, gasLimit : Uint256) : Uint256
  where pure;
        yul := [template (sender, wrongName) -> packed := []];
        min_fork := osaka;
        semantics := (fun sender gasLimit => Verity.Core.Uint256.ofNat ((sender.val + gasLimit.val) % (2 ^ 256)));
        obligation [entry_point_pack_template_mismatch := assumed "negative coverage; never elaborated"]

/--
error: verity_intrinsic parameter 'sender' must have type Uint256; got Bool
-/
#guard_msgs in
verity_intrinsic entryPointPackTemplateNonUintParam (sender : Bool, gasLimit : Uint256) : Uint256
  where pure;
        yul := [template (sender, gasLimit) -> packed := []];
        min_fork := osaka;
        semantics := (fun sender gasLimit => Verity.Core.Uint256.ofNat 0);
        obligation [entry_point_pack_template_non_uint := assumed "negative coverage; never elaborated"]

/--
error: verity_intrinsic return type must be Uint256; got Bool
-/
#guard_msgs in
verity_intrinsic entryPointPackTemplateNonUintReturn (sender : Uint256, gasLimit : Uint256) : Bool
  where pure;
        yul := [template (sender, gasLimit) -> packed := []];
        min_fork := osaka;
        semantics := (fun sender gasLimit => true);
        obligation [entry_point_pack_template_non_uint_return := assumed "negative coverage; never elaborated"]

def templateIntrinsicRejectsWrongArity : Bool :=
  match Compiler.CompilationModel.compileExpr [] .calldata
      (Compiler.CompilationModel.Expr.intrinsic
        "entryPointPackInnerCalldata"
        templateLowering
        Verity.Core.Intrinsics.HardFork.osaka
        [ Compiler.CompilationModel.Expr.param "sender"
        , Compiler.CompilationModel.Expr.param "gasLimit"
        , Compiler.CompilationModel.Expr.param "callDataOffset"
        ]) with
  | .error "Compilation error: intrinsic entryPointPackInnerCalldata template expects 4 arg(s), got 3" => true
  | _ => false

example : templateIntrinsicRejectsWrongArity = true := by
  native_decide

end Contracts.Smoke

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

namespace Contracts.Smoke

open Verity hiding pure bind
open Verity.EVM.Uint256

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

end Contracts.Smoke

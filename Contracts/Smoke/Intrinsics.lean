import Contracts.Smoke.Helpers

set_option linter.unusedVariables false

namespace Contracts.Smoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math

-- Focused minimal verity_intrinsic example (CLZ via EIP-7939 Osaka).
-- Declaration shape per plan.md; the explicit intrinsic use site emits
-- verbatim_1i_1o(hex"1e", x) in Yul.
verity_intrinsic clz (x : Uint256) : Uint256 where pure; yul := verbatim 1 1 (hex "1e"); min_fork := osaka; semantics := (fun x => Verity.Core.Uint256.ofNat (if x.val = 0 then 256 else 255 - Nat.log2 x.val)); obligation [clz_matches_eip7939 := assumed "EIP-7939 CLZ opcode; chain must support Osaka+ execution semantics"]

verity_contract IntrinsicClzSmoke where
  storage

  function countLeadingZeros (x : Uint256) : Uint256 := do
    return (intrinsic "clz" (Verity.Core.Intrinsics.YulLowering.verbatim 1 1 "1e") [x])

verity_contract BitmapIteratorSmoke where
  storage
    lastBit : Uint256 := slot 0

  function leadingZeros (x : Uint256) : Uint256 := do
    return (clz x)

  function mostSignificantBit (x : Uint256) : Uint256 := do
    return (msb x)

  function rememberSetBits (bitmap : Uint256) : Unit := do
    forEachSetBit "bit" bitmap (do
      setStorage lastBit bit)

def genericECMEffectDemoModule : Compiler.ECM.ExternalCallModule where
  name := "genericEffectDemo"
  numArgs := 2
  resultVars := []
  writesState := false
  readsState := false
  axioms := []
  compile := fun _ctx _args => pure []

verity_contract Uint256PowSmoke where
  storage

  function scale (decimals : Uint256) : Uint256 := do
    let exponent := sub 18 decimals
    return (pow 10 exponent)

  function scaleInfix (decimals : Uint256) : Uint256 := do
    let exponent := sub 18 decimals
    return (10 ^ exponent)

end Contracts.Smoke

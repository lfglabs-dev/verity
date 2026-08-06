import Contracts.Common

namespace Contracts.Examples

open Verity hiding pure bind

/- Worked narrow-type example: scalar ABI parameters/returns are widened to
one word, explicit casts truncate like Solidity, and arithmetic checks the
declared width before producing a result. -/
verity_contract NarrowTypes where
  storage
    marker : Uint256 := slot 0

  errors
    error NarrowOverflow(Uint128)

  event_defs
    event NarrowValue(@indexed key : Bytes20, value : Uint128)

  function echoUint128 (value : Uint128) : Uint128 := do
    return value

  function echoInt64 (value : Int64) : Int64 := do
    return value

  function echoBytes20 (value : Bytes20) : Bytes20 := do
    return value

  function castUint128 (value : Uint256) : Uint128 := do
    return narrowUInt 128 value

  function castInt64 (value : Uint256) : Int64 := do
    return narrowInt 64 value

  function castBytes20 (value : Uint256) : Bytes20 := do
    return narrowBytes 20 value

namespace NarrowTypesChecks

example : (narrowUInt 8 (Verity.Core.Uint256.ofNat 0x123) : UIntN 8).toNat = 0x23 := by
  decide

example : (narrowInt 8 (Verity.Core.Uint256.ofNat 0xff) : Int8).toInt = -1 := by
  decide

example : (narrowBytes 4 (Verity.Core.Uint256.ofNat (0xdeadbeef * 2 ^ 224)) : Bytes4).toNat =
    0xdeadbeef := by
  decide

example : Verity.Core.UIntN.addOverflow
    (Verity.Core.UIntN.ofNat 8 250) (Verity.Core.UIntN.ofNat 8 10) = true := by
  decide

end NarrowTypesChecks

end Contracts.Examples

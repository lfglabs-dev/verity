import Contracts.Common

namespace Contracts.Smoke

open Verity hiding pure bind
open Verity.EVM.Uint256

-- One external parameter of each scalar ABI type, echoed back. The generated decoder
-- reverts with empty data on a head word that is not a valid encoding of the narrow
-- types (`address`, `bool`, `bytesN`, `uintN`, `intN`), as solc's ABI coder v2 does,
-- and binds full-width words unchanged (`test/ScalarAbiValidationSmoke.t.sol`).
-- Members of a static tuple parameter are only cleaned (`accountOfPair`).
verity_contract ScalarAbiValidationSmoke where
  storage

  function echoAddress (value : Address) : Address := do
    return value

  function echoBool (value : Bool) : Bool := do
    return value

  function echoBytes4 (value : Bytes4) : Bytes4 := do
    return value

  function echoUint8 (value : Uint8) : Uint8 := do
    return value

  function echoUint16 (value : Uint16) : Uint16 := do
    return value

  function echoUint32 (value : Uint32) : Uint32 := do
    return value

  function echoInt8 (value : Int8) : Int8 := do
    return value

  function echoInt16 (value : Int16) : Int16 := do
    return value

  function echoUint256 (value : Uint256) : Uint256 := do
    return value

  function echoInt256 (value : Int256) : Int256 := do
    return value

  function echoBytes32 (value : Bytes32) : Bytes32 := do
    return value

  -- Every head word is validated, also those the body never reads.
  function firstOfMixed (full : Uint256, _narrow : Uint8, _account : Address, _flag : Bool) :
      Uint256 := do
    return full

  -- A static tuple member is cleaned (masked) but not validated: unlike solc, which
  -- reverts when it reads a dirty member of a calldata struct, this returns the
  -- masked word (pinned by `test/ScalarAbiValidationSmoke.t.sol`).
  function accountOfPair (pair : Tuple [Uint256, Address]) : Address := do
    let account := pair_1
    return account

end Contracts.Smoke

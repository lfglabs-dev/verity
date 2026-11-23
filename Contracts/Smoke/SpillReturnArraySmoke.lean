import Contracts.Common

namespace Contracts.Smoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256

-- An external function with more than `defaultMaxStackLocals` locals that returns a calldata
-- array. `returnArray` encodes the return data from memory address 0 with a runtime size, so
-- the encoding of a long array covers any fixed spill word above it. The array's length and
-- data offset are parameter locals that stay live until that encoding; if they were spilled to
-- fixed words, the copy would overwrite them before they are read again
-- (`test/SpillReturnArraySmoke.t.sol`).
verity_contract SpillReturnArraySmoke where
  storage
    s0 : Uint256 := slot 0
    s1 : Uint256 := slot 1
    s2 : Uint256 := slot 2
    s3 : Uint256 := slot 3
    s4 : Uint256 := slot 4
    s5 : Uint256 := slot 5

  function echoAfterWork (a : Uint256, b : Uint256, c : Uint256, d : Uint256,
      values : Array Uint256) : Array Uint256 := do
    let t1 := mul a b
    setStorage s1 t1
    let t2 := mul b c
    setStorage s2 t2
    let t3 := mul c d
    setStorage s3 t3
    let t4 := mul d a
    setStorage s4 t4
    let t5 := add a d
    setStorage s5 t5
    setStorage s0 (add (add a b) (add c d))
    returnArray values

end Contracts.Smoke

import Contracts.Smoke.Storage

namespace Contracts.Smoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math

-- `mulDiv512Down(a, b, c)` and `mulDiv512Up(a, b, c)` compile to a Yul
-- helper that performs `floor((a * b) / c)` / `ceil((a * b) / c)` at
-- 512-bit precision using the OpenZeppelin/Solmate `FullMath.mulDiv`
-- algorithm. They revert on division by zero and on quotient overflow.
-- Unlike `mulDivDown` / `mulDivUp` (which compile to `div(mul(a, b), c)`
-- and require the intermediate product to fit in 256 bits), the
-- 512-bit variants handle the full Solidity `Math.mulDiv` semantics
-- needed by Cork Phoenix and other DeFi math.
verity_contract MulDiv512Smoke where
  storage
    lastFloor : Uint256 := slot 0
    lastCeil  : Uint256 := slot 1

  function storeFloor (a : Uint256, b : Uint256, c : Uint256) : Uint256 := do
    let q := mulDiv512Down a b c
    setStorage lastFloor q
    return q

  function storeCeil (a : Uint256, b : Uint256, c : Uint256) : Uint256 := do
    let q := mulDiv512Up a b c
    setStorage lastCeil q
    return q

end Contracts.Smoke

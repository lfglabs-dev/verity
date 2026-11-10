import Contracts.Common

namespace Contracts.Smoke

open Verity hiding pure bind
open Verity.EVM.Uint256

-- Whole static composite values (fixed arrays, structs) are returned, passed and
-- bound as all of their ABI words (`test/WholeCompositeValueSmoke.t.sol`).
verity_contract WholeCompositeValueSmoke where
  storage

  struct Quote where
    amount : Uint256,
    fee : Uint256

  function echoFixed (arr : FixedArray Uint256 3) : FixedArray Uint256 3 := do
    return arr

  function internal passOn (a : FixedArray Uint256 2) : FixedArray Uint256 2 := do
    return a

  function viaHelper (arr : FixedArray Uint256 2) : FixedArray Uint256 2 := do
    let s ← passOn arr
    return s

  function internal mkQuote (a : Uint256) : Quote := do
    return Quote.mk a (add a 1)

  function quoteOf (a : Uint256) : Quote := do
    let q ← mkQuote a
    return q

  function echoQuote (q : Quote) : Quote := do
    return q

/--
error: fixed-array parameter 'arr' cannot be used as a single value on the compilation-model path; return it or pass it to a function directly
-/
#guard_msgs in
verity_contract WholeFixedArrayLocalRejected where
  storage

  function bad (arr : FixedArray Uint256 2) : FixedArray Uint256 2 := do
    let x := arr
    return x

end Contracts.Smoke

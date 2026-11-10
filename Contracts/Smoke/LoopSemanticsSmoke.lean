import Contracts.Common

namespace Contracts.Smoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256

-- The executable of a loop runs its body once per index the compiled loop visits, in the
-- same order, threading the reassigned locals (`test/LoopSemanticsSmoke.t.sol` checks the
-- same values on the bytecode).
verity_contract LoopSemanticsSmoke where
  storage

  -- 0 + 1 + … + (n - 1).
  function sumBelow (n : Uint256) : Uint256 := do
    let mut acc := 0
    forEach "i" n (do
      acc := add acc i)
    return acc

  -- Babylonian integer square root: needs many iterations, then checks its result.
  function isqrt (n : Uint256) : Uint256 := do
    let mut z := 0
    if n > 3 then
      z := n
      let mut x := add (div n 2) 1
      forEach "i" 256 (do
        if x < z then
          z := x
          x := div (add (div n x) x) 2)
    else
      if n != 0 then
        z := 1
    require (mul z z <= n) "isqrt: too large"
    require (sub n (mul z z) <= mul 2 z) "isqrt: too small"
    return z

  -- Set-bit indices in visiting order, one byte each: highest bit first.
  function setBitTrace (bitmap : Uint256) : Uint256 := do
    let mut acc := 0
    forEachSetBit "b" bitmap (do
      acc := add (mul acc 256) b)
    return acc

/-- Ten iterations, indices 0 … 9. -/
theorem loopSemanticsSmoke_sumBelow_10 :
    ∃ s, LoopSemanticsSmoke.sumBelow 10 Verity.defaultState = .success 45 s := ⟨_, rfl⟩

set_option maxRecDepth 100000 in
/-- The loop converges: the root of 10^6 is exact. -/
theorem loopSemanticsSmoke_isqrt_1000000 :
    ∃ s, LoopSemanticsSmoke.isqrt 1000000 Verity.defaultState = .success 1000 s := ⟨_, rfl⟩

set_option maxRecDepth 100000 in
/-- Bits 9, 4, 1 visited in that order: 9·256² + 4·256 + 1. -/
theorem loopSemanticsSmoke_setBitTrace :
    ∃ s, LoopSemanticsSmoke.setBitTrace 530 Verity.defaultState = .success 590849 s :=
  ⟨_, rfl⟩

end Contracts.Smoke

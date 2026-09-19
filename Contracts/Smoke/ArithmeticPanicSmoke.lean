import Contracts.Smoke.Storage

namespace Contracts.Smoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math

-- Solidity-0.8 default-revert arithmetic (verity#1752).
--
-- `addPanic` / `subPanic` / `mulPanic` / `divPanic` are ergonomic bind
-- sources that model the Solidity 0.8 default semantics for `a + b`,
-- `a - b`, `a * b`, `a / b` on `uint256`: revert with `Panic(0x11)` on
-- overflow / underflow and `Panic(0x12)` on division by zero, rather
-- than wrapping mod `2^256`. They lower to a direct failure check followed by
-- typed `Stmt.panic`, which collapses the visual divergence from the Solidity source while
-- still reverting on the same boundary conditions.
verity_contract ArithmeticPanicSmoke where
  storage
    balance : Uint256 := slot 0

  function deposit (amount : Uint256) : Uint256 := do
    let current ← getStorage balance
    let next ← addPanic current amount
    setStorage balance next
    return next

  function withdraw (amount : Uint256) : Uint256 := do
    let current ← getStorage balance
    let next ← subPanic current amount
    setStorage balance next
    return next

  function scaleStored (factor : Uint256) : Uint256 := do
    let current ← getStorage balance
    let next ← mulPanic current factor
    setStorage balance next
    return next

  function shareStored (divisor : Uint256) : Uint256 := do
    let current ← getStorage balance
    let next ← divPanic current divisor
    setStorage balance next
    return next

end Contracts.Smoke

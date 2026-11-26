import Contracts.Common

namespace Contracts.Smoke

open Verity hiding pure bind
open Verity.EVM.Uint256

-- A typed interface call whose callee reverts is not caught here, so the caller
-- re-raises the callee's returndata unchanged (`test/RevertBubbleSmoke.t.sol`).
verity_contract RevertBubbleSmoke where
  storage
    last : Uint256 := slot 0

  interfaces
    interface IVault where
      function withdraw(Uint256) returns (Uint256)
      function poke(Uint256)
    end

  function reentrancy_trusted allow_post_interaction_writes pull (vault : IVault, amount : Uint256)
    : Uint256 := do
    let got ← vault.withdraw amount
    setStorage last got
    return got

  function reentrancy_trusted allow_post_interaction_writes nudge (vault : IVault, amount : Uint256)
    : Unit := do
    vault.poke amount
    setStorage last amount

end Contracts.Smoke

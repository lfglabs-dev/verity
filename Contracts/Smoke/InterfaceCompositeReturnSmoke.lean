import Contracts.Common

namespace Contracts.Smoke

open Verity hiding pure bind
open Verity.EVM.Uint256

-- A typed interface call whose single return is a static composite binds every ABI
-- word of it, and `return result` re-encodes them (`test/InterfaceCompositeReturnSmoke.t.sol`).
verity_contract InterfaceCompositeReturnSmoke where
  storage

  struct Quote where
    amount : Uint256,
    payer : Address

  interfaces
    interface IPool where
      function fetchPair() returns (Tuple [Uint256, Address])
      function fetchNested() returns (Tuple [FixedArray Uint256 2, Uint256])
      function fetchQuote() returns (Quote)
    end

  function reentrancy_trusted pair (pool : IPool) : Tuple [Uint256, Address] := do
    let result ← pool.fetchPair
    return result

  function reentrancy_trusted nested (pool : IPool) : Tuple [FixedArray Uint256 2, Uint256] := do
    let result ← pool.fetchNested
    return result

  function reentrancy_trusted quote (pool : IPool) : Quote := do
    let result ← pool.fetchQuote
    return result

end Contracts.Smoke

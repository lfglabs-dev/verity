import Contracts.Common

namespace Contracts.Smoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256

-- Pareto fidelity gaps G8/G10/G11/G14.
verity_contract ParetoSmallFidelityGapsSmoke where
  storage
    ignored : Array Uint256 := slot 0

  interfaces
    interface IPrices where
      function quote(Uint256) view returns (Uint256)
      function bounds(Uint256) view returns (Uint256, Uint256)
    end

  linked_externals
    external pair(Uint256) -> (Uint256, Uint256)

  errors
    error Stopped(Uint256)

  function g8_if_without_else (flag : Bool) : Uint256 := do
    let mut result : Uint256 := 1
    if flag then
      result := 2
    return result

  function g10_mutable_monadic_bind () : Uint256 := do
    let mut result ← getStorageArrayLength ignored
    result ← getStorageArrayLength ignored
    return result

  function view g11_view_require (flag : Bool) : Uint256 := do
    require flag "flag"
    return 1

  function view g11_view_revert () : Uint256 := do
    revert Stopped(1)

  function view g11_typed_static_view (prices : IPrices, asset : Uint256) : Uint256 := do
    let quote ← prices.quote(asset)
    return quote

  function g14_tuple_typed_interface (prices : IPrices, asset : Uint256) : Tuple [Uint256, Uint256] := do
    let (lower, upper) ← prices.bounds(asset)
    return (lower, upper)

  function g14_tuple_call_external (seed : Uint256) : Tuple [Uint256, Uint256] := do
    let (first, second) ← callExternal pair(seed)
    return (first, second)

end Contracts.Smoke

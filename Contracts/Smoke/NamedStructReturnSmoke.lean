import Contracts.Common

namespace Contracts.Smoke

open Verity hiding pure bind
open Verity.EVM.Uint256

-- A static struct return is ABI-encoded as its fields' words inline
-- (`test/NamedStructReturnSmoke.t.sol`).
verity_contract NamedStructReturnSmoke where
  storage

  struct FeeConfig where
    borrowTakerFeeRatio : Uint256,
    lendMakerFeeRatio : Uint256

  function goodReturn (borrowFee : Uint256, lendFee : Uint256) : FeeConfig := do
    return FeeConfig.mk borrowFee lendFee

end Contracts.Smoke

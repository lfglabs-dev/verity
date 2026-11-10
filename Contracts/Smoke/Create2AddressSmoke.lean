import Contracts.Common
import Compiler.Modules.Create2SSTORE2

namespace Contracts.Smoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256

-- CREATE2 from a bytes argument: the EDSL returns the EIP-1014 address
-- (`create2Live`), the compiled code deploys there (`test/Create2AddressSmoke.t.sol`).
verity_contract Create2AddressSmoke where
  storage

  function reentrancy_trusted deploy (initcode : Bytes, salt : Uint256) : Address := do
    unsafe "copy the initcode to memory for create2" do
      copyBytes initcode 0
    let size := bytesLength initcode
    let zero := 0
    let pointer ← ecmCall Compiler.Modules.Create2SSTORE2.deployModule
      [zero, zero, size, salt]
    return wordToAddress pointer

/-- EIP-1014 example 0: deployer 0x00…00, salt 0, initcode 0x00. -/
def create2AddressMatchesEip1014 : Bool :=
  match Create2AddressSmoke.deploy .stub (ByteArray.mk #[0]) 0
      { Verity.defaultState with thisAddress := 0 } with
  | .success addr _ => addr.val == 0x4D1A2e2bB4F88F0250f26Ffff098B0b30B26BF38
  | .revert _ _ => false

example : create2AddressMatchesEip1014 = true := by native_decide

end Contracts.Smoke

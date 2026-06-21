import Contracts.Common
import Compiler.CheckContract
import Contracts.Counter.Counter
import Contracts.SimpleStorage.SimpleStorage
import Contracts.Owned.Owned
import Contracts.SafeCounter.SafeCounter
import Contracts.OwnedCounter.OwnedCounter
import Contracts.Ledger.Ledger
import Contracts.Vault.Vault
import Contracts.SimpleToken.SimpleToken
import Contracts.ERC20.ERC20
import Contracts.ERC721.ERC721
import Compiler.Modules.Calls
import Compiler.Modules.Callbacks
import Compiler.Modules.Create2SSTORE2
import Compiler.Modules.ERC20
import Compiler.Modules.Oracle
import Compiler.Modules.Precompiles

namespace Contracts.Smoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math

def plusInt256Helper (a : Uint256) (b : Int256) : Uint256 :=
  if b < 0 then sub a (toUint256 (-b)) else add a (toUint256 b)

def eqWordHelper (a : Uint256) (b : Uint256) : Uint256 :=
  if a = b then 1 else 0

end Contracts.Smoke

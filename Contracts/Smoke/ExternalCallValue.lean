import Contracts.Common
import Verity.Core.Model.DenoteFunctionCalls
import Verity.Core.Model.MultiContract

namespace Contracts.Smoke.ExternalCallValue

open Contracts
open Verity hiding pure bind
open Compiler.CompilationModel.DenoteFunctionCalls
open Verity.MultiContract

example :
    (lookup (fundedBus 5) busAddr).selfBalance = (5 : Uint256) :=
  fundedBus_bus_balance 5

end Contracts.Smoke.ExternalCallValue

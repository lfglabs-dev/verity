import Verity.EVM.Uint256
import Contracts.SolidityImportSmoke.Structs.Structs

namespace Contracts.SolidityImportSmoke.Structs.Spec

open Verity
open Contracts.SolidityImportSmoke.Structs.Store

def set_spec (amount : Uint256) (_who : Address) (pre post : Storage) : Prop :=
  post.data_amount = amount ∧
  post.other = pre.other

def other_member_unchanged (_a : Uint256 × Address) (pre post : Storage) : Prop :=
  post.other = pre.other

end Contracts.SolidityImportSmoke.Structs.Spec

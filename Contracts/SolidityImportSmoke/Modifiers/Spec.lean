import Verity.EVM.Uint256
import Contracts.SolidityImportSmoke.Modifiers.Modifiers

namespace Contracts.SolidityImportSmoke.Modifiers.Spec

open Verity
open Verity.EVM.Uint256
open Contracts.SolidityImportSmoke.Modifiers.Child

def early_spec (amount : Uint256) (pre post : Storage) : Prop :=
  post.status = 1 ∧
  post.value = amount ∧
  post.owner = pre.owner ∧
  post.paused = pre.paused

def guarded_spec (amount : Uint256) (pre post : Storage) : Prop :=
  post.value = amount ∧
  post.status = pre.status ∧
  post.owner = pre.owner ∧
  post.paused = pre.paused

def tagged_spec (pre post : Storage) : Prop :=
  post.helperValue = 1 ∧
  post.value = 0 ∧
  post.status = pre.status ∧
  post.owner = pre.owner ∧
  post.paused = pre.paused

def snapshot_spec (_amount : Uint256) (pre post : Storage) : Prop :=
  post.status = pre.status ∧
  post.value = pre.value ∧
  post.owner = pre.owner ∧
  post.paused = pre.paused ∧
  post.helperValue = pre.helperValue

end Contracts.SolidityImportSmoke.Modifiers.Spec

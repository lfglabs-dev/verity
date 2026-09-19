import Verity.EVM.Uint256
import Contracts.SolidityImportSmoke.Inheritance.Inheritance

/-!
Named-storage promises for the S1 inheritance smoke. `paused` is a 0/1 flag
set by `_pause`; `childValue` counts how many times the child's override ran.
-/

namespace Contracts.SolidityImportSmoke.Inheritance.Spec

open Verity
open Verity.EVM.Uint256
open Contracts.SolidityImportSmoke.Inheritance.Child

/-- `paused` is a boolean encoded as `uint256` 0 or 1. -/
def pausedFlag (v : Storage) : Prop :=
  v.paused = 0 ∨ v.paused = 1

/-- `pause()` / `go()` run the child's `_pause` override: parent sets `paused`
and the child increments `childValue`. -/
def pause_spec (pre post : Storage) : Prop :=
  post.paused = 1 ∧
  post.childValue = pre.childValue + 1 ∧
  post.baseValue = pre.baseValue ∧
  post.leftValue = pre.leftValue ∧
  post.rightValue = pre.rightValue ∧
  post.owner = pre.owner

/-- `bump()` runs `Base._bump`. -/
def bump_spec (pre post : Storage) : Prop :=
  post.baseValue = pre.baseValue + 1 ∧
  post.childValue = pre.childValue ∧
  post.paused = pre.paused ∧
  post.leftValue = pre.leftValue ∧
  post.rightValue = pre.rightValue ∧
  post.owner = pre.owner

def pauseFits (v : Storage) : Prop :=
  v.childValue.val + 1 ≤ Verity.Core.MAX_UINT256

def bumpFits (v : Storage) : Prop :=
  v.baseValue.val + 1 ≤ Verity.Core.MAX_UINT256

end Contracts.SolidityImportSmoke.Inheritance.Spec

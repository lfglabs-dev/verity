import Contracts.Common
import Compiler.CheckContract

namespace Contracts.Smoke

open Verity hiding pure bind
open Verity.EVM.Uint256

-- Storage-only parent with explicit slots (IdleCDOStorage-like).
verity_contract ParetoStorageParent where
  storage
    one : Uint256 := slot 0
    two : Uint256 := slot 1

-- Pausable-like parent: modifier plus internal virtual `_pause` / `_unpause`.
verity_contract ParetoPausableParent where
  storage
    paused : Uint256 := slot 2

  modifier whenNotPaused := do
    let flag ← getStorage paused
    require (flag == 0) "paused"

  function internal virtual _pause () : Unit := do
    setStorage paused 1

  function internal _unpause () : Unit := do
    setStorage paused 0

-- Ownable-like parent with an owner slot and constructor.
verity_contract ParetoOwnableParent where
  storage
    owner : Address := slot 3

  constructor (initialOwner : Address) := do
    setStorageAddr owner initialOwner

  modifier onlyOwner := do
    let sender ← msgSender
    let currentOwner ← getStorageAddr owner
    require (sender == currentOwner) "Caller is not the owner"

-- Child flattens the three parents left-to-right and overrides the middle
-- parent's internal virtual `_pause`.
verity_contract ParetoChild is ParetoStorageParent, ParetoPausableParent, ParetoOwnableParent where
  storage
    extra : Uint256 := slot 4

  constructor (initialOwner : Address) ParetoOwnableParent(initialOwner) := do
    setStorage extra 0

  function internal override _pause () : Unit := do
    setStorage paused 1
    setStorage extra 1

  function go () with whenNotPaused : Unit := do
    setStorage extra 2

  function stop () with onlyOwner : Unit := do
    _pause

#check_contract ParetoStorageParent
#check_contract ParetoPausableParent
#check_contract ParetoOwnableParent
#check_contract ParetoChild

verity_contract SlotParentA where
  storage
    a : Uint256 := slot 0

verity_contract SlotParentB where
  storage
    b : Uint256 := slot 0

/--
error: duplicate storage slot 0 from parent 'SlotParentB' field 'b' overlaps parent 'SlotParentA' field 'a'
-/
#guard_msgs in
verity_contract SlotCollisionRejected is SlotParentA, SlotParentB where
  storage

verity_contract SigParentA where
  storage

  function foo () : Uint256 := do
    return 1

verity_contract SigParentB where
  storage

  function foo () : Uint256 := do
    return 2

/--
error: function 'foo' from parent 'SigParentB' duplicates a function from parent 'SigParentA'
-/
#guard_msgs in
verity_contract SigCollisionRejected is SigParentA, SigParentB where
  storage

verity_contract DiamondBase where
  storage

verity_contract DiamondLeft is DiamondBase where
  storage

verity_contract DiamondRight is DiamondBase where
  storage

/--
error: diamond inheritance: ancestor 'Contracts.Smoke.DiamondBase' is reached twice (via 'DiamondLeft' and 'DiamondRight')
-/
#guard_msgs in
verity_contract DiamondRejected is DiamondLeft, DiamondRight where
  storage

end Contracts.Smoke

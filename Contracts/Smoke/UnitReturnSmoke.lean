import Contracts.Common

namespace Contracts.Smoke

open Verity hiding pure bind
open Verity.EVM.Uint256

-- `return ()` exits a `Unit` function early, in an external function (EVM `stop()`,
-- committing earlier writes) and in an internal helper (`leave`, resuming the caller).
verity_contract UnitReturnSmoke where
  storage
    hits : Uint256 := slot 0
    after : Uint256 := slot 1

  function internal bumpUnlessZero (x : Uint256) : Unit := do
    if x == 0 then
      return ()
    let current ← getStorage hits
    setStorage hits (add current x)

  function bumpTwice (x : Uint256) : Unit := do
    bumpUnlessZero x
    let current ← getStorage after
    setStorage after (add current 1)
    if x == 7 then
      return ()
    bumpUnlessZero x

  function hitsAndAfter () : Tuple [Uint256, Uint256] := do
    let h ← getStorage hits
    let a ← getStorage after
    return (h, a)

-- The EDSL meaning, which the compiled bytecode must match (`test/UnitReturnSmoke.t.sol`).
/-- `(hits, after)` after one `bumpTwice x` from the default state. -/
def unitReturnAfterBump (x : Uint256) : Option (Uint256 × Uint256) :=
  match UnitReturnSmoke.bumpTwice x Verity.defaultState with
  | .success _ s =>
      match UnitReturnSmoke.hitsAndAfter s with
      | .success v _ => some v
      | .revert _ _ => none
  | .revert _ _ => none

example : unitReturnAfterBump 0 = some (0, 1) := by decide
example : unitReturnAfterBump 3 = some (6, 1) := by decide
example : unitReturnAfterBump 7 = some (7, 1) := by decide

end Contracts.Smoke

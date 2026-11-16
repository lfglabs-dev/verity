import Contracts.Common
import Compiler.CheckContract

namespace Contracts.Smoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256

-- `fallback nonreentrant(lock)` / `receive nonreentrant(lock)`: the special entrypoints get the
-- transient-storage guard of a `nonreentrant` function. The fallback counts its entries and
-- calls `target`, which re-enters it (`test/FallbackNonReentrantSmoke.t.sol`).
verity_contract FallbackNonReentrantSmoke where
  storage
    lock : Uint256 := slot 0
    target : Address := slot 1
    entries : Uint256 := slot 2

  receive nonreentrant(lock) := do
    pure ()

  fallback nonreentrant(lock)
      local_obligations [low_level_call_refinement := assumed "The low-level call must be shown to refine the intended external-call behavior."] := do
    let current ← getStorage entries
    setStorage entries (add current 1)
    let callee ← getStorageAddr target
    let _ok := call 1000000 (addressToWord callee) 0 0 0 0 0
    pure ()

  function setTarget (callee : Address) : Unit := do
    setStorageAddr target callee

  function entryCount () : Uint256 := do
    let current ← getStorage entries
    return current

#check_contract FallbackNonReentrantSmoke

example :
    (FallbackNonReentrantSmoke.spec.functions.filter
        (fun fn => fn.name == "fallback" || fn.name == "receive")).map
      (fun fn => (fn.name, fn.reentrancyTrusted, fn.nonReentrantLock)) =
      [("receive", false, some "lock"), ("fallback", false, some "lock")] := by
  rfl

end Contracts.Smoke

import Contracts.Common
import Compiler.CheckContract

set_option linter.unusedVariables false

namespace Contracts.Smoke

open Verity hiding pure bind
open Verity.EVM.Uint256

-- Unbound inner target. `set` is a mutating external call, so a callee that
-- invokes it opens a reentrancy window and takes `ExecutableCallContext`.
verity_contract ModeledCtxInner where
  storage
    word : Uint256 := slot 0

  function set (v : Uint256) : Unit := do
    setStorage word v

#check_contract ModeledCtxInner

-- Bound callee whose body opens a reentrancy window (`inner.set`). Pareto
-- CDO→strategy calls have the same shape: the hop must forward the caller's
-- `ExecutableCallContext` into this function.
verity_contract ModeledCtxCallee where
  storage
    last : Uint256 := slot 0

  interfaces
    interface IInner where
      function set(Uint256)
    end

  function reentrancy_trusted poke (inner : IInner, v : Uint256) : Unit := do
    inner.set v

#check_contract ModeledCtxCallee

verity_contract ModeledCtxCaller where
  storage
    last : Uint256 := slot 0

  interfaces
    interface ICallee where
      function poke(Address, Uint256)
    end

  linked_contracts
    callee : ICallee := ModeledCtxCallee

  function reentrancy_trusted go (token : ICallee, inner : Address, v : Uint256) : Unit := do
    token.poke inner v

#check_contract ModeledCtxCaller

/-- Generated `go` hops into `ModeledCtxCallee.poke` with the caller's context.
    Without threading, this module fails to elaborate: `poke` expects
    `ExecutableCallContext` as its first argument. -/
theorem go_is_hopCall (ctx : ExecutableCallContext) (token inner : Address) (v : Uint256) :
    ModeledCtxCaller.go ctx token inner v =
      Contract.hopCall token (ModeledCtxCallee.poke ctx inner v) := rfl

end Contracts.Smoke

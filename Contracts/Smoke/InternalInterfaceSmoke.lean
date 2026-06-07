import Contracts.Common

set_option linter.unusedVariables false

namespace Contracts.Smoke

open Verity hiding pure bind
open Verity.EVM.Uint256

verity_contract InternalHelperSmoke where
  storage

  function internal bump (x : Uint256) : Uint256 := do
    return (add x 1)

example :
    (InternalHelperSmoke.spec.functions).any (fun fn =>
      fn.name == "bump" && !fn.isInternal) = false := by
  decide

example :
    (InternalHelperSmoke.spec.functions).any (fun fn =>
      fn.name == "internal_bump" && fn.isInternal) = true := by
  decide

verity_contract TypedInterfaceCallSmoke where
  storage

  interfaces
    interface IERC20 where
      function balanceOf(Address) view returns (Uint256)
      function transfer(Address, Uint256) returns (Bool)
    end

  function readBalance (token : IERC20, owner : Address) : Uint256 := do
    let bal ← token.balanceOf owner
    return bal

  function readBalanceViaAlias (token : IERC20, owner : Address) : Uint256 := do
    let t := token
    let bal ← t.balanceOf owner
    return bal

  function transferToken (token : IERC20, recipient : Address, amount : Uint256) : Bool := do
    let ok ← token.transfer recipient amount
    return ok

  function transferTokenDiscard (token : IERC20, recipient : Address, amount : Uint256) : Unit := do
    let _ ← token.transfer recipient amount
    return ()

example :
    (TypedInterfaceCallSmoke.spec.externals).any (fun ext =>
      ext.name == "IERC20.balanceOf") = true := by
  decide

example :
    (TypedInterfaceCallSmoke.spec.functions).any (fun fn =>
      fn.name == "readBalance" &&
        fn.body.any (fun stmt =>
          match stmt with
          | Compiler.CompilationModel.Stmt.ecm mod args =>
              mod.name == "externalCallWithReturn" &&
                mod.numArgs == 2 &&
                mod.resultVars == ["bal"] &&
                mod.readsState &&
                !mod.writesState &&
                args.length == 2
          | _ => false)) = true := by
  decide

example :
    (TypedInterfaceCallSmoke.spec.functions).any (fun fn =>
      fn.name == "readBalanceViaAlias" &&
        fn.body.any (fun stmt =>
          match stmt with
          | Compiler.CompilationModel.Stmt.ecm mod args =>
              mod.name == "externalCallWithReturn" &&
                mod.numArgs == 2 &&
                mod.resultVars == ["bal"] &&
                mod.readsState &&
                !mod.writesState &&
                args.length == 2
          | _ => false)) = true := by
  decide

example :
    (TypedInterfaceCallSmoke.spec.functions).any (fun fn =>
      fn.name == "transferToken" &&
        fn.body.any (fun stmt =>
          match stmt with
          | Compiler.CompilationModel.Stmt.ecm mod args =>
                mod.name == "externalCallWithReturn" &&
                mod.numArgs == 3 &&
                mod.resultVars == ["ok"] &&
                mod.readsState &&
                mod.writesState &&
                args.length == 3
          | _ => false)) = true := by
  decide

-- Void (no-`returns`) interface methods lower to the no-output `externalCallNoReturn` ECM:
-- a selector+args `call(...)` that bubbles failure returndata but performs no `returndatasize`
-- check and binds no result. This is what real void callees (e.g. Aave V3 `supply`/`borrow`,
-- ERC20 `approve` in OZ's no-return variant) need; the strict `externalCallWithReturn` ECM would
-- otherwise revert after the callee already ran. The selector is computed from the params only, so
-- a void method's canonical signature matches its non-void counterpart exactly.
verity_contract VoidInterfaceCallSmoke where
  storage

  interfaces
    interface IPool where
      function supply(Address, Uint256, Address, Uint16)
      function balanceOf(Address) view returns (Uint256)
    end

  -- statement-position call to a void method → no-output ECM
  function doSupply (pool : IPool, asset : Address, amount : Uint256, onBehalfOf : Address) : Unit := do
    pool.supply asset amount onBehalfOf 0

  -- a non-void method on the same interface still binds and return-checks as before
  function readBal (pool : IPool, owner : Address) : Uint256 := do
    let bal ← pool.balanceOf owner
    return bal

-- the void method is recorded as an external with no return type
example :
    (VoidInterfaceCallSmoke.spec.externals).any (fun ext =>
      ext.name == "IPool.supply" && ext.returns.isEmpty && ext.returnType.isNone) = true := by
  decide

-- `supply` lowers to the void ECM: `externalCallNoReturn`, no result vars, writes state,
-- 5 args (pool + asset, amount, onBehalfOf, referralCode).
example :
    (VoidInterfaceCallSmoke.spec.functions).any (fun fn =>
      fn.name == "doSupply" &&
        fn.body.any (fun stmt =>
          match stmt with
          | Compiler.CompilationModel.Stmt.ecm mod args =>
              mod.name == "externalCallNoReturn" &&
                mod.numArgs == 5 &&
                mod.resultVars == [] &&
                mod.writesState &&
                args.length == 5
          | _ => false)) = true := by
  decide

-- the non-void method on the same interface is unaffected: still `externalCallWithReturn`,
-- binds its result, performs the 32-byte returndata check.
example :
    (VoidInterfaceCallSmoke.spec.functions).any (fun fn =>
      fn.name == "readBal" &&
        fn.body.any (fun stmt =>
          match stmt with
          | Compiler.CompilationModel.Stmt.ecm mod args =>
              mod.name == "externalCallWithReturn" &&
                mod.resultVars == ["bal"] &&
                args.length == 2
          | _ => false)) = true := by
  decide

verity_contract VoidViewInterfaceCallSmoke where
  storage

  interfaces
    interface IHook where
      function ping(Address) view
    end

  function pingHook (hook : IHook, account : Address) : Unit := do
    hook.ping account

example :
    (VoidViewInterfaceCallSmoke.spec.functions).any (fun fn =>
      fn.name == "pingHook" &&
        fn.body.any (fun stmt =>
          match stmt with
          | Compiler.CompilationModel.Stmt.ecm mod args =>
              mod.name == "externalCallNoReturn" &&
                mod.numArgs == 2 &&
                mod.resultVars == [] &&
                mod.readsState &&
                !mod.writesState &&
                args.length == 2
          | _ => false)) = true := by
  decide

/--
error: interface call returns Verity.Macro.ValueType.uint256; bind it with `let ... ← ...`
-/
#guard_msgs in
verity_contract VoidCallBindNonVoidAsStmtRejected where
  storage

  interfaces
    interface IPool where
      function balanceOf(Address) view returns (Uint256)
    end

  function bad (pool : IPool, owner : Address) : Unit := do
    pool.balanceOf owner

/--
error: interface call 'b' binds a void method; call it as a statement, not `let ... ←`
-/
#guard_msgs in
verity_contract VoidCallLetBindVoidRejected where
  storage

  interfaces
    interface IPool where
      function supply(Address, Uint256, Address, Uint16)
    end

  function bad (pool : IPool, asset : Address, amount : Uint256, onBehalfOf : Address) : Unit := do
    let b ← pool.supply asset amount onBehalfOf 0
    pure ()

/--
error: void typed interface call 'IPool.submit' currently supports only static single-word parameters; argument 1 has Verity.Macro.ValueType.bytes
-/
#guard_msgs in
verity_contract VoidCallDynamicParamRejected where
  storage

  interfaces
    interface IPool where
      function submit(Bytes)
    end

  function bad (pool : IPool, payload : Bytes) : Unit := do
    pool.submit payload

example :
    (TypedInterfaceCallSmoke.spec.functions).any (fun fn =>
      fn.name == "transferTokenDiscard" &&
        fn.body.any (fun stmt =>
          match stmt with
          | Compiler.CompilationModel.Stmt.ecm mod args =>
                mod.name == "externalCallWithReturn" &&
                mod.numArgs == 3 &&
                mod.resultVars == ["__discard"] &&
                mod.readsState &&
                mod.writesState &&
                args.length == 3
          | _ => false)) = true := by
  decide

/--
error: interface name 'Clash' conflicts with an existing type name
-/
#guard_msgs in
verity_contract InterfaceTypeNameClashRejected where
  types
    Clash : Uint256

  storage

  interfaces
    interface Clash where
      function read() view returns (Uint256)
    end

  function noop (_item : Clash) : Unit := do
    pure ()

end Contracts.Smoke

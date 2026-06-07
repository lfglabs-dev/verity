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

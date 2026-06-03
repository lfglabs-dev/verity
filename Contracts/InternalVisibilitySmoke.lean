import Compiler.CheckContract
import Compiler.Selector
import Verity.Macro

namespace Contracts.InternalVisibilitySmoke

open Verity hiding pure bind
open Verity.EVM.Uint256

verity_contract InternalVisibilitySmoke where
  storage
    value : Uint256 := slot 0

  function internal pure double (x : Uint256) : Uint256 := do
    return add x x

  function view readDouble (x : Uint256) : Uint256 := do
    let y ← double x
    return y

  function view read () : Uint256 := do
    let current ← getStorage value
    return current

example :
    (InternalVisibilitySmoke.spec.functions.map (fun fn => (fn.name, fn.isInternal))) =
      [ ("internal_double", true)
      , ("readDouble", false)
      , ("read", false)
      , ("internal_readDouble", true)
      , ("internal_read", true)
      ] := by decide

example :
    (InternalVisibilitySmoke.spec.functions.filter
        (fun fn => !fn.isInternal && !Compiler.CompilationModel.isInteropEntrypointName fn.name)
      |>.map (·.name)) =
      ["readDouble", "read"] := by decide

example :
    InternalVisibilitySmoke.spec.functions.all (fun fn =>
      fn.isInternal || fn.name == "readDouble" || fn.name == "read") = true := by decide

#check_contract InternalVisibilitySmoke

end Contracts.InternalVisibilitySmoke

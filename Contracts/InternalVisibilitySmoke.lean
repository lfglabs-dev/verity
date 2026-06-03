import Compiler.ABI
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
      ] := by native_decide

example :
    (InternalVisibilitySmoke.spec.functions.filter
        (fun fn => !fn.isInternal && !Compiler.CompilationModel.isInteropEntrypointName fn.name)
      |>.map (·.name)) =
      ["readDouble", "read"] := by native_decide

example :
    Compiler.ABI.emitContractABIJson InternalVisibilitySmoke.spec =
      "[\n  {\"type\": \"function\", \"name\": \"readDouble\", \"inputs\": [{\"name\": \"x\", \"type\": \"uint256\"}], \"outputs\": [{\"name\": \"\", \"type\": \"uint256\"}], \"stateMutability\": \"view\"},\n  {\"type\": \"function\", \"name\": \"read\", \"inputs\": [], \"outputs\": [{\"name\": \"\", \"type\": \"uint256\"}], \"stateMutability\": \"view\"}\n]\n" := by native_decide

#check_contract InternalVisibilitySmoke

end Contracts.InternalVisibilitySmoke

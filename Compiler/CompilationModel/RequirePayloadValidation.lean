import Compiler.CompilationModel.AbiHelpers

namespace Compiler.CompilationModel

/-- Complete ABI Error(string) extent, including selector and padded data.
The physical REVERT size must fit the EVM word address space exactly. -/
def requirePayloadFitsWord (message : String) : Bool :=
  decide (68 + 32 * (chunkBytes32 (bytesFromString message)).length ≤ Compiler.Constants.evmModulus)

/-- Node-local check; the canonical deep walker visits every nested body. -/
def requirePayloadOverflow : Stmt → Bool
  | .require _ message => !requirePayloadFitsWord message
  | _ => false

def validateRequirePayloads (owner : String) (body : List Stmt) : Except String Unit :=
  if Stmt.anyDeepList requirePayloadOverflow body then
    .error s!"Compilation error: {owner} contains a require message whose ABI Error(string) payload exceeds the EVM word address space."
  else .ok ()

end Compiler.CompilationModel

import Lean
import Verity.Core.Intrinsics
import Verity.Macro.Types

namespace Verity.Macro

open Lean
open Lean.Elab.Command

/-! Minimal session-local registry for intrinsics declared via `verity_intrinsic`.
   Sufficient for same-module declaration-before-use.
   Cross-module requires attribute-based collection (future). -/
private initialize intrinsicDeclRegistry : IO.Ref (Array Verity.Core.Intrinsics.IntrinsicDecl) ← IO.mkRef #[]

def getRegisteredIntrinsics : IO (Array Verity.Core.Intrinsics.IntrinsicDecl) :=
  intrinsicDeclRegistry.get

def registerIntrinsic (d : Verity.Core.Intrinsics.IntrinsicDecl) : IO Unit :=
  intrinsicDeclRegistry.modify (·.push d)

def hardForkTermFromParsed (fork : Verity.Core.Intrinsics.HardFork) : CommandElabM Term := do
  match fork with
  | .cancun => `(Verity.Core.Intrinsics.HardFork.cancun)
  | .prague => `(Verity.Core.Intrinsics.HardFork.prague)
  | .osaka => `(Verity.Core.Intrinsics.HardFork.osaka)

def hardForkTermFromIdent (fork : TSyntax `ident) : CommandElabM Term := do
  match Verity.Core.Intrinsics.HardFork.parse? (toString fork.getId) with
  | some parsed => hardForkTermFromParsed parsed
  | none =>
      throwErrorAt fork
        s!"unknown fork '{toString fork.getId}' (expected cancun, prague, osaka, or fusaka alias)"

def yulLoweringTerm (lowering : Verity.Core.Intrinsics.YulLowering) : CommandElabM Term := do
  match lowering with
  | .verbatim inArity outArity opcodeHex =>
      `(Verity.Core.Intrinsics.YulLowering.verbatim
          $(natTerm inArity) $(natTerm outArity) $(strTerm opcodeHex))
  | .builtin name =>
      `(Verity.Core.Intrinsics.YulLowering.builtin $(strTerm name))

end Verity.Macro

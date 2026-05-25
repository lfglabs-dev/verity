/-!
Verity.Core.Intrinsics

Minimal registry and descriptors for `verity_intrinsic` declarations.
Enables opcode-level intrinsics (e.g. CLZ via EIP-7939) without forking Verity per opcode.

See docs/INTRINSICS.md and plan.md for usage and trust model.
-/

namespace Verity.Core.Intrinsics

/-- Hard fork levels used for `min_fork` guards on intrinsics. -/
inductive HardFork where
  | shanghai
  | fusaka
  deriving Repr, BEq, Inhabited

def HardFork.toString : HardFork → String
  | .shanghai => "shanghai"
  | .fusaka   => "fusaka"

instance : ToString HardFork := ⟨HardFork.toString⟩

/-- Yul emission strategy for an intrinsic. -/
inductive YulLowering where
  /-- `verbatim N M (hex "XX")` → verbatim_Ni_Mo(hex"XX", args...) in Yul. -/
  | verbatim (inArity outArity : Nat) (opcodeHex : String)
  /-- Named Yul builtin (for opcodes Yul names but Verity does not surface as first-class). -/
  | builtin (name : String)
  deriving Repr, BEq

/-- Descriptor for a declared verity_intrinsic (populated at macro expansion time). -/
structure IntrinsicDecl where
  name : String
  /-- Parameter names in declaration order (for docs/semantics). -/
  paramNames : List String
  /-- Parameter type names as strings (e.g. ["Uint256"]). -/
  paramTypes : List String
  returnType : String
  isPure : Bool
  yul : YulLowering
  minFork : HardFork
  /-- Consumer obligation entries: (name, proofStatusString, message) -/
  obligations : List (String × String × String)
  /-- Source location for audit/trust report (module + line if available). -/
  sourceHint : Option String := none
  deriving Repr, BEq

end Verity.Core.Intrinsics

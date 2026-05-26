/-!
Verity.Core.Intrinsics

Minimal registry and descriptors for `verity_intrinsic` declarations.
Enables consumer-owned opcode-level intrinsics without forking Verity per opcode.

See docs/INTRINSICS.md and plan.md for usage and trust model.
-/

namespace Verity.Core.Intrinsics

/-- Hard fork levels used for `min_fork` guards on intrinsics. -/
inductive HardFork where
  | shanghai
  | fusaka
  deriving Repr, BEq, Inhabited

def HardFork.rank : HardFork → Nat
  | .shanghai => 0
  | .fusaka   => 1

/-- `allows target required` is the fail-closed fork guard used by intrinsic
    callers: the target fork must be at least the intrinsic's minimum fork. -/
def HardFork.allows (target required : HardFork) : Bool :=
  match target, required with
  | .shanghai, .shanghai => true
  | .shanghai, .fusaka => false
  | .fusaka, .shanghai => true
  | .fusaka, .fusaka => true

def HardFork.toString : HardFork → String
  | .shanghai => "shanghai"
  | .fusaka   => "fusaka"

instance : ToString HardFork := ⟨HardFork.toString⟩

@[simp] theorem HardFork.allows_refl (fork : HardFork) :
    HardFork.allows fork fork = true := by
  cases fork <;> rfl

@[simp] theorem HardFork.shanghai_not_allow_fusaka :
    HardFork.allows .shanghai .fusaka = false := rfl

@[simp] theorem HardFork.fusaka_allows_shanghai :
    HardFork.allows .fusaka .shanghai = true := rfl

theorem HardFork.allows_trans {a b c : HardFork}
    (hab : HardFork.allows a b = true)
    (hbc : HardFork.allows b c = true) :
    HardFork.allows a c = true := by
  cases a <;> cases b <;> cases c <;> simp [HardFork.allows] at *

/-- Yul emission strategy for an intrinsic. -/
inductive YulLowering where
  /-- `verbatim N M (hex "XX")` → verbatim_Ni_Mo(hex"XX", args...) in Yul. -/
  | verbatim (inArity outArity : Nat) (opcodeHex : String)
  /-- Named Yul builtin (for opcodes Yul names but Verity does not surface as first-class). -/
  | builtin (name : String)
  deriving Repr, BEq

def YulLowering.inputArity : YulLowering → Option Nat
  | .verbatim inArity _ _ => some inArity
  | .builtin _ => none

def YulLowering.outputArity : YulLowering → Option Nat
  | .verbatim _ outArity _ => some outArity
  | .builtin _ => none

def YulLowering.callName : YulLowering → String
  | .verbatim inArity outArity _ => s!"verbatim_{inArity}i_{outArity}o"
  | .builtin name => name

def YulLowering.hexLiteral? : YulLowering → Option String
  | .verbatim _ _ opcodeHex => some s!"hex\"{opcodeHex}\""
  | .builtin _ => none

@[simp] theorem YulLowering.callName_verbatim
    (inArity outArity : Nat) (opcodeHex : String) :
    YulLowering.callName (.verbatim inArity outArity opcodeHex) =
      s!"verbatim_{inArity}i_{outArity}o" := rfl

@[simp] theorem YulLowering.hexLiteral?_verbatim
    (inArity outArity : Nat) (opcodeHex : String) :
    YulLowering.hexLiteral? (.verbatim inArity outArity opcodeHex) =
      some s!"hex\"{opcodeHex}\"" := rfl

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

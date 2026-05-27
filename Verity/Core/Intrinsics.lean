/-!
Verity.Core.Intrinsics

Minimal registry and descriptors for `verity_intrinsic` declarations.
Enables consumer-owned opcode-level intrinsics without forking Verity per opcode.

See docs/INTRINSICS.md and plan.md for usage and trust model.
-/

namespace Verity.Core.Intrinsics

/-- Hard fork levels used for `min_fork` guards on intrinsics.

    The first entry is Cancun because the pinned EVMYulLean fork exposes
    `EvmYul.TargetSchedule := "Cancun"` and models Cancun-era opcodes such as
    `BLOBHASH`, `TSTORE`, `MCOPY`, and `PUSH0`. Newer forks are represented so
    consumer intrinsics can state future-chain requirements even before
    EVMYulLean models those opcodes. -/
inductive HardFork where
  | cancun
  | prague
  | fusaka
  deriving Repr, BEq, DecidableEq, Inhabited

def HardFork.rank : HardFork → Nat
  | .cancun => 0
  | .prague => 1
  | .fusaka => 2

/-- `allows target required` is the fail-closed fork guard used by intrinsic
    callers: the target fork must be at least the intrinsic's minimum fork. -/
def HardFork.allows (target required : HardFork) : Bool :=
  decide (required.rank ≤ target.rank)

def HardFork.toString : HardFork → String
  | .cancun => "cancun"
  | .prague => "prague"
  | .fusaka => "fusaka"

instance : ToString HardFork := ⟨HardFork.toString⟩

def HardFork.parse? (raw : String) : Option HardFork :=
  match raw with
  | "cancun" => some .cancun
  | "prague" => some .prague
  | "fusaka" => some .fusaka
  -- Solidity's execution-layer name for the Fusaka execution upgrade.
  | "osaka" => some .fusaka
  | _ => none

@[simp] theorem HardFork.allows_refl (fork : HardFork) :
    HardFork.allows fork fork = true := by
  simp [HardFork.allows]

@[simp] theorem HardFork.cancun_not_allow_prague :
    HardFork.allows .cancun .prague = false := rfl

@[simp] theorem HardFork.cancun_not_allow_fusaka :
    HardFork.allows .cancun .fusaka = false := rfl

@[simp] theorem HardFork.prague_not_allow_fusaka :
    HardFork.allows .prague .fusaka = false := rfl

@[simp] theorem HardFork.prague_allows_cancun :
    HardFork.allows .prague .cancun = true := rfl

@[simp] theorem HardFork.fusaka_allows_cancun :
    HardFork.allows .fusaka .cancun = true := rfl

@[simp] theorem HardFork.fusaka_allows_prague :
    HardFork.allows .fusaka .prague = true := rfl

theorem HardFork.allows_trans {a b c : HardFork}
    (hab : HardFork.allows a b = true)
    (hbc : HardFork.allows b c = true) :
    HardFork.allows a c = true := by
  cases a <;> cases b <;> cases c <;> simp [HardFork.allows, HardFork.rank] at *

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

def yulBuiltinArity? (name : String) : Option (Nat × Nat) :=
  match name with
  | "stop" | "invalid" => some (0, 0)
  | "add" | "sub" | "mul" | "div" | "sdiv" | "mod" | "smod"
  | "exp" | "lt" | "gt" | "slt" | "sgt" | "eq" | "and" | "or" | "xor"
  | "byte" | "shl" | "shr" | "sar" | "signextend" | "keccak256" => some (2, 1)
  | "addmod" | "mulmod" => some (3, 1)
  | "iszero" | "not" | "balance" | "calldataload" | "extcodesize"
  | "blobhash" | "mload" | "sload" | "tload" => some (1, 1)
  | "address" | "selfbalance" | "origin" | "caller" | "callvalue"
  | "calldatasize" | "codesize" | "gasprice" | "coinbase" | "timestamp"
  | "number" | "difficulty" | "prevrandao" | "gaslimit" | "chainid"
  | "basefee" | "blobbasefee" | "returndatasize" | "msize" | "gas"
  | "pc" => some (0, 1)
  | "calldatacopy" | "codecopy" | "returndatacopy" | "mcopy" => some (3, 0)
  | "mstore" | "mstore8" | "sstore" | "tstore" | "log0" => some (2, 0)
  | "extcodecopy" => some (4, 0)
  | "log1" => some (3, 0)
  | "log2" => some (4, 0)
  | "log3" => some (5, 0)
  | "log4" => some (6, 0)
  | "create" => some (3, 1)
  | "create2" => some (4, 1)
  | "call" | "callcode" => some (7, 1)
  | "delegatecall" | "staticcall" => some (6, 1)
  | "return" | "revert" => some (2, 0)
  | "selfdestruct" | "pop" => some (1, 0)
  | "datasize" | "dataoffset" => some (1, 1)
  | "datacopy" => some (3, 0)
  | _ => none

def YulLowering.inputArity? : YulLowering → Option Nat
  | .verbatim inArity _ _ => some inArity
  | .builtin name => (yulBuiltinArity? name).map Prod.fst

def YulLowering.outputArity? : YulLowering → Option Nat
  | .verbatim _ outArity _ => some outArity
  | .builtin name => (yulBuiltinArity? name).map Prod.snd

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

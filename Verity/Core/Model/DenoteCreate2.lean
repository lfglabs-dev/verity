import Verity.Core.Model.InitCodeExecution

/-!
# Concrete CREATE2 account transition

This executable prerequisite operates on the actual ContractState account
world. Keccak is an explicit byte-hash parameter, never a deployment-result
oracle. The currently checked initcode templates have exact instruction and
deposit costs; all other initcode is rejected as unsupported instrumentation.

`childGas` is the EIP-150 child allowance after the parent has successfully
charged its CREATE2 opcode. Parent instruction charging, memory provenance and
the canonical Stmt arm remain integration obligations; this module alone does
not admit Solidity CREATE2. Osaka deliberately does not apply EIP-7610.
-/
namespace Compiler.CompilationModel.DenoteCreate2

open Verity.Core
open Compiler.CompilationModel.DenoteMemory
open Compiler.CompilationModel.InitCodeExecution

abbrev ByteHash := List Byte → Uint256

def bytesBE (width value : Nat) : List Byte :=
  List.ofFn fun index : Fin width =>
    ⟨(value / 256^(width - 1 - index.val)) % 256, Nat.mod_lt _ (by decide)⟩

def derivedAddress (hash : ByteHash) (creator : Address) (salt : Uint256) (code : List Byte) : Address :=
  Address.ofNat (hash (⟨0xff, by decide⟩ ::
    bytesBE 20 creator.toNat ++ bytesBE 32 salt.val ++ bytesBE 32 (hash code).val)).val

structure Context where
  creator : Address
  value : Uint256 := 0
  childGas : Nat
  depth : Nat := 0
  isStatic : Bool := false

inductive Failure where
  | depth
  | insufficientBalance
  | nonceLimit
  | collision
  | executionGas
  | depositGas
  | codeSize
  | forbiddenPrefix
  | initcodeException
  deriving DecidableEq, Repr

inductive Abort where
  | staticViolation
  | initcodeSize
  deriving DecidableEq, Repr

inductive Control where
  | success (address : Address)
  | zero (reason : Failure)
  | abort (reason : Abort)
  deriving DecidableEq, Repr

structure Result where
  control : Control
  world : Verity.ContractState
  childGasLeft : Nat

private def expandedPrefix : List Byte :=
  [⟨0x60, by decide⟩, ⟨0x0d, by decide⟩, ⟨0x38, by decide⟩,
   ⟨0x03, by decide⟩, ⟨0x80, by decide⟩, ⟨0x60, by decide⟩,
   ⟨0x0d, by decide⟩, ⟨0x60, by decide⟩, ⟨0x00, by decide⟩,
   ⟨0x39, by decide⟩, ⟨0x60, by decide⟩, ⟨0x00, by decide⟩,
   ⟨0xf3, by decide⟩]

/-- Structural byte checks, not a name-based SSTORE2 shortcut. -/
def templateCost (code : List Byte) : Option Nat :=
  if hasMidnightPrefix code then
    let words := (code.length - 11 + 31) / 32
    some (21 + 6 * words + words * words / 512)
  else if code.take 13 == expandedPrefix then
    let words := (code.length - 13 + 31) / 32
    some (23 + 6 * words + words * words / 512)
  else none

/-- Commit exact runtime bytes. Candidate storage is cleared on Osaka creation,
while an existing balance is retained and the transferred value is added. -/
def commitRuntime (world : Verity.ContractState) (creator target : Address)
    (value : Uint256) (runtime : List Byte) : Verity.ContractState :=
  let creatorAccount := world.accountWorld creator
  let targetAccount := world.accountWorld target
  let paid := world.writeAccount creator { creatorAccount with balance := creatorAccount.balance - value }
  paid.writeAccount target
    { nonce := 1, balance := targetAccount.balance + value, code := runtime }

def denoteCreate2 (hash : ByteHash) (world : Verity.ContractState)
    (context : Context) (salt : Uint256) (code : List Byte) : Except String Result := do
  if context.isStatic then
    return { control := .abort .staticViolation, world, childGasLeft := 0 }
  if code.length > 49152 then
    return { control := .abort .initcodeSize, world, childGasLeft := 0 }
  if context.depth ≥ 1024 then
    return { control := .zero .depth, world, childGasLeft := context.childGas }
  let creator := world.accountWorld context.creator
  if context.value > creator.balance then
    return { control := .zero .insufficientBalance, world, childGasLeft := context.childGas }
  if h : creator.nonce.val + 1 < 2^64 then
    let incremented := world.writeAccount context.creator
      { creator with nonce := ⟨creator.nonce.val + 1, h⟩ }
    let target := derivedAddress hash context.creator salt code
    if (incremented.accountWorld target).collidesOsaka then
      return { control := .zero .collision, world := incremented, childGasLeft := 0 }
    let some executionCost := templateCost code
      | throw "CREATE2 initcode gas semantics are unsupported for these bytes"
    if context.childGas < executionCost then
      return { control := .zero .executionGas, world := incremented, childGasLeft := 0 }
    match run 9 code {} with
    | .returned runtime =>
        if runtime.length > 24576 then
          return { control := .zero .codeSize, world := incremented, childGasLeft := 0 }
        if (runtime.head?).map (·.val) == some 0xef then
          return { control := .zero .forbiddenPrefix, world := incremented, childGasLeft := 0 }
        let totalCost := executionCost + 200 * runtime.length
        if context.childGas < totalCost then
          return { control := .zero .depositGas, world := incremented, childGasLeft := 0 }
        return { control := .success target,
                 world := commitRuntime incremented context.creator target context.value runtime,
                 childGasLeft := context.childGas - totalCost }
    | .failed .outOfFuel => throw "CREATE2 initcode execution exhausted its instrument bound"
    | .failed (.unsupportedOpcode opcode) => throw s!"CREATE2 initcode opcode {opcode} is unsupported"
    | .failed _ =>
        return { control := .zero .initcodeException, world := incremented, childGasLeft := 0 }
    | .running _ => throw "CREATE2 initcode execution did not terminate"
  else
    return { control := .zero .nonceLimit, world, childGasLeft := context.childGas }

theorem static_aborts_without_effect (hash : ByteHash) (world : Verity.ContractState)
    (context : Context) (salt : Uint256) (code : List Byte) :
    denoteCreate2 hash world { context with isStatic := true } salt code =
      .ok { control := .abort .staticViolation, world, childGasLeft := 0 } := rfl

theorem commitRuntime_other (world : Verity.ContractState) (creator target query : Address)
    (value : Uint256) (runtime : List Byte) (notCreator : query ≠ creator) (notTarget : query ≠ target) :
    (commitRuntime world creator target value runtime).accountWorld query = world.accountWorld query := by
  simp only [commitRuntime, Verity.ContractState.writeAccount_other _ _ _ _ notTarget,
             Verity.ContractState.writeAccount_other _ _ _ _ notCreator]

@[simp] theorem commitRuntime_storageWords (world : Verity.ContractState) (creator target : Address)
    (value : Uint256) (runtime : List Byte) :
    (commitRuntime world creator target value runtime).storageWords = world.storageWords := rfl

@[simp] theorem commitRuntime_events (world : Verity.ContractState) (creator target : Address)
    (value : Uint256) (runtime : List Byte) :
    (commitRuntime world creator target value runtime).events = world.events := rfl

theorem commitRuntime_target_code (world : Verity.ContractState) (creator target : Address)
    (value : Uint256) (runtime : List Byte) :
    ((commitRuntime world creator target value runtime).accountWorld target).code = runtime := by
  simp [commitRuntime]

theorem commitRuntime_target_nonce (world : Verity.ContractState) (creator target : Address)
    (value : Uint256) (runtime : List Byte) :
    ((commitRuntime world creator target value runtime).accountWorld target).nonce.val = 1 := by
  simp [commitRuntime]

theorem commitRuntime_clears_storage (world : Verity.ContractState) (creator target : Address)
    (value : Uint256) (runtime : List Byte) (slot : Nat) :
    ((commitRuntime world creator target value runtime).accountWorld target).storageAt slot = 0 := by
  simp [commitRuntime, AccountState.storageAt]

end Compiler.CompilationModel.DenoteCreate2

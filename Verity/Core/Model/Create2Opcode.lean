import Verity.Core.Model.Create2ParentGas

/-! Concrete Osaka CREATE2 opcode composition. Parent gas and byte memory
are inputs; the child allowance and initcode bytes are computed. This module
is not a canonical Stmt arm: whole-frame gas tracking and source-memory
refinement are still required before importer admission. -/
namespace Compiler.CompilationModel.Create2Opcode

open Verity.Core
open Compiler.CompilationModel
open DenoteMemory

structure Context where
  creator : Address
  value : Uint256 := 0
  gas : Nat
  depth : Nat := 0
  isStatic : Bool := false

inductive Control where
  | outOfGas
  | creation (control : DenoteCreate2.Control)
  deriving DecidableEq, Repr

structure Result where
  control : Control
  world : Verity.ContractState
  memory : Memory
  gasLeft : Nat
  childGas : Nat := 0
  childGasLeft : Nat := 0

/-- Expansion exposes zero-filled bytes, even if the total backing function
contains arbitrary values beyond the old active memory. -/
def expand (memory : Memory) (words : Nat) : Memory :=
  { bytes := memory.readByte, size := 32 * words }

def execute (hash : DenoteCreate2.ByteHash) (world : Verity.ContractState)
    (memory : Memory) (context : Context) (salt offset size : Uint256) : Except String Result := do
  if context.isStatic then
    return { control := .creation (.abort .staticViolation), world, memory, gasLeft := 0 }
  if size.val > 49152 then
    return { control := .creation (.abort .initcodeSize), world, memory, gasLeft := 0 }
  unless memory.size % 32 = 0 do
    throw "CREATE2 opcode memory size is not word aligned"
  match Create2ParentGas.charge context.gas (memory.size / 32) offset.val size.val with
  | .outOfGas => return { control := .outOfGas, world, memory, gasLeft := 0 }
  | .charged charged =>
      let code := List.ofFn fun index : Fin size.val => memory.readByte (offset.val + index.val)
      let created ← DenoteCreate2.denoteCreate2 hash world
        { creator := context.creator, value := context.value, childGas := charged.childGas,
          depth := context.depth } salt code
      let gasLeft ← Create2ParentGas.finish charged created.childGasLeft
      return { control := .creation created.control,
               world := { created.world with returndata := [] },
               memory := expand memory charged.memoryWords,
               gasLeft, childGas := charged.childGas, childGasLeft := created.childGasLeft }

theorem expand_before (memory : Memory) (words offset : Nat)
    (active : offset < memory.size) (grows : memory.size ≤ 32 * words) :
    (expand memory words).readByte offset = memory.readByte offset := by
  simp [expand, Memory.readByte, active, show offset < 32 * words by omega]

theorem expand_new_zero (memory : Memory) (words offset : Nat)
    (fresh : memory.size ≤ offset) :
    (expand memory words).readByte offset = zeroByte := by
  simp [expand, Memory.readByte, show ¬offset < memory.size by omega]

theorem static_aborts (hash : DenoteCreate2.ByteHash) (world : Verity.ContractState)
    (memory : Memory) (context : Context) (salt offset size : Uint256) :
    execute hash world memory { context with isStatic := true } salt offset size =
      .ok { control := .creation (.abort .staticViolation), world, memory, gasLeft := 0 } := rfl

theorem oversized_aborts (hash : DenoteCreate2.ByteHash) (world : Verity.ContractState)
    (memory : Memory) (context : Context) (salt offset size : Uint256)
    (notStatic : context.isStatic = false) (oversized : size.val > 49152) :
    execute hash world memory context salt offset size =
      .ok { control := .creation (.abort .initcodeSize), world, memory, gasLeft := 0 } := by
  simp [execute, notStatic, oversized]
  rfl

end Compiler.CompilationModel.Create2Opcode

import Verity.Core.Model.Create2Access

/-! Ephemeral execution-frame state, separate from the rollbackable world.
Every field is required when the context is present. `none` at a legacy
execution entry means unknown context, never infinite gas or non-static mode.
Creation must refuse execution if the actual context is unavailable. -/
namespace Verity.Core.Model

structure ExecutionContext where
  opcode : Create2Entry.Context
  warm : Create2Access.WarmAccounts

/-- Same-caller rollback restores the access snapshot but retains current gas,
depth and mode. This does not execute the surrounding caller instructions. -/
def ExecutionContext.rollback (snapshot current : ExecutionContext) : ExecutionContext :=
  { current with warm := snapshot.warm }

theorem ExecutionContext.rollback_gas (snapshot current : ExecutionContext) :
    (snapshot.rollback current).opcode.gas = current.opcode.gas := rfl

theorem ExecutionContext.rollback_warm (snapshot current : ExecutionContext) :
    (snapshot.rollback current).warm = snapshot.warm := rfl

end Verity.Core.Model

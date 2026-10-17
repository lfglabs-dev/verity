import Compiler.Proofs.IRGeneration.CreationIR

/-! Effectful CREATE2 builtin boundary. This consumes the actual IR local
state and the required canonical account world; it never synthesizes accounts
or opcode gas. The legacy pure expression evaluator cannot use this API until
its result carrier can preserve these effects and errors. -/
namespace Compiler.Proofs.IRGeneration.CreationIRDispatch
open Verity.Core Verity.Core.Model

/-- Synchronize the executing account's flat slots and transient slots. Parked
account slots and source channel keys remain in the supplied world. Physical
memory is authoritative; the compatibility word view is recomputed. -/
def synchronize (world : Verity.ContractState) (state : IRState) : Verity.ContractState :=
  let synced :=  world.withStorageWords fun key =>
    match key with
    | .slot slot => Uint256.ofNat (state.storage (IRStorageSlot.ofNat slot)).toNat
    | .transient slot => Uint256.ofNat (state.transientStorage slot)
    | other => world.storageWords other
  { synced.installPhysicalMemory state.byteMemory with returndata := state.returndata }

theorem synchronize_accounts (world : Verity.ContractState) (state : IRState) :
    (synchronize world state).creationAccounts = world.creationAccounts := rfl

theorem synchronize_parked_storage (world : Verity.ContractState) (state : IRState)
    (owner slot : Nat) :
    (synchronize world state).storageWords (.contractSlot owner slot) =
      world.storageWords (.contractSlot owner slot) := rfl

theorem synchronize_scoped_storage (world : Verity.ContractState) (state : IRState)
    (owner : Nat) (key : Verity.StorageKey) :
    (synchronize world state).storageWords (.scoped owner key) =
      world.storageWords (.scoped owner key) := rfl

theorem synchronize_slot (world : Verity.ContractState) (state : IRState) (slot : Nat) :
    (synchronize world state).readSlot slot =
      Uint256.ofNat (state.storage (IRStorageSlot.ofNat slot)).toNat := rfl

theorem synchronize_byteMemory (world : Verity.ContractState) (state : IRState) :
    (synchronize world state).byteMemory = state.byteMemory := rfl

/-- Dispatch already-evaluated EVM operands. Argument expression evaluation
and its ordering belong to the enclosing effectful executor. Nonzero value
is outside the proved creation subset and fails interpretation precisely. -/
def dispatch (state : IRState) (args : List Nat) :
    Except String (CreationOutcome (Nat × IRState)) :=
  match args with
  | [value, offset, size, salt] =>
      if value % Compiler.Constants.evmModulus != 0 then
        .error "CREATE2 nonzero value is unsupported"
      else
        match state.creationWorld with
        | none => .error "CREATE2 requires an actual canonical account world"
        | some world =>
            if world.thisAddress.val != state.thisAddress then
              .error "CREATE2 canonical caller address disagrees with IR state"
            else
              match state.executionContext with
              | none => .error "CREATE2 requires an actual opcode-entry execution context"
              | some context =>
                  match Create2Operation.run
                      { world := synchronize world state, context := context.opcode,
                        warm := context.warm }
                      (Uint256.ofNat offset) (Uint256.ofNat size) (Uint256.ofNat salt) with
                  | .error message => .error message
                  | .ok (.exceptional frame) =>
                      .ok (.exceptional (0, CreationIR.project frame.world state
                        (some { opcode := frame.context, warm := frame.warm })))
                  | .ok (.continued address frame) =>
                      .ok (.continued (address.val, CreationIR.project frame.world state
                        (some { opcode := frame.context, warm := frame.warm })))
  | _ => .error "CREATE2 requires exactly four operands"

theorem dispatch_missing_world (state : IRState) (offset size salt : Nat)
    (missing : state.creationWorld = none) :
    dispatch state [0, offset, size, salt] =
      .error "CREATE2 requires an actual canonical account world" := by
  simp [dispatch, missing]

end Compiler.Proofs.IRGeneration.CreationIRDispatch

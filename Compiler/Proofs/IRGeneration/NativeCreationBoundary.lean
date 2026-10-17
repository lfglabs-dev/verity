import Compiler.Proofs.IRGeneration.IRCreationInterpreter
import Compiler.Proofs.IRGeneration.CreationBytecode

/-! Native-authenticated CREATE2 expression boundary. The native prefix is
executed, never supplied as a context schedule. Operand and physical-memory
agreement are checked before invoking the effectful IR primitive. Canonical
world and persistent/transient slot agreement remain explicit proof inputs;
this is not a compiler-wide or whole-function translation certificate. -/
namespace Compiler.Proofs.IRGeneration.NativeCreationBoundary
open EvmYul Verity.Core.Model

/-- The actual caller's canonical world is shared, not an IR postworld oracle.
Native caller prefixes supported here contain no storage-writing instructions. -/
structure Candidate (before : CreationBytecode.Frame) where
  state : IRState
  world : state.creationWorld = some before.world
  caller : state.thisAddress = before.world.thisAddress.val
  slots : ∀ key, (CreationIRDispatch.synchronize before.world state).storageWords key =
    before.world.storageWords key
  returndata : state.returndata = before.world.returndata

/-- Compare every active physical byte, including zero suffixes, rather than
only the constructor range. A mismatching memory is not overwritten to pass. -/
def memoryAgrees (machine : EVM.State) (state : IRState) : Bool :=
  let actual := CreationCaller.physicalBytes machine
  state.byteMemory.size == actual.size &&
    (List.range actual.size).all (fun index =>
      state.byteMemory.readByte index == actual[index]!.toNat)

/-- Only this executed machine constructs the context. Candidate context and
manual schedules are not read, even if populated. -/
def runtime (before : CreationBytecode.Frame) (machine : EVM.State)
    (candidate : Candidate before) : IRCreationInterpreter.Runtime :=
  { state := candidate.state
    creationContexts := [CreationCaller.context machine before.warm] }

/-- Execute the actual caller prefix and check its CREATE2 stack operands
against the right-to-left IR argument evaluation. Nested creation arguments
need their own authenticated native boundary and are refused here. -/
def run (fuel expressionFuel : Nat) (before : CreationBytecode.Frame)
    (candidate : Candidate before) (args : List Compiler.Yul.YulExpr) :
    Except String (IRCreationInterpreter.Outcome Nat) := do
  if before.world.thisAddress.val != before.machine.executionEnv.codeOwner then
    throw "native CREATE2 boundary caller address mismatch"
  if (before.world.creationAccounts before.world.thisAddress.val).code.data !=
      before.machine.executionEnv.code.data then
    throw "native CREATE2 boundary caller code mismatch"
  let executed ← CreationCaller.run fuel before.machine
  match executed with
  | .exceptional _ _ =>
      throw "native CREATE2 boundary prefix halted exceptionally before CREATE2"
  | .ready machine =>
      if machine.stack.length > 1024 then
        throw "native CREATE2 boundary stack exceeds 1024 words"
      match machine.stack with
      | value :: offset :: size :: salt :: _ =>
          if !memoryAgrees machine candidate.state then
            throw "native CREATE2 boundary physical memory mismatch"
          match IRCreationInterpreter.evalArgs expressionFuel
              { state := candidate.state, creationContexts := [] } args with
          | .interpretationError message => throw message
          | .exceptional _ | .stop _ | .revert _ _ =>
              throw "native CREATE2 boundary argument evaluation did not produce operands"
          | .value values afterArgs =>
              let expected := [value.toNat, offset.toNat, size.toNat, salt.toNat]
              if values.map (fun word => word % Compiler.Constants.evmModulus) != expected then
                throw "native CREATE2 boundary operand mismatch"
              -- evalArgs has no authenticated creation context, so it cannot
              -- perform creation; read-only argument evaluation retains state.
              pure (IRCreationInterpreter.invokeCreate2
                { afterArgs with creationContexts := [CreationCaller.context machine before.warm] }
                values)
      | _ => throw "native CREATE2 boundary requires four native stack operands"

theorem runtime_schedule (before : CreationBytecode.Frame) (machine : EVM.State)
    (candidate : Candidate before) :
    (runtime before machine candidate).creationContexts =
      [CreationCaller.context machine before.warm] := rfl

theorem runtime_state (before : CreationBytecode.Frame) (machine : EVM.State)
    (candidate : Candidate before) :
    (runtime before machine candidate).state = candidate.state := rfl

end Compiler.Proofs.IRGeneration.NativeCreationBoundary

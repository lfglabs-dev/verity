import Compiler.Proofs.IRGeneration.NativeCreationBoundary
import Compiler.Proofs.IRGeneration.DenoteTypedCreationAgreement
namespace SolidityImportSmoke.NativePreparedCreationChecks
open Compiler.Yul Compiler.Proofs.IRGeneration
open Compiler.Proofs.IRGeneration.NativeCreationBoundary
open Compiler.CompilationModel.DenoteMemory Verity.Core.Model
private def constructorWord : Nat := 43441855373900879501489557976705837587736829351010673829379042307146688495616
private def code : ByteArray := ⟨#[127, 96, 11, 56, 3, 128, 96, 11, 95, 57, 95, 243, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 95, 82, 96, 7, 96, 11, 95, 95, 245]⟩
private def world : Verity.ContractState :=
  { Verity.defaultState with
    thisAddress := Verity.Core.Address.ofNat 4096
    creationAccounts := fun query => if query == 4096 then { code := code } else {} }
private def before : CreationBytecode.Frame :=
  { world := world, warm := fun query => query == 4096
    machine := { (Inhabited.default : EvmYul.EVM.State) with
      gasAvailable := .ofNat 1000000
      executionEnv := { (Inhabited.default : EvmYul.ExecutionEnv .EVM) with
        codeOwner := EvmYul.AccountAddress.ofUInt256 (.ofNat 4096)
        code := code, perm := true } } }
private def initial : IRCreationInterpreter.Runtime :=
  { state := { IRState.initial 0 with creationWorld := some world, thisAddress := 4096 }
    creationContexts := [] }
private def prepared : IRState :=
  match IRCreationInterpreter.execStmt 32 initial
    (.exprStmt (.call "mstore" [.lit 0, .lit constructorWord])) with
  | .value _ next => next.state
  | _ => initial.state
private def candidate : Candidate before :=
  { state := prepared
    world := by rfl
    caller := by rfl
    slots := by
      intro key
      cases key <;> simp [CreationIRDispatch.synchronize, prepared, initial,
        IRCreationInterpreter.execStmt, IRCreationInterpreter.evalArgs,
        IRCreationInterpreter.evalExpr, IRCreationInterpreter.Outcome.bind,
        IRCreationInterpreter.invokeMstore, IRState.writePhysicalMemoryValue,
        IRState.installPhysicalMemory, before, world, IRState.initial, Verity.defaultState,
        Verity.ContractState.withStorageWords, Verity.ContractState.installPhysicalMemory]
      rfl
    returndata := by rfl }
def runChecks : IO Unit := do
  let native ← IO.ofExcept (CreationBytecode.run 64 before)
  let native ← match native with
    | .continued frame => pure frame
    | _ => throw (IO.userError "native prepared creation failed")
  let result ← IO.ofExcept (run 64 32 before candidate
    [.lit 0, .lit 0, .lit 11, .lit 7])
  match result with
  | .value address next =>
      unless address != 0 && address == (native.machine.stack.getD 0 (.ofNat 0)).toNat do
        throw (IO.userError "prepared constructor address diverged")
      match next.state.executionContext with
      | some context => unless context.opcode.gas == native.machine.gasAvailable.toNat do
          throw (IO.userError "prepared constructor gas diverged")
      | none => throw (IO.userError "prepared constructor context missing")
  | _ => throw (IO.userError "prepared IR creation failed")
  let sourceModel : Compiler.CompilationModel.CompilationModel :=
    { name := "PreparedCreation", fields := [], functions := [], constructor := none }
  let sourceInitial : SourceSemantics.RuntimeState := { world := world, bindings := [] }
  let sourcePrepared ← match SourceStatementEvaluation.execStmt sourceModel [] 32 sourceInitial
      (.mstore (.literal 0) (.literal constructorWord)) with
    | .continue state => pure state
    | _ => throw (IO.userError "typed Source constructor memory preparation failed")
  let entry ← match ← IO.ofExcept (CreationCaller.run 64 before.machine) with
    | .ready machine => pure machine
    | _ => throw (IO.userError "actual native opcode-entry execution failed")
  let sourceAtEntry := { sourcePrepared with executionContext := some (CreationCaller.context entry before.warm) }
  match SourceStatementEvaluation.execStmt sourceModel [] 32 sourceAtEntry
      (.create2 "created" (.literal 0) (.literal 11) (.literal 7)) with
  | .continue state =>
      let address := SourceSemantics.lookupValue state.bindings "created"
      unless address == (native.machine.stack.getD 0 (.ofNat 0)).toNat &&
          (state.world.creationAccounts address).code.data == (native.world.creationAccounts address).code.data &&
          (state.world.creationAccounts address).nonce == (native.world.creationAccounts address).nonce &&
          (state.world.creationAccounts 4096).nonce == (native.world.creationAccounts 4096).nonce &&
          state.world.returndata == native.world.returndata do
        throw (IO.userError "typed Source/native creation account observations diverged")
      match state.executionContext with
      | some context => unless context.opcode.gas == native.machine.gasAvailable.toNat do
          throw (IO.userError "typed Source/native creation gas diverged")
      | none => throw (IO.userError "typed Source creation lost actual context")
      unless state.world.byteMemory.size == native.world.byteMemory.size do
        throw (IO.userError "typed Source/native memory size diverged")
      for offset in List.range state.world.byteMemory.size do
        unless state.world.byteMemory.readByte offset == native.world.byteMemory.readByte offset do
          throw (IO.userError "typed Source/native memory bytes diverged")
  | _ => throw (IO.userError "typed Source prepared creation failed")
  let denoteInitial : Compiler.CompilationModel.Denote.DenoteState := { world := world, bindings := [] }
  let denotePrepared ← match Compiler.CompilationModel.Denote.execStmt DenoteAgreement.sourceOracle []
      denoteInitial (.mstore (.literal 0) (.literal constructorWord)) with
    | .continue state => pure state
    | _ => throw (IO.userError "Denote constructor memory preparation failed")
  let denoteAtEntry := { denotePrepared with executionContext := some (CreationCaller.context entry before.warm) }
  match Compiler.CompilationModel.Denote.execCreation DenoteAgreement.sourceOracle [] denoteAtEntry
      "created" (.literal 0) (.literal 11) (.literal 7) with
  | .continue state =>
      let address := Compiler.CompilationModel.Denote.lookupValue state.bindings "created"
      unless address == (native.machine.stack.getD 0 (.ofNat 0)).toNat &&
          (state.world.creationAccounts address).code.data == (native.world.creationAccounts address).code.data &&
          (state.world.creationAccounts address).nonce == (native.world.creationAccounts address).nonce &&
          (state.world.creationAccounts 4096).nonce == (native.world.creationAccounts 4096).nonce &&
          state.world.returndata == native.world.returndata do
        throw (IO.userError "Denote/native creation account observations diverged")
      match state.executionContext with
      | some context => unless context.opcode.gas == native.machine.gasAvailable.toNat do
          throw (IO.userError "Denote/native creation gas diverged")
      | none => throw (IO.userError "Denote creation lost actual context")
      unless state.world.byteMemory.size == native.world.byteMemory.size do
        throw (IO.userError "Denote/native memory size diverged")
      for offset in List.range state.world.byteMemory.size do
        unless state.world.byteMemory.readByte offset == native.world.byteMemory.readByte offset do
          throw (IO.userError "Denote/native memory bytes diverged")
  | _ => throw (IO.userError "Denote prepared creation failed")
  IO.println s!"ADDRESS:{(native.machine.stack.getD 0 (.ofNat 0)).toNat}"
  IO.println s!"GAS:{native.machine.gasAvailable.toNat}"
  IO.println "actual IR memory preparation and authenticated native creation passed"
end SolidityImportSmoke.NativePreparedCreationChecks
def main : IO Unit := SolidityImportSmoke.NativePreparedCreationChecks.runChecks

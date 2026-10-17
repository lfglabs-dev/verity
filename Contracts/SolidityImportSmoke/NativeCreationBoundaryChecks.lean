import Compiler.Proofs.IRGeneration.NativeCreationBoundary

namespace SolidityImportSmoke.NativeCreationBoundaryChecks
open Compiler.Yul Compiler.Proofs.IRGeneration
open Compiler.Proofs.IRGeneration.NativeCreationBoundary
open Compiler.CompilationModel.DenoteMemory Verity.Core.Model

private def code : ByteArray :=
  ⟨#[0x60, 7, 0x60, UInt8.ofNat MidnightInitcode.header.size, 0x5f, 0x5f, 0xf5]⟩
private def memory : Memory :=
  Memory.empty.copyFrom (MidnightInitcode.codeByte (MidnightInitcode.initcode ByteArray.empty)) 0 0 64
private def world : Verity.ContractState :=
  { Verity.defaultState with
    thisAddress := Verity.Core.Address.ofNat 1
    creationAccounts := fun query => if query == 1 then { code := code } else {} }
private def before : CreationBytecode.Frame :=
  { world := world
    warm := fun query => query == 1
    machine := { (Inhabited.default : EvmYul.EVM.State) with
      gasAvailable := .ofNat 1000000
      activeWords := .ofNat 2
      memory := MidnightInitcode.memorySlice memory 0 64
      executionEnv := { (Inhabited.default : EvmYul.ExecutionEnv .EVM) with
        codeOwner := EvmYul.AccountAddress.ofUInt256 (.ofNat 1)
        code := code
        perm := true } } }
private def candidate (bytes : Memory) : Candidate before :=
  { state := { IRState.initial 0 with
      creationWorld := some world
      thisAddress := 1
      byteMemory := bytes
      executionContext := some {
        opcode := { gas := 0, depth := 9, isStatic := true }
        warm := fun _ => false } }
    world := rfl
    caller := rfl
    slots := by
      intro key
      cases key <;> simp [CreationIRDispatch.synchronize, before, world, IRState.initial, Verity.defaultState, Verity.ContractState.withStorageWords, Verity.ContractState.installPhysicalMemory]
      rfl
    returndata := by rfl }
private def args : List YulExpr :=
  [.lit 0, .lit 0, .lit MidnightInitcode.header.size, .lit 7]
private def expectError (result : Except String (IRCreationInterpreter.Outcome Nat))
    (expected : String) : IO Unit := do
  match result with
  | .error message => unless message == expected do throw (IO.userError message)
  | .ok _ => throw (IO.userError "native boundary accepted a mismatching input")

def runChecks : IO Unit := do
  let native ← IO.ofExcept (CreationBytecode.run 32 before)
  let native ← match native with
    | .continued frame => pure frame
    | .exceptional _ => throw (IO.userError "native positive control halted exceptionally")
  let result ← IO.ofExcept (run 32 32 before (candidate memory) args)
  match result with
  | .value address next =>
      unless address == (native.machine.stack.getD 0 (.ofNat 0)).toNat &&
          address != 0 && next.creationContexts.isEmpty do
        throw (IO.userError "authenticated boundary lost creation or reused context")
      match next.state.executionContext with
      | some actual => unless actual.opcode.gas == native.machine.gasAvailable.toNat &&
          actual.opcode.gas > 0 && actual.opcode.depth == 0 &&
          !actual.opcode.isStatic do
          throw (IO.userError "authenticated boundary used the poisoned candidate context")
      | none => throw (IO.userError "authenticated boundary lost computed context")
  | _ => throw (IO.userError "authenticated native boundary failed")
  expectError (run 32 32 before (candidate Memory.empty) args)
    "native CREATE2 boundary physical memory mismatch"
  expectError (run 32 32 before (candidate (memory.writeByte 63 ⟨1, by decide⟩)) args)
    "native CREATE2 boundary physical memory mismatch"
  expectError (run 32 32 before (candidate memory)
    [.lit 0, .lit 0, .lit MidnightInitcode.header.size, .lit 8])
    "native CREATE2 boundary operand mismatch"
  expectError (run 32 32 before (candidate memory)
    [.ident "left_missing", .ident "right_missing"])
    "unbound effectful IR variable: right_missing"
  expectError (run 0 32 before (candidate memory) args)
    "caller execution fuel exhausted at bytecode pc 0"
  IO.println "native CREATE2 context, memory and operand authentication passed"
end SolidityImportSmoke.NativeCreationBoundaryChecks

def main : IO Unit := SolidityImportSmoke.NativeCreationBoundaryChecks.runChecks

import Compiler.Proofs.IRGeneration.HelperBodyBridge

namespace SolidityImportSmoke.HelperBodyContextChecks
open Compiler Compiler.CompilationModel Compiler.Proofs.IRGeneration
open SourceSemantics

-- These check the actual bridge, including caller-local restoration and the
-- callee's captured payload/context. No operational refusal is a certificate.
example (caller terminal : IRState) (helper : IRInternalFunctionDef) :
    internalHelperBodyIRExecResultAsCallResult caller helper (.revert terminal) =
      .revert (restoreCallerVars caller terminal) := rfl

example (caller terminal : IRState) (helper : IRInternalFunctionDef) :
    internalHelperBodyIRExecResultAsCallResult caller helper (.exceptional terminal) =
      .exceptional (restoreCallerVars caller terminal) := rfl

example (caller : IRState) (helper : IRInternalFunctionDef) (message : String) :
    internalHelperBodyIRExecResultAsCallResult caller helper (.interpretationError message) =
      .interpretationError message := rfl

example (caller terminal : IRState) (helper : IRInternalFunctionDef) (names : List String) :
    internalHelperAssignCallResult names caller helper (.exceptional terminal) =
      .exceptional (restoreCallerVars caller terminal) := rfl

example (caller : IRState) (helper : IRInternalFunctionDef) (names : List String)
    (message : String) :
    internalHelperAssignCallResult names caller helper (.interpretationError message) =
      .interpretationError message := rfl

example (spec : CompilationModel) (callee : FunctionSpec) (world : Verity.ContractState)
    (fuel : Nat) (args : List Nat) (context : Option Verity.Core.Model.ExecutionContext)
    (oracle : Nat → ExternalCallOutcome) (index : Nat) :
    internalHelperBodyInterpretation spec fuel callee world 0 args context oracle index =
      interpretInternalFunctionFuel spec fuel callee world args
        (externalCallOracle := oracle) (externalCallIndex := index) (executionContext := context) :=
  internalHelperBodyInterpretation_selector_zero_eq_interpretInternalFunctionFuel
    spec fuel callee world args context oracle index

private def errors : List ErrorDef := [{ name := "BadValue", params := [.uint256, .address, .bool] }]
private def model : CompilationModel :=
  { name := "HelperBodyContext", fields := [], functions := [], constructor := none, errors }
private def context : Verity.Core.Model.ExecutionContext :=
  { opcode := { gas := 19, depth := 7, isStatic := false }, warm := fun _ => false }

private def requireBytes (result : InternalFunctionResult) (expected : List UInt8) : IO Unit := do
  unless !result.success && result.returnValue.isNone && result.exceptionalState.isNone &&
      result.interpretationError.isNone && result.revertData == expected do
    throw (IO.userError "helper body bridge lost declared custom-error bytes")

def runChecks : IO Unit := do
  let caller := { IRState.initial 7 with vars := [("caller", 51)] }
  let terminal := { (caller.writePhysicalMemoryValue 0 0xdead).captureRevert 30 2 with
    vars := [("callee", 99)], executionContext := some context }
  let helper : IRInternalFunctionDef := { name := "helper", params := [], rets := [], body := [] }
  match internalHelperBodyIRExecResultAsCallResult caller helper (.revert terminal) with
  | .revert observed =>
      unless observed.revertBytes == some [0xde, 0xad] && observed.vars == caller.vars &&
          observed.executionContext.map (·.opcode.depth) == some 7 do
        throw (IO.userError "IR helper REVERT lost payload, context or caller locals")
  | _ => throw (IO.userError "IR helper REVERT became another result")
  match internalHelperAssignCallResult [] caller helper (.exceptional terminal) with
  | .exceptional observed =>
      unless observed.executionContext.map (·.opcode.depth) == some 7 &&
          observed.vars == caller.vars && observed.memory 0 == 0xdead do
        throw (IO.userError "IR assigning helper exception lost actual terminal state")
  | _ => throw (IO.userError "IR assigning helper exception erased")
  match internalHelperAssignCallResult [] caller helper (.interpretationError "precise refusal") with
  | .interpretationError message =>
      unless message == "precise refusal" do throw (IO.userError "IR helper refusal changed")
  | _ => throw (IO.userError "IR helper refusal acquired EVM status")
  let world := { Verity.defaultState with returndata := [0x1234] }
  let calling : FunctionSpec :=
    { name := "calling", params := [], returnType := some .uint256, isInternal := true,
      body := [.externalCallBind ["receipt"] "oracle" [], .return (.localVar "receipt")] }
  let oracle := fun index =>
    { succeeded := true, returnValues := [100 + index],
      postCallWorld := some (Verity.defaultState.writeSlot 0 (700 + index)) : ExternalCallOutcome }
  let called := internalHelperBodyInterpretation model 8 calling world 0 [] (some context) oracle 3
  unless called.success && called.returnValue == some 103 && called.externalCallIndex == 4 &&
      called.world.readSlot 0 == 703 do
    throw (IO.userError "helper-body interpretation replaced actual oracle or receipt cursor")
  let reverting : FunctionSpec :=
    { name := "reverting", params := [], returnType := none, isInternal := true,
      body := [.revertError "BadValue" [.literal 7, .literal 9, .literal 1]] }
  let expected : List UInt8 := [0x6a, 0x5e, 0xeb, 0xe1] ++ Denote.wordBytes 7 ++
    Denote.wordBytes 9 ++ Denote.wordBytes 1
  -- An independent Ethereum selector, not bytes obtained from the bridge.
  requireBytes (internalHelperBodyInterpretation model 4 reverting world 0 [] (some context)) expected
  requireBytes (interpretInternalFunctionFuel model 4 reverting world []
    (executionContext := some context)) expected
  let copy : FunctionSpec :=
    { name := "copy", params := [], returnType := none, isInternal := true,
      body := [.returndataCopy (.literal 0) (.literal 33) (.literal 0)] }
  let observed := internalHelperBodyInterpretation model 4 copy world 0 [] (some context)
  match observed.exceptionalState with
  | some terminal =>
      unless terminal.executionContext.map (·.opcode.gas) == some 0 &&
          terminal.executionContext.map (·.opcode.depth) == some 7 &&
          !observed.success && observed.interpretationError.isNone do
        throw (IO.userError "contextual helper-body exception changed")
  | none => throw (IO.userError "helper-body exception erased")
  let refused := internalHelperBodyInterpretation model 4 copy world 0 [] none
  unless refused.interpretationError ==
      some "returndata copy exceptional exit requires actual opcode context" &&
      refused.exceptionalState.isNone && !refused.success do
    throw (IO.userError "contextless helper body acquired an EVM result")
  IO.println "Helper-body actual context, error bytes, exception and refusal checks passed"

end SolidityImportSmoke.HelperBodyContextChecks

def main : IO Unit := SolidityImportSmoke.HelperBodyContextChecks.runChecks

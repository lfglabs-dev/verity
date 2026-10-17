import Compiler.Proofs.IRGeneration.NativeCapturedMappingHelper

namespace SolidityImportSmoke.NativeMappingHelperChecks

open EvmYul Compiler.Proofs.IRGeneration.CapturedMappingHelper

def runChecks : IO Unit := do
  let values : List Nat := [0, 1, 31, 2^256 - 1]
  let mut boundaries := 0
  let mut executions := 0
  for gas in ([84, 85, 86, 100000] : List Nat) do
    for base in values do
      for key in values do
        let calldata := (UInt256.ofNat base).toByteArray ++ (UInt256.ofNat key).toByteArray
        let initial : EVM.State := { (Inhabited.default : EVM.State) with
          toState := { (Inhabited.default : State .EVM) with
            executionEnv := { (Inhabited.default : ExecutionEnv .EVM) with code := optimized, calldata := calldata } }
          gasAvailable := UInt256.ofNat gas
          pc := UInt256.ofNat 0
          stack := []
          memory := ByteArray.empty
          activeWords := UInt256.ofNat 0 }
        for stage in List.finRange 17 do
          match checkedSteps stage.val initial with
          | .error .OutOfGass =>
            unless gas == 84 && stage.val >= 15 do
              throw (IO.userError s!"unexpected checked OOG: {gas}/{base}/{key}/{stage.val}")
          | .error reason => throw (IO.userError s!"unexpected checked failure: {repr reason}")
          | .ok actual =>
            let expected := helperStage initial stage
            unless actual.pc == expected.pc && actual.stack == expected.stack &&
                actual.memory == expected.memory && actual.gasAvailable == expected.gasAvailable &&
                actual.activeWords == expected.activeWords && actual.H_return == expected.H_return &&
                actual.execLength == expected.execLength do
              throw (IO.userError s!"boundary mismatch: {gas}/{base}/{key}/{stage.val}")
            boundaries := boundaries + 1
        match EVM.X 17 (EVM.D_J optimized (UInt256.ofNat 0)) initial with
        | .error .OutOfGass =>
          unless gas == 84 do throw (IO.userError s!"unexpected native OOG: {gas}")
        | .ok (.success final output) =>
          unless gas >= 85 && final.gasAvailable.toNat == gas - 85 &&
              output == KeccakEngine.keccak256 (Compiler.Proofs.abiEncodeMappingSlot base key) do
            throw (IO.userError s!"native boundary result differs: {gas}/{base}/{key}")
        | _ => throw (IO.userError "unexpected native result")
        executions := executions + 1
  IO.println s!"BOUNDARY_SUCCESS: executions={executions}; checkedBoundaries={boundaries}"

end SolidityImportSmoke.NativeMappingHelperChecks

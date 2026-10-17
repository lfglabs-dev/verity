import Compiler.SolidityImport.ByteCallTransactions

open Compiler.CompilationModel
open Compiler.CompilationModel.SolidityImport

-- These laws quantify over every real ContractState and retain arbitrary raw
-- payloads (no word-padding assumption) and account-qualified access traces.
example (entry : Verity.ContractState) (state : DenoteByteExternalCalls.State) :
    ByteCallTransactions.bubble entry { success := false, state } = .ok
      { frame := { success := false, data := state.returndata, world := entry }
        touched := state.touched } :=
  ByteCallTransactions.bubble_failure entry _ rfl

example (entry : Verity.ContractState) (state : DenoteByteExternalCalls.State) :
    ByteCallTransactions.bubble entry { success := true, state } =
      .error "cannot bubble a successful external call" :=
  ByteCallTransactions.bubble_success_rejected entry _ rfl

#print axioms ByteCallTransactions.bubble_failure
#print axioms ByteCallTransactions.bubble_success_rejected

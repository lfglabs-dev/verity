import Verity.Core.Model.DenoteByteExternalCalls

open Compiler.CompilationModel
open ByteExternalCall

namespace DenoteBoundaryChecks

-- The real storage carrier uses account-qualified keys; rollback must restore
-- these as well as caller-local keys, while retaining traces of cancelled writes.
example (entry : Denote.DenoteState) (state : DenoteByteExternalCalls.State)
    (data : Bytes) (account slot : Nat) :
    (DenoteByteExternalCalls.rollbackOuter entry state data).frame.world.storageWords
      (.contractSlot account slot) = entry.world.storageWords (.contractSlot account slot) := rfl

example (entry : Denote.DenoteState) (state : DenoteByteExternalCalls.State) :
    (DenoteByteExternalCalls.rollbackOuter entry state [0, 255, 0]).returndata = [0, 255, 0] := rfl

example (entry : Denote.DenoteState) (state : DenoteByteExternalCalls.State) :
    (DenoteByteExternalCalls.rollbackOuter entry state [0]).touched = state.touched := rfl

-- Calls cannot accidentally change caller-local bindings by installing an
-- adversary's world. This holds for arbitrary request-dependent adversaries.
example (adversary : DenoteByteExternalCalls.Adversary) (request : Request)
    (state : DenoteByteExternalCalls.State) :
    (DenoteByteExternalCalls.execute adversary request state).state.frame.bindings =
      state.frame.bindings := rfl

#print axioms DenoteByteExternalCalls.execute_bindings
#print axioms DenoteByteExternalCalls.execute_static_world
#print axioms DenoteByteExternalCalls.execute_revert_world
#print axioms DenoteByteExternalCalls.execute_revert_bytes
#print axioms DenoteByteExternalCalls.execute_revert_touched
#print axioms DenoteByteExternalCalls.rollbackOuter_storageWords
#print axioms DenoteByteExternalCalls.rollbackOuter_events
#print axioms DenoteByteExternalCalls.rollbackOuter_accesses

end DenoteBoundaryChecks

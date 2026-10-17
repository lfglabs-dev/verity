import Compiler.Proofs.IRGeneration.CustomErrorMemoryFrame

namespace SolidityImportSmoke.IRMemoryCoherenceChecks
open Compiler.CompilationModel Compiler.Proofs.IRGeneration Compiler.Yul
open IRMemoryCoherence

-- Every actual statement/list and every result constructor remain covered.
example (fuel : Nat) (state : IRState) (stmt : YulStmt) (initial : Coherent state) :
    Preserves (execIRStmt fuel state stmt) := (executors fuel).1 state stmt initial

example (fuel : Nat) (state : IRState) (body : List YulStmt) (initial : Coherent state) :
    Preserves (execIRStmts fuel state body) := (executors fuel).2 state body initial

example (state : IRState) (offset value : Nat) :
    Coherent (state.writePhysicalMemoryValue offset value) := written state offset value

example (state : IRState) (offset value query : Nat) (initial : Coherent state)
    (disjoint : query + 32 ≤ offset ∨ offset + 32 ≤ query) :
    (state.writePhysicalMemoryValue offset value).memory query = state.memory query :=
  word_outside_store state offset value query initial disjoint

example (spec : CompilationModel) (runtime : SourceSemantics.RuntimeState)
    (state : IRState) (offset value : Nat) (domain : CustomErrorDomain spec runtime state)
    (initial : Coherent state)
    (disjoint : freeMemoryPointer + 32 ≤ offset ∨ offset + 32 ≤ freeMemoryPointer) :
    CustomErrorDomain spec runtime (state.writePhysicalMemoryValue offset value) :=
  CustomErrorMemoryFrame.domain_store spec runtime state offset value domain initial disjoint

example (spec : CompilationModel) (runtime : SourceSemantics.RuntimeState)
    (state : IRState) (source : Nat → DenoteMemory.Byte) (dst src : Nat)
    (domain : CustomErrorDomain spec runtime state) :
    CustomErrorDomain spec runtime (state.copyPhysicalBytes source dst src 0) :=
  CustomErrorMemoryFrame.domain_copy_zero spec runtime state source dst src domain

-- An incoherent legacy observation is excluded from the frame premise.
example (state : IRState) (query : Nat)
    (mismatch : state.memory query ≠
      (DenoteMemory.wordValue (state.byteMemory.readWord query)).val) :
    ¬ Coherent state := by
  intro coherent
  unfold Coherent at coherent
  exact mismatch (coherent query)

end SolidityImportSmoke.IRMemoryCoherenceChecks

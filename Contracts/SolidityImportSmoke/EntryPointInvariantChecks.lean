import Compiler.SolidityImport.EntryPointInvariants

/-! A whole-model invariant across successful writes and a write followed by
rollback. This is a proof-infrastructure example, not importer coverage. -/
namespace SolidityImportSmoke.EntryPointInvariantChecks
open Compiler.CompilationModel
open Compiler.CompilationModel.Denote
open Compiler.CompilationModel.SolidityImport.Transactions

def fields : List Field := [{ name := "stored", ty := .uint256 }]

def zeroEntry : FunctionSpec :=
  { name := "zero", params := [], returnType := none
    body := [.setStorage "stored" (.literal 0), .stop] }

def oneEntry : FunctionSpec :=
  { name := "one", params := [], returnType := none
    body := [.setStorage "stored" (.literal 1), .stop] }

def failedEntry : FunctionSpec :=
  { name := "fail", params := [], returnType := none
    body := [.setStorage "stored" (.literal 99), .panicCode (.literal 1)] }

def model : CompilationModel :=
  { name := "EntryPointInvariant", fields, constructor := none
    functions := [zeroEntry, oneEntry, failedEntry] }

def invariant (world : Verity.ContractState) : Prop :=
  (world.storage 0).val ≤ 1

theorem zero_exec (oracle : DenoteOracle) (before : Verity.ContractState) (bindings : Env) :
    executeBody oracle fields before bindings zeroEntry.body [] =
      .ok ⟨true, [], writeUintFieldSlots fields "stored" (beginTransaction before) [0] 0⟩ := by
  rfl

theorem one_exec (oracle : DenoteOracle) (before : Verity.ContractState) (bindings : Env) :
    executeBody oracle fields before bindings oneEntry.body [] =
      .ok ⟨true, [], writeUintFieldSlots fields "stored" (beginTransaction before) [0] 1⟩ := by
  rfl

theorem failed_exec (oracle : DenoteOracle) (before : Verity.ContractState) (bindings : Env) :
    executeBody oracle fields before bindings failedEntry.body [] =
      .ok ⟨false, panicBytes 1, beginTransaction before⟩ := by
  rfl

theorem every_entry_preserves (oracle : DenoteOracle) :
    AllEntryPointsPreserve oracle model invariant := by
  intro fn member _ before bindings result initial executed
  simp only [model, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · change executeBody oracle fields before bindings zeroEntry.body [] = .ok result at executed
    rw [zero_exec] at executed
    cases executed
    change (0 : Nat) ≤ 1
    decide
  · change executeBody oracle fields before bindings oneEntry.body [] = .ok result at executed
    rw [one_exec] at executed
    cases executed
    change (1 : Nat) ≤ 1
    decide
  · change executeBody oracle fields before bindings failedEntry.body [] = .ok result at executed
    rw [failed_exec] at executed
    cases executed
    exact initial

theorem arbitrary_sequence_preserves (oracle : DenoteOracle)
    (before after : Verity.ContractState) (initial : invariant before)
    (sequence : EntryPointSequence oracle model before after) : invariant after :=
  invariant_of_all_entry_points oracle model invariant (every_entry_preserves oracle)
    before after initial sequence

end SolidityImportSmoke.EntryPointInvariantChecks

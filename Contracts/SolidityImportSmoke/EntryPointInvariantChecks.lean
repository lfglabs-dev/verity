import Compiler.SolidityImport.AdversarialEntryPointInvariants

/-! A whole-model invariant across successful writes and a write followed by
rollback, then under the callee-choosing frameworks: any callees, a callee that
calls back into the contract, and a step whose arguments decode from its frame.
This is a proof-infrastructure example, not importer coverage. -/
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

theorem zero_exec (oracle : DenoteOracle) (before : Verity.ContractState) (bindings : Env)
    {calls : ByteCallEnvironment} :
    executeBody oracle fields before bindings zeroEntry.body [] (byteCalls := calls) =
      .ok ⟨true, [], writeUintFieldSlots fields "stored" (beginTransaction before) [0] 0⟩ := by
  rfl

theorem one_exec (oracle : DenoteOracle) (before : Verity.ContractState) (bindings : Env)
    {calls : ByteCallEnvironment} :
    executeBody oracle fields before bindings oneEntry.body [] (byteCalls := calls) =
      .ok ⟨true, [], writeUintFieldSlots fields "stored" (beginTransaction before) [0] 1⟩ := by
  rfl

theorem failed_exec (oracle : DenoteOracle) (before : Verity.ContractState) (bindings : Env)
    {calls : ByteCallEnvironment} :
    executeBody oracle fields before bindings failedEntry.body [] (byteCalls := calls) =
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

/-- The same obligation with the callees chosen: no entry point calls out, so it holds for
every byte-call environment and every admitted set of calls. -/
theorem every_entry_preserves_with (oracle : DenoteOracle) (calls : ByteCallEnvironment)
    (admits : FunctionSpec → Verity.ContractState → Prop) :
    AllEntryPointsPreserveWith oracle calls model invariant (admits := admits) := by
  intro fn member _ before bindings result _ _ initial executed
  simp only [model, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · change executeBody oracle fields before bindings zeroEntry.body [] (byteCalls := calls)
      = .ok result at executed
    rw [zero_exec] at executed
    cases executed
    change (0 : Nat) ≤ 1
    decide
  · change executeBody oracle fields before bindings oneEntry.body [] (byteCalls := calls)
      = .ok result at executed
    rw [one_exec] at executed
    cases executed
    change (1 : Nat) ≤ 1
    decide
  · change executeBody oracle fields before bindings failedEntry.body [] (byteCalls := calls)
      = .ok result at executed
    rw [failed_exec] at executed
    cases executed
    exact initial

/-- Between steps the environment may change everything but the contract's storage. -/
def keepsStorage (before prepared : Verity.ContractState) : Prop :=
  prepared.storageWords = before.storageWords

theorem keepsStorage_preserves (before prepared : Verity.ContractState)
    (kept : keepsStorage before prepared) (initial : invariant before) : invariant prepared := by
  show (prepared.storageWords (.slot 0)).val ≤ 1
  rw [kept]
  exact initial

theorem callee_sequence_preserves
    (allowed : DenoteOracle → FunctionSpec → Verity.ContractState → Prop)
    (callees : ByteCallEnvironment → Prop) (before after : Verity.ContractState)
    (initial : invariant before)
    (sequence : CalleeEntryPointSequence model (fun _ => 0) keepsStorage allowed callees
      before after) :
    invariant after :=
  invariant_of_callee_entry_points model (fun _ => 0) invariant keepsStorage allowed callees
    keepsStorage_preserves
    (fun oracle calls _ => every_entry_preserves_with oracle calls (allowed oracle))
    before after initial sequence

theorem zero_exec_reentrant (oracle : DenoteOracle) (before : Verity.ContractState)
    (bindings : Env) {calls : ByteCallEnvironment} :
    executeReentrantBody oracle fields before bindings zeroEntry.body [] (byteCalls := calls) =
      .ok ⟨true, [], writeUintFieldSlots fields "stored" (beginReentrantFrame before) [0] 0⟩ := by
  rfl

theorem one_exec_reentrant (oracle : DenoteOracle) (before : Verity.ContractState)
    (bindings : Env) {calls : ByteCallEnvironment} :
    executeReentrantBody oracle fields before bindings oneEntry.body [] (byteCalls := calls) =
      .ok ⟨true, [], writeUintFieldSlots fields "stored" (beginReentrantFrame before) [0] 1⟩ := by
  rfl

theorem failed_exec_reentrant (oracle : DenoteOracle) (before : Verity.ContractState)
    (bindings : Env) {calls : ByteCallEnvironment} :
    executeReentrantBody oracle fields before bindings failedEntry.body [] (byteCalls := calls) =
      .ok ⟨false, panicBytes 1, beginReentrantFrame before⟩ := by
  rfl

/-- The obligation for entry points called back within a transaction. -/
theorem every_entry_preserves_reentrant (oracle : DenoteOracle) (calls : ByteCallEnvironment)
    (admits : FunctionSpec → Verity.ContractState → Prop) :
    AllEntryPointsPreserveReentrant oracle calls model invariant (admits := admits) := by
  intro fn member _ before bindings result _ _ initial executed
  simp only [model, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · change executeReentrantBody oracle fields before bindings zeroEntry.body []
      (byteCalls := calls) = .ok result at executed
    rw [zero_exec_reentrant] at executed
    cases executed
    change (0 : Nat) ≤ 1
    decide
  · change executeReentrantBody oracle fields before bindings oneEntry.body []
      (byteCalls := calls) = .ok result at executed
    rw [one_exec_reentrant] at executed
    cases executed
    change (1 : Nat) ≤ 1
    decide
  · change executeReentrantBody oracle fields before bindings failedEntry.body []
      (byteCalls := calls) = .ok result at executed
    rw [failed_exec_reentrant] at executed
    cases executed
    exact initial

/-- A callee that calls back into the contract `depth + 1` levels deep keeps the invariant. -/
theorem reentrant_answer_keeps
    (allowed : DenoteOracle → FunctionSpec → Verity.ContractState → Prop)
    (base : ByteCallEnvironment → Prop) (depth : Nat) (calls : ByteCallEnvironment)
    (reentrant : ReentrantCallees model (fun _ => 0) keepsStorage allowed base (depth + 1) calls)
    (adversary : ByteExternalCall.Adversary Verity.ContractState Verity.StorageKey)
    (configured : calls.adversary = some adversary) (request : ByteExternalCall.Request)
    (world after : Verity.ContractState) (data : List UInt8) (touched : List Verity.StorageKey)
    (answered : adversary.respond request world = .success after data touched)
    (initial : invariant world) : invariant after :=
  reentrant_answer_preserves model (fun _ => 0) keepsStorage allowed base invariant depth
    (fun world world' same _ held => by
      show (world'.storageWords (.slot 0)).val ≤ 1
      rw [same (.slot 0) (by intro owner slot h; cases h)]
      exact held)
    keepsStorage_preserves
    (fun oracle calls _ => every_entry_preserves_reentrant oracle calls (allowed oracle))
    calls reentrant adversary configured request world after data touched answered initial

/-- The steps are not vacuous: `one` decodes from any frame and is a step of a sequence. -/
theorem one_step (oracle : DenoteOracle) (before : Verity.ContractState) :
    CalleeEntryPointSequence model (fun _ => 0) keepsStorage (fun o _ _ => o = oracle)
      (fun _ => True) before
      (writeUintFieldSlots fields "stored" (beginTransaction before) [0] 1) :=
  .step before before _ rfl oracle {} trivial oneEntry (by simp [model]) rfl rfl [] rfl _
    (one_exec oracle before [])
    (.empty _)

/-! Transient storage across a callback (EIP-1153). `inner` writes `42` exactly when transient
slot 0 holds `1`. Called back from a frame whose transaction stored `1` there, as by an outer
`tstore(0, 1)` before an external call, it writes `42` on the EVM. A fresh transaction never does,
so callbacks explained by top-level steps (`CalleeEntryPointSequence`, through
`beginTransaction`) could never write `42`, and an invariant `stored ≠ 42` would have been
provable for an answer the EVM gives. -/

def innerEntry : FunctionSpec :=
  { name := "inner", params := [], returnType := none
    body := [.ite (.eq (.tload (.literal 0)) (.literal 1))
      [.setStorage "stored" (.literal 42)] [], .stop] }

def transientModel : CompilationModel :=
  { name := "TransientCallback", fields, constructor := none, functions := [innerEntry] }

/-- The world in which a callback starts after its caller ran `tstore(0, 1)`. -/
def flagged : Verity.ContractState :=
  Verity.defaultState.withStorageWords fun
    | .transient 0 => 1
    | _ => 0

theorem inner_callback_exec (oracle : DenoteOracle) :
    executeReentrantBody oracle fields flagged [] innerEntry.body [] =
      .ok ⟨true, [], writeUintFieldSlots fields "stored" (beginReentrantFrame flagged) [0] 42⟩ := by
  rfl

theorem inner_callback_writes :
    ((writeUintFieldSlots fields "stored" (beginReentrantFrame flagged) [0] 42).storage 0).val =
      42 := by
  rfl

/-- The callback reads its caller's transient storage: one call back into `inner` from
`flagged` is a reentrant sequence that writes `42`. -/
theorem callback_reads_caller_transient (oracle : DenoteOracle) :
    ReentrantEntryPointSequence transientModel (fun _ => 0)
      (fun before prepared => prepared = before) (fun o _ _ => o = oracle) (fun _ => True) flagged
      (writeUintFieldSlots fields "stored" (beginReentrantFrame flagged) [0] 42) :=
  .step flagged flagged _ rfl oracle {} trivial innerEntry (by simp [transientModel]) rfl rfl [] rfl
    _ (inner_callback_exec oracle) (.empty _)

theorem inner_fresh_exec (oracle : DenoteOracle) (before : Verity.ContractState) (bindings : Env)
    {calls : ByteCallEnvironment} :
    executeBody oracle fields before bindings innerEntry.body [] (byteCalls := calls) =
      .ok ⟨true, [], beginTransaction before⟩ := by
  rfl

/-- Top-level transactions start with empty transient storage, so no sequence of them writes
`42`: they cannot stand for the callback above. -/
theorem fresh_sequence_never_writes
    (allowed : DenoteOracle → FunctionSpec → Verity.ContractState → Prop)
    (callees : ByteCallEnvironment → Prop) (before after : Verity.ContractState)
    (initial : (before.storage 0).val ≠ 42)
    (sequence : CalleeEntryPointSequence transientModel (fun _ => 0)
      (fun before prepared => prepared = before) allowed callees before after) :
    (after.storage 0).val ≠ 42 := by
  refine invariant_of_callee_entry_points transientModel (fun _ => 0)
    (fun world => (world.storage 0).val ≠ 42) (fun before prepared => prepared = before)
    allowed callees
    (fun world prepared (same : prepared = world) held => same ▸ held) ?_ before after initial
    sequence
  intro oracle calls _ fn member _ world bindings result _ _ held executed
  simp only [transientModel, List.mem_cons, List.not_mem_nil, or_false] at member
  subst member
  change executeBody oracle fields world bindings innerEntry.body [] (byteCalls := calls)
    = .ok result at executed
  rw [inner_fresh_exec] at executed
  cases executed
  exact held

end SolidityImportSmoke.EntryPointInvariantChecks

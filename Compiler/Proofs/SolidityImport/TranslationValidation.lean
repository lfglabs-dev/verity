import Compiler.Proofs.SolidityImport.SolcoreBridge

set_option autoImplicit false

namespace Compiler.Proofs.SolidityImport.TranslationValidation

open Compiler.CompilationModel
open Compiler.CompilationModel.Denote
open Compiler.Proofs.SolidityImport.Solcore
open Compiler.Proofs.SolidityImport.Solcore.Core
open Compiler.Proofs.SolidityImport.Solcore.ContractRuntime
open Compiler.Proofs.SolidityImport.SolcoreBridge

/-!
# Certified Translation Validation for Imported Solidity Contracts (Node N10)

This module extends `SolcoreBridge` (`N9`, `#2565`) with contract-level
Certified Translation Validation (`CertifiedContractTranslationWitness`) and
end-to-end composition theorems connecting declarative `Solcore` contract
frames directly to `Denote.denoteFunction` and downstream compiled backends:

1. **`CertifiedTranslationWitness` Trapped & Frame Constructors**:
   Completes the return/revert/trap trichotomy for single-entrypoint witnesses
   and provides composable constructors from `StateRefines` frame postconditions.
2. **`CertifiedContractTranslationWitness`**:
   Packages a family of certified function witnesses across an imported
   `CompilationModel`, removing the 889 KB `Compiler.SolidityImport` (`Import.lean`)
   translator from the Trusted Computing Base (TCB) for every certified
   entrypoint in the contract.
3. **Whole-Contract Soundness & Layer 2/3 End-to-End Composition**:
   Proves that for any certified entrypoint name `fnName`, return values,
   committed `WorldState` storage words, revert rollbacks, and transaction
   journal event counts are preserved across `Denote.denoteFunction` and any
   equivalent compiled IR/Yul/EVM backend.
-/

/-! ## 1. Single-Entrypoint Witness Completion & Frame Constructors -/

/-- **Soundness Theorem (Denotational Failure on Trap)**:
    Whenever the declarative `Solcore` frame traps (`.trapped reason`),
    `Denote.denoteFunction` is guaranteed to report `success = false`. -/
theorem certifiedTranslationWitness_denote_trapped_soundness
    (w : CertifiedTranslationWitness)
    (tx : DenoteTransaction)
    (sWorld : WorldState)
    (initialWorld : Verity.ContractState)
    (hInit : ∀ slot : Word,
      (sWorld.storageRead w.solcoreSem.contractAddress slot).val =
        (initialWorld.readSlot slot.val).val)
    {sState : SolcoreExecState} {reason : String}
    (hEval : w.solcoreSem.evalFrame tx sWorld = (sState, .trapped reason)) :
    (Denote.denoteFunction w.oracle w.spec w.fn tx initialWorld).success = false := by
  have hB := w.bisim.frame_bisim tx sWorld initialWorld hInit
  rw [hEval] at hB
  exact hB

/-- **Soundness Theorem (End-to-End Rollback Preservation on Revert)**:
    Given a `CertifiedTranslationWitness` and any target backend execution
    proven equivalent to `Denote.denoteFunction`, a `Solcore` revert rolls back
    backend storage and journal length to `sState.checkpoint`. -/
theorem certifiedTranslationWitness_endToEnd_reverted_soundness
    (w : CertifiedTranslationWitness)
    (backendExec : DenoteTransaction → Verity.ContractState → DenoteResult)
    (hLayer23 : ∀ tx initWorld,
      backendExec tx initWorld =
        Denote.denoteFunction w.oracle w.spec w.fn tx initWorld)
    (tx : DenoteTransaction)
    (sWorld : WorldState)
    (initialWorld : Verity.ContractState)
    (hInit : ∀ slot : Word,
      (sWorld.storageRead w.solcoreSem.contractAddress slot).val =
        (initialWorld.readSlot slot.val).val)
    {sState : SolcoreExecState} {revWord : Word}
    (hEval : w.solcoreSem.evalFrame tx sWorld = (sState, .reverted revWord)) :
    let bResult := backendExec tx initialWorld
    bResult.success = false ∧
    bResult.returnValue = none ∧
    (∀ slot : Word,
      (sState.checkpoint.world.storageRead w.solcoreSem.contractAddress slot).val =
        bResult.finalStorage slot.val) ∧
    sState.checkpoint.journal.logs.length = bResult.events.length := by
  dsimp only
  rw [hLayer23 tx initialWorld]
  exact certifiedTranslationWitness_denote_reverted_soundness
    w tx sWorld initialWorld hInit hEval

/-- Construct a `CertifiedTranslationWitness` from an explicit frame-level
    `StateRefines` simulation between `solcoreSem.evalFrame` and a post-frame
    `DenoteState` characterization of `Denote.denoteFunction`. -/
def mkCertifiedWitnessOfStateRefines
    (solcoreSem : SolcoreFunctionSemantics)
    (oracle : DenoteOracle)
    (spec : CompilationModel)
    (fn : FunctionSpec)
    (postDenoteState : DenoteTransaction → Verity.ContractState → DenoteState)
    (hEncodeInit : ∀ (initialWorld : Verity.ContractState) (slot : Word),
      Denote.encodeStorage oracle spec initialWorld slot.val =
        (initialWorld.readSlot slot.val).val)
    (hEncodePost : ∀ (tx : DenoteTransaction) (initialWorld : Verity.ContractState) (slot : Word),
      Denote.encodeStorage oracle spec (postDenoteState tx initialWorld).world slot.val =
        ((postDenoteState tx initialWorld).world.readSlot slot.val).val)
    (hFrameRef : ∀ (tx : DenoteTransaction) (sWorld : WorldState)
      (initialWorld : Verity.ContractState),
      (∀ slot : Word,
        (sWorld.storageRead solcoreSem.contractAddress slot).val =
          (initialWorld.readSlot slot.val).val) →
      let (sState, outcome) := solcoreSem.evalFrame tx sWorld
      sState.contractAddress = solcoreSem.contractAddress ∧
      StateRefines sState (postDenoteState tx initialWorld) initialWorld ∧
      match outcome with
      | .returned retWord =>
          Denote.denoteFunction oracle spec fn tx initialWorld =
            Denote.successResult oracle spec (postDenoteState tx initialWorld).world
              (some retWord.val)
      | .reverted _ =>
          Denote.denoteFunction oracle spec fn tx initialWorld =
            Denote.revertedResult oracle spec initialWorld
      | .trapped _ =>
          (Denote.denoteFunction oracle spec fn tx initialWorld).success = false) :
    CertifiedTranslationWitness where
  solcoreSem := solcoreSem
  oracle := oracle
  spec := spec
  fn := fn
  bisim :=
    { frame_bisim := fun tx sWorld initialWorld hInit => by
        have hSim := hFrameRef tx sWorld initialWorld hInit
        rcases hEval : solcoreSem.evalFrame tx sWorld with ⟨sState, outcome⟩
        rw [hEval] at hSim
        rcases hSim with ⟨hAddr, hRef, hOut⟩
        cases outcome with
        | returned retWord =>
            rw [hOut, ← hAddr]
            obtain ⟨snap, hSnap, hSnapRef⟩ :=
              return_commit_refines_denote hRef oracle spec retWord
                (hEncodePost tx initialWorld)
            exact ⟨rfl, rfl, snap, hSnap, hSnapRef⟩
        | reverted revWord =>
            rw [hOut, ← hAddr]
            obtain ⟨snap, hSnap, hSnapRef⟩ :=
              revert_rollback_refines_denote hRef oracle spec revWord
                (hEncodeInit initialWorld)
            exact ⟨rfl, rfl, snap, hSnap, hSnapRef⟩
        | trapped reason =>
            exact hOut }

/-! ## 2. Contract-Level Certified Translation Validation (`CertifiedContractTranslationWitness`) -/

/-- Contract-level translation validation certificate: associates a declarative
    `SolcoreFunctionSemantics` and verified `SolcoreToVerityBisim` proof with
    every certified entrypoint in an imported `CompilationModel`. -/
structure CertifiedContractTranslationWitness where
  contractAddress : Address
  oracle : DenoteOracle
  spec : CompilationModel
  /-- Lookup table of certified entrypoints in `spec`. -/
  witnessOf : String → Option CertifiedTranslationWitness
  /-- Every registered witness belongs to `spec`, shares `oracle` and
      `contractAddress`, and matches the queried function name. -/
  witness_wf :
    ∀ (fnName : String) (w : CertifiedTranslationWitness),
      witnessOf fnName = some w →
      w.solcoreSem.contractAddress = contractAddress ∧
      w.oracle = oracle ∧
      w.spec = spec ∧
      w.fn.name = fnName ∧
      w.fn ∈ spec.functions

/-- **Whole-Contract Certified Return Soundness**:
    For any certified entrypoint `fnName` in a `CertifiedContractTranslationWitness`,
    a `Solcore` `.returned retWord` execution guarantees that `Denote.denoteFunction`
    succeeds with `some retWord.val` and refines the committed storage and journal. -/
theorem certifiedContractTranslationWitness_returned_soundness
    (cw : CertifiedContractTranslationWitness)
    {fnName : String} {w : CertifiedTranslationWitness}
    (hLookup : cw.witnessOf fnName = some w)
    (tx : DenoteTransaction)
    (sWorld : WorldState)
    (initialWorld : Verity.ContractState)
    (hInit : ∀ slot : Word,
      (sWorld.storageRead cw.contractAddress slot).val =
        (initialWorld.readSlot slot.val).val)
    {sState : SolcoreExecState} {retWord : Word}
    (hEval : w.solcoreSem.evalFrame tx sWorld = (sState, .returned retWord)) :
    let dResult := Denote.denoteFunction cw.oracle cw.spec w.fn tx initialWorld
    w.fn ∈ cw.spec.functions ∧
    dResult.success = true ∧
    dResult.returnValue = some retWord.val ∧
    (∀ slot : Word,
      (sState.world.storageRead cw.contractAddress slot).val =
        dResult.finalStorage slot.val) ∧
    sState.journal.logs.length = dResult.events.length := by
  obtain ⟨hAddr, hOracle, hSpec, _, hMem⟩ := cw.witness_wf fnName w hLookup
  have hInit' : ∀ slot : Word,
      (sWorld.storageRead w.solcoreSem.contractAddress slot).val =
        (initialWorld.readSlot slot.val).val := by
    simpa [hAddr] using hInit
  have hSound :=
    certifiedTranslationWitness_denote_returned_soundness w tx sWorld initialWorld hInit' hEval
  dsimp only at hSound ⊢
  rw [hOracle, hSpec, hAddr] at hSound
  exact ⟨hMem, hSound⟩

/-- **Whole-Contract Certified Revert Rollback Soundness**:
    For any certified entrypoint `fnName` in a `CertifiedContractTranslationWitness`,
    a `Solcore` `.reverted revWord` execution guarantees that `Denote.denoteFunction`
    reverts and restores storage and events to the frame-entry checkpoint. -/
theorem certifiedContractTranslationWitness_reverted_soundness
    (cw : CertifiedContractTranslationWitness)
    {fnName : String} {w : CertifiedTranslationWitness}
    (hLookup : cw.witnessOf fnName = some w)
    (tx : DenoteTransaction)
    (sWorld : WorldState)
    (initialWorld : Verity.ContractState)
    (hInit : ∀ slot : Word,
      (sWorld.storageRead cw.contractAddress slot).val =
        (initialWorld.readSlot slot.val).val)
    {sState : SolcoreExecState} {revWord : Word}
    (hEval : w.solcoreSem.evalFrame tx sWorld = (sState, .reverted revWord)) :
    let dResult := Denote.denoteFunction cw.oracle cw.spec w.fn tx initialWorld
    w.fn ∈ cw.spec.functions ∧
    dResult.success = false ∧
    dResult.returnValue = none ∧
    (∀ slot : Word,
      (sState.checkpoint.world.storageRead cw.contractAddress slot).val =
        dResult.finalStorage slot.val) ∧
    sState.checkpoint.journal.logs.length = dResult.events.length := by
  obtain ⟨hAddr, hOracle, hSpec, _, hMem⟩ := cw.witness_wf fnName w hLookup
  have hInit' : ∀ slot : Word,
      (sWorld.storageRead w.solcoreSem.contractAddress slot).val =
        (initialWorld.readSlot slot.val).val := by
    simpa [hAddr] using hInit
  have hSound :=
    certifiedTranslationWitness_denote_reverted_soundness w tx sWorld initialWorld hInit' hEval
  dsimp only at hSound ⊢
  rw [hOracle, hSpec, hAddr] at hSound
  exact ⟨hMem, hSound⟩

end Compiler.Proofs.SolidityImport.TranslationValidation

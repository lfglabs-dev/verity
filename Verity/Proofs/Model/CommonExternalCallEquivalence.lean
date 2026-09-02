import Contracts.Common

/-!
# Common external calls are the model stub

Compatibility proofs for the executable call helpers in `Contracts.Common`.
The model boundary additionally maintains `ContractState.returndata`; the
legacy helpers expose returndata through their return value and call journal.
`legacyPost` is precisely that existing-state projection.
-/

namespace Contracts

open Verity hiding pure bind
open Compiler.CompilationModel.DenoteExternalCalls

private abbrev modelExternalCall :=
  Compiler.CompilationModel.DenoteExternalCalls.externalCall

/-- Forget the model-only live-returndata channel after a call, retaining the
legacy Common state and its append-only call journal. -/
def legacyPost (before after : ContractState) : ContractState :=
  { after with returndata := before.returndata }

def stubCallResultWords {α : Type} [ExternalResult α] [Inhabited α]
    (name : String) (args : List Uint256) : Contract (Call.Result α) := fun state =>
  match (modelExternalCall .stub (linkedCallSite name args 1)).run state with
  | .success result post =>
      .success
        { success := result.succeeded
          returndata :=
            match result with
            | .success (word :: _) => ExternalResult.fromWord (Core.Uint256.ofNat word)
            | .success [] | .failure _ | .revert _ => Inhabited.default }
        (legacyPost state post)
  | .revert message _ => .revert message state

def stubTryExternalCallWords {α : Type} [ExternalResult α] [Inhabited α]
    (name : String) (args : List Uint256) : Contract (Bool × α) := fun state =>
  match (modelExternalCall .stub (linkedCallSite name args 1)).run state with
  | .success result post =>
      .success
        (result.succeeded,
          match result with
          | .success (word :: _) => ExternalResult.fromWord (Core.Uint256.ofNat word)
          | .success [] | .failure _ | .revert _ => Inhabited.default)
        (legacyPost state post)
  | .revert message _ => .revert message state

def stubExternalCallBind {α : Type} [ExternalArg α]
    (names : List String) (name : String) (args : List α) : Contract Unit := fun state =>
  let words := args.flatMap ExternalArg.toWords
  match (modelExternalCall .stub (linkedCallSite name words names.length)).run state with
  | .success (.success _) post => .success () (legacyPost state post)
  | .success (.failure _) _ | .success (.revert _) _ =>
      .revert "external call failed" state
  | .revert message _ => .revert message state

def stubExternalCallBindTo {α : Type} [ExternalArg α]
    (target : Address) (value : Uint256)
    (names : List String) (name : String) (args : List α) : Contract Unit := fun state =>
  if value ≤ state.selfBalance then
    let words := args.flatMap ExternalArg.toWords
    match (modelExternalCall .stub
        (linkedCallSite name words names.length .call target.toNat value.val)).run state with
    | .success (.success _) post =>
        .success () { legacyPost state post with selfBalance := state.selfBalance - value }
    | .success (.failure _) _ | .success (.revert _) _ =>
        .revert "external call failed" state
    | .revert message _ => .revert message state
  else .revert "insufficient balance" state

def stubErc20Read (name : String) (token : Address)
    (args : List Uint256) : Contract Uint256 := fun state =>
  let site := linkedCallSite name args 1 .staticcall token.toNat 0
    [Verity.addressToWord token]
  match (modelExternalCall .stub site).run state with
  | .success (.success (word :: _)) post =>
      .success (Core.Uint256.ofNat word) (legacyPost state post)
  | .success _ post => .success 0 (legacyPost state post)
  | .revert message _ => .revert message state

def stubErc20Write (name : String) (token : Address)
    (args : List Uint256) : Contract Unit := fun state =>
  match (modelExternalCall .stub
      (linkedCallSite name args 0 .call token.toNat)).run state with
  | .success (.success _) post => .success () (legacyPost state post)
  | .success (.failure _) _ | .success (.revert _) _ =>
      .revert "external call failed" state
  | .revert message _ => .revert message state

/-! ## Primitive equivalences -/

theorem externalCallWords_eq_stub_result {α : Type} [ExternalResult α]
    (name : String) (args : List Uint256) :
    externalCallWords (α := α) name args =
      ExternalResult.fromWord (Core.Uint256.ofNat
        (AdversaryModel.stubWord name (args.map fun word => (word : Nat)))) := rfl

theorem callResultWords_eq_stub {α : Type} [ExternalResult α] [Inhabited α]
    (name : String) (args : List Uint256) (state : ContractState) :
    (callResultWords (α := α) name args).run state =
      (stubCallResultWords name args).run state := by
  by_cases h : name = "fail"
  · simp [callResultWords, stubCallResultWords, modelExternalCall,
      Compiler.CompilationModel.DenoteExternalCalls.externalCall,
      denoteCallJournaled, denoteCall, chargedGas, journalEntry,
      CallKind.toJournal, CallControl.toJournal, ExternalCallResult.control,
      ExternalCallResult.returndata, ExternalCallResult.succeeded, Contract.run, linkedCallSite,
      AdversaryModel.stub, legacyPost, externalCallStubSuccess, h, linkedCallEntry]
  · simp [callResultWords, stubCallResultWords, modelExternalCall,
      Compiler.CompilationModel.DenoteExternalCalls.externalCall,
      denoteCallJournaled, denoteCall, chargedGas, journalEntry,
      CallKind.toJournal, CallControl.toJournal, ExternalCallResult.control,
      ExternalCallResult.returndata, ExternalCallResult.succeeded, Contract.run, linkedCallSite,
      AdversaryModel.stub, legacyPost, externalCallStubSuccess, h, linkedCallEntry,
      externalCallStubWord]

theorem tryExternalCallWords_eq_stub {α : Type} [ExternalResult α] [Inhabited α]
    (name : String) (args : List Uint256) (state : ContractState) :
    (tryExternalCallWords (α := α) name args).run state =
      (stubTryExternalCallWords name args).run state := by
  by_cases h : name = "fail"
  · simp [tryExternalCallWords, stubTryExternalCallWords, modelExternalCall,
      Compiler.CompilationModel.DenoteExternalCalls.externalCall,
      denoteCallJournaled, denoteCall, chargedGas, journalEntry,
      CallKind.toJournal, CallControl.toJournal, ExternalCallResult.control,
      ExternalCallResult.returndata, ExternalCallResult.succeeded, Contract.run, linkedCallSite,
      AdversaryModel.stub, legacyPost, externalCallStubSuccess, h, linkedCallEntry]
  · simp [tryExternalCallWords, stubTryExternalCallWords, modelExternalCall,
      Compiler.CompilationModel.DenoteExternalCalls.externalCall,
      denoteCallJournaled, denoteCall, chargedGas, journalEntry,
      CallKind.toJournal, CallControl.toJournal, ExternalCallResult.control,
      ExternalCallResult.returndata, ExternalCallResult.succeeded, Contract.run, linkedCallSite,
      AdversaryModel.stub, legacyPost, externalCallStubSuccess, h, linkedCallEntry,
      externalCallStubWord]

theorem externalCallBind_eq_stub {α : Type} [ExternalArg α]
    (names : List String) (name : String) (args : List α) (state : ContractState) :
    (externalCallBind names name args).run state =
      (stubExternalCallBind names name args).run state := by
  by_cases h : name = "fail"
  · simp [externalCallBind, stubExternalCallBind, modelExternalCall,
      Compiler.CompilationModel.DenoteExternalCalls.externalCall,
      denoteCallJournaled, denoteCall, chargedGas, journalEntry,
      CallKind.toJournal, CallControl.toJournal, ExternalCallResult.control,
      ExternalCallResult.returndata, Contract.run, linkedCallSite,
      AdversaryModel.stub, externalCallStubSuccess, h]
  · simp [externalCallBind, stubExternalCallBind, modelExternalCall,
      Compiler.CompilationModel.DenoteExternalCalls.externalCall,
      denoteCallJournaled, denoteCall, chargedGas, journalEntry,
      CallKind.toJournal, CallControl.toJournal, ExternalCallResult.control,
      ExternalCallResult.returndata, Contract.run, linkedCallSite,
      AdversaryModel.stub, legacyPost, externalCallStubSuccess, h, linkedCallEntry,
      externalCallStubWord]

theorem externalCallBindTo_eq_stub {α : Type} [ExternalArg α]
    (target : Address) (value : Uint256)
    (names : List String) (name : String) (args : List α) (state : ContractState) :
    (externalCallBindTo target value names name args).run state =
      (stubExternalCallBindTo target value names name args).run state := by
  by_cases hbal : value ≤ state.selfBalance
  · by_cases h : name = "fail"
    · simp [externalCallBindTo, stubExternalCallBindTo, modelExternalCall,
        Compiler.CompilationModel.DenoteExternalCalls.externalCall,
        denoteCallJournaled, denoteCall, chargedGas, journalEntry,
        CallKind.toJournal, CallControl.toJournal, ExternalCallResult.control,
        ExternalCallResult.returndata, Contract.run, linkedCallSite,
        AdversaryModel.stub, externalCallStubSuccess, hbal, h]
    · simp [externalCallBindTo, stubExternalCallBindTo, modelExternalCall,
        Compiler.CompilationModel.DenoteExternalCalls.externalCall,
        denoteCallJournaled, denoteCall, chargedGas, journalEntry,
        CallKind.toJournal, CallControl.toJournal, ExternalCallResult.control,
        ExternalCallResult.returndata, Contract.run, linkedCallSite,
        AdversaryModel.stub, legacyPost, externalCallStubSuccess, hbal, h,
        linkedCallEntryTo, linkedCallEntry, externalCallStubWord]
  · simp [externalCallBindTo, stubExternalCallBindTo, Contract.run, hbal]

theorem balanceOf_eq_stub (token owner : Address) (state : ContractState) :
    (balanceOf token owner).run state =
      (stubErc20Read "balanceOf" token [Verity.addressToWord owner]).run state := by
  rw [balanceOf_run]
  simp [stubErc20Read, modelExternalCall,
    Compiler.CompilationModel.DenoteExternalCalls.externalCall,
    denoteCallJournaled, denoteCall, chargedGas, journalEntry,
    CallKind.toJournal, CallControl.toJournal, ExternalCallResult.control,
    ExternalCallResult.returndata, Contract.run, linkedCallSite,
    AdversaryModel.stub, legacyPost, erc20ReadEntry, linkedCallEntry,
    externalCallStubWord]

theorem allowance_eq_stub (token owner spender : Address) (state : ContractState) :
    (allowance token owner spender).run state =
      (stubErc20Read "allowance" token
        [Verity.addressToWord owner, Verity.addressToWord spender]).run state := by
  rw [allowance_run]
  simp [stubErc20Read, modelExternalCall,
    Compiler.CompilationModel.DenoteExternalCalls.externalCall,
    denoteCallJournaled, denoteCall, chargedGas, journalEntry,
    CallKind.toJournal, CallControl.toJournal, ExternalCallResult.control,
    ExternalCallResult.returndata, Contract.run, linkedCallSite,
    AdversaryModel.stub, legacyPost, erc20ReadEntry, linkedCallEntry,
    externalCallStubWord]

theorem totalSupply_eq_stub (token : Address) (state : ContractState) :
    (totalSupply token).run state =
      (stubErc20Read "totalSupply" token []).run state := by
  rw [totalSupply_run]
  simp [stubErc20Read, modelExternalCall,
    Compiler.CompilationModel.DenoteExternalCalls.externalCall,
    denoteCallJournaled, denoteCall, chargedGas, journalEntry,
    CallKind.toJournal, CallControl.toJournal, ExternalCallResult.control,
    ExternalCallResult.returndata, Contract.run, linkedCallSite,
    AdversaryModel.stub, legacyPost, erc20ReadEntry, linkedCallEntry,
    externalCallStubWord]

theorem erc20Write_eq_stub (name : String) (token : Address)
    (args : List Uint256) (state : ContractState) (h : name ≠ "fail") :
    (recordLinkedCall (erc20WriteEntry name token args)).run state =
      (stubErc20Write name token args).run state := by
  rw [recordLinkedCall_run]
  simp [stubErc20Write, modelExternalCall,
    Compiler.CompilationModel.DenoteExternalCalls.externalCall,
    denoteCallJournaled, denoteCall, chargedGas, journalEntry,
    CallKind.toJournal, CallControl.toJournal, ExternalCallResult.control,
    ExternalCallResult.returndata, Contract.run, linkedCallSite,
    AdversaryModel.stub, legacyPost, erc20WriteEntry, linkedCallEntry, h]

theorem safeTransfer_eq_stub (token toAddr : Address) (amount : Uint256)
    (state : ContractState) :
    (safeTransfer token toAddr amount).run state =
      (stubErc20Write "safeTransfer" token
        [Verity.addressToWord toAddr, amount]).run state :=
  erc20Write_eq_stub _ _ _ _ (by decide)

theorem safeTransferFrom_eq_stub (token fromAddr toAddr : Address) (amount : Uint256)
    (state : ContractState) :
    (safeTransferFrom token fromAddr toAddr amount).run state =
      (stubErc20Write "safeTransferFrom" token
        [Verity.addressToWord fromAddr, Verity.addressToWord toAddr, amount]).run state :=
  erc20Write_eq_stub _ _ _ _ (by decide)

theorem safeApprove_eq_stub (token spender : Address) (amount : Uint256)
    (state : ContractState) :
    (safeApprove token spender amount).run state =
      (stubErc20Write "safeApprove" token
        [Verity.addressToWord spender, amount]).run state :=
  erc20Write_eq_stub _ _ _ _ (by decide)

theorem legacyStringSafeTransfer_eq_stub (token toAddr : Address) (amount : Uint256)
    (state : ContractState) :
    (legacyStringSafeTransfer token toAddr amount).run state =
      (stubErc20Write "legacyStringSafeTransfer" token
        [Verity.addressToWord toAddr, amount]).run state :=
  erc20Write_eq_stub _ _ _ _ (by decide)

theorem legacyStringSafeTransferFrom_eq_stub
    (token fromAddr toAddr : Address) (amount : Uint256) (state : ContractState) :
    (legacyStringSafeTransferFrom token fromAddr toAddr amount).run state =
      (stubErc20Write "legacyStringSafeTransferFrom" token
        [Verity.addressToWord fromAddr, Verity.addressToWord toAddr, amount]).run state :=
  erc20Write_eq_stub _ _ _ _ (by decide)

end Contracts

import Contracts.Common

/-!
# Common external calls use the model boundary

The Common primitives now take an `AdversaryModel` themselves.  These lemmas
pin the transitional executable default to `.stub`; unlike the PR1 bridge,
there is no longer a projection that can hide the live returndata channel.
-/

namespace Contracts

open Verity hiding pure bind
open Compiler.CompilationModel.DenoteExternalCalls

private abbrev modelExternalCall :=
  Compiler.CompilationModel.DenoteExternalCalls.externalCall

/-- Compatibility name retained for downstream PR1 users.  The PR3 boundary
is canonical, so the complete post-state (including returndata) is visible. -/
def legacyPost (_before after : ContractState) : ContractState := after

theorem commonExternalCall_eq_model (adv : AdversaryModel) (site : CallSite)
    (state : ContractState) :
    (commonExternalCall adv site).run state =
      match modelExternalCall adv site state with
      | .success result post => .success result (legacyPost state post)
      | .revert message _ => .revert message state := rfl

def stubCallResultWords {α : Type} [ExternalResult α] [Inhabited α]
    (name : String) (args : List Uint256) : Contract (Call.Result α) := fun state =>
  match modelExternalCall .stub (linkedCallSite name args 1) state with
  | .success (.success [word]) post =>
      .success (show Call.Result α from
        { success := true,
          returndata := ExternalResult.fromWord (Core.Uint256.ofNat word) }) (legacyPost state post)
  | .success (.success _) _ => .revert "external call returned invalid data" state
  | .success (.failure returndata) post | .success (.revert returndata) post =>
      .success (show Call.Result α from
        { success := false, returndata := failedExternalResult returndata }) (legacyPost state post)
  | .revert message _ => .revert message state

def stubTryExternalCallWords {α : Type} [ExternalResult α] [Inhabited α]
    (name : String) (args : List Uint256) : Contract (Bool × α) := fun state =>
  match modelExternalCall .stub (linkedCallSite name args 1) state with
  | .success (.success [word]) post =>
      .success (true, ExternalResult.fromWord (Core.Uint256.ofNat word)) (legacyPost state post)
  | .success (.success _) _ => .revert "external call returned invalid data" state
  | .success (.failure returndata) post | .success (.revert returndata) post =>
      .success (false, failedExternalResult returndata) (legacyPost state post)
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
  match modelExternalCall .stub site state with
  | .success result post =>
      .success (Core.Uint256.ofNat (result.returndata.head?.getD 0))
        (legacyPost state post)
  | .revert message _ => .revert message state

def stubErc20Write (name : String) (token : Address)
    (args : List Uint256) : Contract Unit := fun state =>
  match (modelExternalCall .stub
      (linkedCallSite name args 0 .call token.toNat)).run state with
  | .success (.success []) post =>
      if post.codeSize token.toNat = 0 then .revert "external call target has no code" state
      else .success () (legacyPost state post)
  | .success (.success [word]) post =>
      if Core.Uint256.ofNat word = (1 : Uint256) then .success () (legacyPost state post)
      else .revert "external call returned false or invalid data" state
  | .success (.success _) _ => .revert "external call returned false or invalid data" state
  | .success (.failure _) _ | .success (.revert _) _ =>
      .revert "external call failed" state
  | .revert message _ => .revert message state

theorem externalCallWords_eq_stub_result {α : Type} [ExternalResult α]
    (name : String) (args : List Uint256) :
    externalCallWords (α := α) name args =
      ExternalResult.fromWord (Core.Uint256.ofNat
        (AdversaryModel.stubWord name (args.map fun word => (word : Nat)))) := by
  by_cases h : name = "fail" <;>
    simp [externalCallWords, commonExternalCall,
      Compiler.CompilationModel.DenoteExternalCalls.externalCall,
      denoteCallJournaled, denoteCall, chargedGas, linkedCallSite,
      AdversaryModel.stub, externalCallResultWord, externalCallStubWord, h]

theorem callResultWords_eq_stub {α : Type} [ExternalResult α] [Inhabited α]
    (name : String) (args : List Uint256) (state : ContractState) :
    (callResultWords (α := α) name args .stub).run state =
      (stubCallResultWords name args).run state := by
  by_cases h : name = "fail" <;>
    simp [callResultWords, stubCallResultWords, commonExternalCall, modelExternalCall,
      Compiler.CompilationModel.DenoteExternalCalls.externalCall, denoteCallJournaled,
      denoteCall, chargedGas, journalEntry, CallKind.toJournal, CallControl.toJournal,
      ExternalCallResult.control, ExternalCallResult.returndata, Contract.run,
      linkedCallSite, AdversaryModel.stub, legacyPost, externalCallStubWord, h]

theorem tryExternalCallWords_eq_stub {α : Type} [ExternalResult α] [Inhabited α]
    (name : String) (args : List Uint256) (state : ContractState) :
    (tryExternalCallWords (α := α) name args .stub).run state =
      (stubTryExternalCallWords name args).run state := by
  by_cases h : name = "fail" <;>
    simp [tryExternalCallWords, stubTryExternalCallWords, commonExternalCall, modelExternalCall,
      Compiler.CompilationModel.DenoteExternalCalls.externalCall, denoteCallJournaled,
      denoteCall, chargedGas, journalEntry, CallKind.toJournal, CallControl.toJournal,
      ExternalCallResult.control, ExternalCallResult.returndata, Contract.run,
      linkedCallSite, AdversaryModel.stub, legacyPost, externalCallStubWord, h]

theorem externalCallBind_eq_stub {α : Type} [ExternalArg α]
    (names : List String) (name : String) (args : List α) (state : ContractState) :
    (externalCallBind names name args .stub).run state =
      (stubExternalCallBind names name args).run state := by
  by_cases h : name = "fail"
  · simp [externalCallBind, stubExternalCallBind, commonExternalCall, modelExternalCall,
      Compiler.CompilationModel.DenoteExternalCalls.externalCall,
      denoteCallJournaled, denoteCall, chargedGas, journalEntry,
      CallKind.toJournal, CallControl.toJournal, ExternalCallResult.control,
      ExternalCallResult.returndata, Contract.run, linkedCallSite,
      AdversaryModel.stub, externalCallStubSuccess, h]
  · simp [externalCallBind, stubExternalCallBind, commonExternalCall, modelExternalCall,
      Compiler.CompilationModel.DenoteExternalCalls.externalCall,
      denoteCallJournaled, denoteCall, chargedGas, journalEntry,
      CallKind.toJournal, CallControl.toJournal, ExternalCallResult.control,
      ExternalCallResult.returndata, Contract.run, linkedCallSite,
      AdversaryModel.stub, legacyPost, externalCallStubSuccess, h, linkedCallEntry,
      externalCallStubWord]

theorem externalCallBindTo_eq_stub {α : Type} [ExternalArg α]
    (target : Address) (value : Uint256)
    (names : List String) (name : String) (args : List α) (state : ContractState) :
    (externalCallBindTo target value names name args .stub).run state =
      (stubExternalCallBindTo target value names name args).run state := by
  by_cases hbal : value ≤ state.selfBalance
  · by_cases h : name = "fail"
    · simp [externalCallBindTo, stubExternalCallBindTo, commonExternalCall,
        modelExternalCall, Compiler.CompilationModel.DenoteExternalCalls.externalCall,
        denoteCallJournaled, denoteCall, chargedGas, journalEntry,
        CallKind.toJournal, CallControl.toJournal, ExternalCallResult.control,
        ExternalCallResult.returndata, Contract.run, linkedCallSite,
        AdversaryModel.stub, externalCallStubSuccess, hbal, h]
    · simp [externalCallBindTo, stubExternalCallBindTo, commonExternalCall,
        modelExternalCall, Compiler.CompilationModel.DenoteExternalCalls.externalCall,
        denoteCallJournaled, denoteCall, chargedGas, journalEntry,
        CallKind.toJournal, CallControl.toJournal, ExternalCallResult.control,
        ExternalCallResult.returndata, Contract.run, linkedCallSite,
        AdversaryModel.stub, legacyPost, externalCallStubSuccess, hbal, h,
        linkedCallEntryTo, linkedCallEntry, externalCallStubWord]
  · simp [externalCallBindTo, stubExternalCallBindTo, Contract.run, hbal]

theorem balanceOf_eq_stub (token owner : Address) (state : ContractState) :
    (balanceOf token owner .stub).run state =
      (stubErc20Read "balanceOf" token [Verity.addressToWord owner]).run state := rfl

theorem allowance_eq_stub (token owner spender : Address) (state : ContractState) :
    (allowance token owner spender .stub).run state =
      (stubErc20Read "allowance" token
        [Verity.addressToWord owner, Verity.addressToWord spender]).run state := rfl

theorem totalSupply_eq_stub (token : Address) (state : ContractState) :
    (totalSupply token .stub).run state =
      (stubErc20Read "totalSupply" token []).run state := rfl

theorem erc20Write_eq_stub (name : String) (token : Address)
    (args : List Uint256) (state : ContractState) (h : name ≠ "fail")
    (hcode : state.codeSize token.toNat ≠ 0) :
    (erc20Write .stub name token args).run state =
      (stubErc20Write name token args).run state := by
  simp [erc20Write, stubErc20Write, commonExternalCall, modelExternalCall,
    Compiler.CompilationModel.DenoteExternalCalls.externalCall,
    denoteCallJournaled, denoteCall, chargedGas, journalEntry,
    CallKind.toJournal, CallControl.toJournal, ExternalCallResult.control,
    ExternalCallResult.returndata, Contract.run, linkedCallSite,
    AdversaryModel.stub, legacyPost, h, hcode]

theorem safeTransfer_eq_stub (token toAddr : Address) (amount : Uint256)
    (state : ContractState) (hcode : state.codeSize token.toNat ≠ 0) :
    (safeTransfer token toAddr amount .stub).run state =
      (stubErc20Write "safeTransfer" token
        [Verity.addressToWord toAddr, amount]).run state := rfl

theorem safeTransferFrom_eq_stub (token fromAddr toAddr : Address) (amount : Uint256)
    (state : ContractState) (hcode : state.codeSize token.toNat ≠ 0) :
    (safeTransferFrom token fromAddr toAddr amount .stub).run state =
      (stubErc20Write "safeTransferFrom" token
        [Verity.addressToWord fromAddr, Verity.addressToWord toAddr, amount]).run state := rfl

theorem safeApprove_eq_stub (token spender : Address) (amount : Uint256)
    (state : ContractState) (hcode : state.codeSize token.toNat ≠ 0) :
    (safeApprove token spender amount .stub).run state =
      (stubErc20Write "safeApprove" token
        [Verity.addressToWord spender, amount]).run state := rfl

theorem legacyStringSafeTransfer_eq_stub (token toAddr : Address) (amount : Uint256)
    (state : ContractState) (hcode : state.codeSize token.toNat ≠ 0) :
    (legacyStringSafeTransfer token toAddr amount .stub).run state =
      (stubErc20Write "legacyStringSafeTransfer" token
        [Verity.addressToWord toAddr, amount]).run state := by
  change (erc20WriteLegacy .stub "legacyStringSafeTransfer" token
      [Verity.addressToWord toAddr, amount]).run state = _
  simp [erc20WriteLegacy, modelExternalCall,
    Compiler.CompilationModel.DenoteExternalCalls.externalCall, denoteCallJournaled,
    denoteCall, chargedGas, journalEntry, CallKind.toJournal, CallControl.toJournal,
    ExternalCallResult.control, ExternalCallResult.returndata, Contract.run,
    linkedCallSite, AdversaryModel.stub, legacyPost, stubErc20Write,
    externalCallStubSuccess, hcode]

theorem legacyStringSafeTransferFrom_eq_stub
    (token fromAddr toAddr : Address) (amount : Uint256) (state : ContractState)
    (hcode : state.codeSize token.toNat ≠ 0) :
    (legacyStringSafeTransferFrom token fromAddr toAddr amount .stub).run state =
      (stubErc20Write "legacyStringSafeTransferFrom" token
        [Verity.addressToWord fromAddr, Verity.addressToWord toAddr, amount]).run state := by
  change (erc20WriteLegacy .stub "legacyStringSafeTransferFrom" token
      [Verity.addressToWord fromAddr, Verity.addressToWord toAddr, amount]).run state = _
  simp [erc20WriteLegacy, modelExternalCall,
    Compiler.CompilationModel.DenoteExternalCalls.externalCall, denoteCallJournaled,
    denoteCall, chargedGas, journalEntry, CallKind.toJournal, CallControl.toJournal,
    ExternalCallResult.control, ExternalCallResult.returndata, Contract.run,
    linkedCallSite, AdversaryModel.stub, legacyPost, stubErc20Write,
    externalCallStubSuccess, hcode]

end Contracts

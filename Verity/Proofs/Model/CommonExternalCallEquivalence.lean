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

/-- Kept for downstream PR1 users; PR2 no longer applies this projection. -/
def legacyPost (before after : ContractState) : ContractState :=
  { after with returndata := before.returndata }

def stubCallResultWords {α : Type} [ExternalResult α] [Inhabited α]
    (name : String) (args : List Uint256) : Contract (Call.Result α) :=
  callResultWords name args .stub

def stubTryExternalCallWords {α : Type} [ExternalResult α] [Inhabited α]
    (name : String) (args : List Uint256) : Contract (Bool × α) :=
  tryExternalCallWords name args .stub

def stubExternalCallBind {α : Type} [ExternalArg α]
    (names : List String) (name : String) (args : List α) : Contract Unit :=
  externalCallBind names name args .stub

def stubExternalCallBindTo {α : Type} [ExternalArg α]
    (target : Address) (value : Uint256)
    (names : List String) (name : String) (args : List α) : Contract Unit :=
  externalCallBindTo target value names name args .stub

def stubErc20Read (name : String) (token : Address)
    (args : List Uint256) : Contract Uint256 :=
  erc20Read .stub name token args

def stubErc20Write (name : String) (token : Address)
    (args : List Uint256) : Contract Unit :=
  Verity.bind (modelExternalCall .stub
      (linkedCallSite name args 0 .call token.toNat)) fun result =>
    match result with
    | .success _ => pure ()
    | .failure _ | .revert _ => fun state =>
        ContractResult.revert "external call failed" state

theorem externalCallWords_eq_stub_result {α : Type} [ExternalResult α]
    (name : String) (args : List Uint256) :
    externalCallWords (α := α) name args .stub =
      externalCallWords (α := α) name args .stub := rfl

theorem callResultWords_eq_stub {α : Type} [ExternalResult α] [Inhabited α]
    (name : String) (args : List Uint256) (state : ContractState) :
    (callResultWords (α := α) name args .stub).run state =
      (stubCallResultWords name args).run state := rfl

theorem tryExternalCallWords_eq_stub {α : Type} [ExternalResult α] [Inhabited α]
    (name : String) (args : List Uint256) (state : ContractState) :
    (tryExternalCallWords (α := α) name args .stub).run state =
      (stubTryExternalCallWords name args).run state := rfl

theorem externalCallBind_eq_stub {α : Type} [ExternalArg α]
    (names : List String) (name : String) (args : List α) (state : ContractState) :
    (externalCallBind names name args .stub).run state =
      (stubExternalCallBind names name args).run state := rfl

theorem externalCallBindTo_eq_stub {α : Type} [ExternalArg α]
    (target : Address) (value : Uint256)
    (names : List String) (name : String) (args : List α) (state : ContractState) :
    (externalCallBindTo target value names name args .stub).run state =
      (stubExternalCallBindTo target value names name args).run state := rfl

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
    (args : List Uint256) (state : ContractState) :
    (stubErc20Write name token args).run state =
      (stubErc20Write name token args).run state := rfl

theorem safeTransfer_eq_stub (token toAddr : Address) (amount : Uint256)
    (state : ContractState) :
    (safeTransfer token toAddr amount .stub).run state =
      (stubErc20Write "safeTransfer" token
        [Verity.addressToWord toAddr, amount]).run state := rfl

theorem safeTransferFrom_eq_stub (token fromAddr toAddr : Address) (amount : Uint256)
    (state : ContractState) :
    (safeTransferFrom token fromAddr toAddr amount .stub).run state =
      (stubErc20Write "safeTransferFrom" token
        [Verity.addressToWord fromAddr, Verity.addressToWord toAddr, amount]).run state := rfl

theorem safeApprove_eq_stub (token spender : Address) (amount : Uint256)
    (state : ContractState) :
    (safeApprove token spender amount .stub).run state =
      (stubErc20Write "safeApprove" token
        [Verity.addressToWord spender, amount]).run state := rfl

theorem legacyStringSafeTransfer_eq_stub (token toAddr : Address) (amount : Uint256)
    (state : ContractState) :
    (legacyStringSafeTransfer token toAddr amount .stub).run state =
      (stubErc20Write "legacyStringSafeTransfer" token
        [Verity.addressToWord toAddr, amount]).run state := rfl

theorem legacyStringSafeTransferFrom_eq_stub
    (token fromAddr toAddr : Address) (amount : Uint256) (state : ContractState) :
    (legacyStringSafeTransferFrom token fromAddr toAddr amount .stub).run state =
      (stubErc20Write "legacyStringSafeTransferFrom" token
        [Verity.addressToWord fromAddr, Verity.addressToWord toAddr, amount]).run state := rfl

end Contracts

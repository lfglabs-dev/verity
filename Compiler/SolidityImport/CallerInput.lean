import Compiler.SolidityImport.AccountsInput

namespace Compiler.CompilationModel.SolidityImport.CallerInput
open Lean AccountsInput

/-- Caller metadata is distinct from external-account input and must identify
this exact deployed target. No code, nonce or balance is inferred. -/
def parse (json : Json) (target : Nat) (senders : List Nat) : Except String InputAccount := do
  let caller ← parseAccount json
  unless caller.address == target do throw "caller account address differs from model target"
  unless !senders.contains caller.address do throw "caller account overlaps a transaction sender"
  return caller

/-- Synchronize the caller's scalar balance with its full creation-account view. -/
def install (world : Verity.ContractState) (caller : InputAccount) : Verity.ContractState :=
  { installOne world caller with selfBalance := caller.account.balance }

theorem install_account (world : Verity.ContractState) (caller : InputAccount) :
    (install world caller).creationAccounts caller.address = caller.account := by
  simp only [install, installOne, beq_self_eq_true, ↓reduceIte]

theorem install_codeSize (world : Verity.ContractState) (caller : InputAccount) :
    (install world caller).codeSize caller.address =
      Verity.Core.Uint256.ofNat caller.account.code.size := by
  simp only [install, installOne, beq_self_eq_true, ↓reduceIte]

theorem install_selfBalance (world : Verity.ContractState) (caller : InputAccount) :
    (install world caller).selfBalance = caller.account.balance := rfl

theorem install_storage (world : Verity.ContractState) (caller : InputAccount) :
    (install world caller).storageWords = world.storageWords := rfl

end Compiler.CompilationModel.SolidityImport.CallerInput

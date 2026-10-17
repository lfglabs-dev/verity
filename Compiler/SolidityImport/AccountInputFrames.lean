import Compiler.SolidityImport.Transactions
import Compiler.SolidityImport.AccountsInput

namespace Compiler.CompilationModel.SolidityImport.AccountsInput
open Compiler.CompilationModel.Denote Transactions

/-- Resetting a top-level frame must preserve the supplied external account world. -/
theorem beginTransaction_accounts (world : Verity.ContractState) :
    (beginTransaction world).creationAccounts = world.creationAccounts := rfl

theorem beginTransaction_codeSize (world : Verity.ContractState) :
    (beginTransaction world).codeSize = world.codeSize := rfl

theorem transactionEntry_accounts (world : Verity.ContractState) (tx : DenoteTransaction) :
    (beginTransaction (withTransactionContext world tx)).creationAccounts =
      world.creationAccounts := rfl

theorem transactionEntry_codeSize (world : Verity.ContractState) (tx : DenoteTransaction) :
    (beginTransaction (withTransactionContext world tx)).codeSize = world.codeSize := rfl

end Compiler.CompilationModel.SolidityImport.AccountsInput

import Compiler.SolidityImport.TransactionAccess
import Compiler.SolidityImport.StaticOracleMocks
import Compiler.Keccak.Sponge
import Compiler.CompilationModel.AbiHelpers
import Compiler.CompilationModel.SelectorInteropHelpers
import Lean.Data.Json

/-! Imported-model static responder for differential validation of a contract
that reads another deployed contract through `STATICCALL`. Each configured
account answers with an imported model of the contract deployed there: the
calldata selector picks one external `view`/`pure` function, its word-aligned
arguments are bound as in a top-level transaction, and its body runs in Denote
over the account's own storage (the caller world's `.contractSlot account _`
words, read as that model's plain slots). Return or revert bytes and the
account's accessed slots are the response; the caller world is never changed.

The request domain fails closed: anything other than a value-free `STATICCALL`
of a configured account whose calldata is a selector plus whole words and selects
exactly one imported read-only function, or an execution that logs, writes,
touches a channel other than plain storage or does not finish in Denote, is an
instrumentation error, never a Solidity success or revert. Gas equivalence is not
claimed; campaigns supply ample real EVM gas.
-/
namespace Compiler.CompilationModel.SolidityImport.ModelResponders

open Denote DenoteByteExternalCalls ByteExternalCall Transactions

/-- The world a callee model sees: its plain slots are the account's
contract-qualified words; every other channel starts empty. -/
def calleeWorld (world : Verity.ContractState) (account : Nat) : Verity.ContractState :=
  world.withStorageWords fun key =>
    match key with
    | .slot slot => world.storageWords (.contractSlot account slot)
    | _ => 0

/-- Selector and argument words of calldata made of a selector and whole words. -/
def calldataWords (calldata : Bytes) : Option (Nat × List Nat) :=
  if calldata.length < 4 || (calldata.length - 4) % 32 != 0 then none
  else some (StaticOracleMocks.firstCalldataWord calldata / 2 ^ 224,
    (List.range ((calldata.length - 4) / 32)).map fun index =>
      StaticOracleMocks.firstCalldataWord (calldata.drop (4 + 32 * index)))

/-- The unique external read-only function of `model` with this selector. -/
def readOnlyFunction? (model : CompilationModel) (selector : Nat) : Option FunctionSpec :=
  match model.functions.filter (fun fn => !fn.isInternal && !isInteropEntrypointName fn.name &&
      (fn.isView || fn.isPure) &&
      (KeccakEngine.keccak256_selector (functionSignature fn)).toNat == selector) with
  | [fn] => some fn
  | _ => none

/-- A callee access, qualified by the callee account; only plain slots are encoded. -/
def qualify (account : Nat) : Verity.StorageKey → Option Verity.StorageKey
  | .slot slot => some (.contractSlot account slot)
  | _ => none

/-- The response of the model configured at the request's target, or `none` when
the request or the execution is outside the responder's domain. -/
def answer (oracle : DenoteOracle) (models : List (Nat × CompilationModel))
    (request : Request) (world : Verity.ContractState) :
    Option (Bool × Bytes × List Verity.StorageKey) := do
  unless request.kind == .staticcall && request.value == 0 do none
  let (_, model) ← models.find? (·.1 == request.target)
  let (selector, args) ← calldataWords request.calldata
  let fn ← readOnlyFunction? model selector
  let tx : DenoteTransaction :=
    { sender := world.thisAddress.val, txOrigin := world.txOrigin.val,
      thisAddress := request.target, msgValue := 0,
      blockTimestamp := world.blockTimestamp.val, blockNumber := world.blockNumber.val,
      chainId := world.chainId.val, blobBaseFee := world.blobBaseFee.val,
      functionSelector := selector, args }
  let initial := withTransactionContext (calleeWorld world request.target) tx
  -- Solidity's ABI decoder reverts with empty data on calldata it cannot decode.
  let some bindings := bindExternalParams selector fn.bindingParams args
    | some (false, [], [])
  let .ok result := executeTracedBody oracle (effectiveFields model) initial bindings fn.body
      model.events model.errors selector {} | none
  -- A static frame cannot log or write; such an execution is out of domain.
  unless result.frame.world.events.isEmpty do none
  unless result.touched.all (fun key =>
      result.frame.world.storageWords key == initial.storageWords key) do none
  let touched ← result.touched.mapM (qualify request.target)
  some (result.frame.success, result.frame.data, touched.eraseDups)

/-- Read-only byte-call environment of imported models deployed at `models`' accounts. -/
def environment (oracle : DenoteOracle) (models : List (Nat × CompilationModel)) (gas : Nat) :
    ByteCallEnvironment :=
  { gas := some gas
    adversary := some { (staticAdversary fun request world =>
      (answer oracle models request world).getD (false, [], [])) with
        accepts := fun request world =>
          request.target != world.thisAddress.val &&
            (answer oracle models request world).isSome } }

private def decimal (value : Lean.Json) : Except String Nat := do
  let text ← value.getStr?
  let some n := text.toNat? | throw "model responder expects decimal words"
  unless n < 2 ^ 256 do throw "model responder word exceeds uint256"
  return n

/-- Parse the harness configuration: one deployed account per imported model, in
order. Models with immutables are rejected: their deployment values are not
supplied to the responder. -/
def configure (oracle : DenoteOracle) (models : List CompilationModel) (input : Lean.Json) :
    Except String ByteCallEnvironment := do
  let config ← input.getObjVal? "byteCallEnvironment"
  let program ← config.getObjValAs? String "program"
  unless program == "imported-model-static-v1" do throw "unsupported byte-call model program"
  let caller ← decimal (← input.getObjVal? "account")
  let accounts ← (← (← config.getObjVal? "accounts").getArr?).toList.mapM fun entry => do
    let address ← decimal entry
    unless address < 2 ^ 160 do throw "model responder account exceeds address width"
    unless !StaticOracleMocks.reservedPrecompile address do
      throw "model responder cannot replace a reserved precompile"
    unless address != caller do throw "model responder cannot replace caller code"
    return address
  unless accounts.eraseDups.length == accounts.length do throw "duplicate model responder account"
  unless accounts.length == models.length do throw "one account per responder model required"
  unless models.all (·.immutables.isEmpty) do
    throw "model responder does not supply immutable values"
  return environment oracle (accounts.zip models) (← decimal (← config.getObjVal? "gas"))

end Compiler.CompilationModel.SolidityImport.ModelResponders

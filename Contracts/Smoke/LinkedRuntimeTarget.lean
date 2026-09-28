import Contracts.Common
import Compiler.CheckContract

set_option linter.unusedVariables false

/-!
# Runtime-target dispatch for typed calls and mutable deferred links

* **Runtime target (named bindings).** Two bindings of one interface to the
  same callee contract (`AATranche`, `BBTranche : ITranche := RtToken`) are
  interchangeable, so a typed call on a receiver that is not named after
  either binding (a parameter `_tranche : ITranche`) runs `RtToken`'s body in
  `Contract.hopCall` / `hopCallView` at the **runtime** target address. Storage
  is namespaced per target, so the two tranches are distinct tokens. Before,
  such calls fell back to the fixed adversary stub (mint did nothing,
  `totalSupply` was always the stub word).
* **G25 fail-closed.** Bindings of one interface to different callees (or a
  mix of named and `deferred` bindings) reject an unnamed receiver at
  elaboration.
* **Mutable deferred links.** `ExecutableCallContext.withLinks` answers
  state-changing typed calls on `deferred` bindings by running the linked body
  in `Contract.hopCall` at the target (commit on success, revert rolls back),
  and static calls exactly like `withViewLinks`.
-/

namespace Contracts.Smoke.LinkedRuntimeTarget

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256
open Compiler.CompilationModel.DenoteExternalCalls

verity_contract RtToken where
  storage
    supply : Uint256 := slot 0
    balances : Address → Uint256 := slot 1

  function mint (recipient : Address, amount : Uint256) : Unit := do
    let s ← getStorage supply
    setStorage supply (add s amount)
    let b ← getMapping balances recipient
    setMapping balances recipient (add b amount)

  function burn (amount : Uint256) : Unit := do
    let s ← getStorage supply
    require (amount <= s) "burn exceeds supply"
    setStorage supply (sub s amount)

  function view totalSupply () : Uint256 := do
    let s ← getStorage supply
    return s

#check_contract RtToken

/-! ## Runtime-target dispatch: two tranches of one token contract -/

verity_contract RtVault where
  storage
    last : Uint256 := slot 0

  interfaces
    interface ITranche where
      function mint(Address, Uint256)
      function burn(Uint256)
      function totalSupply() view returns (Uint256)
    end

  linked_contracts
    AATranche : ITranche := RtToken
    BBTranche : ITranche := RtToken

  function reentrancy_trusted mintTo (_tranche : ITranche, _to : Address, _shares : Uint256) : Unit := do
    _tranche.mint _to _shares

  function reentrancy_trusted burnFrom (_tranche : ITranche, _shares : Uint256) : Unit := do
    _tranche.burn _shares

  function view supplyOf (_tranche : ITranche) : Uint256 := do
    let s ← _tranche.totalSupply
    return s

  function reentrancy_trusted mintAndSupply (_tranche : ITranche, _to : Address, _shares : Uint256) : Uint256 := do
    _tranche.mint _to _shares
    let s ← _tranche.totalSupply
    return s

  -- Mint on one tranche, then read the other tranche's supply.
  function reentrancy_trusted mintThenOther (_mintOn : ITranche, _other : ITranche, _to : Address, _shares : Uint256) : Uint256 := do
    _mintOn.mint _to _shares
    let s ← _other.totalSupply
    return s

#check_contract RtVault

/-- `_tranche.mint _to _shares` on a parameter elaborates to the callee body
run in a mutating hop at the runtime target `_tranche`. -/
theorem mintTo_is_hopCall (ctx : ExecutableCallContext) (t recipient : Address) (shares : Uint256) :
    RtVault.mintTo ctx t recipient shares = Contract.hopCall t (RtToken.mint recipient shares) := rfl

theorem supplyOf_is_hopCallView (t : Address) :
    RtVault.supplyOf t = (do
      let s ← Contract.hopCallView t RtToken.totalSupply
      return s) := rfl

/-- The compilation model keeps the ABI external call (no bytecode change). -/
example :
    (RtVault.spec.externals).any (fun ext => ext.name == "ITranche.mint") = true := by
  decide

def vaultAddr : Address := (60 : Address)
def aaAddr : Address := (61 : Address)
def bbAddr : Address := (62 : Address)
def holder : Address := (7 : Address)

/-- Vault at `vaultAddr` (own slot 0 = 9); AA's namespaced supply = 100, BB's = 5. -/
def trancheState : ContractState :=
  (({ defaultState with thisAddress := vaultAddr, sender := (1 : Address) }.writeSlot 0 9
    ).writeContractSlot aaAddr.toNat 0 100).writeContractSlot bbAddr.toNat 0 5

/-- Minting on AA is real: the supply read back after the mint is 100 + 7. -/
theorem mintAndSupply_reads_real_supply :
    (RtVault.mintAndSupply ExecutableCallContext.stub aaAddr holder 7 trancheState).getValue? = some (107 : Uint256) := by
  decide

/-- Minting on AA does not change BB's supply, and commits AA's new supply
under AA's namespace; the vault's own slot 0 is untouched. -/
theorem mintTo_AA_leaves_BB :
    (RtVault.mintTo ExecutableCallContext.stub aaAddr holder 7 trancheState).getState.readContractSlot aaAddr.toNat 0 = 107 ∧
    (RtVault.mintTo ExecutableCallContext.stub aaAddr holder 7 trancheState).getState.readContractSlot bbAddr.toNat 0 = 5 ∧
    (RtVault.mintTo ExecutableCallContext.stub aaAddr holder 7 trancheState).getState.readSlot 0 = 9 := by
  decide

/-- Reading the other tranche after a mint on AA returns BB's own supply. -/
theorem mintThenOther_reads_BB :
    (RtVault.mintThenOther ExecutableCallContext.stub aaAddr bbAddr holder 7 trancheState).getValue? = some (5 : Uint256) := by
  decide

/-- Reading back BB after minting on AA, as two separate transactions. -/
theorem supply_after_mint_per_target :
    (RtVault.supplyOf aaAddr (RtVault.mintTo ExecutableCallContext.stub aaAddr holder 7 trancheState).getState).getValue? =
      some (107 : Uint256) ∧
    (RtVault.supplyOf bbAddr (RtVault.mintTo ExecutableCallContext.stub aaAddr holder 7 trancheState).getState).getValue? =
      some (5 : Uint256) := by
  decide

def revertMessage? {α : Type} : ContractResult α → Option String
  | .revert msg _ => some msg
  | .success _ _ => none

/-- A callee revert bubbles with its message and rolls AA back. -/
theorem burnFrom_revert_bubbles :
    revertMessage? (RtVault.burnFrom ExecutableCallContext.stub bbAddr 6 trancheState) = some "burn exceeds supply" ∧
    (RtVault.burnFrom ExecutableCallContext.stub bbAddr 6 trancheState).getState.readContractSlot bbAddr.toNat 0 = 5 := by
  decide

/-! ## G25: bindings to different callees fail closed -/

verity_contract RtOtherToken where
  storage
    supply : Uint256 := slot 0

  function mint (recipient : Address, amount : Uint256) : Unit := do
    setStorage supply amount

  function burn (amount : Uint256) : Unit := do
    setStorage supply 0

  function view totalSupply () : Uint256 := do
    let s ← getStorage supply
    return s

/--
error: linked_contracts: typed call 'ITrancheX.totalSupply' on receiver '_t' is ambiguous: interface 'ITrancheX' is bound to different contracts (x := RtToken, y := RtOtherToken). Name the receiver after one binding, or bind every 'ITrancheX' binding as `deferred` and answer the calls per runtime target with `ExecutableCallContext.withLinks` (G25)
-/
#guard_msgs in
verity_contract RtAmbiguous where
  storage
    last : Uint256 := slot 0

  interfaces
    interface ITrancheX where
      function totalSupply() view returns (Uint256)
    end

  linked_contracts
    x : ITrancheX := RtToken
    y : ITrancheX := RtOtherToken

  function view supplyOf (_t : ITrancheX) : Uint256 := do
    let s ← _t.totalSupply
    return s

-- A receiver named after a binding still selects that binding.
verity_contract RtNamed where
  storage
    last : Uint256 := slot 0

  interfaces
    interface ITrancheN where
      function totalSupply() view returns (Uint256)
    end

  linked_contracts
    x : ITrancheN := RtToken
    y : ITrancheN := RtOtherToken

  function view supplyOfY (y : ITrancheN) : Uint256 := do
    let s ← y.totalSupply
    return s

theorem supplyOfY_is_other (t : Address) :
    RtNamed.supplyOfY t = (do
      let s ← Contract.hopCallView t RtOtherToken.totalSupply
      return s) := rfl

/-! ## Mutable deferred links -/

verity_contract DefVault where
  storage
    last : Uint256 := slot 0

  interfaces
    interface ITrancheD where
      function mint(Address, Uint256)
      function burn(Uint256)
      function totalSupply() view returns (Uint256)
    end

  linked_contracts
    tranche : ITrancheD := deferred

  function reentrancy_trusted mintAndSupply (_t : ITrancheD, _to : Address, _shares : Uint256) : Uint256 := do
    _t.mint _to _shares
    let s ← _t.totalSupply
    return s

  function reentrancy_trusted burnFrom (_t : ITrancheD, _shares : Uint256) : Unit := do
    _t.burn _shares

#check_contract DefVault

-- The token is declared after the vault (the cyclic situation `deferred`
-- exists for).
verity_contract LateToken where
  storage
    supply : Uint256 := slot 0
    balances : Address → Uint256 := slot 1

  function mint (recipient : Address, amount : Uint256) : Unit := do
    let s ← getStorage supply
    setStorage supply (add s amount)
    let b ← getMapping balances recipient
    setMapping balances recipient (add b amount)

  function burn (amount : Uint256) : Unit := do
    let s ← getStorage supply
    require (amount <= s) "burn exceeds supply"
    setStorage supply (sub s amount)

  function view totalSupply () : Uint256 := do
    let s ← getStorage supply
    return s

#check_contract LateToken

/-- `ITrancheD.mint` calldata is `[to, amount]`. -/
def lateMint : List Uint256 → Contract (List Uint256)
  | [recipient, amount] => linkUnit (LateToken.mint (wordToAddress recipient) amount) []
  | _ => fun s => ContractResult.revert "bad calldata" s

def lateBurn : List Uint256 → Contract (List Uint256)
  | [amount] => linkUnit (LateToken.burn amount) []
  | _ => fun s => ContractResult.revert "bad calldata" s

/-- Both tranche addresses hold a `LateToken`; links are keyed by target. -/
def trancheLinks : String → Address → Option (List Uint256 → Contract (List Uint256))
  | "ITrancheD.mint", t => if t = aaAddr ∨ t = bbAddr then some lateMint else none
  | "ITrancheD.burn", t => if t = aaAddr ∨ t = bbAddr then some lateBurn else none
  | "ITrancheD.totalSupply", t =>
      if t = aaAddr ∨ t = bbAddr then some (viewLinkWord LateToken.totalSupply) else none
  | _, _ => none

def linkedCtx : ExecutableCallContext := ExecutableCallContext.stub.withLinks trancheLinks

/-- With the stub context the mint does nothing and `totalSupply` is the stub
word ("ITrancheD.totalSupply".length = 21). -/
theorem deferred_stub :
    (DefVault.mintAndSupply ExecutableCallContext.stub aaAddr holder 7 trancheState).getValue? =
      some (21 : Uint256) := by
  decide

/-- With `withLinks`, the mint runs `LateToken.mint` at AA: the supply read
back is real (107), BB is unchanged, and one journal entry per call is
recorded. -/
theorem deferred_withLinks :
    (DefVault.mintAndSupply linkedCtx aaAddr holder 7 trancheState).getValue? = some (107 : Uint256) ∧
    (DefVault.mintAndSupply linkedCtx aaAddr holder 7 trancheState).getState.readContractSlot
      aaAddr.toNat 0 = 107 ∧
    (DefVault.mintAndSupply linkedCtx aaAddr holder 7 trancheState).getState.readContractSlot
      bbAddr.toNat 0 = 5 ∧
    (DefVault.mintAndSupply linkedCtx aaAddr holder 7 trancheState).getState.calls.length = 2 := by
  decide

/-- A reverting linked body makes the typed call revert (ABI failed call) and
rolls the target back. -/
theorem deferred_withLinks_revert :
    revertMessage? (DefVault.burnFrom linkedCtx bbAddr 6 trancheState) =
      some "external call failed" ∧
    (DefVault.burnFrom linkedCtx bbAddr 6 trancheState).getState.readContractSlot
      bbAddr.toNat 0 = 5 := by
  decide

/-- Fidelity lemma instantiation for the `ITrancheD.mint` site. -/
theorem mint_site_faithful (s : ContractState) (recipient : Address) (amount : Uint256)
    (words : List Uint256) (s' : ContractState)
    (hhop : Contract.hopCall aaAddr (lateMint (ExternalArg.toWords recipient ++ [amount])) s =
      ContractResult.success words s') :
    (externalCallEffectWordsTo "ITrancheD.mint" aaAddr (ExternalArg.toWords recipient ++ [amount])
        (AdversaryModel.stub.withLinks trancheLinks) 0).run s =
      ContractResult.success ()
        { s' with
          calls := s.calls ++
            [journalEntry (linkedCallSite "ITrancheD.mint" (ExternalArg.toWords recipient ++ [amount]) 0 .call
              aaAddr.toNat 0 [] 0) (.success (words.map Core.Uint256.val))]
          returndata := (words.map Core.Uint256.val).map
            Compiler.CompilationModel.Denote.wordNormalize } :=
  externalCallEffectWordsTo_withLinks _ trancheLinks "ITrancheD.mint" aaAddr _ 0 s lateMint
    words s' (by simp [trancheLinks]) hhop

end Contracts.Smoke.LinkedRuntimeTarget

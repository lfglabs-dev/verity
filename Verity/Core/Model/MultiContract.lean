import Verity.Core

/-!
# Multi-contract world with ETH-valued calls

A finite map `Address → ContractState`. A hop debits the caller,
credits the callee (so `selfBalance` is the post-call balance),
installs the call context (`sender` / `thisAddress` / `msgValue`),
applies an explicit callee step, and journals `target` and `value`
on the caller.

The P-ETH-1 ensemble is `Bus → Gateway → Vault → (Lido | request)`.
This is a model-plane composition, not a claim that those contracts
are compiled or L2-proved. No keccak injectivity, no new axiom.
-/

namespace Verity.MultiContract

/-- One named account in the ensemble. -/
structure Account where
  address : Address
  state : ContractState
  deriving Repr

/-- Finite multi-contract world. Missing addresses read as `defaultState`. -/
structure MultiWorld where
  accounts : List Account
  deriving Repr

def lookup (w : MultiWorld) (addr : Address) : ContractState :=
  match w.accounts.find? (fun a => a.address == addr) with
  | some a => a.state
  | none => defaultState

def upsert (w : MultiWorld) (addr : Address) (s : ContractState) : MultiWorld :=
  if w.accounts.any (fun a => a.address == addr) then
    { accounts := w.accounts.map (fun a =>
        if a.address == addr then { a with state := s } else a) }
  else
    { accounts := w.accounts ++ [{ address := addr, state := s }] }

/-- Call-frame context installed on the callee: sender, this, msg.value,
    and `selfBalance` after receiving `value`. -/
def withCallContext (callee : ContractState) (caller this : Address)
    (value : Core.Uint256) : ContractState :=
  { callee with
    sender := caller
    thisAddress := this
    msgValue := value
    selfBalance := callee.selfBalance + value }

def totalSelfBalance (w : MultiWorld) : Nat :=
  w.accounts.foldl (fun acc a => acc + a.state.selfBalance.val) 0

/-- One ETH-valued hop. Fails when the caller cannot pay. The callee
    step sees the credited, re-contextualized world. -/
def callValue (w : MultiWorld) (caller callee : Address) (value : Core.Uint256)
    (name : String := "") (calldata : List Nat := [])
    (calleeStep : ContractState → ContractState := id) : Option MultiWorld :=
  let fromS := lookup w caller
  let toS := lookup w callee
  if value ≤ fromS.selfBalance then
    let fromPaid : ContractState :=
      { fromS with selfBalance := fromS.selfBalance - value }
    let toAfter := calleeStep (withCallContext toS caller callee value)
    let fromJournaled : ContractState :=
      { fromPaid with
        calls := fromPaid.calls ++
          [{ siteId := callee.toNat
             kind := .call
             target := callee.toNat
             value := value.val
             calldata := calldata
             control := .success
             returndata := []
             name := name }] }
    some (upsert (upsert w caller fromJournaled) callee toAfter)
  else
    none

/-! ## P-ETH-1 ensemble: Bus → Gateway → Vault → (Lido | request) -/

def busAddr : Address := (1 : Address)
def gatewayAddr : Address := (2 : Address)
def vaultAddr : Address := (3 : Address)
def lidoAddr : Address := (4 : Address)
def requestAddr : Address := (5 : Address)

inductive VaultRoute where
  | lido
  | request
  deriving DecidableEq, Repr

def accountAt (addr : Address) (bal : Nat) : Account :=
  { address := addr
    state := { defaultState with thisAddress := addr, selfBalance := bal } }

def fundedBus (busWei : Nat) : MultiWorld :=
  { accounts :=
      [accountAt busAddr busWei,
       accountAt gatewayAddr 0,
       accountAt vaultAddr 0,
       accountAt lidoAddr 0,
       accountAt requestAddr 0] }

/-- Forward `value` along Bus → Gateway → Vault → route. -/
def routeEth (w : MultiWorld) (value : Core.Uint256) (route : VaultRoute) :
    Option MultiWorld :=
  match callValue w busAddr gatewayAddr value (name := "busToGateway") with
  | none => none
  | some w1 =>
      match callValue w1 gatewayAddr vaultAddr value (name := "gatewayToVault") with
      | none => none
      | some w2 =>
          match route with
          | .lido =>
              callValue w2 vaultAddr lidoAddr value (name := "vaultToLido")
          | .request =>
              callValue w2 vaultAddr requestAddr value (name := "vaultToRequest")

/-! ## Laws -/

theorem withCallContext_selfBalance (callee : ContractState)
    (caller this : Address) (value : Core.Uint256) :
    (withCallContext callee caller this value).selfBalance =
      callee.selfBalance + value :=
  rfl

theorem withCallContext_msgValue (callee : ContractState)
    (caller this : Address) (value : Core.Uint256) :
    (withCallContext callee caller this value).msgValue = value :=
  rfl

theorem withCallContext_this (callee : ContractState)
    (caller this : Address) (value : Core.Uint256) :
    (withCallContext callee caller this value).thisAddress = this :=
  rfl

theorem withCallContext_sender (callee : ContractState)
    (caller this : Address) (value : Core.Uint256) :
    (withCallContext callee caller this value).sender = caller :=
  rfl

theorem callValue_none_of_cannot_pay (w : MultiWorld)
    (caller callee : Address) (value : Core.Uint256)
    (h : (lookup w caller).selfBalance < value) :
    callValue w caller callee value = none := by
  simpa [callValue] using h

theorem fundedBus_bus_balance (n : Nat) :
    (lookup (fundedBus n) busAddr).selfBalance =
      (n : Core.Uint256) := by
  unfold lookup fundedBus accountAt
  simp [busAddr]

end Verity.MultiContract

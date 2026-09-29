import Contracts.Common
import Compiler.CheckContract

set_option linter.unusedVariables false

namespace Contracts.Smoke.LinkedGettersAndDeferred

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256
open Compiler.CompilationModel.DenoteExternalCalls

/-! ## G23 (#2439): public state-variable getters as hop targets -/

verity_contract GetterCalleeBase where
  storage
    total : Uint256 := slot 0

  function view readTotal () : Uint256 := do
    let v ← getStorage total
    return v

verity_contract GetterCallee is GetterCalleeBase where
  storage
    manager : Address := slot 1
    flag : Uint256 := slot 2
    balances : Address → Uint256 := slot 3
    ids : Uint256 → Uint256 := slot 4
    allowances : Address → Address → Uint256 := slot 5

  function setFlag (v : Uint256) : Unit := do
    setStorage flag v

#check_contract GetterCallee

verity_contract GetterCaller where
  storage
    last : Uint256 := slot 0

  interfaces
    interface IGetters where
      function manager() view returns (Address)
      function total() view returns (Uint256)
      function flag() view returns (Bool)
      function balances(Address) view returns (Uint256)
      function ids(Uint256) view returns (Uint256)
      function allowances(Address, Address) view returns (Uint256)
    end

  linked_contracts
    callee : IGetters := GetterCallee

  function view readManager (c : IGetters) : Address := do
    let a ← c.manager
    return a

  function view readTotal (c : IGetters) : Uint256 := do
    let v ← c.total
    return v

  function view readFlag (c : IGetters) : Bool := do
    let b ← c.flag
    return b

  function view readBalance (c : IGetters, who : Address) : Uint256 := do
    let v ← c.balances who
    return v

  function view readId (c : IGetters, k : Uint256) : Uint256 := do
    let v ← c.ids k
    return v

  function view readAllowance (c : IGetters, o : Address, sp : Address) : Uint256 := do
    let v ← c.allowances o sp
    return v

#check_contract GetterCaller

/-- Inherited field constant (declared in the parent) is emitted in the child. -/
example : GetterCallee.total.slot = 0 := rfl

/-- The generated getter hops are literally view hops reading callee storage. -/
theorem readTotal_is_hopCallView (c : Address) :
    GetterCaller.readTotal c = (do
      let v ← Contract.hopCallView c (getStorage GetterCallee.total)
      return v) := rfl

theorem readManager_is_hopCallView (c : Address) :
    GetterCaller.readManager c = (do
      let a ← Contract.hopCallView c (getStorageAddr GetterCallee.manager)
      return a) := rfl

theorem readFlag_is_hopCallView (c : Address) :
    GetterCaller.readFlag c = (do
      let b ← Contract.hopCallView c
        (Verity.bind (getStorage GetterCallee.flag) fun w => Verity.pure (w != 0))
      return b) := rfl

theorem readBalance_is_hopCallView (c who : Address) :
    GetterCaller.readBalance c who = (do
      let v ← Contract.hopCallView c (getMapping GetterCallee.balances who)
      return v) := rfl

theorem readId_is_hopCallView (c : Address) (k : Uint256) :
    GetterCaller.readId c k = (do
      let v ← Contract.hopCallView c (getMappingUint GetterCallee.ids k)
      return v) := rfl

theorem readAllowance_is_hopCallView (c o sp : Address) :
    GetterCaller.readAllowance c o sp = (do
      let v ← Contract.hopCallView c (getMapping2 GetterCallee.allowances o sp)
      return v) := rfl

-- A getter whose interface return type does not match the field fails closed.
/--
error: linked_contracts 'callee': 'GetterCallee.manager' is a storage field of type `StorageSlot (Address)`; interface return type Verity.Macro.ValueType.uint256 does not match an Address getter
-/
#guard_msgs in
verity_contract BadGetterCaller where
  storage
    last : Uint256 := slot 0

  interfaces
    interface IBad where
      function manager() view returns (Uint256)
    end

  linked_contracts
    callee : IBad := GetterCallee

  function view readManagerWord (c : IBad) : Uint256 := do
    let a ← c.manager
    return a

def callerAddr : Address := (20 : Address)
def calleeAddr : Address := (21 : Address)
def holder : Address := (7 : Address)

/-- Caller state holding the callee's namespaced scalar slots (total = 42 at
slot 0, flag = 1 at slot 2) and, in the caller's own slots, different values. -/
def getterState : ContractState :=
  ((({ defaultState with thisAddress := callerAddr, sender := (1 : Address) }.writeSlot 0 5).writeSlot 2 0
    ).writeContractSlot calleeAddr.toNat 0 42).writeContractSlot calleeAddr.toNat 2 1

/-- Concrete: the caller's `total()` returns the callee's namespaced slot 0. -/
theorem readTotal_returns_callee_total :
    (GetterCaller.readTotal calleeAddr getterState).getValue? = some (42 : Uint256) := by
  decide

/-- Concrete: the Bool getter decodes the callee's 0/1 word as `word != 0`. -/
theorem readFlag_returns_callee_flag :
    (GetterCaller.readFlag calleeAddr getterState).getValue? = some true := by
  decide

/-- The caller's own slot 0 is untouched and differs from the callee value. -/
example : getterState.storage 0 = 5 := by decide

/-- Address/mapping getters return what the callee's own read returns inside the
hop frame (stated against `enterHop`, so it stays valid once non-slot channels
are namespaced per contract). -/
theorem readManager_returns_callee_read (s : ContractState) (h : s.thisAddress ≠ calleeAddr) :
    (GetterCaller.readManager calleeAddr s).getValue? =
      (getStorageAddr GetterCallee.manager (s.enterHop s.thisAddress calleeAddr)).getValue? := by
  rw [readManager_is_hopCallView]
  simp only [Bind.bind, Verity.bind, Pure.pure, Verity.pure]
  rw [Contract.hopCallView_of_ne _ _ _ h]
  rfl

theorem readBalance_returns_callee_read (s : ContractState) (who : Address)
    (h : s.thisAddress ≠ calleeAddr) :
    (GetterCaller.readBalance calleeAddr who s).getValue? =
      (getMapping GetterCallee.balances who (s.enterHop s.thisAddress calleeAddr)).getValue? := by
  rw [readBalance_is_hopCallView]
  simp only [Bind.bind, Verity.bind, Pure.pure, Verity.pure]
  rw [Contract.hopCallView_of_ne _ _ _ h]
  rfl

/-- The model plane keeps the ABI external call for getters. -/
example :
    (GetterCaller.spec.externals).any (fun ext => ext.name == "IGetters.total") = true := by
  decide

/-! ## G15 (#2415): deferred (cyclic) bindings -/

verity_contract DeferredA where
  storage
    x : Uint256 := slot 0

  interfaces
    interface IB where
      function value() view returns (Uint256)
      function double() view returns (Uint256)
    end

  linked_contracts
    b : IB := deferred

  function view getX () : Uint256 := do
    let v ← getStorage x
    return v

  function internal view _bValue (t : IB) : Uint256 := do
    let v ← t.value
    return v

  function view sumB (t : IB) : Uint256 := do
    let v ← _bValue t
    let d ← t.double
    return (add v d)

#check_contract DeferredA

verity_contract DeferredB where
  storage
    y : Uint256 := slot 0

  interfaces
    interface IA where
      function getX() view returns (Uint256)
    end

  linked_contracts
    a : IA := DeferredA

  function view value () : Uint256 := do
    let v ← getStorage y
    return v

  function internal view _readA (t : IA) : Uint256 := do
    let v ← t.getX
    return v

  -- Not marked `view`: the generated view-frame theorem does not see through
  -- a bound hop whose target is `msg.sender`; the caller's interface still
  -- declares `double()` as view, so A reaches it with a static call.
  function double () : Uint256 := do
    let p ← msgSender
    let ax ← _readA p
    return (add ax ax)

#check_contract DeferredB

/-- `sumB` (and the helper it calls) take the call context: the deferred calls
    are answered by the threaded context, not by the fixed stub. -/
example : DeferredA.sumB = fun (ctx : ExecutableCallContext) (t : Address) =>
    DeferredA.sumB ctx t := rfl
example : DeferredA._bValue = fun (ctx : ExecutableCallContext) (t : Address) =>
    DeferredA._bValue ctx t := rfl

/-- The model plane keeps the ABI external call for deferred bindings. -/
example :
    (DeferredA.spec.externals).any (fun ext => ext.name == "IB.double") = true := by
  decide

def aAddr : Address := (30 : Address)
def bAddr : Address := (31 : Address)

/-- A at `aAddr` with its own slot 0 = 3; B's namespaced slot 0 (`y`) = 10.
B's `double` calls back `msg.sender` (= A inside the hop). Only scalar slots
are used, so the check is independent of address/mapping channel namespacing. -/
def cyclicState : ContractState :=
  ({ defaultState with thisAddress := aAddr, sender := (1 : Address) }.writeSlot 0 3
    ).writeContractSlot bAddr.toNat 0 10

/-- With the stub context nothing changes vs. before: each deferred static call
returns the fixed stub word `name.length + Σ args` ("IB.value" = 8,
"IB.double" = 9). -/
theorem sumB_stub :
    (DeferredA.sumB ExecutableCallContext.stub bAddr cyclicState).getValue? =
      some (17 : Uint256) := by
  decide

/-- Faithful responder: answer the deferred IB calls by B's generated bodies. -/
def bLinks : String → Address → Option (List Uint256 → Contract (List Uint256))
  | "IB.value", t => if t = bAddr then some (viewLinkWord DeferredB.value) else none
  | "IB.double", t => if t = bAddr then some (viewLinkWord DeferredB.double) else none
  | _, _ => none

/-- `value` returns B's storage (10); `double` hops back into A (`getX` = 3)
and doubles it (6): 10 + 6 = 16. -/
theorem sumB_withViewLinks :
    (DeferredA.sumB (ExecutableCallContext.stub.withViewLinks bLinks) bAddr cyclicState).getValue? =
      some (16 : Uint256) := by
  decide

/-- Fidelity lemma instantiation for the `IB.value` site. -/
theorem value_site_faithful (s : ContractState) (words : List Uint256) (s' : ContractState)
    (hhop : Contract.hopCallView bAddr (viewLinkWord DeferredB.value []) s =
      ContractResult.success words s')
    (harity : 1 ≤ words.length) :
    ∃ post,
      (externalStaticCallContractWordsTo (α := Uint256) "IB.value" bAddr []
          (AdversaryModel.stub.withViewLinks bLinks) 1 0).run s =
        ContractResult.success (ExternalResult.fromWords (words.take 1)) post ∧
      post.storageWords = s.storageWords :=
  externalStaticCallContractWordsTo_withViewLinks _ bLinks "IB.value" bAddr [] 1 0 s
    (viewLinkWord DeferredB.value) words s' (by simp [bLinks]) hhop harity

end Contracts.Smoke.LinkedGettersAndDeferred

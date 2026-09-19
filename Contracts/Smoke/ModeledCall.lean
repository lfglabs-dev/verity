import Contracts.Common
import Compiler.CheckContract
import Verity.Core.Model.ModeledCall

set_option linter.unusedVariables false

namespace Contracts.Smoke

open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.MultiContract
open Compiler.CompilationModel.DenoteExternalCalls

def addrA : Address := (10 : Address)
def addrB : Address := (11 : Address)

verity_contract ModeledCallee where
  storage
    value : Uint256 := slot 0

  function view get () : Uint256 := do
    let v ← getStorage value
    return v

  function set (v : Uint256) : Unit := do
    setStorage value v

  function boom () : Unit := do
    require false "callee revert"

#check_contract ModeledCallee

verity_contract ModeledCaller where
  storage
    last : Uint256 := slot 0

  interfaces
    interface ICallee where
      function get() view returns (Uint256)
      function set(Uint256)
      function boom()
    end

  linked_contracts
    callee : ICallee := ModeledCallee

  function reentrancy_trusted allow_post_interaction_writes record (token : ICallee) : Uint256 := do
    let v ← token.get
    setStorage last v
    return v

  function reentrancy_trusted ping (token : ICallee, v : Uint256) : Unit := do
    token.set v

#check_contract ModeledCaller

example :
    (ModeledCaller.spec.externals).any (fun ext =>
      ext.name == "ICallee.get") = true := by
  decide

example :
    (ModeledCaller.spec.functions).any (fun fn =>
      fn.name == "record" &&
        fn.body.any (fun stmt =>
          match stmt with
          | Compiler.CompilationModel.Stmt.ecm mod _ =>
              mod.name == "oracleSummary" &&
                mod.summaryName == "ICallee.get"
          | _ => false)) = true := by
  decide

def world0 : MultiWorld :=
  { accounts :=
      [{ address := addrA
         state := { defaultState with thisAddress := addrA } },
       { address := addrB
         state := { defaultState with thisAddress := addrB } }] }

def writeBody (v : Uint256) : Contract Unit :=
  setStorage ⟨0⟩ v

def readBody : Contract Uint256 :=
  getStorage ⟨0⟩

def revertBody : Contract Unit := fun s =>
  ContractResult.revert "callee revert" s

def sampleFrame : CallFrame :=
  { caller := addrA
    callee := addrB
    site := modeledSite addrB
    callerBefore := lookup world0 addrA
    calleeBefore := lookup world0 addrB
    calleeEntry := withCallContext (lookup world0 addrB) addrA addrB 0 }

theorem modeled_addrs_ne : addrA ≠ addrB := by
  intro h
  have hv := congrArg (fun a : Address => a.val) h
  have ha : addrA.val = 10 := rfl
  have hb : addrB.val = 11 := rfl
  rw [ha, hb] at hv
  cases hv

/-- Named Feature 2 theorem: callee sees the caller as sender. -/
example : (withCallContext (lookup world0 addrB) addrA addrB 0).sender = addrA :=
  enter_sender (lookup world0 addrB) addrA addrB 0

theorem modeled_external_success :
    (runContract (writeBody 7) sampleFrame).result = .success [] := by
  simp [runContract, writeBody, setStorage, sampleFrame]

theorem modeled_external_success_world :
    (executeHop world0 sampleFrame (runContract (writeBody 7))).result = .success [] := by
  have hneq : sampleFrame.caller ≠ sampleFrame.callee := by
    simpa [sampleFrame] using modeled_addrs_ne
  have hrun : (runContract (writeBody 7) sampleFrame).result = .success [] :=
    modeled_external_success
  have ⟨hr, _, _, _, _⟩ :=
    external_success world0 sampleFrame (runContract (writeBody 7)) [] hneq hrun
  exact hr

theorem modeled_external_failure :
    (executeHop world0 sampleFrame (runContract revertBody)).result = .revert [] := by
  have hneq : sampleFrame.caller ≠ sampleFrame.callee := by
    simpa [sampleFrame] using modeled_addrs_ne
  have hrun : (runContract revertBody sampleFrame).result = .revert [] := by
    simp [runContract, revertBody]
  have ⟨hr, _, _⟩ :=
    external_failure world0 sampleFrame (runContract revertBody) [] hneq hrun
  exact hr

/-- View hop from B into A discards callee writes (A's storage stays). -/
theorem modeled_view_discards :
    (executeViewHop world0 sampleFrame (runContract (writeBody 7))).result =
      (runContract (writeBody 7) sampleFrame).result := by
  have hneq : sampleFrame.caller ≠ sampleFrame.callee := by
    simpa [sampleFrame] using modeled_addrs_ne
  simp [executeViewHop, hneq]

theorem modeled_selfCall_restores_sender (s : ContractState) :
    ∀ s',
      revertBody { s with sender := s.thisAddress, msgValue := 0, returndata := [] } =
          ContractResult.revert "callee revert" s' →
        Contract.selfCall revertBody s = ContractResult.revert "callee revert" s :=
  fun s' h => selfCall_failure revertBody s "callee revert" s' h

def callerState : ContractState :=
  { defaultState with thisAddress := addrA, sender := (1 : Address) }

theorem caller_addr_ne_callee : callerState.thisAddress ≠ addrB := by
  simpa [callerState] using modeled_addrs_ne

theorem addrB_toNat_ne_zero : addrB.toNat ≠ 0 := by
  intro h
  have hb : addrB.val = 11 := rfl
  have ht : addrB.toNat = addrB.val := rfl
  rw [ht, hb] at h
  cases h

/-- Bound view hop reads the callee's namespaced slot, not the caller's. -/
theorem hopCallView_reads_callee_slot :
    (Contract.hopCallView addrB readBody
      (callerState.writeContractSlot addrB.toNat 0 7)).getValue? = some (7 : Uint256) := by
  set s := callerState.writeContractSlot addrB.toNat 0 7
  have hneq : s.thisAddress ≠ addrB := by
    simpa [s, ContractState.writeContractSlot_thisAddress] using caller_addr_ne_callee
  rw [Contract.hopCallView_of_ne addrB readBody s hneq]
  have hread :
      readBody (s.enterHop s.thisAddress addrB) =
        ContractResult.success (s.storageWords (.contractSlot addrB.toNat 0))
          (s.enterHop s.thisAddress addrB) := by
    simp [readBody, getStorage, ContractState.enterHop_readSlot]
  simp [hread, ContractResult.getValue?]
  exact ContractState.writeContractSlot_contract callerState addrB.toNat 0 7
    addrB_toNat_ne_zero

/-- Mutating hop commits the callee body into `contractSlot callee`. -/
theorem hopCall_commits_callee_slot :
    (Contract.hopCall addrB (writeBody 9) callerState).getState.storageWords
      (.contractSlot addrB.toNat 0) = (9 : Uint256) := by
  rw [Contract.hopCall_of_ne addrB (writeBody 9) callerState caller_addr_ne_callee]
  have hwrite :
      writeBody 9 (callerState.enterHop callerState.thisAddress addrB) =
        ContractResult.success ()
          ((callerState.enterHop callerState.thisAddress addrB).writeSlot 0 9) := by
    simp [writeBody, setStorage]
  simp [hwrite, ContractResult.getState, ContractState.exitHop,
    ContractState.switchSlotWorld, ContractState.writeSlot]

/-- Revert restores the pre-call snapshot, including caller slots. -/
theorem hopCall_failure_restores :
    Contract.hopCall addrB revertBody callerState =
      ContractResult.revert "callee revert" callerState := by
  rw [Contract.hopCall_of_ne addrB revertBody callerState caller_addr_ne_callee]
  simp [revertBody]

/-- View hop discards callee writes. -/
theorem hopCallView_discards_callee_slot :
    (Contract.hopCallView addrB (writeBody 9) callerState).getState.storageWords
      (.contractSlot addrB.toNat 0) =
      callerState.storageWords (.contractSlot addrB.toNat 0) := by
  rw [Contract.hopCallView_of_ne addrB (writeBody 9) callerState caller_addr_ne_callee]
  have hwrite :
      writeBody 9 (callerState.enterHop callerState.thisAddress addrB) =
        ContractResult.success ()
          ((callerState.enterHop callerState.thisAddress addrB).writeSlot 0 9) := by
    simp [writeBody, setStorage]
  simp [hwrite, ContractResult.getState]

/-- Callee storage field is slot 0, the key `writeContractSlot addrB 0` parks. -/
theorem modeled_callee_value_slot : ModeledCallee.value.slot = 0 := rfl

/-- Oracle-stub word for a skipped `ICallee.get` hop (`name.length + Σ args`). -/
theorem icaller_get_stub_word :
    AdversaryModel.stubWord "ICallee.get" [] = 11 := rfl

/-- Generated `record` is a view hop into `ModeledCallee.get`, not the oracle stub.
    A skipped hop would take an `ExecutableCallContext` and return `stubWord` 11. -/
theorem record_is_hopCallView (token : Address) :
    ModeledCaller.record token = (do
      let v ← Contract.hopCallView token ModeledCallee.get
      setStorage ModeledCaller.last v
      return v) := rfl

/-- Generated `ping` hops into `ModeledCallee.set`. -/
theorem ping_is_hopCall (ctx : ExecutableCallContext) (token : Address) (v : Uint256) :
    ModeledCaller.ping ctx token v = Contract.hopCall token (ModeledCallee.set v) := rfl

/-- Bound view hop through the generated caller reads the callee body, not the stub. -/
theorem record_executes_modeled_callee_get :
    (ModeledCaller.record addrB
      (callerState.writeContractSlot addrB.toNat 0 7)).getValue? =
      some (7 : Uint256) := by
  rw [record_is_hopCallView]
  set s := callerState.writeContractSlot addrB.toNat 0 7
  have hneq : s.thisAddress ≠ addrB := by
    simpa [s, ContractState.writeContractSlot_thisAddress] using caller_addr_ne_callee
  have hget :
      ModeledCallee.get (s.enterHop s.thisAddress addrB) =
        ContractResult.success (s.storageWords (.contractSlot addrB.toNat 0))
          (s.enterHop s.thisAddress addrB) := by
    simp [ModeledCallee.get, Bind.bind, Verity.bind, Pure.pure, Verity.pure,
      getStorage, modeled_callee_value_slot, ContractState.enterHop_readSlot]
  simp [Bind.bind, Verity.bind]
  rw [Contract.hopCallView_of_ne addrB ModeledCallee.get s hneq]
  simp [hget, setStorage, ModeledCaller.last, Pure.pure, Verity.pure,
    ContractResult.getValue?]
  exact ContractState.writeContractSlot_contract callerState addrB.toNat 0 7
    addrB_toNat_ne_zero

/-- The generated hop result is not the adversary-oracle stub word. -/
theorem record_result_ne_stub_word :
    (ModeledCaller.record addrB
      (callerState.writeContractSlot addrB.toNat 0 7)).getValue? ≠
      some (AdversaryModel.stubWord "ICallee.get" [] : Uint256) := by
  rw [record_executes_modeled_callee_get, icaller_get_stub_word]
  intro h
  have hv := congrArg (fun o : Option Uint256 => o.map (fun w => w.val)) h
  simp at hv
  cases hv

/-- Bound mutating hop through the generated caller commits callee storage. -/
theorem ping_executes_modeled_callee_set :
    (ModeledCaller.ping ExecutableCallContext.stub addrB 9 callerState).getState.storageWords
      (.contractSlot addrB.toNat 0) = (9 : Uint256) := by
  rw [ping_is_hopCall]
  rw [Contract.hopCall_of_ne addrB (ModeledCallee.set 9) callerState caller_addr_ne_callee]
  have hwrite :
      ModeledCallee.set 9 (callerState.enterHop callerState.thisAddress addrB) =
        ContractResult.success ()
          ((callerState.enterHop callerState.thisAddress addrB).writeSlot 0 9) := by
    simp [ModeledCallee.set, setStorage, modeled_callee_value_slot]
  simp [hwrite, ContractResult.getState, ContractState.exitHop,
    ContractState.switchSlotWorld, ContractState.writeSlot]

/-- Bound revert hop restores the pre-call snapshot. A skipped hop through the
    oracle stub would not revert (`boom` is not the reserved `"fail"` name). -/
theorem hopCall_modeled_callee_boom_restores :
    Contract.hopCall addrB ModeledCallee.boom callerState =
      ContractResult.revert "callee revert" callerState := by
  rw [Contract.hopCall_of_ne addrB ModeledCallee.boom callerState caller_addr_ne_callee]
  simp [ModeledCallee.boom, require]

end Contracts.Smoke

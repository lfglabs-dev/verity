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

end Contracts.Smoke

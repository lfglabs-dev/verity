import Verity.Proofs.LoopSimulationResultAware

/-! A two-site external-call loop that stops on failure and reverts on revert. -/
namespace Contracts.Examples.ResultAwareLoop

open Compiler.CompilationModel.DenoteExternalCalls
open Verity.Proofs.LoopSimulationResultAware

def first : CallSite :=
  { siteId := 1, kind := .call, target := 10, gas := 30 }

def second : CallSite :=
  { siteId := 2, kind := .delegatecall, target := 20, gas := 30 }

/-- Successful calls continue from the observed post-call state, failures stop,
and external reverts become loop reverts. -/
def stopOnFailure : Body := fun _ _ observation =>
  match observation.result with
  | .success _ => .continue observation.state
  | .failure _ => .stop observation.state
  | .revert _ => .revert

/-- A failure at the first site stops the loop before `second` is executed. -/
example (adversary : AdversaryModel) (state : CallState) (data : List Nat)
    (hfailure : adversary.result first state.world = .failure data) :
    execResultAwareForEach adversary stopOnFailure state [first, second] =
      .stop (denoteCall adversary first state).state := by
  simp [execResultAwareForEach, stopOnFailure, denoteCall, hfailure]

/-- A revert at the first site is propagated unchanged. -/
example (adversary : AdversaryModel) (state : CallState) (data : List Nat)
    (hrevert : adversary.result first state.world = .revert data) :
    execResultAwareForEach adversary stopOnFailure state [first, second] = .revert := by
  simp [execResultAwareForEach, stopOnFailure, denoteCall, hrevert]

end Contracts.Examples.ResultAwareLoop

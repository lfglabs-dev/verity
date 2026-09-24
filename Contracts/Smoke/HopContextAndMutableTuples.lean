import Contracts.Common
import Compiler.CheckContract

set_option linter.unusedVariables false

/-!
# Bound hops into context-taking callees (G26) and mutable typed tuple calls (G14)

* G26: a bound typed call whose resolved callee function takes the
  `ExecutableCallContext` (because the callee reaches a `deferred` link or opens
  a reentrancy window) makes the enclosing caller take the context too, so the
  callee's nested calls are answered by the context the proof instantiates and
  never by the fixed stub. Propagated to callers through internal helpers.
* G14 residual: `let (a, b) ← s.m x` on a state-changing interface method.
  Bound: `Contract.hopCall target (Callee.m x)` (callee revert bubbles).
  Unbound: the mutable ABI external call with arity = number of results.
  Compilation model: `Compiler.Modules.Calls.withReturnsModule` (ABI `call`
  binding several return words).
-/

namespace Contracts.Smoke.HopContextAndMutableTuples

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256
open Compiler.CompilationModel.DenoteExternalCalls

/-! ## G26 -/

verity_contract G26A where
  storage
    k : Uint256 := slot 0

  interfaces
    interface IOracle where
      function price() view returns (Uint256)
    end

  linked_contracts
    oracle : IOracle := deferred

  function view preview (o : IOracle, x : Uint256) : Tuple [Uint256, Uint256] := do
    let p ← o.price
    let kk ← getStorage k
    return (add p x, kk)

  function view previewOne (o : IOracle) : Uint256 := do
    let p ← o.price
    return p

  function view readK () : Uint256 := do
    let v ← getStorage k
    return v

#check_contract G26A

verity_contract G26B where
  storage
    last : Uint256 := slot 0

  interfaces
    interface IA where
      function preview(Address, Uint256) view returns (Uint256, Uint256)
      function previewOne(Address) view returns (Uint256)
      function readK() view returns (Uint256)
    end

  linked_contracts
    a : IA := G26A

  -- Context-free-looking view wrapper: no external call of its own besides the
  -- bound tuple call into `G26A.preview`, which takes the context.
  function view wrap (_s : IA, o : Address, x : Uint256) : Tuple [Uint256, Uint256] := do
    let (p, q) ← _s.preview o x
    return (p, q)

  function internal view _one (_s : IA, o : Address) : Uint256 := do
    let p ← _s.previewOne o
    return p

  -- Reaches the context-taking callee only through an internal helper.
  function view viaHelper (_s : IA, o : Address) : Uint256 := do
    let p ← _one _s o
    return p

  function internal view _pair (_s : IA, o : Address, x : Uint256) : Tuple [Uint256, Uint256] := do
    let (p, q) ← _s.preview o x
    return (p, q)

  -- Reaches the context-taking callee through a destructuring bind of an
  -- internal tuple helper (`let (a, b) ← helper args`).
  function view viaPairHelper (_s : IA, o : Address, x : Uint256) : Uint256 := do
    let (p, q) ← _pair _s o x
    return add p q

  -- Control: `G26A.readK` is context-free, so this wrapper stays context-free.
  function view wrapK (_s : IA) : Uint256 := do
    let v ← _s.readK
    return v

#check_contract G26B

/-- The wrapper, the helper and its caller take the call context. -/
example : G26B.wrap = fun (ctx : ExecutableCallContext) (s o : Address) (x : Uint256) =>
    G26B.wrap ctx s o x := rfl
example : G26B._one = fun (ctx : ExecutableCallContext) (s o : Address) =>
    G26B._one ctx s o := rfl
example : G26B.viaHelper = fun (ctx : ExecutableCallContext) (s o : Address) =>
    G26B.viaHelper ctx s o := rfl
example : G26B.viaPairHelper = fun (ctx : ExecutableCallContext) (s o : Address) (x : Uint256) =>
    G26B.viaPairHelper ctx s o x := rfl
/-- A bound hop into a context-free callee keeps the context-free signature. -/
example : G26B.wrapK = fun (s : Address) => G26B.wrapK s := rfl

/-- The bound hop forwards the caller's context into the callee body. -/
theorem wrap_forwards_ctx (ctx : ExecutableCallContext) (s o : Address) (x : Uint256) :
    G26B.wrap ctx s o x = (do
      let r ← Contract.hopCallView s (G26A.preview ctx o x)
      match r with
      | (p, q) => Verity.pure (p, q)) := rfl

def bAddr : Address := (40 : Address)
def aAddr : Address := (41 : Address)
def oAddr : Address := (42 : Address)

/-- B at `bAddr`; A's namespaced slot 0 (`k`) = 5; B's own slot 0 = 9. -/
def g26State : ContractState :=
  ({ defaultState with thisAddress := bAddr, sender := (1 : Address) }.writeSlot 0 9
    ).writeContractSlot aAddr.toNat 0 5

/-- Faithful responder for the oracle `A` reads through its deferred link. -/
def oracleLinks : String → Address → Option (List Uint256 → Contract (List Uint256))
  | "IOracle.price", t => if t = oAddr then some (viewLinkWord (Verity.pure 100)) else none
  | _, _ => none

/-- With the stub, A's nested `IOracle.price` returns the stub word
("IOracle.price".length = 13): (13 + 2, k = 5). -/
theorem wrap_stub :
    (G26B.wrap ExecutableCallContext.stub aAddr oAddr 2 g26State).getValue? =
      some ((15 : Uint256), (5 : Uint256)) := by
  decide

/-- The context instantiated by the proof reaches the nested deferred call:
`price` = 100, so the wrapper returns (102, 5). -/
theorem wrap_withViewLinks :
    (G26B.wrap (ExecutableCallContext.stub.withViewLinks oracleLinks) aAddr oAddr 2
      g26State).getValue? = some ((102 : Uint256), (5 : Uint256)) := by
  decide

/-- Same through an internal helper chain. -/
theorem viaHelper_withViewLinks :
    (G26B.viaHelper ExecutableCallContext.stub aAddr oAddr g26State).getValue? =
        some (13 : Uint256) ∧
    (G26B.viaHelper (ExecutableCallContext.stub.withViewLinks oracleLinks) aAddr oAddr
      g26State).getValue? = some (100 : Uint256) := by
  decide

/-- Same through a destructuring bind of an internal tuple helper:
(102, 5) sums to 107 with the faithful responder, (15, 5) to 20 with the stub. -/
theorem viaPairHelper_withViewLinks :
    (G26B.viaPairHelper ExecutableCallContext.stub aAddr oAddr 2 g26State).getValue? =
        some (20 : Uint256) ∧
    (G26B.viaPairHelper (ExecutableCallContext.stub.withViewLinks oracleLinks) aAddr oAddr 2
      g26State).getValue? = some (107 : Uint256) := by
  decide

/-! ## G14 residual: mutable typed tuple calls -/

verity_contract G14Callee where
  storage
    counter : Uint256 := slot 0

  function prepare (x : Uint256) : Tuple [Uint256, Uint256] := do
    let c ← getStorage counter
    require (x != 0) "zero"
    setStorage counter (add c x)
    return (c, add c x)

#check_contract G14Callee

verity_contract G14Caller where
  storage
    last : Uint256 := slot 0

  interfaces
    interface IPrep where
      function prepare(Uint256) returns (Uint256, Uint256)
    end

  linked_contracts
    callee : IPrep := G14Callee

  function reentrancy_trusted run (s : IPrep, x : Uint256) : Tuple [Uint256, Uint256] := do
    setStorage last x
    let (before, after) ← s.prepare x
    return (before, after)

#check_contract G14Caller

verity_contract G14Unbound where
  storage
    last : Uint256 := slot 0

  interfaces
    interface IPrepU where
      function prepare(Uint256) returns (Uint256, Uint256)
    end

  function reentrancy_trusted run (s : IPrepU, x : Uint256) : Tuple [Uint256, Uint256] := do
    setStorage last x
    let (before, after) ← s.prepare x
    return (before, after)

#check_contract G14Unbound

verity_contract G14Deferred where
  storage
    last : Uint256 := slot 0

  interfaces
    interface IPrepD where
      function prepare(Uint256) returns (Uint256, Uint256)
    end

  linked_contracts
    p : IPrepD := deferred

  function reentrancy_trusted run (s : IPrepD, x : Uint256) : Tuple [Uint256, Uint256] := do
    let (before, after) ← s.prepare x
    return (before, after)

#check_contract G14Deferred

/-- The bound mutable tuple call is a mutating hop running the callee body. -/
theorem run_is_hopCall (ctx : ExecutableCallContext) (s : Address) (x : Uint256) :
    G14Caller.run ctx s x = (do
      setStorage G14Caller.last x
      let r ← Contract.hopCall s (G14Callee.prepare x)
      match r with
      | (before, after) => Verity.pure (before, after)) := rfl

def callerAddr : Address := (50 : Address)
def calleeAddr : Address := (51 : Address)

/-- Caller at `callerAddr` (own slot 0 = 1); callee's namespaced `counter` = 7. -/
def g14State : ContractState :=
  ({ defaultState with thisAddress := callerAddr, sender := (1 : Address) }.writeSlot 0 1
    ).writeContractSlot calleeAddr.toNat 0 7

/-- The callee body runs: returns (7, 10) and writes 10 into the callee's own
namespaced `counter`; the caller's own slot 0 holds its pre-call write (3). -/
theorem run_bound_executes_callee :
    (G14Caller.run ExecutableCallContext.stub calleeAddr 3 g14State).getValue? = some ((7 : Uint256), (10 : Uint256)) ∧
    (G14Caller.run ExecutableCallContext.stub calleeAddr 3 g14State).getState.readContractSlot calleeAddr.toNat 0 = 10 ∧
    (G14Caller.run ExecutableCallContext.stub calleeAddr 3 g14State).getState.readSlot 0 = 3 := by
  decide

def revertMessage? {α : Type} : ContractResult α → Option String
  | .revert msg _ => some msg
  | .success _ _ => none

/-- A callee revert bubbles with its message, and the callee's namespaced
`counter` is restored (the hop snapshot is rolled back). -/
theorem run_bound_revert_bubbles :
    revertMessage? (G14Caller.run ExecutableCallContext.stub calleeAddr 0 g14State) = some "zero" ∧
    (G14Caller.run ExecutableCallContext.stub calleeAddr 0 g14State).getState.readContractSlot
      calleeAddr.toNat 0 = 7 := by
  decide

/-- The model plane lowers the mutable tuple call to the multi-word ABI `call`. -/
example :
    (G14Caller.spec.functions.any fun fn => fn.body.any fun
      | .ecm mod _ => mod.name == "externalCallWithReturns" && mod.resultVars == ["before", "after"] &&
          mod.writesState
      | _ => false) = true := by
  decide

/-- Unbound: the mutable ABI external call with arity 2 is answered by the
threaded context; the stub answers each word with `name.length + Σ args`
("IPrepU.prepare".length + 3 = 17). -/
theorem run_unbound_stub :
    (G14Unbound.run ExecutableCallContext.stub calleeAddr 3 g14State).getValue? =
      some ((17 : Uint256), (17 : Uint256)) := by
  decide

/-- Deferred binding: same mutable ABI path, answered by the threaded context
("IPrepD.prepare".length + 3 = 17). -/
theorem run_deferred_stub :
    (G14Deferred.run ExecutableCallContext.stub calleeAddr 3 g14State).getValue? =
      some ((17 : Uint256), (17 : Uint256)) := by
  decide

end Contracts.Smoke.HopContextAndMutableTuples

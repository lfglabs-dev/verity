import Init

/-!
Byte-exact external-call observation boundary. The adversary is an explicit
parameter; this module does not supply an implementation of an external
contract, opcode gas semantics, or an importer admission rule.

`World` must include every account and its logs. `Access` must identify the
account and slot. The caller supplies those types when connecting this boundary
to Denote. Failed calls cannot carry a committed world; their touched accesses
and arbitrary-length revert bytes remain observable.
-/
namespace Compiler.CompilationModel.ByteExternalCall

abbrev Bytes := List UInt8

inductive Kind where
  | call | staticcall | delegatecall
  deriving BEq, DecidableEq, Repr

structure Request where
  kind : Kind
  caller : Nat
  target : Nat
  value : Nat
  calldata : Bytes
  gas : Nat
  deriving Repr

/-- An exceptional child halt has an empty return buffer. A revert is distinct
and retains its exact byte payload, including leading and trailing zero bytes. -/
inductive Response (World Access : Type) where
  | success (world : World) (data : Bytes) (touched : List Access)
  | revert (data : Bytes) (touched : List Access)
  | exceptional (touched : List Access)

namespace Response

def succeeded : Response World Access → Bool
  | .success .. => true
  | .revert .. | .exceptional .. => false

def returndata : Response World Access → Bytes
  | .success _ data _ | .revert data _ => data
  | .exceptional _ => []

def accesses : Response World Access → List Access
  | .success _ _ touched | .revert _ touched | .exceptional touched => touched

def commit (before : World) : Response World Access → World
  | .success after _ _ => after
  | .revert .. | .exceptional .. => before

/-- A successful static call must already preserve the complete world. We do
not turn an adversarial state-changing success into a fictitious success by
silently discarding its writes or logs. -/
def valid (request : Request) (before : World) (response : Response World Access) : Prop :=
  match response with
  | .success after _ _ => request.kind = .staticcall → after = before
  | .revert .. | .exceptional .. => True

@[simp] theorem revert_commit (before : World) (data : Bytes) (touched : List Access) :
    (Response.revert data touched).commit before = before := rfl

@[simp] theorem exceptional_commit (before : World) (touched : List Access) :
    (Response.exceptional touched).commit before = before := rfl

@[simp] theorem revert_bytes (data : Bytes) (touched : List Access) :
    (Response.revert data touched : Response World Access).returndata = data := rfl

@[simp] theorem revert_accesses (data : Bytes) (touched : List Access) :
    (Response.revert data touched : Response World Access).accesses = touched := rfl

theorem valid_static_preserves_world (request : Request) (before : World)
    (response : Response World Access) (hkind : request.kind = .staticcall)
    (hvalid : response.valid request before) :
    response.commit before = before := by
  cases response with
  | success after data touched => exact hvalid hkind
  | revert data touched => rfl
  | exceptional touched => rfl

end Response

/-- Every request is passed to the adversary together with the full pre-world.
Validity is a proof obligation of the model, not a project axiom. -/
structure Adversary (World Access : Type) where
  /-- A partial configured program must reject unmodeled requests as
      instrumentation errors, rather than fabricate empty-code responses.
      Arbitrary complete adversaries retain the default total domain. -/
  accepts : Request → World → Bool := fun _ _ => true
  respond : Request → World → Response World Access
  valid : ∀ request before, (respond request before).valid request before

structure Observation (World Access : Type) where
  success : Bool
  world : World
  returndata : Bytes
  touched : List Access

def execute (adversary : Adversary World Access) (request : Request) (before : World) :
    Observation World Access :=
  let response := adversary.respond request before
  { success := response.succeeded
    world := response.commit before
    returndata := response.returndata
    touched := response.accesses }

/-- Instrumented execution of a possibly partial program. The total response
algebra above remains useful for generic frame proofs; EVM replay uses this
checked boundary so out-of-domain requests never become Solidity reverts. -/
def executeChecked (adversary : Adversary World Access) (request : Request) (before : World) :
    Except String (Observation World Access) := do
  unless adversary.accepts request before do throw "byte call request outside adversary domain"
  return execute adversary request before

theorem executeChecked_rejects (adversary : Adversary World Access)
    (request : Request) (before : World) (h : adversary.accepts request before = false) :
    executeChecked adversary request before =
      .error "byte call request outside adversary domain" := by
  simp [executeChecked, h] <;> rfl

theorem executeChecked_agrees (adversary : Adversary World Access)
    (request : Request) (before : World) (h : adversary.accepts request before = true) :
    executeChecked adversary request before = .ok (execute adversary request before) := by
  simp [executeChecked, h] <;> rfl

theorem execute_static_world (adversary : Adversary World Access)
    (request : Request) (before : World) (hkind : request.kind = .staticcall) :
    (execute adversary request before).world = before :=
  Response.valid_static_preserves_world request before _ hkind (adversary.valid request before)

/-- Outer rollback restores the entry world but retains the accesses made by
all child calls. Logs are part of `World`, so restoring it also cancels logs. -/
def rollbackOuter (entry : World) (observed : Observation World Access) (data : Bytes) :
    Observation World Access :=
  { observed with success := false, world := entry, returndata := data }

@[simp] theorem rollbackOuter_world (entry : World) (observed : Observation World Access)
    (data : Bytes) : (rollbackOuter entry observed data).world = entry := rfl

@[simp] theorem rollbackOuter_accesses (entry : World) (observed : Observation World Access)
    (data : Bytes) : (rollbackOuter entry observed data).touched = observed.touched := rfl

@[simp] theorem rollbackOuter_bytes (entry : World) (observed : Observation World Access)
    (data : Bytes) : (rollbackOuter entry observed data).returndata = data := rfl

end Compiler.CompilationModel.ByteExternalCall

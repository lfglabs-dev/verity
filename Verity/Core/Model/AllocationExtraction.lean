import Compiler.Proofs.Storage.SolidityStorage
import Compiler.Proofs.LoopSimulation
import Compiler.Proofs.IRGeneration.DenoteEquivalence
import Verity.Core.Model.DenoteExternalCalls

/-!
# Storage allocation extraction

This module extracts a small, typed storage-footprint summary from the actual
declarative compiler IR, `CompilationModel.FunctionSpec`.  Slot numbers cannot
be recovered from a `FunctionSpec` alone (its syntax names fields), so the
enclosing `CompilationModel` is an explicit argument.

Mapping and dynamic-array accesses are summarized by their canonical root
slot.  Key-dependent derived slots are intentionally left to a later refinement
of `constraint`.
-/

namespace Verity.Core.Model.AllocationExtraction

open Compiler.CompilationModel
open Compiler.Proofs.Storage

inductive AllocKind
  | read
  | write
  | readWrite
  deriving Repr, Inhabited, DecidableEq

structure AllocEntry where
  contract : ContractId
  slot : Nat
  kind : AllocKind
  constraint : Word → Prop

instance : Repr AllocEntry where
  reprPrec entry prec := reprPrec (entry.contract, entry.slot, entry.kind) prec

structure Allocation where
  slots : List AllocEntry
  returns : List ParamType

instance : Repr Allocation where
  reprPrec allocation prec := reprPrec (allocation.slots, allocation.returns) prec

/-- The empty committed footprint, retaining no ABI return values. -/
def emptyAllocation : Allocation := { slots := [], returns := [] }

/-- ABI returns as represented by the current typed function model. -/
def functionReturns (fn : FunctionSpec) : List ParamType :=
  if fn.returns.isEmpty then
    match fn.returnType with
    | some .uint256 => [.uint256]
    | some .address => [.address]
    | _ => []
  else fn.returns

/-- Storage-root read at one expression node. -/
def exprStorageRoot? : Expr → Option String
  | .storage field | .storageAddr field
  | .mapping field _ | .mappingWord field _ _ | .mappingPackedWord field _ _ _
  | .mapping2 field _ _ | .mapping2Word field _ _ _
  | .mappingUint field _ | .mappingChain field _
  | .structMember field _ _ | .structMember2 field _ _ _
  | .storageArrayLength field | .storageArrayElement field _
  | .adtTag _ field | .adtField _ _ _ _ field => some field
  | _ => none

partial def exprStorageReads (expr : Expr) : List String :=
  (exprStorageRoot? expr).toList ++ expr.children.flatMap exprStorageReads

/-- Transparent specialization for expressions whose children are leaves. -/
def shallowExprStorageReads? (expr : Expr) : Option (List String) :=
  if expr.children.all (fun child => child.children.isEmpty) then
    some ((exprStorageRoot? expr).toList ++
      expr.children.flatMap (fun child => (exprStorageRoot? child).toList))
  else none

def storageReads (expr : Expr) : List String :=
  (shallowExprStorageReads? expr).getD (exprStorageReads expr)

/-- Direct accesses performed by one statement, excluding child statement lists. -/
def directStorageAccesses (stmt : Stmt) : List (String × AllocKind) :=
  let metadata := stmt.directMetadata
  metadata.subexpressions.flatMap (fun expr =>
      (storageReads expr).map (fun field => (field, .read))) ++
    metadata.scopeEffects.storageWrites.map (fun field => (field, .write))

/-- Field names in source order. Reads from write operands precede the write,
matching evaluation order; nested branches and loops are traversed once. -/
def storageAccessesFromStmts (stmts : List Stmt) : List (String × AllocKind) :=
  Stmt.foldList (fun accesses stmt _ => accesses ++ directStorageAccesses stmt) [] stmts

/-- A transparent specialization for a single conditional with leaf branches.
It supports kernel reduction in worked examples while the general recursive
case remains the compiler model's canonical `Stmt.foldList`. -/
def shallowConditionalAccesses? : List Stmt → Option (List (String × AllocKind))
  | [stmt@(.ite _ thenBranch elseBranch)] =>
      if (thenBranch ++ elseBranch).all (fun child => child.childLists.isEmpty) then
        some (directStorageAccesses stmt ++
          thenBranch.flatMap directStorageAccesses ++
          elseBranch.flatMap directStorageAccesses)
      else none
  | _ => none

/-- Recognize any nesting of allocation-only loop wrappers as transparent
summary boundaries. Ordinary source loops are still traversed structurally by
`storageAccessesFromStmts`. -/
def storageAccessesBody : (stmts : List Stmt) → List (String × AllocKind)
  | [.forEach "__allocation_index" (.literal _) body] => storageAccessesBody body
  | body => (shallowConditionalAccesses? body).getD (storageAccessesFromStmts body)
termination_by stmts => sizeOf stmts
decreasing_by simp_wf; omega

def storageAccesses (fn : FunctionSpec) : List (String × AllocKind) :=
  storageAccessesBody fn.body

/-- Stable contract discriminator.  The declarative model currently has a
contract name rather than a numeric address, so allocation summaries use the
same neutral contract id as the single-contract source semantics. -/
def contractId (_spec : CompilationModel) : ContractId := 0

def resolveAccess (spec : CompilationModel) (access : String × AllocKind) : Option AllocEntry :=
  match findFieldWithResolvedSlot spec.fields access.1 with
  | none => none
  | some (_, slot) =>
      some ⟨contractId spec, slot, access.2, fun _ => True⟩

/-- Extract the canonical storage-root footprint of a typed function. -/
def extractAllocation (spec : CompilationModel) (fn : FunctionSpec) : Allocation :=
  { slots := (storageAccesses fn).filterMap (resolveAccess spec)
    returns := functionReturns fn }

/-- Allocation entries already contain resolved canonical slots; this
projection names that boundary explicitly for downstream proofs. -/
def canonicalSlot (_spec : CompilationModel) (_contract : ContractId) (slot : Nat) : Nat := slot

theorem extractAllocation_canonical
    (spec : CompilationModel) (fn : FunctionSpec)
    (_h : validateFunctionSpec fn = .ok ()) :
    ∀ entry ∈ (extractAllocation spec fn).slots,
      entry.slot = canonicalSlot spec entry.contract entry.slot := by
  intro entry _
  rfl

/-- Allocation visible after a call boundary: only successful calls commit. -/
def committedAllocation (result :
    Compiler.CompilationModel.DenoteExternalCalls.ExternalCallResult)
    (allocation : Allocation) : Allocation :=
  if result.succeeded then allocation else emptyAllocation

/-- A.1 rollback bridge: a reverted mutable call preserves the caller world
and exposes no committed allocation side effect. -/
theorem extractAllocation_revert
    (spec : CompilationModel) (fn : FunctionSpec)
    (adversary : Compiler.CompilationModel.DenoteExternalCalls.AdversaryModel)
    (site : Compiler.CompilationModel.DenoteExternalCalls.CallSite)
    (state : Compiler.CompilationModel.DenoteExternalCalls.CallState)
    (data : List Nat)
    (hkind : site.kind = .call ∨ site.kind = .delegatecall)
    (hresult : adversary.result site state.world = .revert data) :
    (Compiler.CompilationModel.DenoteExternalCalls.denoteCall adversary site state).state.world =
        state.world ∧
      committedAllocation (.revert data) (extractAllocation spec fn) = emptyAllocation := by
  constructor
  · exact Compiler.CompilationModel.DenoteExternalCalls.denoteCall_revert_world
      adversary site state data hkind hresult
  · rfl

/-- Put a function body under the source IR's bounded-loop constructor. -/
def wrapInLoop (fn : FunctionSpec) (n : Nat) : FunctionSpec :=
  { fn with body := [.forEach "__allocation_index" (.literal n) fn.body] }

/-- 1K-shaped footprint law: a bounded loop contributes its body footprint
once, independently of its runtime iteration count. -/
theorem extractAllocation_loop
    (spec : CompilationModel) (body : FunctionSpec) (n : Nat)
    (_h : validateFunctionSpec body = .ok ()) :
    extractAllocation spec (wrapInLoop body n) = extractAllocation spec body := by
  have hslots : storageAccesses (wrapInLoop body n) = storageAccesses body := by
    simp [storageAccesses, wrapInLoop, storageAccessesBody]
  have hreturns : functionReturns (wrapInLoop body n) = functionReturns body := by
    rfl
  unfold extractAllocation
  rw [hslots, hreturns]

/-! The source-side surface is deliberately a thin alias in A.3.  A later
phase can replace it with a Solidity AST while preserving the theorem name. -/

abbrev SolidityFunction := FunctionSpec

def compileSolidity (fn : SolidityFunction) : Option FunctionSpec := some fn

def extractAllocationFromSource (spec : CompilationModel)
    (fn : SolidityFunction) : Allocation := extractAllocation spec fn

/-- 1J-shaped bridge at the current typed-source boundary. -/
theorem extractAllocation_source_equiv
    (spec : CompilationModel) (fn : SolidityFunction) (ir : FunctionSpec)
    (hcompile : compileSolidity fn = some ir) :
    extractAllocation spec ir = extractAllocationFromSource spec fn := by
  simp [compileSolidity] at hcompile
  subst ir
  rfl

end Verity.Core.Model.AllocationExtraction

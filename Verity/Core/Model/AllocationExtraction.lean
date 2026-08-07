import Compiler.Proofs.Storage.SolidityStorage
import Compiler.Proofs.LoopSimulation
import Compiler.Proofs.IRGeneration.DenoteEquivalence
import Compiler.CompilationModel.ReservedScratchNames
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

def exprStorageReads (expr : Expr) : List String :=
  (exprStorageRoot? expr).toList ++ (expr.children.pmap (fun child hchild =>
    have := Expr.children_sizeOf_lt expr child hchild
    exprStorageReads child) (fun child hchild => hchild)).flatten
termination_by sizeOf expr

/-- Transparent specialization for expressions whose children are leaves. -/
def shallowExprStorageReads? (expr : Expr) : Option (List String) :=
  if expr.children.all (fun child => child.children.isEmpty) then
    some ((exprStorageRoot? expr).toList ++
      expr.children.flatMap (fun child => (exprStorageRoot? child).toList))
  else none

/-- The shallow specialization agrees with the canonical recursive traversal
whenever its leaf-child precondition holds. -/
theorem shallowExprStorageReads_eq_exprStorageReads
    (expr : Expr) (reads : List String)
    (h : shallowExprStorageReads? expr = some reads) :
    reads = exprStorageReads expr := by
  unfold shallowExprStorageReads? at h
  split at h
  · rename_i hleaves
    simp only [Option.some.injEq] at h
    subst reads
    rw [exprStorageReads]
    congr 1
    rw [List.pmap_eq_map]
    apply List.flatMap_congr
    intro child hchild
    have hempty : child.children = [] := by
      simpa using List.all_eq_true.mp hleaves child hchild
    rw [exprStorageReads]
    simp only [hempty, List.pmap, List.flatten_nil, List.append_nil]
  · contradiction

def storageReads (expr : Expr) : List String :=
  (shallowExprStorageReads? expr).getD (exprStorageReads expr)

/-- Direct accesses performed by one statement, excluding child statement lists. -/
def directStorageAccesses (stmt : Stmt) : List (String × AllocKind) :=
  let metadata := stmt.directMetadata
  metadata.subexpressions.flatMap (fun expr =>
      (storageReads expr).map (fun field => (field, .read))) ++
    metadata.scopeEffects.storageWrites.map (fun field => (field, .write))

/-- Accesses below one statement, in the same preorder as `Stmt.fold`. -/
def storageAccessesFromStmt (stmt : Stmt) : List (String × AllocKind) :=
  directStorageAccesses stmt ++ (stmt.childLists.pmap (fun childList hlist =>
    (childList.pmap (fun child hchild =>
      have := Stmt.childLists_sizeOf_lt stmt childList hlist child hchild
      storageAccessesFromStmt child) (fun child hchild => hchild)).flatten)
    (fun childList hlist => hlist)).flatten
termination_by sizeOf stmt
decreasing_by exact Nat.lt_trans this.1 this.2

/-- Field names in source order. Reads from write operands precede the write,
matching evaluation order; nested branches and loops are traversed once. -/
def storageAccessesFromStmts (stmts : List Stmt) : List (String × AllocKind) :=
  stmts.flatMap storageAccessesFromStmt

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

/-- The shallow conditional specialization agrees with the canonical
statement fold whenever its leaf-branch precondition holds. -/
theorem shallowConditionalAccesses?_eq_storageAccesses
    (stmts : List Stmt) (accesses : List (String × AllocKind))
    (h : shallowConditionalAccesses? stmts = some accesses) :
    accesses = storageAccessesFromStmts stmts := by
  cases stmts with
  | nil => simp [shallowConditionalAccesses?] at h
  | cons stmt tail =>
      cases tail with
      | cons next rest => simp [shallowConditionalAccesses?] at h
      | nil =>
          cases stmt <;> simp [shallowConditionalAccesses?] at h
          rename_i cond thenBranch elseBranch
          rcases h with ⟨hleaves, rfl⟩
          simp only [storageAccessesFromStmts, List.flatMap_cons, List.flatMap_nil]
          rw [storageAccessesFromStmt]
          simp only [Stmt.childLists]
          rw [List.pmap_eq_map]
          simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
            List.append_nil, List.pmap_eq_map]
          have hthen : ∀ child ∈ thenBranch, storageAccessesFromStmt child =
              directStorageAccesses child := by
            intro child hchild
            rw [storageAccessesFromStmt]
            simp only [hleaves.1 child hchild, List.pmap, List.flatten_nil,
              List.append_nil]
          have helse : ∀ child ∈ elseBranch, storageAccessesFromStmt child =
              directStorageAccesses child := by
            intro child hchild
            rw [storageAccessesFromStmt]
            simp only [hleaves.2 child hchild, List.pmap, List.flatten_nil,
              List.append_nil]
          rw [List.map_congr_left hthen, List.map_congr_left helse]
          rfl

/-- Recognize any nesting of allocation-only loop wrappers as transparent
summary boundaries. Ordinary source loops are still traversed structurally by
`storageAccessesFromStmts`. -/
def storageAccessesBody : (stmts : List Stmt) → List (String × AllocKind)
  | [.forEach index (.literal n) body] =>
      if index = allocationIndexScratch then storageAccessesBody body
      else (shallowConditionalAccesses? [.forEach index (.literal n) body]).getD
        (storageAccessesFromStmts [.forEach index (.literal n) body])
  | body => (shallowConditionalAccesses? body).getD (storageAccessesFromStmts body)
termination_by stmts => sizeOf stmts
decreasing_by simp_wf; omega

def storageAccesses (fn : FunctionSpec) : List (String × AllocKind) :=
  storageAccessesBody fn.body

/-- Stable, explicit contract discriminator. Existing model literals default
to identity `1`; multi-contract models set distinct identities. -/
def contractId (spec : CompilationModel) : ContractId := spec.contractId

def resolveAccess (spec : CompilationModel) (access : String × AllocKind) : Option AllocEntry :=
  match findFieldWithResolvedSlot spec.fields access.1 with
  | none => none
  | some (_, slot) =>
      some ⟨contractId spec, slot, access.2, fun _ => True⟩

/-- Extract the canonical storage-root footprint of a typed function. -/
def extractAllocation (spec : CompilationModel) (fn : FunctionSpec) : Allocation :=
  { slots := (storageAccesses fn).filterMap (resolveAccess spec)
    returns := functionReturns fn }

/-- Contract-sensitive canonical slot name. Contract id `0` deliberately keeps
the historical slot number; positive ids occupy exponentially separated names. -/
def canonicalSlot (_spec : CompilationModel) (contract : ContractId) (slot : Nat) : Nat :=
  if contract = 0 then slot else 2 ^ contract * (2 * slot + 1)

theorem extractAllocation_canonical
    (spec : CompilationModel) (fn : FunctionSpec)
    (_h : validateFunctionSpec fn = .ok ()) :
    ∀ entry ∈ (extractAllocation spec fn).slots,
      canonicalSlot spec entry.contract entry.slot =
        canonicalSlot spec (contractId spec) entry.slot := by
  intro entry hentry
  simp only [extractAllocation, List.mem_filterMap] at hentry
  obtain ⟨access, _, hresolve⟩ := hentry
  unfold resolveAccess at hresolve
  split at hresolve <;> simp_all
  cases hresolve
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
  { fn with body := [.forEach allocationIndexScratch (.literal n) fn.body] }

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

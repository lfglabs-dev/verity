import Lean
import Compiler.CompilationModel.InternalNaming
import Verity.Macro.Types

namespace Verity.Macro

open Lean
open Lean.Elab.Command

def localFunctionAppSyntax?
    (stx : Term) : Option (String × Array Term) :=
  let stx := stripParens stx
  match stx.raw with
  | .node _ `Lean.Parser.Term.app args =>
      match args.getD 0 Syntax.missing with
      | .ident _ raw _ _ =>
          let argTerms := (args.getD 1 Syntax.missing).getArgs.map (fun syn => ⟨syn⟩)
          some (raw.toString, argTerms)
      | _ => none
  | .ident _ raw _ _ =>
      some (raw.toString, #[])
  | _ => none

/-! ### Higher-order internal helper monomorphization (#1747)

    Verity's `CompilationModel` has no first-class function-pointer values: an
    internal helper cannot receive another helper as a runtime argument.  Rather
    than extend the model, IR and proof stack with a closure representation, we
    *eliminate* higher-order internal calls with a compile-time monomorphization
    pre-pass over the parsed `FunctionDecl` array, run before any model/IR
    lowering or elaboration.

    A *higher-order* (HO) helper has at least one function-pointer parameter
    (recorded as `ParamDecl.funcPtr?`).  For every call site that passes a
    statically-known internal-helper name in a function-pointer position, we
    synthesize a specialized first-order clone of the HO helper — with the
    function-pointer parameters removed and each occurrence replaced by the
    concrete helper — and rewrite the call site to target the clone.  The
    original HO helpers are dropped.  The result contains only first-order
    helpers, so 100% of the existing machinery applies unchanged, and there is
    zero overhead (the pre-pass is a no-op) when no helper is higher-order.

    Specialization runs to a fixpoint: a clone body may itself forward a
    function pointer to another HO helper, which requires a further clone.

    Restrictions (a clear error is raised otherwise):
      * a function-pointer argument must be a statically-known internal helper
        name (no dynamic dispatch, no qualified cross-contract names);
      * a function-pointer parameter may only be *called*, never otherwise used
        or shadowed within the helper body. -/

private def paramIsFuncPtr (p : ParamDecl) : Bool := p.funcPtr?.isSome

private def functionIsHigherOrder (fn : FunctionDecl) : Bool :=
  fn.params.any paramIsFuncPtr

/-- Indices of the function-pointer parameters of `fn`, in declaration order. -/
private def funcPtrParamIndices (fn : FunctionDecl) : Array Nat :=
  fn.params.zipIdx.filterMap (fun (p, i) => if paramIsFuncPtr p then some i else none)

/-- The printed name of `stx` when it is a bare (parenthesis-stripped)
    identifier — i.e. a candidate statically-known helper reference. -/
private def bareIdentName? (stx : Term) : Option String :=
  match (stripParens stx).raw with
  | .ident _ _ val _ => some val.toString
  | _ => none

private def monoSpecBaseName (hoName : String) (concretes : Array String) : String :=
  concretes.foldl (fun acc c => acc ++ "_" ++ c) (hoName ++ "_mono")

/-- Replace every identifier whose macro-scope-erased name is a key of `subst`
    with an identifier carrying the mapped name (preserving source position).
    Used to substitute a function-pointer parameter by its concrete helper. -/
private partial def substituteIdentNames (subst : Array (Name × Name)) (stx : Syntax) : Syntax :=
  match stx with
  | .ident _ _ val _ =>
      match subst.find? (fun (frm, _) => frm == val.eraseMacroScopes) with
      | some (_, repl) => (mkIdentFrom stx repl).raw
      | none => stx
  | .node info kind args => .node info kind (args.map (substituteIdentNames subst))
  | other => other

/-- Build a Verity-EDSL call term `head arg₀ … argₙ` (application by
    juxtaposition), matching the shape `localFunctionAppSyntax?` decodes. -/
private def mkLocalCallTerm (head : Ident) (args : Array Term) : Term :=
  if args.isEmpty then ⟨head.raw⟩
  else ⟨Syntax.node .none `Lean.Parser.Term.app
        #[head.raw, Lean.mkNullNode (args.map (·.raw))]⟩

private structure MonoState where
  /-- Assigned specialized name for each `(HO helper, concrete helper names)`
      key, so identical call sites share a single clone. -/
  assigned : Array ((String × Array String) × String) := #[]
  /-- All function names in use, to keep synthesized names fresh. -/
  usedNames : Array String := #[]
  /-- Specializations still to generate: `(specName, hoHelper, concreteNames)`. -/
  pending : Array (String × FunctionDecl × Array String) := #[]

private def monoSpecNameFor
    (ref : IO.Ref MonoState) (hoFn : FunctionDecl) (concretes : Array String) :
    CommandElabM String := do
  let st ← ref.get
  let key := (hoFn.name, concretes)
  match st.assigned.find? (fun (k, _) => k == key) with
  | some (_, nm) => pure nm
  | none =>
      let nm := Compiler.CompilationModel.pickFreshName
        (monoSpecBaseName hoFn.name concretes) st.usedNames.toList
      ref.set { st with
        assigned := st.assigned.push (key, nm)
        usedNames := st.usedNames.push nm
        pending := st.pending.push (nm, hoFn, concretes) }
      pure nm

/-- Rewrite every higher-order call in a syntax tree to its monomorphic
    specialization, enqueuing the specializations that must be generated.
    Bottom-up, so nested higher-order calls are specialized first. -/
private partial def monoRewriteCalls
    (hoHelpers : Array FunctionDecl) (allHelperNames : Array String)
    (ref : IO.Ref MonoState) (stx : Syntax) : CommandElabM Syntax := do
  match stx with
  | .node info kind args =>
      let args ← args.mapM (monoRewriteCalls hoHelpers allHelperNames ref)
      let node := Syntax.node info kind args
      match localFunctionAppSyntax? ⟨node⟩ with
      | none => pure node
      | some (fnName, argTerms) =>
          match hoHelpers.find? (fun fn => fn.name == fnName) with
          | none => pure node
          | some hoFn =>
              unless argTerms.size == hoFn.params.size do
                throwErrorAt stx s!"#1747: call to higher-order helper '{fnName}' expects {hoFn.params.size} argument(s), got {argTerms.size}"
              let fpIdxs := funcPtrParamIndices hoFn
              let mut concretes : Array String := #[]
              for i in fpIdxs do
                match argTerms[i]? with
                | none =>
                    throwErrorAt stx s!"#1747: internal error: missing argument {i} specializing '{fnName}'"
                | some arg =>
                    match bareIdentName? arg with
                    | none =>
                        throwErrorAt arg "#1747: a higher-order argument must be a statically-known internal helper name (no expressions, runtime values, or qualified cross-contract names)"
                    | some nm =>
                        unless allHelperNames.contains nm do
                          throwErrorAt arg s!"#1747: function-pointer argument '{nm}' is not a known internal helper in this contract"
                        concretes := concretes.push nm
              let specName ← monoSpecNameFor ref hoFn concretes
              let keptArgs := argTerms.zipIdx.filterMap (fun (a, i) =>
                if fpIdxs.contains i then none else some a)
              pure (mkLocalCallTerm (mkIdentFrom stx (Name.mkSimple specName)) keptArgs).raw
  | other => pure other

/-- Names of internal helpers (drawn from `allNames`) that `stx` calls. -/
private partial def collectCalleeNames (allNames : Array String) (stx : Syntax) : Array String :=
  match stx with
  | .node _ _ args =>
      let fromArgs := args.foldl (fun acc a => acc ++ collectCalleeNames allNames a) #[]
      match localFunctionAppSyntax? ⟨stx⟩ with
      | some (fnName, _) =>
          if allNames.contains fnName && !fromArgs.contains fnName then fromArgs.push fnName
          else fromArgs
      | none => fromArgs
  | _ => #[]

/-- A helper can be emitted once every internal helper it calls (other than
    itself) has already been emitted — executable emission requires
    callee-before-caller ordering with no forward references. -/
private def funcDeclEmittable
    (allNames : Array String) (emitted : Array String) (fn : FunctionDecl) : Bool :=
  (collectCalleeNames allNames fn.body.raw).all (fun d => d == fn.name || emitted.contains d)

/-- Remove the first emittable helper from `fns`, preserving the order of the
    rest (so the sort is stable). -/
private def pickEmittableFunction (allNames : Array String) (emitted : Array String) :
    List FunctionDecl → Option (FunctionDecl × List FunctionDecl)
  | [] => none
  | fn :: rest =>
      if funcDeclEmittable allNames emitted fn then some (fn, rest)
      else (pickEmittableFunction allNames emitted rest).map (fun (p, r) => (p, fn :: r))

private partial def topoEmitFunctions (allNames : Array String)
    (remaining : List FunctionDecl) (emitted : Array String)
    (output : Array FunctionDecl) : Array FunctionDecl :=
  match pickEmittableFunction allNames emitted remaining with
  | some (fn, rest) => topoEmitFunctions allNames rest (emitted.push fn.name) (output.push fn)
  | none => output ++ remaining.toArray

/-- Stable topological sort placing every internal helper after the helpers it
    calls.  Monomorphization can introduce a clone that depends on a first-order
    helper yet is itself called by a first-order helper, so neither "clones
    first" nor "clones last" yields a valid executable emission order; this sort
    does.  Genuine recursive cycles fall back to original order. -/
private def orderFunctionsByInternalCalls (fns : Array FunctionDecl) : Array FunctionDecl :=
  topoEmitFunctions (fns.map (·.name)) fns.toList #[] #[]

/-- Eliminate higher-order internal helpers by compile-time monomorphization
    (#1747).  Returns a first-order-only `FunctionDecl` array; a no-op when no
    helper is higher-order.  See the section comment above for the design. -/
def monomorphizeHigherOrderHelpers
    (functions : Array FunctionDecl) : CommandElabM (Array FunctionDecl) := do
  let hoHelpers := functions.filter functionIsHigherOrder
  if hoHelpers.isEmpty then
    return functions
  let allHelperNames := functions.map (·.name)
  let ref ← IO.mkRef ({ usedNames := allHelperNames : MonoState })
  -- 1. Rewrite every first-order body; higher-order originals are dropped.
  let mut firstOrder : Array FunctionDecl := #[]
  for fn in functions do
    if functionIsHigherOrder fn then
      continue
    let body ← monoRewriteCalls hoHelpers allHelperNames ref fn.body.raw
    firstOrder := firstOrder.push { fn with body := ⟨body⟩ }
  -- 2. Generate specializations to a fixpoint.
  let mut clones : Array FunctionDecl := #[]
  let mut idx := 0
  for _ in [0:100001] do
    match (← ref.get).pending[idx]? with
    | none => break
    | some (specName, hoFn, concretes) =>
        idx := idx + 1
        let fpIdxs := funcPtrParamIndices hoFn
        let subst : Array (Name × Name) := (fpIdxs.zip concretes).filterMap (fun (i, nm) =>
          match hoFn.params[i]? with
          | some p => some (p.ident.getId.eraseMacroScopes, Name.mkSimple nm)
          | none => none)
        let substituted := substituteIdentNames subst hoFn.body.raw
        let body ← monoRewriteCalls hoHelpers allHelperNames ref substituted
        let cloneParams := hoFn.params.zipIdx.filterMap (fun (p, i) =>
          if fpIdxs.contains i then none else some p)
        clones := clones.push { hoFn with
          ident := mkIdentFrom hoFn.ident (Name.mkSimple specName)
          name := specName
          params := cloneParams
          body := ⟨body⟩ }
  if idx < (← ref.get).pending.size then
    throwError "#1747: higher-order monomorphization exceeded the specialization budget; this usually indicates an unsupported unbounded recursive function-pointer pattern"
  -- A clone may depend on a first-order helper while being called by another
  -- first-order helper, so order the combined set by callee-before-caller.
  let result := orderFunctionsByInternalCalls (firstOrder ++ clones)
  if result.any functionIsHigherOrder then
    throwError "#1747 internal error: a higher-order helper survived monomorphization"
  return result

def internalHelperSpecName
    (functions : Array FunctionDecl)
    (fnName : String) : String :=
  Compiler.CompilationModel.pickFreshName
    (Compiler.CompilationModel.internalFunctionPrefix ++ fnName)
    (functions.map (·.name)).toList

private partial def hasDynamicInternalHelperType (ty : ValueType) : Bool :=
  match ty with
  | .string | .bytes | .array _ => true
  | .fixedArray elemTy _ => hasDynamicInternalHelperType elemTy
  | .tuple elemTys => elemTys.any hasDynamicInternalHelperType
  | .struct _ fields => fields.any (fun field => hasDynamicInternalHelperType field.snd)
  | _ => false

def supportsInternalHelperParamType (ty : ValueType) : Bool :=
  match ty with
  | .string | .bytes => true
  | .array _ => true
  | .struct _ _ => true
  | .tuple _ => true
  | _ => !hasDynamicInternalHelperType ty

def supportsInternalHelperSpec (fn : FunctionDecl) : Bool :=
  fn.name != "fallback" &&
    fn.name != "receive" &&
    fn.params.all (fun param => supportsInternalHelperParamType param.ty) &&
    !hasDynamicInternalHelperType fn.returnTy

def ensureSupportsInternalHelperSpec
    (stx : Syntax)
    (fn : FunctionDecl) : CommandElabM Unit := do
  unless supportsInternalHelperSpec fn do
    throwErrorAt stx
      s!"helper call '{fn.name}' uses a parameter or return type that direct macro helper lowering does not support yet; only static non-fallback/non-receive helpers can be lowered to internal specs"

def ensureCallableAsInternalHelper
    (stx : Syntax)
    (fn : FunctionDecl) : CommandElabM Unit := do
  -- Fail closed on internal calls to a function whose only reentrancy
  -- protection is its `nonreentrant(<lock>)` guard. The transient-storage
  -- guard is synthesised solely at the external dispatch boundary
  -- (`attachNonReentrantGuard`, #1893); the internal-helper shadow drops the
  -- lock, so routing a call through the shadow would execute the body without
  -- the lock and bypass reentrancy protection. `reentrancy_trusted` is the only
  -- sound exemption: it is an author assertion that the body is safe under every
  -- entry path, so it covers the lock-free internal path too. (Bugbot HIGH on
  -- PR #2032.) This is the call-site gate; the declaration-site rejection of
  -- `internal nonreentrant(<lock>)` lives in `validateFunctionDeclsPublic` (#1971).
  if fn.nonReentrantLock.isSome && !fn.reentrancyTrusted then
    throwErrorAt stx
      s!"helper call '{fn.name}': nonreentrant(<lock>) functions cannot be invoked as internal helpers; the synthesised transient-storage guard runs only at the external dispatch boundary, so an internal call would execute the body without the reentrancy lock. Expose '{fn.name}' only as an external entrypoint, or add `reentrancy_trusted` if its body is safe under every entry path."
  ensureSupportsInternalHelperSpec stx fn

end Verity.Macro

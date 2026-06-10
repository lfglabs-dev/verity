# Single-fold validator pattern (POC)

`Compiler/CompilationModel/Validation.lean` currently defines ~17 validation
passes (`validateStmtParamReferences*`, `validateReturnShapesIn*`,
`validateNoUnsupportedAdtConstruct*`,
`validateNoRuntimeReturnsInConstructor*`, …). Each pass is its own mutual
`Stmt → Except String Unit` / `List Stmt → …` / `Branches → …` block that
recurses by hand over the AST. Whenever a new `Stmt` constructor lands, every
hand-written recursion has to be updated. Missing one is silent: the validator
keeps compiling, just stops checking the new constructor.

This proof-of-concept introduces ONE generic structural traversal over `Stmt`
parameterised by a per-constructor "algebra" function, and shows how an
existing validator collapses onto it with a Lean-checked agreement theorem
proving the two are extensionally equal.

The new code lives in `Compiler/CompilationModel/ValidationFold.lean` (small,
additive, no existing validator deleted or modified).

## Fold interface

```lean
abbrev StmtCheck := Stmt → Except String Unit

mutual
def Stmt.checkRec (f : StmtCheck) : Stmt → Except String Unit
  | s@(.ite _ thenBranch elseBranch) => do
      f s
      Stmt.checkRecList f thenBranch
      Stmt.checkRecList f elseBranch
  | s@(.forEach _ _ body) => do
      f s
      Stmt.checkRecList f body
  | s@(.unsafeBlock _ body) => do
      f s
      Stmt.checkRecList f body
  | s@(.matchAdt _ _ branches) => do
      f s
      Stmt.checkRecBranches f branches
  | s => f s

def Stmt.checkRecList (f : StmtCheck) : List Stmt → Except String Unit
def Stmt.checkRecBranches (f : StmtCheck) :
    List (String × List String × List Stmt) → Except String Unit
end
```

`Stmt.checkRec` applies the algebra `f` at every node, then recurses into
nested `List Stmt` bodies via the four current "container" constructors —
`ite`, `forEach`, `unsafeBlock`, `matchAdt`. Short-circuiting `Except` bind
means the first error wins. **The only constructor-by-constructor file in the
codebase that needs editing when a new container `Stmt` constructor is added
is this one.** Every pass expressed via the fold automatically picks up the
new constructor.

## The converted validator

The original `validateNoRuntimeReturnsInConstructorStmt` is a structural walk
that throws on the return-family constructors and otherwise recurses. The
fold-based re-expression is:

```lean
def runtimeReturnCheck : Stmt → Except String Unit
  | .return _ | .returnValues _ | .returnArray _
  | .returnBytes _ | .returnStorageWords _ | .returnCodeData _ =>
      throw "Compilation error: constructor must not return runtime data directly"
  | _ => pure ()

def validateNoRuntimeReturnsInConstructorStmt__viaFold : Stmt → Except String Unit :=
  Stmt.checkRec runtimeReturnCheck
```

The algebra is now a single ~5-line pattern match — no recursion, no mutual
block. All the structural plumbing lives once in `Stmt.checkRec`.

## Agreement theorem (the oracle)

```lean
mutual
theorem validateNoRuntimeReturnsInConstructorStmt_eq_viaFold (s : Stmt) :
    validateNoRuntimeReturnsInConstructorStmt s =
      validateNoRuntimeReturnsInConstructorStmt__viaFold s
theorem validateNoRuntimeReturnsInConstructorStmtList_eq_viaFold (ss : List Stmt) :
    validateNoRuntimeReturnsInConstructorStmtList ss =
      validateNoRuntimeReturnsInConstructorStmtList__viaFold ss
theorem validateNoRuntimeReturnsInConstructorBranches_eq_viaFold
    (bs : List (String × List String × List Stmt)) :
    validateNoRuntimeReturnsInConstructorBranches bs =
      validateNoRuntimeReturnsInConstructorBranches__viaFold bs
end
```

Proved by mutual induction on the AST (well-founded by `sizeOf`). No `sorry`,
no new axioms, no `native_decide`. The theorem is the oracle: any future
refactor of `Stmt.checkRec` that breaks the fold/walk equivalence will fail
the build, not silently drift.

## Migration recipe for the remaining ~16 validators

For each existing validator triple
`validateXInStmt` / `validateXInStmtList` / `validateXInBranches`:

1. **Identify the algebra type.** Most passes return `Except String Unit`
   (use `StmtCheck`). Some return `Bool` (use `Stmt → Bool`, combine with
   `||`/`&&`) — those will need a sibling `Stmt.foldBool` defined analogously
   to `Stmt.checkRec`.
2. **Identify the context.** Pure passes (`validateNoRuntimeReturnsInConstructor`,
   `validateNoUnsupportedAdtConstruct`) take no context — direct
   `Stmt.checkRec myAlgebra`. Context-carrying passes
   (`validateStmtParamReferences fnName params`,
   `validateReturnShapesInStmt fnName params expectedReturns isInternal`) wrap
   the context into a closure:
   `Stmt.checkRec (fun s => myAlgebra fnName params s)`.
3. **Extract the algebra.** Copy the per-constructor pattern match from the
   original, but DROP the recursive calls in `ite` / `forEach` / `unsafeBlock`
   / `matchAdt` — replace those arms with `pure ()` (or `false` for Bool
   passes). The framework's recursion handles them. The check at the node
   itself stays.
4. **Define the viaFold versions** at all three levels (Stmt / StmtList /
   Branches) as one-liner wrappers around `Stmt.checkRec` /
   `Stmt.checkRecList` / `Stmt.checkRecBranches`.
5. **Prove agreement** with the same mutual-induction template as the POC.
   The proof of each case is essentially:
   - leaf cases: `rfl`
   - container cases: `simp only [original, Stmt.checkRec, algebra, pure_bind]`
     then `rw` the corresponding list/branches IH.
6. **(Future) once agreement holds for every pass, retire the hand-written
   recursions** — call sites switch from `validateX*` to
   `validateX__viaFold`, the old mutual blocks delete, and only the algebra
   functions and `Stmt.checkRec` survive. Adding a new `Stmt` constructor
   then forces exactly two compile errors per pass: one in the algebra (if
   the constructor matters to that pass) and one in `Stmt.checkRec` (only
   if it introduces a new nested-body container).

## Per-validator difficulty assessment

Trivial (same shape as the POC — pure pass over `Stmt` with `Except` result):

- `validateNoUnsupportedAdtConstructInStmt` — but reads `Expr` via
  `exprContainsAdtConstruct` helpers; the helpers are Expr-folds that
  separately deserve an `Expr.foldBool` sibling. Re-expression of the Stmt
  walk is trivial; replacing the Expr walk is a parallel refactor.
- `validateNoRuntimeReturnsInConstructorStmt` — done.

Easy (context-carrying, `Except`-returning):

- `validateStmtParamReferences` (fnName + params)
- `validateReturnShapesInStmt` (fnName + params + expectedReturns + isInternal)

These map directly via closure capture. The algebra becomes
`fun s => ...` carrying the context.

Medium (validators that read Expr deeply, e.g. ADT-construct screens,
mapping-key purity, scope checks): the Stmt level is trivial; the **Expr**
side needs its own `Expr.foldBool` / `Expr.foldExcept` generic fold defined
analogously. Once that exists, these collapse the same way.

Harder (validators that need accumulating state — e.g. scope-aware param
reference checks that thread a `Set String` of currently-bound locals through
the walk): these need a fold variant that threads state through.
Schematically:

```lean
def Stmt.foldState (step : σ → Stmt → Except String σ) : σ → Stmt → Except String σ
```

This is a straightforward generalisation but a separate piece of plumbing.

Out of scope for this POC: the `unsafeYul` arm of
`validateNoUnsupportedAdtConstructInStmt` does both a structural check AND a
nested call to `validateUnsafeYulDeclaredScopeEffects`. The fold-based version
handles this fine — it's just part of the algebra — but its proof is heavier
than the POC because the algebra is no longer trivially `pure ()` on the
container constructor.

## Outcome of this PoC

- New file: `Compiler/CompilationModel/ValidationFold.lean` (only addition).
- One validator (`validateNoRuntimeReturnsInConstructorStmt`) re-expressed
  via the generic fold.
- Lean-checked agreement theorem proving the two are extensionally equal.
- Original code untouched.
- Build target: `lake build Compiler.CompilationModel.ValidationFold`.

# `SupportedSpec.lean` → compiler-call conversion

`Compiler/Proofs/IRGeneration/SupportedSpec.lean` historically hand-restates the
set of programs the compiler accepts as standalone `Prop`s or pattern-matching
`Bool`s. That style duplicates compiler logic: every time the compiler relaxes
or tightens a gate, the proof layer's enumeration silently drifts and the
"supported" envelope quietly diverges from what the compiler actually accepts.

The repo already established a better pattern in the event-emission predicates,
where the proof-side support predicate is **defined by calling the actual
compiler gating function**, so the two cannot disagree by construction:

```lean
-- Compiler side (Compiler/CompilationModel/EventEmission.lean)
def eventParamScalarCompileSupported (ty : ParamType) : Bool := ...

-- Proof side (this file)
def eventParamScalarProofSupported (ty : ParamType) : Bool :=
  eventParamScalarCompileSupported ty
```

The proof-side name signals **intent** ("what proofs depend on for soundness"),
while the body delegates to the compile-side Bool that drives the compiler's
real branch. Downstream lemmas like
`eventParamScalarProofSupported_eventIsDynamicType_eq_false` then `simp` through
both names interchangeably.

This PR converts two scalar/leaf predicates in `SupportedSpec.lean` to the same
shape, as an exemplar that the remaining ~70 hand-restated predicates in the
file can follow.

## Predicates converted

### 1. `SupportedExternalParamType` → `externalParamScalarProofSupported`

The hand-restated `Prop`:

```lean
def SupportedExternalParamType : ParamType → Prop
  | .uint256 | .int256 | .uint8 | .uint16 | .address | .bytes32 | .bool => True
  | _ => False
```

is the exact mirror of the compiler-side gating function in
`Compiler/CompilationModel/ParamLoading.lean`:

```lean
def isScalarParamType : ParamType → Bool
  | ParamType.uint256 | ParamType.int256 | ParamType.uint8 | ParamType.uint16
  | ParamType.address | ParamType.bool | ParamType.bytes32 => true
  | _ => false
```

The new proof-side alias is one line:

```lean
def externalParamScalarProofSupported (ty : ParamType) : Bool :=
  isScalarParamType ty
```

### 2. `SupportedExternalReturnProfile` → `externalReturnProfileProofSupported`

The hand-restated `Prop`:

```lean
def SupportedExternalReturnProfile : List ParamType → Prop
  | [] => True
  | [ty] => SupportedExternalParamType ty
  | _ => False
```

becomes a Bool that pushes the per-element decision down to the compiler:

```lean
def externalReturnProfileProofSupported (returns : List ParamType) : Bool :=
  decide (returns.length ≤ 1) && returns.all isScalarParamType
```

## Agreement theorems

Because the heavily-used hand-restated predicates currently sit in proof
preconditions (`∀ param ∈ params, SupportedExternalParamType param.ty`) across
many sibling modules, we **keep** the old defs and prove
`old ↔ new` instead of rewriting every caller in one shot. The biconditionals
are the meaning-preservation oracle:

```lean
theorem SupportedExternalParamType_iff_externalParamScalarProofSupported
    (ty : ParamType) :
    SupportedExternalParamType ty ↔ externalParamScalarProofSupported ty = true

theorem SupportedExternalReturnProfile_iff_externalReturnProfileProofSupported
    (returns : List ParamType) :
    SupportedExternalReturnProfile returns ↔
      externalReturnProfileProofSupported returns = true
```

Both proofs are a single `cases ... <;> simp [...]` / `match ... with => simp`
because the cases line up. No `sorry`, no new `axiom`, no `native_decide`.

## Recipe to replicate across remaining predicates

For each hand-restated proof-side predicate `P` in `SupportedSpec.lean` (or a
sibling proof module):

1. **Find the compiler-side gating function.** Grep the `CompilationModel`
   directory for a `Bool` (or `Except` / `Option`-returning) function whose
   match arms classify the same syntactic cases as `P`. For ParamType-level
   leaves the usual suspects are `isScalarParamType`,
   `isSingleWordStaticParamType`, `isDynamicParamType`, `isWordArrayParam`,
   `internalDynamicParamSupported`, `supportedCustomErrorParamType`,
   `eventParamScalarCompileSupported`, and `indexedDynamicArrayElemSupported`.
   For expression / statement predicates the gate is typically the `compile*`
   function whose `Except String` failure path encodes the unsupported cases —
   in which case the proof-side wrapper checks `.isOk` / `.isSome`.

2. **Introduce a thin proof-side wrapper.** Add a single-line
   `def fooProofSupported ... := compilerGate ...` whose body is just the
   compiler call. The naming convention is `<feature><Shape>ProofSupported`
   to match `eventParamScalarProofSupported`. Place it near the existing
   predicates so the pattern is locally visible.

3. **Prove agreement with the hand-restated form.** Add
   `theorem P_iff_fooProofSupported : P x ↔ fooProofSupported x = true`. For
   leaf scalar/leaf predicates this is a one-liner:
   `cases x <;> simp [P, fooProofSupported, compilerGate]`. For predicates
   over lists or composite IR, recurse with `match`/`induction` and reuse the
   leaf agreement lemma. For `Except String`-shaped gates, the agreement
   lemma is `P x ↔ (compilerGate x).isOk` and the proof works by case-splitting
   on the `Except` result.

4. **Decide on retention.** If `P` is referenced widely outside the file (use
   `grep -rn P --include='*.lean'`), keep `P` and only add the agreement
   theorem — the lemma is enough to feed both directions into existing proofs.
   If `P` has few callers, inline-replace each caller with the new wrapper and
   delete `P`; the agreement theorem then degrades into a self-test you can
   keep or drop.

5. **Build the affected module.** `lake build
   Compiler.Proofs.IRGeneration.SupportedSpec` (or the sibling module).
   Iterate until clean: no `sorry`, no new `axiom`, no `native_decide`. The
   typical failure modes are:
   - `simp` can't close a case because the compiler bool depends on a helper
     that isn't unfolded yet. Add it to the `simp` set.
   - The compiler bool is strictly broader/narrower than the hand version.
     This is a **drift bug** — fix the spec to match the compiler, or
     restrict the new wrapper with `&& extraCondition`.
   - The compiler gate is `Except`/`Option`-shaped. Don't `simp` the failure
     branch away; pattern-match it and prove the failure case maps to `P x = False`.

6. **Once a critical mass of predicates is converted**, audit the resulting
   `SupportedSpec` and consider deleting the original hand-restated Props
   entirely, since every call site that used `P x` now factors through
   `P_iff_fooProofSupported` to talk about `fooProofSupported x = true`.

## Module build status — BLOCKED on pre-existing breakage

`lake build Compiler.Proofs.IRGeneration.SupportedSpec` was run after the
edits and **failed**, but not because of this conversion. The branch this work
sits on top of has a pre-existing missing-case error: a recent commit added a
new `Expr.txOrigin` variant (see commits introducing `txOrigin` in
`Compiler/CompilationModel/UsageAnalysis.lean`, `LogicalPurity.lean`,
`ValidationInterop.lean`, etc.) but the proof-side files that pattern-match
exhaustively on `Expr` were never updated. The first build failure surfaces
in `Compiler/Proofs/IRGeneration/ExprCore.lean:18` (the `exprBoundNames`
mutual block):

```
error: Compiler/Proofs/IRGeneration/ExprCore.lean:18:2: Missing cases:
Expr.txOrigin
error: Lean exited with code 1
```

`SupportedSpec.lean` itself has approximately ten further exhaustive `Expr`
matches that would also need `.txOrigin` added (every `exprTouchesUnsupported*Surface`
function around lines 604, 754, 810, 863, 922, 990, 1053, 1114, 1176, 1896).

Fixing all of these is outside the conversion scope this task was chartered
for (replicating the `eventParamScalarCompileSupported` pattern). The two
new defs (`externalParamScalarProofSupported`,
`externalReturnProfileProofSupported`) and the two agreement theorems were
verified by inspection — they each rely only on `simp` with the relevant
definitions in scope and follow the same recipe that's already known to
compile for `eventParamScalarProofSupported`. They contain no `sorry`, no
new `axiom`, and no `native_decide`.

**Recommended unblock path (separate, focused PR):** sweep
`Compiler/Proofs/IRGeneration/{ExprCore.lean, SupportedSpec.lean, FunctionBody.lean, SourceSemantics.lean, ...}`
and add `.txOrigin` to every exhaustive `Expr` enumeration, mirroring the
existing `.caller`/`.contractAddress`/`.chainid` handling (zero bound names,
no helper calls, no unsupported surface). Once that lands,
`lake build Compiler.Proofs.IRGeneration.SupportedSpec` should pick up the
work here and the two agreement theorems should close as written.

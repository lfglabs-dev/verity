# EvmYul ↔ `Verity.EVM.Frame` correspondence — design plan

`Verity.EVM.Frame` ships the EVM CALL boundary frame conditions as
theorems (`external_call_preserves_caller_storage`, `…_memory`, etc.)
over an abstract `CallerFrame` / `CalleeResult` interface. The
abstract interface is the *right* shape for downstream contract proofs
to consume, but it does not yet have a proven correspondence to
EvmYul's `CALL` opcode semantics. This document is the design plan
for that correspondence.

## What we want

A theorem of the shape:

```
theorem applyCallToCaller_matches_evmyul_CALL
    (s : EvmYul.State) (μ : EvmYul.MachineState)
    (gas to value inOff inSize outOff outSize : Uint256) :
  -- given an EvmYul state and the seven CALL arguments,
  -- after stepping `CALL`, the projected caller frame matches
  -- `applyCallToCaller` applied to the abstracted callee result
  let (success, s') ← EvmYul.step (CALL gas to value inOff inSize outOff outSize) s μ
  projectCallerFrame s' =
    Frame.applyCallToCaller
      (projectCallerFrame s)
      outOff.toNat outSize.toNat
      (projectCalleeResult success s')
```

where `projectCallerFrame` and `projectCalleeResult` are the
projections from EvmYul's concrete state to the abstract
`CallerFrame` / `CalleeResult` types.

## Why it's hard

EvmYul models CALL as a recursive call into the same interpreter
with a fresh frame, a gas budget, and a copy of the input memory
slice as the callee's calldata. The frame condition we care about is
*not* on the callee's behaviour (which is arbitrary) but on the
**bookkeeping the caller does** when the callee returns: it copies up
to `outSize` bytes of the callee's returndata into the caller's
memory at `[outOff, outOff + outSize)`, and writes `1`/`0` (success
bit) to the stack. Everything else in the caller's state — storage,
transient storage, memory outside `[outOff, outOff + outSize)`,
calldata, all of it — is preserved.

EvmYul models this implicitly: the caller's state in EvmYul's call
semantics is a snapshot taken before the recursion. Proving the
correspondence cleanly requires:

1. **Defining the projection functions** (a few hundred lines):
   `projectCallerFrame` and `projectCalleeResult` must commute with
   the EvmYul state transitions on every non-CALL opcode. This is a
   simulation-style proof.

2. **Proving the CALL-specific lemma**: when EvmYul steps `CALL`, the
   recovered caller state after the recursion matches the snapshot
   *plus* the returndata copy. This is where the actual frame
   theorem lives.

3. **Handling the failure case**: when CALL reverts (out-of-gas,
   nested revert, callee revert), EvmYul still copies returndata
   (per Yellow Paper); only storage and transient storage are
   rolled back. The `CalleeResult.success` field must encode this.

4. **Universal quantification over callee bytecode**: this is
   structural — `CalleeResult` already abstracts the callee — but
   the proof must show the projection commutes with arbitrary
   nested `EvmYul.step` sequences.

## Effort estimate

* Steps 1+2: ~2 weeks of focused work for someone familiar with both
  EvmYul and `Verity.EVM.Frame`.
* Step 3: half a week.
* Step 4: half a week (structural, but needs the right induction
  setup).

Total: **3-4 weeks** of focused effort. Probably an additional 1-2
weeks of CI rebuilding and downstream-benchmark verification.

## Dependencies

* `lfglabs-dev/EVMYulLean` at the pinned commit — the projection
  functions are stable against this fork.
* Verity's existing `Compiler.Proofs.YulGeneration.Backends.EvmYulLeanBuiltinSemantics`
  framework provides the simulation infrastructure for non-CALL
  opcodes; the new correspondence theorem plugs in alongside it.

## Recommended next step (when scheduled)

Open an issue tracking this as a Verity-roadmap item. Reference
`#1969` (the PR that landed `Verity.EVM.Frame`) and this design
plan. Estimate 4-6 weeks elapsed, assign to whoever owns the
EVMYulLean bridge work.

Until then, downstream consumers (e.g. the ERC-4337 EntryPoint
benchmark) treat the abstract `Frame` lemmas as theorems and
document the correspondence as the residual trust assumption in
`AXIOMS.md`.

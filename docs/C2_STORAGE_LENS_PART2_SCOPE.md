# C2 Storage Lens Part 2 Scope

## Current State

C1 and C2 part 1 are already landed, but this checkout has no committed
`storage_lens`, `StorageLens`, or "storage lens" symbols under `Compiler/`,
`Contracts/`, or `Compiler/Proofs/`. The C2 part 2 slice therefore needs a
small proof-facing entry point before it can safely refactor compiler or layout
surfaces.

## Smallest Landable Part 2 Unit

Pick one new lens type: `view_lens`.

This is the smallest useful unit because a view lens can be introduced as a
read-only projection over existing flat-storage and mapping-slot proof
surfaces, without changing compiler lowering or taking ownership of the
uncommitted transient layout work.

## Proposed Shape

The first implementation should live near the proof-facing storage model, most
likely under `Compiler/Proofs/StorageLens.lean`, imported only by a focused test
or proof file until the API is stable.

Minimal API:

```lean
structure ViewLens (α : Type) where
  read : (IRStorageSlot → IRStorageWord) → α
```

First concrete constructors:

- `ViewLens.word slot`: reads one resolved storage slot.
- `ViewLens.mappingWord baseSlot key`: reads through
  `solidityMappingSlot baseSlot key`.

The mapping constructor should reuse `Compiler.Proofs.MappingSlot` rather than
introducing a second slot-derivation model.

## First Proof/Test

Land one theorem proving that a write to a different flat slot preserves a
`ViewLens.word` read:

```lean
theorem ViewLens.word_read_store_other
    (storage : IRStorageSlot → IRStorageWord)
    (readSlot writeSlot value : Nat)
    (h : readSlot ≠ writeSlot) :
    (ViewLens.word readSlot).read
      (abstractStoreStorageOrMapping storage writeSlot value) =
    (ViewLens.word readSlot).read storage
```

This theorem is narrow, builds on `abstractStoreStorageOrMapping`, and gives C2
part 2 a concrete proof artifact before broadening to mapping/non-alias
certificates.

## Not In This Unit

- No compiler lowering changes.
- No layout report changes.
- No transient mapping semantics yet.
- No global storage-lens import into Layer 2 or native Layer 3 proofs.

## Follow-Up Slice

After `ViewLens.word` lands, add `ViewLens.mappingWord` preservation using the
finite non-alias certificate surface already present in
`Compiler/Proofs/MappingSlot.lean`.

# Modifiers, inheritance, and mixins

`verity_contract` supports precondition-only user-defined modifiers, flattened
inheritance (`is A` or `is A, B, C`), mixin include (import, not flatten),
direct parent/mixin constructor calls, and compile-time `virtual`/`override`
specialization.

## Modifiers

Modifiers are declared with `modifier name := do ...` and attached with
`with name`. Their statements are inserted, in declaration order, before the
function body in both executable semantics and the compilation model. The
current stage is intended for checks such as `onlyOwner`; Solidity-style `_`
placement and postcondition code are not supported.

## Flatten (`is`)

A child uses `verity_contract Child is Parent where` or
`verity_contract Child is A, B, C where`. Each parent must already be
elaborated (same module or imported `.olean`). Storage, declarations,
modifiers, and functions are **flattened** into the child: new `StorageSlot`
and function definitions are generated.

Multi-parent flattening is **left to right**: apply the existing single-parent
flatten for `A`, then `B` onto the result, then `C`. There is no C3
linearization. The same ancestor reached twice (a diamond) is a compile-time
error naming both paths.

A child constructor names each parent that has a constructor, in `is` order:
`constructor (...) A(args) B(args) C(args) := do ...`. Parent initialization
runs in that order, then the child body. Parents without a constructor are
omitted from the call list.

Mark a parent slot with `function virtual ...` and replace the same ABI
signature in the child with `function override ...`. Missing targets,
overrides of non-virtual functions, and accidental signature collisions are
compile-time errors. Dispatch is specialized during elaboration, so no runtime
dispatch table or additional proof axiom is introduced.

Sibling parents may not share a storage slot number, a non-overridable
function signature, or a modifier/role/error/event name. Collision errors
name both parents.

Because `is` re-elaborates a copied syntax tree, parent proofs do **not**
apply to the child. Use mixin `include` when you need proof reuse.

`is` and `include` cannot be combined. Cross-namespace inheritance is rejected.

## Mixin include (import, not flatten)

`verity_mixin Name where ...` is the reusable facet form. It emits the same
executable Lean definitions and `CompilationModel` as a contract, plus Lean
`def`s for modifiers and the constructor. Mixins cannot use `is`, `include`,
`receive`, or `fallback`.

A host writes `verity_contract Host include M1, M2 where ...`. Include
**imports** the mixin's existing Lean names (same `StorageSlot` values) and
merges CompilationModels. `with onlyOwner` binds the mixin's `onlyOwner`
definition; it does not copy the modifier body. Constructor inits
`M1(args) M2(args)` run the mixin `constructor` values in include order,
then the host body.

Name, role, modifier, function (including internal helpers), error, event,
constant, immutable, external, type, and slot clashes fail closed at
elaboration. Hidden executable slots used by mixin immutables are reserved.
`with` applies local and mixin modifiers in declared order. Mixin modifiers
validate against mixin errors/constants; mixin immutables are initialized in
the host constructor model.
Mixin slots are absolute as written (including mixin-owned ERC-7201 roots).
The host does not remap mixin slots. v1 has no `exclude` and no `override`
on the include path.

C3 linearization, abstract body-less functions, parameterized modifiers, and
modifier postludes remain out of scope. Multi-parent `is A, B, C` is
left-to-right flatten with diamond rejection; it is not Solidity MRO.

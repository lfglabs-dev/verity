# Modifiers and inheritance

`verity_contract` supports precondition-only user-defined modifiers, flattened
single inheritance, direct parent-constructor calls, and compile-time
`virtual`/`override` specialization.

Modifiers are declared with `modifier name := do ...` and attached with
`with name`. Their statements are inserted, in declaration order, before the
function body in both executable semantics and the compilation model. The
current stage is intended for checks such as `onlyOwner`; Solidity-style `_`
placement and postcondition code are not supported.

A child uses `verity_contract Child is Parent where`. The parent must be
declared earlier in the same module. Storage, declarations, modifiers, and
functions are flattened into the child. A child constructor calls its direct
parent with `constructor (...) Parent(args...) := do ...`; parent initialization
runs before the child body.

Mark a parent slot with `function virtual ...` and replace the same ABI
signature in the child with `function override ...`. Missing targets,
overrides of non-virtual functions, and accidental signature collisions are
compile-time errors. Dispatch is specialized during elaboration, so no runtime
dispatch table or additional proof axiom is introduced.

Multiple inheritance/C3 linearization, abstract body-less functions,
parameterized modifiers, and modifier postludes remain out of scope.

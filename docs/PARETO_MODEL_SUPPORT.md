# Pareto Credit Vault model support

This note tracks the four Verity language features needed to model the Pareto
Credit Vault (`IdleCDOCreditVault`, `IdleCDOEpochVariant`, `IdleCreditVault`)
as `verity_contract` sources that read one-to-one against the Solidity.

The inheritance chain in Solidity is

```
IdleCDOEpochVariant
  is IdleCDOCreditVault
    is PausableUpgradeable,
       GuardedLaunchUpgradable(Initializable, OwnableUpgradeable, ReentrancyGuardUpgradeable),
       IdleCDOStorage
```

and the strategy is

```
IdleCreditVault is Initializable, OwnableUpgradeable, ERC20Upgradeable, ReentrancyGuardUpgradeable
```

The vault calls the strategy about forty times, the strategy reads vault
getters about a dozen times, both call ERC20 tokens, and the vault wraps
three external self-calls in `try/catch`. Signed `int256` arithmetic appears
in the price waterfall and in withdraw-request adjustments.

## Feature 1: checked Int256 arithmetic and int256 storage

**Syntax.** `Int256` is already a word-like value type. New operations:

| Surface | Meaning |
|---------|---------|
| `Int256.safeAdd` / `safeSub` / `safeMul` / `safeDiv` / `safeNeg` / `safeMod` | `Option Int256`; `none` on the Solidity 0.8 failure boundary |
| `addPanic` / `subPanic` / `mulPanic` / `divPanic` | `Contract` wrappers, overloaded on `Uint256` and `Int256` |
| `negPanic` / `modPanic` | signed-only `Contract` wrappers |
| `slt` / `sgt` / `sle` / `sge` / `isNeg` | signed comparisons; lower to Yul `slt`/`sgt` |
| `Uint256.toInt256` / `Int256.toUint256` | bit-reinterpretation; **no range check** |

`ofNatChecked` / `toNatChecked` are omitted: Pareto's `uint256(int256(x))`
pattern is the bit-reinterpretation already provided by `toUint256`.

**Storage.** `storage last : Int256 := slot 0` now emits
`FieldType.int256` (one EVM word, layout-identical to `uint256`) so the
field round-trips through `Storage.lean`, layout reports, and
`#check_contract`. The executable slot remains a `Uint256` word; the DSL
and compilation model keep the signed tag.

**Compilation model.** Bound `let x ← addPanic a b` with `Int256`
operands lowers to wrapping `add`/`sub`/`mul` plus an `slt`-based overflow
guard, or to `sdiv`/`smod` with divide-by-zero and `minValue / -1` guards.
The panic codes match the unsigned wrappers: `Panic(0x11)` overflow,
`Panic(0x12)` division by zero.

**Proofs.** Option-level success/failure is definitional in
`Verity/Core/Int256.lean`. Wrapping ≡ unbounded `Int` on the success side
is in `Verity/Proofs/Stdlib/Int256.lean` (mathlib): two's-complement
residues modulo `2^256` are unique in range, so `add`/`sub`/`mul`/`neg`
agree with `Int` exactly when the mathematical result is in range.
`divPanic`/`modPanic` success is `Int.tdiv`/`Int.tmod` (towards-zero,
sign-of-dividend remainder). No `sorry`, no new axioms.

**Alternative considered.** Putting the `Contract` wrappers in
`Verity/Core/Int256.lean` would import the `Contract` monad into the core
numeric module (circular with `Verity.Core`). Option-level `*Panic` lives
in `Int256.lean`; `Contract` wrappers live next to the unsigned ones in
`Verity.Stdlib.Math` and dispatch through small typeclasses so the source
spelling stays `addPanic`. Heavy wrapping proofs live under
`Verity.Proofs.Stdlib` rather than Core so the numeric module stays
mathlib-free.

## Feature 2: modeled-callee calls

**Syntax.** Keep the existing `interfaces` block. Add a binding:

```
linked_contracts strategy : IStrategy := IdleCreditVault
```

The name may also match an interface-typed storage field or parameter.
The callee contract must already be declared. Duplicate binding names fail
closed.

**Public getters (G23).** If the interface method names a public storage
field of the callee (a Solidity `public` state variable's auto-generated
getter), the bound call lowers to a view hop reading that field:
`getStorage` / `getStorageAddr` / `getMapping` / `getMappingUint` /
`getMapping2`. A `Bool` return decodes the 0/1 storage word as `word != 0`.
Fields declared in a parent (`Callee is Parent`) resolve through the child's
flattened storage. Packed/transient fields are rejected.

**Deferred bindings (G15).** For cyclic pairs (the callee is declared after
the caller) write

```
linked_contracts cdo : IIdleCDO := deferred
```

Typed calls on a deferred binding keep the ABI external call, answered by the
threaded `ExecutableCallContext` (the enclosing function takes the context).
Proofs choose the responder: `ExecutableCallContext.stub` reproduces the
fixed stub word; `ctx.withViewLinks links` answers static sites
`links "IFace.method" target = some body` by running `body` (e.g.
`viewLinkWord Callee.method`) in `Contract.hopCallView`, with
`Contracts.externalStaticCallContractWordsTo_withViewLinks` as the fidelity
lemma. A contract literally named `deferred` must be bound by a qualified
name.

**One interface, several contracts (G25).** A named binding dispatches by
interface (and receiver name), not by the runtime target address. If one
interface is called on addresses holding different contracts, a named binding
would run the bound callee's body for all of them. Bind such interfaces as
`deferred` and answer them with `withViewLinks`, whose `links` function is
keyed by target address.

**Context forwarding (G26).** A bound call into a callee function that takes
the call context (it reaches a `deferred` link or opens a reentrancy window)
makes the caller, and helper chains calling it, take the context too, so a
view wrapper such as `let (a, b) ← _s.preview x` forwards the context the
proof instantiates instead of the fixed stub.

**Mutable tuple calls (G14).** `let (a, b) ← s.prepare x` on a
state-changing interface method is supported: bound calls run
`Contract.hopCall target (Callee.prepare x)` (reverts bubble), unbound or
deferred calls use the mutable ABI external call with arity = number of
results, and the compilation model emits `Calls.withReturnsModule`.

**Model plane.** A bound call is a CALL-shaped hop in
`Verity.MultiContract.MultiWorld` (`Verity/Core/Model/ModeledCall.lean`):
install `sender := caller.thisAddress`, `thisAddress := callee`,
`msgValue := 0`, empty returndata; run the callee body against the callee
account; success commits callee storage and journals the caller; revert
restores the pre-call world and bubbles. `view` hops run the body and
discard callee writes.

The `Contract` monad still carries one `ContractState`. Cross-contract
hops are a MultiWorld state transformer (`hop` / `hopContract`) **and** an
executable combinator (`Contract.hopCall` / `Contract.hopCallView`) that
namespaces every word-valued storage channel per contract: scalar slots
through `StorageKey.contractSlot`, and address / transient / mapping keys
through `StorageKey.scoped` (G24). `storageArray` (dynamic arrays) is still
global across hops. Generated bound
calls run the callee body; they do not go through the adversary-oracle
stub. Unbound interfaces keep the stub; deferred bindings use the threaded
call context. Same-contract `this.f(...)` uses
`Contract.selfCall` (new frame, sender replaced) so try/catch can wrap it.
That is distinct from DELEGATECALL `selfDelegateEntry`.

**Compilation model.** Bound calls still lower to the existing interface
ABI/ECM shape (`oracleSummary` / `externalCallWithReturn` /
`externalCallWithReturns`). The binding is
a model-level assumption that the address holds the named contract; no
bytecode claim (see `TRUST_ASSUMPTIONS.md`).

**Alternative considered.** Putting `MultiWorld` inside `ContractState`
(world field) or namespacing peer storage onto `StorageKey.contractSlot`.
Rejected as more invasive than a hop combinator over the existing
multi-contract world.

## Feature 3: real try/catch

**Syntax.**

```
tryCall (selfCall failHop) then
  (do setStorage last 1)
catch
  (do setStorage last 2)
```

`selfCall f(a, b)` passes arguments to the hop (Solidity `this.f(a, b)`);
`selfCall f` is the zero-argument form. A hop may make external calls: the
executable plane threads the call context into it. Argument count and types
are checked against `f`'s declaration.

`tryCatch attempt handler` remains the word-level stub (`tryCatchWord`
branches on `attempt == 0`) so existing low-level `call(...)` tests keep
working. Prefer `try`/`selfCall` for modeled hops.

**Model plane.** `Contract.tryWith` runs the attempt with `Contract.run`
snapshot rollback. On revert the failure continuation starts at that
snapshot. On success the success continuation runs from the hop's
post-state; a revert there is **not** caught. Failed-call returndata is
not bound into the handler (same compilation-model gap as `tryCatch`
payload names); read `ContractState.returndata` if needed.

**Compilation model.** `selfCall f` / `selfCall f(args)` lower to `Expr.call`
targeting `contractAddress` (CALL-with-status to this, empty calldata). The
`try` form is `let successBit := call(...); ite (successBit == 0) failure success`.
Selector/ABI encoding of `f` and of its arguments is a documented gap; the
status-bearing CALL plus conditional matches `docs/REVERT_STATE_MODEL.md`
bubbling (failure does not revert the outer frame).

**Alternative considered.** Replacing `tryCatch` in place would break
`LowLevelTryCatchSmoke`. Keeping the stub as an alias is simpler.

## Feature 4: multi-parent `is A, B, C`

**Syntax.** `verity_contract Child is A, B, C where`. Single-parent `is A`
is unchanged.

**Flatten.** Left-to-right: merge sibling parents with fail-closed
collisions, then reuse the existing single-parent flatten so the child can
`override` a virtual from any parent. No C3 linearization.

**Diamonds.** If the same ancestor is reached twice (`Child is Left, Right`
where both inherit `Base`), elaboration fails:
`diamond inheritance: ancestor 'Base' is reached twice (via 'Left' and 'Right')`.

**Collisions.** Duplicate storage slot numbers, function signatures,
modifiers, roles, errors, and events across sibling parents fail closed and
name both parents.

**Constructors.** The child names each parent that has a constructor, in
`is` order: `constructor (x) A() B(x) C() := do ...`.

**Alternative considered.** Solidity C3 MRO. Rejected: Pareto's chain is a
list of mixins plus a storage parent, not a diamond, and C3 would need a
new linearization proof story.

## Feature 5: executable hashed nested and struct mappings (G2, #2416)

**Problem.** `IdleCreditVault` keeps its receipts in
`mapping(address => mapping(uint256 => uint256))` and its APR-0 bucket in a
struct-valued mapping. The compilation model of those fields was right, but
the executable plane read `0` from every `getMappingN` and dropped every
`setMappingN`, so no executable-plane theorem about claims could be trusted.
A mixed key list (`[user, epoch]` with an `Address` and a `Uint256`) did not
even typecheck.

**Slot model.** `Contracts.getMappingN` / `setMappingN` /
`getMappingWord` / `setMappingWord` now read and write
`ContractState.storage` at the Solidity slot, sharing the proof model's
`Compiler.Proofs.abstractMappingSlot` (`keccak256(key ‖ slot)`):

| Solidity | Executable slot |
|----------|-----------------|
| `m[k]` at `p` | `keccak256(k ‖ p)` (`mappingChainSlot p [k]`) |
| `m[k₁][k₂]` at `p` | `keccak256(k₂ ‖ keccak256(k₁ ‖ p))` (`mappingChainSlot p [k₁, k₂]`) |
| `m[k].member` at `p`, word `w` | `(keccak256(k ‖ p) + w) mod 2²⁵⁶` (`structSlot p k w`) |
| `m[k₁][k₂].member` | `(keccak256(k₂ ‖ keccak256(k₁ ‖ p)) + w) mod 2²⁵⁶` (`structSlot2`) |

`mappingChainSlot_single` / `_pair`, `structSlot_eq_mappingSlotLocation` and
`structSlot2_eq_nestedMappingSlotLocation` are `rfl` against the compiler's
`MappingSlot` definitions, so the executable plane, the model plane
(`DenoteOracle.mappingSlot`) and the Yul lowering derive the same slot.

**Keys.** `getMappingN` / `setMappingN` take a `List MappingKeyWord`;
`Address`, `Uint256` and `Bytes32` coerce through `StorageKey.toWord`, so
`getMappingN withdrawsRequestsByEpoch [user, epoch]` typechecks.

**Transient chains.** A `transient` mapping chain routes to
`getTransientMappingN` / `setTransientMappingN` (EIP-1153 channel); the
macro inserts the rewrite, matching `readFieldWord` in the model plane.

**`structMembers`.** `let (a, b) := structMembers f k [m₁, m₂]` and
`return structMembers f k [..]` lower to one generated `structMember` read
per member in the executable plane. The pure expression form elsewhere is
still the `default` stub.

**Channels.** This hashed channel is disjoint from the constructor-keyed
`storageMap` / `storageMapUint` / `storageMap2` channels behind
`getMapping` / `getMappingUint` / `getMapping2`. A field is accessed through
exactly one family, chosen by its declared storage type, so no contract
observes both channels for one slot.

**Proofs.** `Contracts/Smoke/HashedMappings.lean` proves, through the
generated functions, that a nested-mapping write is read back at the same
keys, that a struct receipt destructures to the written words, that a
transient lock is read back and leaves persistent storage untouched, and
that the slots are the Solidity slots. Adjacent struct words are distinct
without keccak reasoning (`structSlot_ne_succ`); distinct keys rely on the
existing `solidityMappingSlot_injective` axiom. No new axioms.

**Alternative considered.** A new `StorageKey.hashed` constructor would keep
keys symbolic but breaks every exhaustive match on `StorageKey` (EVMYulLean
bridges, lens laws) and still needs a keccak-parity story for the compiler.
Reusing the `.slot` channel is what the generated struct-mapping accessors
already did; this feature extends it to chains and words.

## How to translate an OpenZeppelin-style contract chain

1. Declare each parent as its own `verity_contract` (storage-only parents
   with explicit slots, `Pausable`-like parents with modifiers, `Ownable`-like
   parents with an owner slot).
2. Flatten with `is A, B, C` in Solidity declaration order. Give each parent
   disjoint slots; Verity rejects overlapping slot numbers instead of packing
   them.
3. Bind cross-contract interfaces with `linked_contracts`; keep unbound
   `interfaces` for ERC-20 tokens whose bodies are not modeled.
4. Replace Solidity `try this.f(...) catch` with
   `tryCall (selfCall f) then (do ...) catch (do ...)`.
5. Use `addPanic` / `subPanic` / `Int256` storage for signed price math.

See `Contracts/Smoke/Arithmetic.lean` (`Int256CheckedSmoke`) for Feature 1,
`Contracts/Smoke/ModeledCall.lean` for Feature 2,
`Contracts/Smoke/TryCatch.lean` for Feature 3, and
`Contracts/Smoke/MultiParent.lean` (`ParetoChild`) for Feature 4.

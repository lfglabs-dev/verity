# Solidity import roadmap: from the Vault POC to the Pareto Credit Vault

**Status**: planning document. This file commits to a slice order, the files
each slice touches, the tests and acceptance evidence each slice must ship,
and what each slice explicitly leaves out. It contains no importer code.

**Goal**: a minimal proof-only Solidity import of `IdleCDOCreditVault`,
`IdleCDOEpochVariant` and `IdleCreditVault` from
[Idle-Labs/idle-tranches @ `54502d1`](https://github.com/Idle-Labs/idle-tranches/tree/54502d1)
together with their OpenZeppelin 4.9.6 upgradeable parents, built by
extending the existing proof-only importer under
[`Contracts/VaultFromSolidity`](../Contracts/VaultFromSolidity).

**Inputs**

- POC: [`Contracts/VaultFromSolidity`](../Contracts/VaultFromSolidity)
  (`Importer/Importer.lean`, `Importer/Syntax.lean`,
  `Importer/Semantics.lean`, `Spec.lean`, `Proofs/ExecutionProof.lean`,
  `Importer/scripts/solidity_importer_test.py`).
- Feature list: `audit/VERITY-GAPS.md` in
  `lfglabs-dev/pareto-credit-vault-proof-closure`
  (branch `assessment/source-faithful-accounting`, read-only), rows G1–G18.
- Existing `verity_contract` support for the same contracts:
  [`docs/PARETO_MODEL_SUPPORT.md`](PARETO_MODEL_SUPPORT.md),
  [`docs/MODIFIERS_AND_INHERITANCE.md`](MODIFIERS_AND_INHERITANCE.md),
  [`docs/EXTERNAL_CALL_MODULES.md`](EXTERNAL_CALL_MODULES.md).

**Slice order** (fixed): inheritance → modifiers/structs → external calls and
try/catch → signed integers → solc 0.8.10 → one Pareto smoke.

---

## 1. Hard rules for every slice

These apply to every PR on this roadmap, including the last one.

1. **No `sorry`, no `admit`, no `native_decide`, no new axioms.** The
   axiom audit in `solidity_importer_test.py` (every theorem in every
   importer proof file reports only `propext` and `Quot.sound`) is extended
   to each new smoke and stays a hard CI gate. External-call behaviour is a
   *parameter* of the imported definitions (Section 4.3), never an axiom.
   `AXIOMS.md` keeps "Active axioms: 1".
2. **The POC stays green.** `lake build VaultFromSolidity` and the full
   `solidity_importer_test.py` run must pass unchanged on every slice. The
   seven Vault theorems are the regression baseline for `solidity_simp`.
3. **The accepted subset stays closed and intrinsically typed.** New
   constructs are new constructors in `Syntax.lean` with one meaning in
   `Semantics.lean`. No generated Lean source, no serialized IR, no
   `unsafe`, no `partial` definitions in the semantics. Kernel checking stays
   synchronous (`Elab.async := false` inside the import transaction) with
   full environment rollback on failure.
4. **Fail closed with a source position.** Every rejection is a
   `path:line:col` diagnostic. The AST schema stays an allowlist
   (`allowedNodeFields` / `requiredNodeFields`); a new node kind is accepted
   only when its meaning is defined.
5. **The digest covers the whole trusted translation.** `sourceDigest`
   keeps hashing source bytes, solc output, `Importer.lean`, `Syntax.lean`,
   `Semantics.lean`, and the compiler pin. Any new trusted file (for example
   a version-indexed schema table) is added to the digest and to the
   "content change invalidates artifacts" mutation checks.
6. **Docs move with the boundary.** Each slice updates
   `TRUST_ASSUMPTIONS.md` (the "Proof-only Solidity Vault import" section),
   `AUDIT.md`, the `AXIOMS.md` audit paragraph, `README.md`'s importer
   section, `docs/VERIFICATION_STATUS.md`, `scripts/check_contract_structure.py`
   exemptions, and regenerates `PrintAxioms.lean` and
   `artifacts/verification_status.json` when theorem counts change.
7. **Git discipline.** One branch per slice from current `origin/main`, one
   PR per slice (S2 may be split as noted), never rebase or force-push a
   published branch, merge commits from `main` only. Proofs under 30 lines
   or allowlisted per `scripts/check_proof_length.py`.

---

## 2. Where we are: the POC

`solidity_contract Alias from "Vault.sol"` runs pinned solc 0.8.33
(`--standard-json --no-import-callback`, optimizer off, `evmVersion: cancun`),
validates the typed AST and storage layout against a closed schema, parses
each function body into the intrinsically typed inductive in `Syntax.lean`,
and registers each entry point as `Sol.Fn.meaning body slots env`. It also
elaborates a kernel-checked `Storage` structure, a `view : ContractState →
Storage`, and the entry-point relation `step`.

Accepted today:

| Area | Accepted | Rejected (diagnostic) |
|------|----------|-----------------------|
| Source unit | one pragma `^0.8.33`, exactly one non-abstract contract, no bases | imports, several contracts, `abstract`, `is` |
| Storage | `uint256` scalars, `mapping(address => uint256)`, offset 0, 32-byte slots | any other type, packed fields, initializers, constants, `layout at` |
| Declarations | zero-argument custom errors, public getters | events, modifiers, structs, enums, `using for`, constructors |
| Functions | external/public, nonpayable or view, ≤1 parameter (`uint256`/`address`), ≤1 unnamed `uint256` return, no modifiers, not virtual | everything else ("unsupported function surface") |
| Statements | `x = / += / -= e`, `uint256 x = e`, `if (a < b) revert E();`, terminal `return e` | loops, `unchecked`, `if/else`, calls, `emit`, `delete` |
| Expressions | locals, `msg.sender`, literals, state reads, mapping reads, checked `+`/`-` | `*`, `/`, comparisons outside guards, casts, calls, `address(this)` |

Trust story (`TRUST_ASSUMPTIONS.md`): solc's typed AST/storage layout and the
Lean translation are trusted; kernel checking establishes well-typed
definitions and theorems about their execution; storage keys are logical,
not keccak; `Contract.run` rolls back failed executions; no deployment,
calldata, gas, or bytecode claim. This roadmap keeps that story and only
widens the accepted fragment.

---

## 3. Where we are going: the Pareto sources

Inheritance chains at `54502d1`:

```
IdleCDOEpochVariant
  is IdleCDOCreditVault
    is PausableUpgradeable,                       (Initializable, ContextUpgradeable)
       GuardedLaunchUpgradable                    (Initializable, OwnableUpgradeable, ReentrancyGuardUpgradeable)
       IdleCDOStorage

IdleCreditVault
  is Initializable, OwnableUpgradeable, ERC20Upgradeable, ReentrancyGuardUpgradeable, IIdleCDOStrategy
```

`Initializable` and `ContextUpgradeable` are reached more than once in both
chains: these are real Solidity diamonds resolved by C3 linearization, so the
importer must accept them (unlike `verity_contract is`, which rejects diamonds;
gap G7).

Files the compiler must see (all vendored, pinned by hash, Section 9):

- idle-tranches: `IdleCDOCreditVault.sol`, `IdleCDOEpochVariant.sol`,
  `strategies/idle/IdleCreditVault.sol`, `GuardedLaunchUpgradable.sol`,
  `IdleCDOStorage.sol`, `IdleCDOTranche.sol`, and the interfaces
  `IIdleCDOStrategy`, `IERC20Detailed`, `IProgrammableBorrower`,
  `keyring/IKeyring`, plus `@uniswap/v2-periphery`'s `IUniswapV2Router02`
  (only as the type of an opaque storage field).
- OpenZeppelin contracts-upgradeable 4.9.6: `Initializable`,
  `ContextUpgradeable`, `OwnableUpgradeable`, `PausableUpgradeable`,
  `ReentrancyGuardUpgradeable`, `ERC20Upgradeable` (+ `IERC20Upgradeable`,
  `IERC20MetadataUpgradeable`), `SafeERC20Upgradeable` (+
  `AddressUpgradeable`, `IERC20PermitUpgradeable`).

Construct inventory (from the three target contracts, their idle-tranches
parents, and the OZ parents), with the slice that owns each construct and the
`VERITY-GAPS.md` row it relates to:

| Construct | Where it appears | Slice | Gap |
|-----------|------------------|-------|-----|
| `is A, B, C`, C3 linearization, diamonds, `abstract`, body-less `virtual` (`getContractValue`), `override`, `super._transfer` / `super._deposit` | all chains | S1 | G6, G7, G18 |
| internal function calls, internal helpers with several parameters, named return variables | everywhere (`_checkOnlyOwner`, `_virtualPriceAux`, …) | S1 | G13 |
| `uint256[N] __gap`, `address[]`, `bytes32`, `string`, interface-typed fields | OZ parents, `IdleCDOStorage`, `IdleCreditVault` | S1 (opaque fields) | G5, G17 |
| modifiers with prelude only (`onlyOwner`, `whenNotPaused`, `onlyInitializing`) and with postlude (`nonReentrant`, `initializer`) | OZ parents | S2 | G18 |
| `bool`, `uint8`, `address` scalars, packed sub-word fields (`_initialized`/`_initializing`, `isEpochRunning`/`allowAAWithdrawRequest`/…) | OZ, `IdleCDOStorage`, `IdleCDOEpochVariant` | S2 | G4 |
| structs in mappings (`Apr0UserData`), storage pointers to struct members, `delete`, nested mappings `mapping(address => mapping(uint256 => uint256))`, `mapping(uint256 => uint256)` | `IdleCreditVault` | S2 | G2 |
| constants (`FULL_ALLOC`, `YEAR = 365 days`, `10**18`, `type(uint256).max`), `require(cond, "…")`, `if/else`, ternary, `&&`, `\|\|`, `!`, all comparisons, checked `*`, `/`, `%`, `block.timestamp`, `address(this)`, `emit` | everywhere | S2 | G8, G9, G10 |
| typed interface calls on `IERC20Detailed(token)`, `IdleCreditVault(strategy)`, `IIdleCDOEpochVariant(idleCDO)`, `IKeyring`, `IProgrammableBorrower`; multi-value external returns | `IdleCDO*`, `IdleCreditVault` | S3 | G1, G5, G14, G15 |
| `using SafeERC20Upgradeable for …`: `safeTransfer`, `safeTransferFrom`, `safeIncreaseAllowance` | `IdleCDOCreditVault`, `GuardedLaunchUpgradable`, `IdleCreditVault` | S3 | — |
| `try this.f(x) { … } catch { … }` (three sites, all bare `catch`, all self-calls) | `IdleCDOEpochVariant.startEpoch`, `_stopEpoch`, `getInstantWithdrawFunds` | S3 | G3 |
| `int256` storage (`interestForOverUnderPerformance`), locals, tuple returns `(uint256, int256)`, `int256(x)`/`uint256(y)`, unary `-`, signed compare, signed checked arithmetic | `_virtualPriceAux`, `_updateAccounting`, `_calcInterestWithdrawRequest`, `IdleCreditVault` | S4 | G9 |
| `pragma solidity 0.8.10;`, `^0.8.0` / `^0.8.2` in OZ files, `import` directives, remappings, multi-file source units | all | S5 | — |
| `initialize` (`new IdleCDOTranche`, `string` concatenation, `abi.encodePacked`, `10**decimals()`), constructors, function-typed locals (`_getAARatio`), `tx.origin` | `IdleCDOCreditVault`, `IdleCreditVault` | out of scope: excluded entry points (S6) | — |

Two facts shape the design more than any other:

- **solc already flattens.** The `storageLayout` output for a most-derived
  contract lists every inherited variable with its final slot and offset, and
  `linearizedBaseContracts` gives the C3 order. The importer never computes
  an inheritance layout itself; this is why gap G7 (absolute slots that
  cannot serve two chains) does not exist on the import route.
- **The importer owns its AST.** Gaps G8–G10, G12, G13 and G16 are
  limitations of the `verity_contract` surface syntax. The imported term is
  built in `MetaM` from solc declaration ids; Lean identifiers, keyword
  clashes, and definition order are not constraints. Gaps that concern the
  *executable core* (G1, G2, G4, G14) do apply and are addressed in S2/S3.

---

## 4. Design decisions that span slices

### 4.1 Program shape: callee-first function table

`Syntax.lean` gains a function context in the same de Bruijn style as `Ctx`
and `Layout`:

- `Sig := (params : Ctx) × (rets : List Ty)`; `Fns := List Sig`.
- `FVar : Fns → Sig → Type` indexes an already-registered function.
- `Expr`/`Stmt` become `Expr L F Γ t` / `Stmt L F Γ r`; `Expr.call :
  FVar F σ → Args L F Γ σ.params → …`.

Each Solidity function (internal or external, from any contract in the
linearization) is registered as its own Lean constant in callee-first order.
`Fn.meaning body slots fns env` takes an `FnEnv F` term built from the
already-registered constants (the same pattern as `slotsTerm`). Consequences:

- Recursion (direct or mutual) is unrepresentable and is rejected by the
  parser with a diagnostic naming the cycle. The Pareto sources are expected
  to be recursion-free; S1's acceptance run on the vendored sources confirms
  it (a hit would be a scoped rejection of that function, not a design
  change).
- `#print Child.bump` shows the call to `Base._bump` by constant name, so the
  "parsed AST under its meaning" readability property of the POC is kept.
- Kernel terms stay per-function sized; nothing grows with the size of the
  whole contract except `step`.

### 4.2 Storage: solc layout is the only layout

Every entry in solc's `storageLayout.storage` is either an **imported field**
(type in the accepted set, gets a `<var>Slot` handle, a `Storage` member and,
if public, a getter) or an **opaque field** (any other type: `__gap` arrays,
`bytes32`, `string`, `address[]`, interface-typed fields). Opaque fields keep
their slot reserved, appear in an `opaqueFields` audit constant, and are not
in `Storage`; any body that reads or writes one is rejected at that
statement. This replaces the POC's "unaccounted layout field" rejection and
is the mechanism that lets each slice widen the type set independently.

Sub-word (packed) fields and struct members are read and written on the
word at their slot with shift/mask (S2). Nested mappings and struct members
inside mappings derive a **logical** inner base with a provably injective
`Nat` pairing offset by `2^256` so it can never equal a solc slot (S2).
This is consistent with the existing "logical keys, not keccak" trust
stance and needs no axiom.

### 4.3 External behaviour is a parameter, never an axiom

Imported definitions that perform external calls take an explicit
`world : Sol.CallModel` argument (S3). `CallModel` has a `call` field for
state-changing calls and a `staticCall` field that cannot write. Theorems
quantify over `world` and state their assumptions as hypotheses; the S6
smoke and later work may instantiate `world` with the imported strategy's
own meaning through `Verity.MultiContract` hops. `try this.f()` is
`Contract.selfCall` under `Contract.tryWith` and does not touch `world`.

### 4.4 Entry points and `step`

`step` stays the disjunction of every public/external function and public
getter, in a fixed order: the target contract's functions in source order,
then each base in linearization order, then getters in layout order. S6
adds an explicit entry-point allowlist for partial imports; the excluded
functions are recorded in a registered `unmodeledEntryPoints` constant that
the trust docs and the smoke's spec must cite.

### 4.5 Registered sources

`registeredSource : String` becomes a hard-coded manifest
`registeredSources : List (String × String)` (logical path, package-relative
path) in `Importer.lean`, still part of the digest, still checked for
canonical package containment. The lakefile tracks each smoke directory with
`input_dir` plus a `lean_lib` with `needs`, mirroring the `VaultFromSolidity`
target.

---

## 5. Slice S1: inheritance

**Goal**: import a most-derived contract whose bases live in the same source
unit, with solc's linearization, flattened layout, virtual dispatch, `super`,
abstract bases, internal function calls, and opaque storage fields.

### Files

- `Contracts/VaultFromSolidity/Importer/Syntax.lean`: `Sig`, `Fns`, `FVar`,
  `Args`; index `Expr`/`Stmt` by `F`; `Expr.call`, `Stmt.callStmt`;
  `Ret` generalized to `List Ty` (parser still accepts 0 or 1 until S3).
- `Contracts/VaultFromSolidity/Importer/Semantics.lean`: `FnEnv`,
  `Fn.meaning` with `fns`; call meaning in Solidity evaluation order
  (arguments left to right, then callee body under the caller's
  `msg.sender`/`msg.value`).
- `Contracts/VaultFromSolidity/Importer/Importer.lean`:
  - accept several `ContractDefinition`s; `solidity_contract A from "f.sol"
    contract "Name"` selects the target (defaults to the sole non-abstract
    contract);
  - accept `abstract`, `baseContracts`, `InheritanceSpecifier`,
    `linearizedBaseContracts` with more than one id, `contractDependencies`
    (must reference contracts in the unit), body-less `virtual` functions
    whose signature is implemented in the linearization (`fullyImplemented`
    of the target must be true), `override`/`overrides` metadata and
    `baseFunctions`;
  - virtual dispatch and `super` resolved by signature over the target's
    `linearizedBaseContracts` (most-derived first for calls; next-after-the
    -defining-contract for `super`), cross-checked against the AST's
    `referencedDeclaration`/`baseFunctions` and rejected on disagreement;
  - storage entries matched by `astId` to the declaring contract in the
    linearization instead of `logicalPath:contractName`; opaque fields;
  - callee-first registration order with cycle rejection; `<Contract>_`
    -prefixed Lean names for base functions to avoid collisions;
  - `step` order per Section 4.4;
  - `registeredSources` manifest.
- `Contracts/SolidityImportSmoke/Inheritance/{Inheritance.sol,
  Inheritance.lean, Spec.lean, Proofs.lean}`: synthetic `Storage`-like base,
  `Pausable`-like base with `internal virtual _pause`, `Ownable`-like base,
  child overriding `_pause` and calling `super._pause()`, one diamond
  (`Base` reached twice). Only POC types plus `address` scalars.
- `Contracts/SolidityImportSmoke/Inheritance/scripts/inheritance_test.py`
  (same disposable-package pattern as `solidity_importer_test.py`).
- `lakefile.lean`, `scripts/check_contract_structure.py`, docs per rule 6.

### Tests

- Acceptance suite runs the full POC suite unchanged, then:
  - builds the synthetic smoke; probes slot numbers of inherited fields
    against solc's layout (`[base slots…, child slots…]`);
  - `#print Child.go` shows `Expr.call` to `Child__pause` and
    `#print Child__pause` shows the `super` hop to `PausableLike__pause`;
  - mutation: swapping the `is` order changes the linearization and the slot
    probe; changing the override body breaks the dispatch theorem; adding a
    public function to a base adds a `step` disjunct and breaks the
    invariant theorem; importer/syntax/semantics content edits move the
    digest;
  - rejections with positions: direct and mutual recursion, unimplemented
    virtual in a non-abstract target, a body touching an opaque field,
    `is` referencing a contract from another file (until S5), function
    overloading by parameter type (same name, different signature: rejected
    in v1 to keep name resolution simple).
- Proofs (no `sorry`): `dispatch_is_child` (an entry point in the base that
  calls the virtual observes the child's override), `super_runs_parent`,
  `paused_invariant : PreservedBy … step`, and one `*_meets_spec` per entry
  point.

### Acceptance

- `lake build VaultFromSolidity SolidityImportSmokeInheritance` green; both
  python suites pass; axiom audit reports only `propext`, `Quot.sound` for
  every theorem in both proof files.
- Dry run on the vendored Pareto sources is **not** required here (they
  need S2–S5), but the slice records in its PR the list of Pareto functions
  that are recursion-free (expected: all).

### Non-goals

Modifiers, events, constructors, initializers, multi-file units, packed or
non-word storage, external calls, `this.`, overloading, function-typed
values, libraries, `using for`.

---

## 6. Slice S2: modifiers, structs, and the declaration surface

**Goal**: the declaration and statement surface that OpenZeppelin parents
and the Pareto bodies use, without external calls or signed integers. May
land as three PRs in this order: S2a modifiers and events, S2b storage
shapes, S2c statements and expressions. One roadmap slice, one acceptance
suite.

### Design

- **Modifiers** are inlined at parse time; `Semantics.lean` never sees `_`.
  A function with modifiers `m1 m2` and body `B` is parsed as
  `m1-pre; (m2-pre; let r ← block B; m2-post); m1-post; return r`. A
  `block` is a new `Stmt` form whose `return` exits the block only, so
  `nonReentrant`'s postlude runs after an early `return` exactly as in
  Solidity, and a `revert` anywhere still aborts the whole call. Modifier
  bodies may call internal functions (S1 machinery); a modifier with more
  than one `_`, or with arguments (`reinitializer(uint8)`), is rejected.
- **Events** parse to `Stmt.emit name args` whose meaning is
  `Verity.emitEvent`; events are part of the state and available to specs
  but no slice proves anything about them.
- **Storage shapes**: `bool`, `uint8`, `address`, `int256` (tag only; S4
  gives it arithmetic) scalars at any `offset` with `numberOfBytes` 1/20/32,
  read as shift-and-mask on the word and written by masked merge;
  `mapping(uint256 => uint256)`, `mapping(address => mapping(uint256 =>
  uint256))`, `mapping(address => Struct)` with word-sized members, storage
  pointer locals `S storage p = m[k]`, member read/write, `delete m[k]`
  (writes every member to zero). Logical inner bases per Section 4.2.
  `Storage` exposes `apr0Users : Address → Apr0UserData` as a Lean structure.
- **Constants** (`constant` state variables with literal or
  literal-arithmetic initializers, `365 days`, `10**18`, `type(uint256).max`)
  are evaluated at import time to `Nat` literals; the evaluator is part of
  the digest and rejects non-literal initializers.
- **Statements/expressions**: `if/else`, nested blocks, `bool` locals,
  ternary, `&&`/`||` with short circuit (both operands are pure in the
  accepted subset, so evaluation order is not observable; the parser rejects
  operands with calls until S3 decides), `!`, `==`/`!=`/`<`/`<=`/`>`/`>=` on
  `uint256`, `address`, `bool`; checked `*`, `/`, `%` (`Panic(0x11)`,
  `Panic(0x12)`) via `Verity.Stdlib.Math`; `require(cond, "…")` with the
  string kept verbatim; `revert E(args)` with word-sized arguments;
  `block.timestamp`, `address(this)`; assignment to locals and named return
  variables; `return;` in unit functions.

### Files

- `Syntax.lean`, `Semantics.lean`, `Importer.lean` as above; new allowed
  node kinds: `ModifierDefinition`, `ModifierInvocation`,
  `PlaceholderStatement`, `EventDefinition`, `EmitStatement`,
  `StructDefinition`, `UserDefinedTypeName`, `UnaryOperation`,
  `Conditional`, `TupleExpression` (parenthesized only), `MemberAccess` on
  structs, `ElementaryTypeNameExpression` (for `type(uint256).max`), `Literal`
  with `subdenomination`.
- `Verity/Core.lean` or `Verity/Core/Semantics.lean`: word-level packed
  read/write helpers and their `solidity_simp` lemmas if not already
  exported (`compiledPackedRead` exists on the compiler side; the executable
  core needs the same two functions with proofs `packed_read_write`,
  `packed_write_other_field`). No `ContractState` field is added.
- `Verity/Proofs/Stdlib/SolidityImport.lean`: `solidity_simp` extended with
  the new primitives and the pairing lemmas.
- `Contracts/SolidityImportSmoke/Modifiers/…` (OZ-shaped `Ownable`,
  `Pausable`, `ReentrancyGuard`, `Initializable` re-typed in one file with
  `pragma ^0.8.33`, plus a child using `nonReentrant` with an early return),
  `Contracts/SolidityImportSmoke/Storage/…` (packed bools at the same slot,
  a struct mapping, a nested mapping, `delete`), each with `Spec.lean`,
  `Proofs.lean`, and a python acceptance script.

### Tests

- Modifier order mutation (swap `nonReentrant whenNotPaused`) breaks a
  theorem that pins the revert reason order; dropping a postlude breaks
  `status_restored`; a `return` before `_` in the synthetic body still
  restores `_status` (theorem, not just a test).
- Packed layout: solc's `offset`/`numberOfBytes` drive the mask; mutation
  reordering two bools in one slot changes the probe and keeps proofs
  passing (names bind to solc offsets, as slots do today).
- Struct/nested mapping: `set_then_get` and frame theorems
  (`other_key_unchanged`, `other_member_unchanged`) proved from the pairing
  injectivity lemma; `#print axioms` on that lemma shows none.
- Rejections: modifier with two `_`, modifier arguments, struct with a
  dynamic member, `mapping` with struct key, `unchecked`, loops,
  inline assembly, `string` locals, arrays, `delete` on a scalar of opaque
  type, `require` without a message is *accepted* (empty reason).

### Acceptance

- All prior suites green; new smokes build; axiom audit clean.
- Dry run: the importer applied to the vendored OZ parents alone (with the
  OZ pragmas rewritten to `^0.8.33` in the smoke copy) accepts
  `OwnableUpgradeable`, `PausableUpgradeable`, `ReentrancyGuardUpgradeable`,
  `Initializable` bodies except those that call `AddressUpgradeable`
  (`initializer`'s `isContract` check, which lands in S3 as a static call
  primitive) and `_msgData` (`bytes calldata`, out of scope; never called by
  the Pareto sources).

### Non-goals

External calls, libraries, `try`, signed arithmetic, dynamic arrays,
strings and `bytes`, `enum`, parameterized modifiers, `unchecked`, loops,
events in specs, gas.

---

## 7. Slice S3: external calls and try/catch

**Goal**: typed interface calls, the three OpenZeppelin SafeERC20 helpers
the Pareto sources use, multi-value returns, and `try this.f(args) {…}
catch {…}`, with callee behaviour as an explicit model parameter.

### Design

- `Sol.CallModel` in `Semantics.lean`:
  `call : Address → Selector → List Uint256 → Contract (List Uint256)` and
  `staticCall : Address → Selector → List Uint256 → ContractState →
  Except String (List Uint256)`. Selectors are computed from the interface
  signature with the existing kernel-computable keccak engine (already used
  for `functionSelector` checks elsewhere in the repo), so a `CallModel`
  instantiation can be keyed by real ABI selectors later.
- Interface calls: `I(expr).f(args)` where `I` is an `interface` (or a
  contract used as an interface, as in `IdleCreditVault(strategy)`) parse to
  `Expr.extCall`/`Stmt.extCallStmt` with the target address expression,
  selector, word-typed arguments, and word-typed returns (0..n). `view`
  interface methods route to `staticCall`; a `view` importing function may
  only contain static calls (checked from `stateMutability`).
- Library helpers: `using SafeERC20Upgradeable for …` plus
  `token.safeTransfer(to, v)`, `safeTransferFrom(from, to, v)`,
  `safeIncreaseAllowance(spender, v)` parse to `Expr.libCall` over a closed
  `LibFn` enumeration. Their meaning is written directly in `Semantics.lean`
  as the ERC-20 call through `world.call` plus the OZ optional-return check
  (`_callOptionalReturn`: revert unless returndata is empty or decodes to
  `true`); `safeIncreaseAllowance` is `allowance` static read, checked add,
  `approve`. The library bodies themselves (assembly, `abi.encodeWithSelector`)
  are never imported; this is a documented trusted translation of three
  functions, pinned to the OZ 4.9.6 source hash.
- `try this.f(args) { S } catch { C }`: `f` must be an external function of
  the same contract; meaning is `Contract.tryWith (Contract.selfCall (f args
  with sender := address(this), value := 0)) (fun _ => S) C`. Only bare
  `catch` is accepted (all three Pareto sites are bare). Returndata is not
  bound.
- Multi-value returns: `(uint256 a, uint256 b) = e;` and
  `(a, b) = e;` for internal and external calls; named return variables of
  any arity.
- `address(this)` compares and `msg.sender != address(this)` guards are S2
  expressions; `IERC20Detailed(_token).balanceOf(address(this))` is the
  canonical static-call test.

### Files

- `Syntax.lean`, `Semantics.lean` (`CallModel`, `extCall`, `libCall`,
  `tryCatch`, tuple binding), `Importer.lean` (new nodes:
  `TryStatement`, `TryCatchClause`, `FunctionCall` with `tryCall = true`,
  `UsingForDirective`, `InterfaceDefinition` / `contractKind = interface`,
  `FunctionCall` of kind `typeConversion` for `I(addr)` and `address(x)`,
  `MemberAccess` on interface-typed expressions, `Identifier` `this`).
- `Verity/Core.lean`: lemmas `tryWith_success`, `tryWith_revert_rollback`,
  `selfCall_sender` if missing; added to `solidity_simp`.
- `Contracts/SolidityImportSmoke/Calls/…`: an interface, a token param,
  `safeTransfer`, a static read, a self-call `try` with a success path and a
  revert path (`sendFunds` reverts when `amount > balance`), a two-value
  external return.

### Tests

- Theorems: `catch_iff_selfcall_reverts`, `catch_state_is_snapshot`
  (post-state of the catch branch equals the pre-`try` state plus the
  handler's writes), `success_path_writes`, `static_call_does_not_write`,
  `safeTransfer_reverts_on_false` (for any `world` returning `false`),
  all universally quantified over `world`.
- Mutations: remove the handler write; make `sendFunds` revert
  unconditionally; swap argument order in an interface call (selector and
  argument list change, theorem breaks); change the OZ helper hash pin
  (import fails).
- Rejections: `try` on a non-self target, `catch Error(string)`,
  `catch Panic`, `.call{value: …}`, `delegatecall`, `payable`, library
  functions outside the closed set, interface methods with dynamic
  arguments or returns (`bytes`, `string`, arrays), `new`.

### Acceptance

- All suites green; axiom audit clean (`CallModel` is a binder, so
  `#print axioms` is unchanged by design).
- Dry run on the vendored `GuardedLaunchUpgradable` and `IdleCDOStorage`
  (pragmas rewritten) accepts every function except `_deployTranche`-style
  code, and the S2 leftover `initializer` now accepts `isContract` as a
  static primitive (`extcodesize` modelled as a `staticCall` on a reserved
  selector in `CallModel`).

### Non-goals

Modeled callees inside the importer (instantiating `world` with another
imported contract is proof-side work after S6), ETH value, reentrancy
adversary registries, returndata in `catch`, dynamic ABI, events in specs.

---

## 8. Slice S4: signed integers

**Goal**: `int256` as a first-class accepted type with Solidity 0.8 checked
semantics, enough for `_virtualPriceAux`, `_updateAccounting` and
`_calcInterestWithdrawRequest`.

### Design

- `Ty.int` denotes `Verity.Core.Int256`. Storage scalars (`FieldType.int256`
  already exists in the layout reports), locals, parameters, single and
  tuple returns.
- Literals: non-negative literals typed `int256` by solc; unary minus on
  any `int256` expression is checked negation (`Panic(0x11)` on `minValue`).
- Conversions `int256(u)` / `uint256(i)` are bit reinterpretation
  (`Int256.ofUint256` / `toUint256`, no range check) exactly as Solidity
  0.8 defines explicit conversion between same-width signed/unsigned types.
- Checked `+ - * /` and `%` via `Int256.safeAdd/safeSub/safeMul/safeDiv/
  safeMod` (`Panic(0x11)` overflow, `Panic(0x12)` division by zero; `minValue
  / -1` is `Panic(0x11)`); `-=`/`+=`/`*=`/`/=` on `int256` lvalues;
  comparisons via `slt/sgt/sle/sge`; ternary on `int256`.
- `solidity_simp` gains the `Verity/Proofs/Stdlib/Int256.lean` bridge
  lemmas (wrapping equals unbounded `Int` on success). PR #2414 removes
  `native_decide` from the sign-bit lemmas; S4 depends on it being merged
  and its acceptance suite re-checks that every lemma it uses reports no
  `Lean.ofReduceBool`.

### Files

- `Syntax.lean`, `Semantics.lean`, `Importer.lean` (type strings
  `int256`, `t_int256`, `t_rational_*` literal typing, `UnaryOperation` `-`,
  `FunctionCall` kind `typeConversion` between `int256`/`uint256`).
- `Verity/Proofs/Stdlib/SolidityImport.lean`: signed lemma set.
- `Contracts/SolidityImportSmoke/Signed/…`: a re-typed `_virtualPriceAux`
  (`gain = int(nav) - int(lastNav)`, fee split, `max(gain, -int(lastNavBB))`
  waterfall, `uint256(int256(x) + gain)`), with `pragma ^0.8.33`.

### Tests

- Theorems: `bb_absorbs_loss_first`, `aa_never_below_zero_when_bb_covers`,
  `conversion_roundtrip`, overflow premises stated as `Int` inequalities;
  `gain_split_sum` (AA gain + BB gain = total gain after fee, as `Int`).
- Mutations: flip a `>` to `>=` in the waterfall; drop the fee term; replace
  checked `-` by unchecked wrap (via `unchecked` would be rejected, so the
  mutation edits the *spec* instead, as the POC does for Spec.lean).
- Rejections: `int128`/narrow signed types, `>>`/`<<` on `int256`, `int256`
  mapping keys, implicit conversions solc would reject anyway (fixture
  proves the diagnostic is ours, not solc's).

### Acceptance

- All suites green; axiom audit clean; no `native_decide` in any lemma
  reachable from the smoke (checked by the suite through `#print axioms`
  rejecting `Lean.ofReduceBool`).
- Dry run: the importer accepts `IdleCDOCreditVault._virtualPriceAux`,
  `_updateAccounting` and `IdleCDOEpochVariant._calcInterestWithdrawRequest`
  bodies from the vendored sources (pragmas rewritten).

### Non-goals

`sar`/shifts, narrow signed widths, signed `**`, `int256` in ABI-dynamic
positions, signed constants beyond literals.

---

## 9. Slice S5: solc 0.8.10 and multi-file source units

**Goal**: compile the Pareto sources unmodified (`pragma solidity 0.8.10;`)
through a second pinned compiler, with imports and remappings resolved
entirely from a vendored, hash-pinned manifest.

### Findings that fix the design (verified against the real binaries)

| | solc 0.8.33 (current pin) | solc 0.8.10 |
|-|---------------------------|-------------|
| Binary | `solc-linux-amd64-v0.8.33+commit.64118f21`, sha256 `1274e5c4…5468` | `solc-linux-amd64-v0.8.10+commit.fc410830`, sha256 `c7effacf28b9d64495f81b75228fbf4266ac0ec87e8f1adc489ddd8a4dd06d89` |
| `--no-import-callback` | supported | **absent** (added in 0.8.22) |
| `evmVersion: cancun` | supported | **rejected** (0.8.10 tops out at `london`) |
| AST fields missing in 0.8.10 on the POC Vault | — | `ContractDefinition.usedEvents`, `ErrorDefinition.errorSelector`, `FunctionCall.nameLocations`, `MemberAccess.memberLocation`, `Mapping.keyName/keyNameLocation/valueName/valueNameLocation` |
| Pragma literals | `["solidity","^","0.8",".33"]` | `["solidity","0.8",".10"]` (exact); OZ files use `^0.8.0` / `^0.8.2` |

### Design

- **Compiler table**: `Importer.lean` carries a closed table
  `{version output string, sha256, evmVersion, supportsNoImportCallback}`
  for 0.8.33 and 0.8.10. The pragma of the *target* file selects the
  compiler; every file in the manifest must have a pragma satisfied by that
  version (exact `0.8.10` or a caret range containing it). The chosen
  compiler's sha256 goes into the digest.
- **Fail-closed imports without `--no-import-callback`**: every source is
  supplied inline in standard JSON; `settings.remappings` maps
  `@openzeppelin/contracts-upgradeable/` and `@uniswap/v2-periphery/` onto
  logical paths in the same JSON; solc runs with `cwd` set to an empty
  temporary directory and no `--base-path`/`--allow-paths`; the output
  `sources` keys must equal the manifest exactly and `ImportDirective.
  absolutePath` values must all be manifest keys. Any file-callback
  resolution therefore fails.
- **Version-indexed schema**: `allowedNodeFields`/`requiredNodeFields`
  become functions of the compiler entry; the differences above are the
  initial delta. The first task of the slice is a committed fixture
  (`Importer/fixtures/ast-fields-0.8.10.txt`, generated by a script that
  walks the AST of the vendored Pareto sources) diffed against the 0.8.33
  fixture; every difference is either allowed with a meaning or rejected.
- **Multi-file**: `ImportDirective` (plain and `{X} from`), several
  `SourceUnit`s, `exportedSymbols` across files, `linearizedBaseContracts`
  and `referencedDeclaration` ids resolving across files, storage entries'
  `contract` field naming another file. Source positions in diagnostics
  carry the logical path of the right file.
- **Vendoring**: `Contracts/ParetoFromSolidity/vendor/idle-tranches/…` at
  `54502d1` and `…/vendor/openzeppelin-contracts-upgradeable/…` at
  v4.9.6, byte-identical, with `vendor/MANIFEST.json` (upstream URL,
  commit/tag, path, sha256 per file) checked by a script and the same
  hashes recorded in the pareto closure repo's `audit/source-map.yaml`.
  Licenses: idle-tranches files are `UNLICENSED`/Apache-2.0 per header, OZ
  is MIT; the vendor directory carries both notices.
- **CI**: `.github/actions/setup-solc` gains a second version triple
  (`SOLC_IMPORT_LEGACY_VERSION/URL/SHA256`) installed to
  `.lake/solidity-import/solc-0.8.10`; `scripts/check_solc_pin.py` checks
  both; `Makefile` target `test-solidity-import` runs every importer suite.
  Runner architecture must be confirmed (this workspace reports `x86_64`;
  official 0.8.10 binaries exist for `linux-amd64` only).

### Files

- `Importer.lean` (compiler table, manifest, remappings, multi-file
  resolution, version-indexed schema), `Importer/fixtures/*`,
  `Importer/scripts/ast_fields_fixture.py`.
- `Contracts/SolidityImportSmoke/Vault810/{Vault.sol, …}`: the POC Vault
  with `pragma solidity 0.8.10;` and the same `Spec.lean` and
  `ExecutionProof.lean` (copied, not shared), proving the seven theorems
  under the other compiler.
- `Contracts/SolidityImportSmoke/MultiFile/…`: a child importing a base
  from a second file through a remapping.
- `.github/actions/setup-solc/action.yml`, `.github/workflows/verify.yml`,
  `scripts/check_solc_pin.py`, `Makefile`, `TRUST_ASSUMPTIONS.md` (two pins).

### Tests

- Compiler substitution: 0.8.33 binary for a `0.8.10` target → "compiler
  version mismatch"; tampered 0.8.10 binary → "compiler checksum mismatch";
  a manifest file missing → solc error surfaced with position; an import
  resolving outside the manifest (probe writes a file into the temp cwd) →
  "unexpected compiler sources"; a pragma outside the table → rejected.
- Schema: the synthetic AST wrapper probes from the POC re-run for 0.8.10
  (`ast`, `metadata`, `typed`, `missing`, `span`, `layout`).
- Seven Vault theorems pass under 0.8.10; slot probe identical to 0.8.33.

### Acceptance

- All suites green under both pins; axiom audit clean.
- The vendored Pareto sources compile through the importer's solc
  invocation with no solc errors, and the AST-field fixture for 0.8.10 is
  committed and fully classified (every field allowed or rejected, none
  "unvalidated").

### Non-goals

Any 0.8.x other than 0.8.10 and 0.8.33; `viaIR`; optimizer settings;
`hardhat`/`foundry` build parity; on-chain bytecode matching.

---

## 10. Slice S6: one Pareto smoke

**Goal**: import `IdleCDOEpochVariant` (most-derived, full chain, unmodified
vendored sources, solc 0.8.10) as a **partial import** with an explicit
entry-point allowlist, and prove one contract-level property about a real
entry point.

### Smoke selection

Entry point: `IdleCDOEpochVariant.getInstantWithdrawFunds()`. It exercises
every slice at once:

- S1: `_checkOnlyOwnerOrManager` (child) → `owner()` (OwnableUpgradeable,
  via GuardedLaunchUpgradable) and `IdleCreditVault(strategy).manager()`;
  `_handleBorrowerDefault` → `_pause()` (PausableUpgradeable, `internal
  virtual`).
- S2: packed bools `isEpochRunning`, `allowInstantWithdraw`, `defaulted`;
  `whenNotPaused` on `_pause`; `emit BorrowerDefault(funds)`; `NotAllowed`
  custom error through `_checkNotAllowed`.
- S3: `_pendingInstant()` static call to the strategy, `try
  this.getFundsFromBorrower(_instantWithdraws)` with `safeTransferFrom`
  inside, `_strategy.collectInstantWithdrawFunds(...)` in the success path.
- S4: not on this path; covered by the additional view entry point
  `virtualPrice(address)` (→ `_virtualPriceAux`, static calls to the
  strategy and the token) which the allowlist also includes so the signed
  path is imported from the real source.
- S5: real pragmas, real OZ files, real remappings.

Property (spec sketch, stated over `view` and a universally quantified
`world`):

- if the self-call reverts under `world`, the post-state has `defaulted =
  true`, `allowInstantWithdraw` unchanged, the epoch contract paused, and
  `world.call` was never invoked with the strategy's
  `collectInstantWithdrawFunds` selector (stated as a trace predicate on the
  `CallModel` log, which S3's `CallModel` records in `ContractState`
  returndata-style journal or as an explicit log field of the model, to be
  decided in S3 and reused here);
- if it succeeds, `allowInstantWithdraw = true` and the strategy was called
  exactly once with the `_pendingInstant()` value.

Candidate properties beyond this one are listed in the closure repo's
`audit/PROPERTIES.md`; only the two above are in scope.

### Partial import mechanism

`solidity_contract IdleCDOEpochVariant from "vendor/idle-tranches/contracts/
IdleCDOEpochVariant.sol" contract "IdleCDOEpochVariant" entry_points
[getInstantWithdrawFunds, virtualPrice, getFundsFromBorrower]`:

- every function reachable from the allowlist (internal calls, modifiers,
  `super`, `this.` targets) must be fully accepted; anything else in the
  contract is not parsed, is listed in the registered
  `unmodeledEntryPoints : List String`, and is omitted from `step`;
- getters stay in `step` (they are cheap and needed for the views);
- the trust docs state that `step` covers the allowlist only, and the
  smoke's `Spec.lean` header repeats the list.

This is what makes `initialize` (`new IdleCDOTranche`, `string`
concatenation, `abi.encodePacked`), `_getAARatio`'s function-typed local,
and `IdleCreditVault`-side code stay out without weakening any rule in
Section 1. The alternative, a full import of every entry point, was rejected
for this roadmap: it requires contract creation, `string`/`bytes` memory,
and function-typed values, none of which serve the property.

### Files

- `Contracts/ParetoFromSolidity/vendor/…` (S5), `ParetoFromSolidity.lean`,
  `Spec.lean`, `Proofs/InstantWithdrawSmoke.lean`,
  `scripts/pareto_smoke_test.py`, `lakefile.lean` target
  `ParetoFromSolidity`, `docs/VERIFICATION_STATUS.md` row, `README.md`
  table row, `AUDIT.md` evidence entry.

### Tests

- The smoke script: builds `ParetoFromSolidity`; axiom audit; `#print`
  probes that `getInstantWithdrawFunds` unfolds through `Stmt.tryCatch`,
  `Expr.libCall .safeTransferFrom`, and `PausableUpgradeable__pause`;
  vendored-hash check against `vendor/MANIFEST.json` and against upstream
  `54502d1` (network-free: hashes are committed; a separate manual script
  re-derives them from the pinned commit);
- mutations on a disposable copy of the vendored source: remove
  `defaulted = true` from `_handleBorrowerDefault` → theorem breaks; move
  `allowInstantWithdraw = true` into the `catch` → theorem breaks; add
  an entry point to the allowlist that touches `initialize` → import
  rejected with the position of the first unsupported node;
- unmodeled-entry-point manifest equals the expected list (any new
  accepted function must be a deliberate change).

### Acceptance

- `lake build ParetoFromSolidity` green on `dgx-spark`; wall-clock and peak
  memory recorded in the PR against the baseline in
  [`docs/DGX_SPARK_BOTTLENECK_REPORT.md`](DGX_SPARK_BOTTLENECK_REPORT.md);
  the kernel-check time of the largest imported function is reported.
- Axiom audit clean; every theorem under 30 lines or allowlisted.
- `TRUST_ASSUMPTIONS.md` has a "Proof-only Pareto import" section listing
  the allowlist, `unmodeledEntryPoints`, the three trusted SafeERC20
  translations, both compiler pins, and the `CallModel` parameterization.

### Non-goals

`IdleCreditVault` as a modeled callee (instantiating `world`), any
`initialize`/constructor path, `IdleCDOCreditVault` deposits, the full
`step` relation, cross-contract invariants (for example strategy/vault
accounting equalities from the closure repo), events in specs, gas, bytecode,
proxy upgrade safety, `keyring` policy semantics.

---

## 11. Sequencing and dependencies

```
S1 inheritance ──► S2 modifiers/structs ──► S3 external calls/try ──► S4 signed ──► S5 solc 0.8.10 ──► S6 Pareto smoke
                                                                         ▲
                                                             PR #2414 (Int256 lemmas without native_decide)
```

- S2 may be split into S2a/S2b/S2c PRs; each keeps the S1 smoke green.
- S3 and S4 touch disjoint constructors and could be developed in parallel
  branches, but merge in order (S3 first) to keep tuple-return handling in
  one place.
- S5 can be prototyped early (the compiler-table and fixture work does not
  depend on S1–S4) but merges after S4 so the fixture classification covers
  the final node set.
- Relative size: S1 large, S2 large (three PRs), S3 medium, S4 small,
  S5 medium, S6 medium.

---

## 12. Risks and open questions

| Risk | Impact | Mitigation / decision point |
|------|--------|-----------------------------|
| `super` annotation in solc's AST is relative to the defining contract, not the imported most-derived contract | wrong dispatch would be a silent semantic bug | S1 resolves `super` itself over the target's linearization and treats disagreement with the AST as a rejection; a synthetic diamond test pins it |
| Kernel-check time of large intrinsically typed bodies (`_stopEpoch` is ~190 lines) | S6 build time on `dgx-spark` | per-function constants (4.1); S6 records timings; if a body exceeds budget, split it via the allowlist rather than weakening checks |
| Packed-field semantics duplicated between compiler (`compiledPackedRead`) and the executable core | drift | S2 proves the two agree on word inputs (`width < 256` calculation, already the compiler's argument) |
| `CallModel` call log representation | S6 property needs "the strategy was called once" | decide in S3: explicit journal on the model side, never a `ContractState` field (EVMYulLean exhaustive matches) |
| Function-typed local in `_getAARatio` | blocks `getApr`/`getCurrentAARatio` | out of allowlist; if ever needed, a narrow rewrite (`cond ? f : g` used only in call position → `if` at each call site) is a separate slice |
| solc 0.8.10 has no official `linux-arm64` binary | CI on non-x86 runners | confirm runner architecture before S5; fallback is building solc from source with a pinned hash, documented as a trust surface |
| OZ `initializer` modifier uses `AddressUpgradeable.isContract` (`extcodesize`) | needed only if `initialize` were modeled | out of allowlist in S6; S3 models `isContract` as a reserved static primitive so the OZ file still parses |
| `require` reason strings and panic codes are model strings, not ABI revert bytes | unchanged from the POC | keep the existing trust wording; no slice claims revert-data equivalence |
| Upstream `54502d1` sources contain `UNLICENSED` headers | vendoring | vendor with the upstream notice, proof-only use, confirm with the closure repo owners before S5 merges |

---

## 13. Gap coverage summary

| Gap | Route on this roadmap |
|-----|-----------------------|
| G1 modeled callee | `CallModel` parameter (S3); instantiation with the imported strategy is post-S6 |
| G2 nested mappings / struct mappings are stubs | real logical keys via injective pairing (S2) |
| G3 `selfCall` with arguments | `try this.f(args)` (S3) |
| G4 packed `bool`/`address` fields | shift/mask on solc offsets (S2) |
| G5 interface-typed storage fields | opaque field (S1) + typed call on `I(addr)` expressions (S3) |
| G6 override cannot see child helpers | dispatch by linearization, no positional elaboration (S1) |
| G7 absolute slots, diamonds rejected | solc layout per chain, C3 accepted (S1) |
| G8–G10 statement/expression forms | importer-owned AST (S2) |
| G11 `view` frame theorem | not generated by the importer; `view` functions are ordinary definitions, static-call-only (S3) |
| G12, G13, G16 naming and ordering | non-issues: declaration ids, callee-first registration (S1) |
| G14 multi-value interface returns | tuple returns (S3) |
| G15 cyclic `linked_contracts` | `CallModel` needs no binding order (S3) |
| G17 gaps, `bytes32`, `string`, `uint8` storage | opaque fields (S1); `uint8` packed scalar (S2) |
| G18 modifiers calling helpers, postludes, abstract functions | inlined modifiers with blocks (S2), abstract bases (S1) |

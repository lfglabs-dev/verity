import Contracts.Smoke.Namespaces

namespace Contracts.Smoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math

-- ADT (inductive) section smoke test (#1727, Axis 1 Steps 5a/5b)
-- Declares algebraic data types with typed variant fields.
-- ADT type definitions flow through to ContractSpec.adtTypes.
-- ADT-typed storage fields are represented as Uint256 (tag value) at the EVM level.
verity_contract AdtSmoke where
  types
    TokenId : Uint256
  inductive
    OptionalUint := | Some(value : Uint256) | None
    Result := | Ok(amount : Uint256, recipient : Address) | Err(code : Uint256)
  storage
    counter : Uint256 := slot 0
    result : OptionalUint := slot 1

  function increment () : Unit := do
    let current ← getStorage counter
    setStorage counter (add current 1)

#check_contract AdtSmoke

-- Verify ADT type definitions flow through to spec (#1727, Step 5b plumbing)
example : AdtSmoke.spec.adtTypes.length = 2 := rfl
example : AdtSmoke.spec.adtTypes.map (·.name) = ["OptionalUint", "Result"] := rfl
example : (AdtSmoke.spec.adtTypes.map (·.variants.length)) = [2, 2] := rfl

-- Unsafe block smoke test (#1424, Phase 6 Step 6a).
-- `unsafe "reason" do` wraps a block of statements; Step 6a is the transparent
-- wrapper (validation/compilation recurse into the body unchanged).
verity_contract UnsafeBlockSmoke where
  storage
    counter : Uint256 := slot 0

  function incrementUnsafe () : Unit := do
    unsafe "demo: testing unsafe block syntax" do
      let current ← getStorage counter
      setStorage counter (add current 1)

  function getCounter () : Uint256 := do
    let current ← getStorage counter
    return current

#check_contract UnsafeBlockSmoke

-- Unsafe gating positive test (#1728, Phase 6 Step 6b).
-- Low-level mstore inside `unsafe` block passes #check_contract
-- WITHOUT requiring local_obligations.
verity_contract UnsafeGatingAccepted where
  storage
    counter : Uint256 := slot 0

  function writeMem () : Unit := do
    unsafe "manual memory write for packed encoding" do
      mstore 0 1
    pure ()

#check_contract UnsafeGatingAccepted

-- Unsafe gating negative test (#1728, Phase 6 Step 6b).
-- Low-level mstore OUTSIDE unsafe block (and no local_obligations) is rejected.
verity_contract UnsafeGatingRejected where
  storage

  constructor () := do
    mstore 0 1
    pure ()

  function noop () : Unit := do
    pure ()

/--
error: #check_contract failed for 'Contracts.Smoke.UnsafeGatingRejected': Compilation error: constructor uses low-level/assembly mechanic(s) mstore outside an unsafe block without any local_obligations entry (Issue #1424 (controlled unsafe/assembly escape hatches)). Wrap the low-level code in `unsafe "reason" do` or add local_obligations [...] to make the trust boundary explicit.
-/
#guard_msgs in
#check_contract UnsafeGatingRejected

-- CEI violation test: this contract compiles but #check_contract rejects it
verity_contract CEIViolationRejected where
  storage
    result : Uint256 := slot 0
  linked_externals
    external echo(Uint256) -> (Uint256)

  function callThenStore (x : Uint256) : Unit := do
    let echoed := externalCall "echo" [x]
    setStorage result echoed

/--
error: #check_contract failed for 'Contracts.Smoke.CEIViolationRejected': Compilation error: function 'callThenStore' violates CEI (Checks-Effects-Interactions) ordering: state write after external call. Reorder state writes before external calls, or annotate with allow_post_interaction_writes / nonreentrant(<lock>) to opt out (Issue #1728 (CEI enforcement — Checks-Effects-Interactions ordering))
-/
#guard_msgs in
#check_contract CEIViolationRejected

/--
error: function 'guarded': nonreentrant lock field 'lock' must be a scalar Uint256 storage field
-/
#guard_msgs in
verity_contract NonreentrantAddressLockRejected where
  storage
    lock : Address := slot 0

  function nonreentrant(lock) guarded () : Unit := do
    pure ()

-- Regression for the Bugbot review on PR #1971 ("Internal nonreentrant
-- skips guard", High Severity): the transient-storage reentrancy guard
-- prologue is only attached to external dispatch entries, so an
-- `internal` helper carrying `nonreentrant(<lock>)` would be CEI-exempted
-- without ever materialising a runtime guard. Fail closed at parse time.
/--
error: function 'guardedHelper': nonreentrant(<lock>) is only supported on external entrypoints; the synthesised transient-storage guard runs at the dispatch boundary, so internal helpers cannot rely on it. Move the guard to the public caller or drop the annotation.
-/
#guard_msgs in
verity_contract NonreentrantInternalHelperRejected where
  storage
    lock : Uint256 := slot 0

  function internal nonreentrant(lock) guardedHelper () : Unit := do
    pure ()

-- ════════════════════════════════════════════════════════════════════════════
-- Stress-test contracts: edge-case coverage for Language Design Axes (#1731)
-- ════════════════════════════════════════════════════════════════════════════

-- CEI edge case 1: write after external call, inside an if-branch — should detect
verity_contract CEIWriteInBranchAfterCall where
  storage
    counter : Uint256 := slot 0
  linked_externals
    external echo(Uint256) -> (Uint256)

  -- Call then conditional write: CEI violation
  function callThenConditionalWrite (x : Uint256) : Unit := do
    let echoed := externalCall "echo" [x]
    if echoed != 0 then
      setStorage counter echoed
    else
      pure ()

/--
error: #check_contract failed for 'Contracts.Smoke.CEIWriteInBranchAfterCall': Compilation error: function 'callThenConditionalWrite' violates CEI (Checks-Effects-Interactions) ordering: in if-then branch: state write after external call. Reorder state writes before external calls, or annotate with allow_post_interaction_writes / nonreentrant(<lock>) to opt out (Issue #1728 (CEI enforcement — Checks-Effects-Interactions ordering))
-/
#guard_msgs in
#check_contract CEIWriteInBranchAfterCall

-- CEI edge case 2: call at top level, write after — same as CEIViolationRejected but
-- with the write in both branches of an if (to test compound-statement propagation)
verity_contract CEICallBothBranchesWrite where
  storage
    counter : Uint256 := slot 0
  linked_externals
    external echo(Uint256) -> (Uint256)

  function callThenBranchWrite (x : Uint256) : Unit := do
    let echoed := externalCall "echo" [x]
    if echoed != 0 then
      setStorage counter echoed
    else
      setStorage counter 0

/--
error: #check_contract failed for 'Contracts.Smoke.CEICallBothBranchesWrite': Compilation error: function 'callThenBranchWrite' violates CEI (Checks-Effects-Interactions) ordering: in if-then branch: state write after external call. Reorder state writes before external calls, or annotate with allow_post_interaction_writes / nonreentrant(<lock>) to opt out (Issue #1728 (CEI enforcement — Checks-Effects-Interactions ordering))
-/
#guard_msgs in
#check_contract CEICallBothBranchesWrite

-- ════════════════════════════════════════════════════════════════════════════
-- Cross-function reentrancy gate (#1728): the Midnight `take`/`liquidate` shape
-- ════════════════════════════════════════════════════════════════════════════
-- `takeWithoutDisposition` is textbook CEI-CLEAN: every state write precedes the
-- external call, so the single-function CEI check is satisfied — yet the
-- contract is still REJECTED. That is the entire point of the gate. A CEI-clean
-- `take` is exactly the Midnight bug shape: while the external call is in
-- flight, control is handed to an untrusted callee that can re-enter a
-- *different* entrypoint (e.g. `liquidate`) and observe this contract's
-- half-updated state. CEI reasons within one function and cannot see that
-- cross-function window; only an explicit disposition can close it. This is the
-- keystone regression test — it proves the Midnight callback reentrancy bug
-- cannot pass `#check_contract` undeclared.
verity_contract ReentrancyDispositionRequired where
  storage
    balance : Uint256 := slot 0
  linked_externals
    external echo(Uint256) -> (Uint256)

  function takeWithoutDisposition (amount : Uint256) : Uint256 := do
    setStorage balance amount
    let echoed := externalCall "echo" [amount]
    return echoed

/--
error: #check_contract failed for 'Contracts.Smoke.ReentrancyDispositionRequired': Compilation error: function 'takeWithoutDisposition' makes an external call but declares no reentrancy disposition. An external call hands control to an untrusted callee that may re-enter another entrypoint while this contract's state is mid-update (cross-function reentrancy). Add `nonreentrant(<lock>)` to synthesise a runtime guard, or `reentrancy_trusted` to assert — and own — that every external callee is trusted not to re-enter (Issue #1728 (CEI enforcement — Checks-Effects-Interactions ordering)). cei_safe / allow_post_interaction_writes cover only single-function CEI and do not satisfy this gate.
-/
#guard_msgs in
#check_contract ReentrancyDispositionRequired

-- Positive control: the SAME CEI-clean body is ACCEPTED once it declares a
-- disposition. `reentrancy_trusted` is the audited author assertion that every
-- external callee ('echo' here, an in-repo trusted fixture) will not re-enter.
-- Pairing this with the rejection above isolates the gate as the deciding pass:
-- identical bodies, opposite verdicts, the disposition the only difference.
verity_contract ReentrancyDispositionDeclared where
  storage
    balance : Uint256 := slot 0
  linked_externals
    external echo(Uint256) -> (Uint256)

  function reentrancy_trusted takeWithDisposition (amount : Uint256) : Uint256 := do
    setStorage balance amount
    let echoed := externalCall "echo" [amount]
    return echoed

#check_contract ReentrancyDispositionDeclared

-- Modifies + roles: combined annotation
verity_contract ModifiesRolesSmoke where
  storage
    admin : Address := slot 0
    counter : Uint256 := slot 1
    flag : Uint256 := slot 2

  constructor (initialAdmin : Address) := do
    setStorageAddr admin initialAdmin

  -- Combines requires(admin), modifies(counter), and no_external_calls
  function no_external_calls setCounter (value : Uint256) requires(admin) modifies(counter) : Unit := do
    setStorage counter value

  -- Combines requires(admin) and modifies(counter, flag)
  function setCounterAndFlag (value : Uint256, flagValue : Uint256) requires(admin) modifies(counter, flag) : Unit := do
    setStorage counter value
    setStorage flag flagValue

  function view getCounter () : Uint256 := do
    let current ← getStorage counter
    return current

#check_contract ModifiesRolesSmoke

-- Modifies + namespace: namespaced storage with modifies annotations
verity_contract ModifiesNamespaceSmoke where
  storage_namespace
  storage
    counter : Uint256 := slot 0
    owner : Address := slot 1

  constructor (initialOwner : Address) := do
    setStorageAddr owner initialOwner

  function increment () modifies(counter) : Unit := do
    let current ← getStorage counter
    setStorage counter (add current 1)

  function transferOwnership (newOwner : Address) modifies(owner) : Unit := do
    setStorageAddr owner newOwner

  function view getCounter () : Uint256 := do
    let current ← getStorage counter
    return current

#check_contract ModifiesNamespaceSmoke

-- Verify namespaced modifies slots are actually offset
example : ModifiesNamespaceSmoke.counter.slot ≠ 0 := by decide
example : ModifiesNamespaceSmoke.owner.slot ≠ 1 := by decide

-- ADT edge case: single variant (no branching needed)
verity_contract AdtSingleVariant where
  inductive
    Sentinel := | Active
  storage
    tag : Sentinel := slot 0

  function store () : Unit := do
    setStorage tag (adt "Active")

#check_contract AdtSingleVariant

-- ADT edge case: variant with zero fields vs variant with multiple fields
verity_contract AdtMixedFieldCounts where
  inductive
    Maybe := | Nothing | Just(value : Uint256)
    Pair := | MkPair(fst : Uint256, snd : Uint256)
  storage
    result : Maybe := slot 0

  function clear () : Unit := do
    setStorage result (adt "Nothing")

  function set (_value : Uint256) : Unit := do
    setStorage result (adt "Just" [_value])

#check_contract AdtMixedFieldCounts

-- Verify ADT spec plumbing for mixed field counts
example : AdtMixedFieldCounts.spec.adtTypes.length = 2 := rfl
example : AdtMixedFieldCounts.spec.adtTypes.map (·.name) = ["Maybe", "Pair"] := rfl

-- Newtype + modifies: newtypes used in function params with modifies annotation
verity_contract NewtypeModifiesSmoke where
  types
    TokenId : Uint256
    Amount : Uint256
  storage
    nextTokenId : Uint256 := slot 0
    totalMinted : Uint256 := slot 1

  function mint (id : TokenId, amount : Amount) modifies(nextTokenId, totalMinted) : Unit := do
    setStorage nextTokenId id
    let current ← getStorage totalMinted
    setStorage totalMinted (add current amount)

  function view getNextId () : Uint256 := do
    let current ← getStorage nextTokenId
    return current

#check_contract NewtypeModifiesSmoke

-- Newtype + namespace combo
verity_contract NewtypeNamespaceSmoke where
  types
    TokenId : Uint256
  storage_namespace "newtype.ns.v0"
  storage
    nextId : Uint256 := slot 0

  function setId (id : TokenId) : Unit := do
    setStorage nextId id

  function view getId () : Uint256 := do
    let current ← getStorage nextId
    return current

#check_contract NewtypeNamespaceSmoke

-- Verify namespace offset applies
example : NewtypeNamespaceSmoke.nextId.slot ≠ 0 := by decide

-- Unsafe block + CEI: write after unsafe block that has a call — should detect
verity_contract UnsafeCEIViolation where
  storage
    counter : Uint256 := slot 0
  linked_externals
    external echo(Uint256) -> (Uint256)

  function unsafeCallThenWrite (x : Uint256) : Unit := do
    let echoed := externalCall "echo" [x]
    unsafe "test: write inside unsafe after call" do
      setStorage counter echoed

/--
error: #check_contract failed for 'Contracts.Smoke.UnsafeCEIViolation': Compilation error: function 'unsafeCallThenWrite' violates CEI (Checks-Effects-Interactions) ordering: in unsafe block: state write after external call. Reorder state writes before external calls, or annotate with allow_post_interaction_writes / nonreentrant(<lock>) to opt out (Issue #1728 (CEI enforcement — Checks-Effects-Interactions ordering))
-/
#guard_msgs in
#check_contract UnsafeCEIViolation

-- Unsafe block + CEI: write inside unsafe before call — should pass
verity_contract UnsafeCEICompliant where
  storage
    counter : Uint256 := slot 0
  linked_externals
    external echo(Uint256) -> (Uint256)

  function reentrancy_trusted writeBeforeUnsafeCall (x : Uint256) : Uint256 := do
    setStorage counter x
    unsafe "test: call inside unsafe after write" do
      let echoed := externalCall "echo" [x]
      return echoed

#check_contract UnsafeCEICompliant

-- CEI: internal call after external call — the internal call may write storage,
-- so this should be flagged as a CEI violation.
verity_contract CEIInternalCallAfterExternalRejected where
  storage
    counter : Uint256 := slot 0
  linked_externals
    external echo(Uint256) -> (Uint256)

  function increment (amount : Uint256) : Unit := do
    let current ← getStorage counter
    setStorage counter (add current amount)

  function callThenHelper (x : Uint256) : Unit := do
    let echoed := externalCall "echo" [x]
    increment echoed

/--
error: #check_contract failed for 'Contracts.Smoke.CEIInternalCallAfterExternalRejected': Compilation error: function 'callThenHelper' violates CEI (Checks-Effects-Interactions) ordering: state write after external call. Reorder state writes before external calls, or annotate with allow_post_interaction_writes / nonreentrant(<lock>) to opt out (Issue #1728 (CEI enforcement — Checks-Effects-Interactions ordering))
-/
#guard_msgs in
#check_contract CEIInternalCallAfterExternalRejected

-- Roles + CEI combo: role guard with CEI-compliant external call
verity_contract RolesCEISmoke where
  storage
    admin : Address := slot 0
    counter : Uint256 := slot 1
  linked_externals
    external echo(Uint256) -> (Uint256)

  constructor (initialAdmin : Address) := do
    setStorageAddr admin initialAdmin

  -- CEI compliant: write, then call
  function reentrancy_trusted setAndCall (value : Uint256) requires(admin) : Uint256 := do
    setStorage counter value
    let echoed := externalCall "echo" [value]
    return echoed

  function view getCounter () : Uint256 := do
    let current ← getStorage counter
    return current

#check_contract RolesCEISmoke

-- Nonreentrant + modifies: combined annotations
verity_contract NonreentrantModifiesSmoke where
  storage
    lock : Uint256 := slot 0
    counter : Uint256 := slot 1
    balance : Uint256 := slot 2
  linked_externals
    external echo(Uint256) -> (Uint256)

  -- nonreentrant metadata composes with modifies, while the body remains CEI-ordered.
  function nonreentrant(lock) deposit (amount : Uint256) modifies(counter, balance) : Uint256 := do
    let current ← getStorage counter
    setStorage counter (add current 1)
    let bal ← getStorage balance
    setStorage balance (add bal amount)
    let echoed := externalCall "echo" [amount]
    return echoed

  function view getBalance () : Uint256 := do
    let bal ← getStorage balance
    return bal

#check_contract NonreentrantModifiesSmoke

-- Multiple ADTs + newtype in same contract
verity_contract AdtNewtypeCombo where
  types
    TokenId : Uint256
    Owner : Address
  inductive
    Status := | Active | Paused | Deprecated
    OptionalId := | SomeId(id : Uint256) | NoId
  storage
    contractStatus : Status := slot 0
    lastTokenId : OptionalId := slot 1

  function pause () : Unit := do
    setStorage contractStatus (adt "Paused")

  function unpause () : Unit := do
    setStorage contractStatus (adt "Active")

  function setLastId (_id : TokenId) : Unit := do
    setStorage lastTokenId (adt "SomeId" [_id])

#check_contract AdtNewtypeCombo

-- Verify ADT spec for 3-variant enum
example : AdtNewtypeCombo.spec.adtTypes.length = 2 := rfl
example : AdtNewtypeCombo.spec.adtTypes.map (·.name) = ["Status", "OptionalId"] := rfl
-- Status has 3 variants: Active(0), Paused(1), Deprecated(2); OptionalId has 2
example : AdtNewtypeCombo.spec.adtTypes.map (·.variants.length) = [3, 2] := rfl

-- Full combo: namespace + newtype + modifies + roles + CEI
verity_contract FullComboSmoke where
  types
    Amount : Uint256
  inductive
    TokenStatus := | Active | Frozen
  storage_namespace "fullcombo.v0"
  storage
    admin : Address := slot 0
    balance : Uint256 := slot 1
    status : TokenStatus := slot 2

  constructor (initialAdmin : Address) := do
    setStorageAddr admin initialAdmin

  function no_external_calls deposit (amount : Amount) requires(admin) modifies(balance) : Unit := do
    let current ← getStorage balance
    setStorage balance (add current amount)

  function no_external_calls freeze () requires(admin) modifies(status) : Unit := do
    setStorage status (adt "Frozen")

  function view no_external_calls getBalance () : Uint256 := do
    let current ← getStorage balance
    return current

#check_contract FullComboSmoke

-- Verify combo properties
example : FullComboSmoke.balance.slot ≠ 1 := by decide  -- namespaced
example : FullComboSmoke.spec.storageNamespace.isSome = true := rfl
example : FullComboSmoke.spec.adtTypes.length = 1 := rfl
example : FullComboSmoke.spec.adtTypes.map (·.name) = ["TokenStatus"] := rfl

-- ════════════════════════════════════════════════════════════════════════════
-- Storage non-alias certificate (#1966): decidable subset
-- ════════════════════════════════════════════════════════════════════════════

-- The storage layout audit artifact tags each pairwise non-alias claim with
-- a justification. `distinctScalarSlots` claims — both families scalar with
-- distinct declared slots — are *decidable* against the certificate: the
-- claim reduces to `aSlot ≠ bSlot` and `decide` discharges it without any
-- keccak assumption. The four examples below ground that property on the
-- ERC20 contract, exercising all three justification kinds emitted by
-- `Compiler.CompilationModel.LayoutReport`:
--
-- * `ownerSlot` (slot 0, address) ⟂ `totalSupplySlot` (slot 1, uint256)
--   — `distinctScalarSlots`, decidable.
-- * `ownerSlot` (slot 0, scalar) ⟂ `balancesSlot` (slot 2, mapping)
--   — `keccakDomainScalar`, the layout claim records `aSlot=0, bSlot=2`
--     so the per-family obligation can be discharged against a named
--     `keccak_above_max_declared_slot` axiom. The smoke here only locks
--     down the slot values (the proof side discharges via the axiom).
-- * `balancesSlot` (mapping, slot 2) ⟂ `allowancesSlot` (nestedMapping,
--   slot 3) — `keccakPreimageDistinct`, locked down structurally.

example :
    (Contracts.ERC20.spec.fields.zipIdx.find? (fun (f, _) => f.name == "ownerSlot")).isSome
    && (Contracts.ERC20.spec.fields.zipIdx.find? (fun (f, _) => f.name == "totalSupplySlot")).isSome
    = true := by decide

example :
    (Contracts.ERC20.spec.fields.zipIdx.findSome? (fun (f, idx) =>
      if f.name == "ownerSlot" then some (f.slot.getD idx) else none)) =
    some 0 := by decide

example :
    (Contracts.ERC20.spec.fields.zipIdx.findSome? (fun (f, idx) =>
      if f.name == "totalSupplySlot" then some (f.slot.getD idx) else none)) =
    some 1 := by decide

-- `distinctScalarSlots` reduces to `0 ≠ 1` and is decidable.
example :
    (Contracts.ERC20.spec.fields.zipIdx.findSome? (fun (f, idx) =>
      if f.name == "ownerSlot" then some (f.slot.getD idx) else none)) ≠
    (Contracts.ERC20.spec.fields.zipIdx.findSome? (fun (f, idx) =>
      if f.name == "totalSupplySlot" then some (f.slot.getD idx) else none)) := by
  decide

-- The two keccak-derived families have *distinct* root slots, so their
-- preimage shapes are structurally disjoint (`keccak256(k || 2)` vs
-- `keccak256(innerK || keccak256(outerK || 3))`). The non-alias proof
-- against this pair is a `keccakPreimageDistinct` axiom; the smoke just
-- locks down the structural shape the axiom is parameterised over.
example :
    Contracts.ERC20.spec.fields.any (fun f =>
      f.name == "balancesSlot" &&
      match f.ty with
      | Compiler.CompilationModel.FieldType.mappingTyped _ => true
      | _ => false) = true := by decide

example :
    Contracts.ERC20.spec.fields.any (fun f =>
      f.name == "allowancesSlot" &&
      match f.ty with
      | Compiler.CompilationModel.FieldType.mappingTyped _ => true
      | _ => false) = true := by decide

end Contracts.Smoke

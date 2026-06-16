import Contracts.Smoke.SpecGenAndChecks

namespace Contracts.Smoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math

-- #1729, Axis 3 Step 1b: smoke test for modifies(...) annotation
verity_contract ModifiesSmoke where
  storage
    counter : Uint256 := slot 0
    owner : Address := slot 1
    balances : Address → Uint256 := slot 2

  constructor (initialOwner : Address) := do
    setStorageAddr owner initialOwner

  -- Only modifies `counter`; owner and balances are untouched
  function increment () modifies(counter) : Unit := do
    let current ← getStorage counter
    setStorage counter (add current 1)

  -- Modifies `owner` only
  function transferOwnership (newOwner : Address) modifies(owner) : Unit := do
    setStorageAddr owner newOwner

  -- Modifies both counter and balances
  function deposit (amount : Uint256) modifies(counter, balances) : Unit := do
    let sender ← msgSender
    let current ← getStorage counter
    setStorage counter (add current 1)
    let balance ← getMapping balances sender
    setMapping balances sender (add balance amount)

  -- View function (no modifies needed)
  function view getCounter () : Uint256 := do
    let current ← getStorage counter
    return current

-- #1729, Axis 3 Step 1c: smoke test for no_external_calls annotation
verity_contract NoExternalCallsSmoke where
  storage
    counter : Uint256 := slot 0
    owner : Address := slot 1

  -- Pure arithmetic, no external calls
  function no_external_calls increment () : Unit := do
    let current ← getStorage counter
    setStorage counter (add current 1)

  -- Read-only with no_external_calls
  function view no_external_calls getCounter () : Uint256 := do
    let current ← getStorage counter
    return current

  -- Regular function without the annotation (for comparison)
  function setOwner (newOwner : Address) : Unit := do
    setStorageAddr owner newOwner

-- #1729, Axis 3 Step 1d: smoke test for annotation composition (_effects theorem)
verity_contract EffectCompositionSmoke where
  storage
    counter : Uint256 := slot 0
    owner : Address := slot 1
    balances : Address → Uint256 := slot 2

  -- view + no_external_calls: _effects bundles _is_view ∧ _no_calls
  function view no_external_calls getCounter () : Uint256 := do
    let current ← getStorage counter
    return current

  -- no_external_calls + modifies: _effects bundles _no_calls ∧ _modifies
  function no_external_calls increment () modifies(counter) : Unit := do
    let current ← getStorage counter
    setStorage counter (add current 1)

  -- Single annotation only (no _effects expected)
  function no_external_calls setOwner (newOwner : Address) : Unit := do
    setStorageAddr owner newOwner

  -- No annotations at all
  function deposit (amount : Uint256) : Unit := do
    let sender ← msgSender
    let balance ← getMapping balances sender
    setMapping balances sender (add balance amount)

-- #1728, Axis 2 Step 2a: smoke test for CEI enforcement
verity_contract CEISmoke where
  storage
    counter : Uint256 := slot 0
    balances : Address → Uint256 := slot 1
  linked_externals
    external echo(Uint256) -> (Uint256)

  -- CEI-compliant: effects before interactions (no external calls here)
  function increment () : Unit := do
    let current ← getStorage counter
    setStorage counter (add current 1)

  -- CEI-compliant: no state writes at all (view-like)
  function getCounter () : Uint256 := do
    let current ← getStorage counter
    return current

  -- CEI-compliant: effects before interaction
  function updateThenCall (next : Uint256) : Uint256 := do
    setStorage counter next
    let echoed := externalCall "echo" [next]
    return echoed

  -- Opted out with allow_post_interaction_writes: writes after call
  function allow_post_interaction_writes callThenUpdate (next : Uint256) : Unit := do
    let echoed := externalCall "echo" [next]
    setStorage counter echoed

-- #1728, Axis 2 Step 2b: smoke test for CEI escalation ladder (nonreentrant, cei_safe)
verity_contract CEILadderSmoke where
  storage
    counter : Uint256 := slot 0
    lock : Uint256 := slot 1
    balances : Address → Uint256 := slot 2
  linked_externals
    external echo(Uint256) -> (Uint256)

  -- `nonreentrant(lock)` now synthesizes a transient-storage reentrancy
  -- guard during compileFunctionSpec (#1893), so CEI ordering inside the
  -- body is no longer required: state writes after external calls are
  -- safe because the guard reverts on reentry.
  function nonreentrant(lock) callThenStoreGuarded (x : Uint256) : Uint256 := do
    let echoed := externalCall "echo" [x]
    setStorage counter echoed
    return echoed

  -- cei_safe is recorded as metadata; it does not bypass CEI by itself.
  function cei_safe callThenStoreProved (x : Uint256) : Uint256 := do
    setStorage counter x
    let echoed := externalCall "echo" [x]
    return echoed

  -- Normal function: CEI-compliant (effects before interactions), gets _cei_compliant
  function storeThenCall (x : Uint256) : Uint256 := do
    setStorage counter x
    let echoed := externalCall "echo" [x]
    return echoed

  -- Normal function: no external calls at all, gets _cei_compliant
  function increment () : Unit := do
    let current ← getStorage counter
    setStorage counter (add current 1)

-- Regression for #1893 (real nonreentrant guard semantics). The
-- compileFunctionSpec injection emits a transient-storage acquire
-- prologue for any `nonreentrant(lockField)` function: a `tload`/`eq`
-- reentry-revert guard followed by a `tstore` that takes the lock. The
-- guard runs before any user-authored Yul, so the function reverts on
-- reentry; transient storage auto-clears at end of transaction,
-- removing the need for explicit release Yul on every return path. The
-- visible behavioural change is that CEI ordering inside the body is no
-- longer required — `callThenStoreGuarded` writes to `counter` *after*
-- calling `echo`, which would have been rejected as a CEI violation
-- before this issue, but now compiles cleanly because the synthesized
-- guard prevents reentrant state corruption at runtime.
#check_contract CEILadderSmoke

-- `cei_safe` is proof-backed metadata, not a CEI escape hatch: a post-call
-- persistent write is still rejected unless the function uses an explicit
-- trust exit such as `allow_post_interaction_writes` or `nonreentrant`.
verity_contract CEISafePostInteractionWriteRejected where
  storage
    result : Uint256 := slot 0
  linked_externals
    external echo(Uint256) -> (Uint256)

  function cei_safe callThenStoreClaimed (x : Uint256) : Unit := do
    let echoed := externalCall "echo" [x]
    setStorage result echoed

/--
error: #check_contract failed for 'Contracts.Smoke.CEISafePostInteractionWriteRejected': Compilation error: function 'callThenStoreClaimed' violates CEI (Checks-Effects-Interactions) ordering: state write after external call. Reorder state writes before external calls, or annotate with allow_post_interaction_writes / nonreentrant(<lock>) to opt out (Issue #1728 (CEI enforcement — Checks-Effects-Interactions ordering))
-/
#guard_msgs in
#check_contract CEISafePostInteractionWriteRejected

-- Roles / requires(field) smoke test (#1728, Axis 2 Step 2c)
verity_contract RolesSmoke where
  storage
    admin : Address := slot 0
    counter : Uint256 := slot 1
  roles
    adminRole := admin

  constructor (initialAdmin : Address) := do
    setStorageAddr admin initialAdmin

  -- requires(admin) auto-injects: require(caller == admin) "Access denied: caller is not admin"
  function setCounter (value : Uint256) requires(adminRole) : Unit := do
    setStorage counter value

  -- Normal function without access control
  function getCounter () : Uint256 := do
    let current ← getStorage counter
    return current

-- Mapping-keyed roles / requires(<mapping>) smoke test (verity#1837)
--
-- For role-as-mapping access control (the `onlyRelayer` / `onlyMinter`
-- pattern), the role storage is a `mapping(address => uint256)` (0/1 flag)
-- instead of a scalar Address. `requires(relayers)` then auto-injects
-- `require(storage[relayers][caller] != 0) "Access denied: caller is not relayers"`.
verity_contract RolesMappingSmoke where
  storage
    relayers : Address → Uint256 := slot 0
    counter  : Uint256 := slot 1
  roles
    relayer := relayers

  constructor (initialRelayer : Address) := do
    setMapping relayers initialRelayer 1

  -- requires(relayers) auto-injects:
  --   let sender ← msgSender
  --   let value  ← getMapping relayers sender
  --   require (value != 0) "Access denied: caller is not relayers"
  function setCounter (value : Uint256) requires(relayer) : Unit := do
    setStorage counter value

  -- Normal function without access control
  function getCounter () : Uint256 := do
    let current ← getStorage counter
    return current

-- Newtype smoke test (#1727, Axis 1 Step 3a)
-- Declares semantic newtypes that are erased to base types at EVM level
verity_contract NewtypeSmoke where
  types
    TokenId : Uint256
    Amount : Uint256
    Owner : Address
  storage
    nextTokenId : Uint256 := slot 0
    totalSupply : Uint256 := slot 1
    minter : Address := slot 2

  constructor (initialMinter : Address) := do
    setStorageAddr minter initialMinter

  -- Newtypes are erased to their base types: TokenId → Uint256, Amount → Uint256
  function mint (id : TokenId, amount : Amount) : Unit := do
    setStorage nextTokenId id
    let current ← getStorage totalSupply
    setStorage totalSupply (add current amount)

  -- Owner erases to Address
  function setMinter (newMinter : Owner) : Unit := do
    setStorageAddr minter newMinter

  function getNextTokenId () : Uint256 := do
    let current ← getStorage nextTokenId
    return current

#check_contract RolesSmoke
#check_contract RolesMappingSmoke

-- Explicit role declarations for owner/admin/minter/relayer-style policies
-- (#1894). Scalar address roles and mapping-backed roles are reported through
-- the same `spec.roles` surface and generate readable access-control facts.
verity_contract RolesDeclaredSmoke where
  storage
    owner : Address := slot 0
    admin : Address := slot 1
    minters : Address → Uint256 := slot 2
    relayers : Address → Uint256 := slot 3
    counter : Uint256 := slot 4
  roles
    ownerRole := owner
    adminRole := admin
    minterRole := minters
    relayerRole := relayers

  constructor (initialOwner : Address) := do
    setStorageAddr owner initialOwner
    setStorageAddr admin initialOwner
    setMapping minters initialOwner 1
    setMapping relayers initialOwner 1

  function setByOwner (value : Uint256) requires(ownerRole) : Unit := do
    setStorage counter value

  function setByAdmin (value : Uint256) requires(adminRole) : Unit := do
    setStorage counter value

  function mintLike (value : Uint256) requires(minterRole) : Unit := do
    setStorage counter value

  function relayLike (value : Uint256) requires(relayerRole) : Unit := do
    setStorage counter value

#check_contract RolesDeclaredSmoke

example : RolesDeclaredSmoke.spec.«roles».length = 4 := rfl
example :
    RolesDeclaredSmoke.setByOwner_model.requiresRole = some "ownerRole" ∧
      RolesDeclaredSmoke.spec.«roles».contains
        { name := "ownerRole", field := "owner",
          kind := Compiler.CompilationModel.RoleKind.scalarAddress } = true :=
  RolesDeclaredSmoke.setByOwner_access_control
example :
    RolesDeclaredSmoke.mintLike_model.requiresRole = some "minterRole" ∧
      RolesDeclaredSmoke.spec.«roles».contains
        { name := "minterRole", field := "minters",
          kind := Compiler.CompilationModel.RoleKind.mappingAddressToUint256 } = true :=
  RolesDeclaredSmoke.mintLike_access_control

/--
error: role 'badRole' uses unsupported backing field 'flag'; roles require an Address scalar field or Address→Uint256 mapping
-/
#guard_msgs in
verity_contract UnsupportedRoleShapeRejected where
  storage
    flag : Uint256 := slot 0
  roles
    badRole := flag

  function guarded () requires(badRole) : Unit := do
    pure ()

#check_contract NewtypeSmoke

-- Smoke test for newtype-TYPED storage fields (not just newtype params).
-- Verifies that setStorage/setStorageAddr/getStorage/getStorageAddr work
-- when the storage field itself is declared with a newtype type.
verity_contract NewtypeStorageSmoke where
  types
    TokenId : Uint256
    Owner : Address
  storage
    currentTokenId : TokenId := slot 0
    admin : Owner := slot 1

  constructor (initialAdmin : Owner) := do
    setStorageAddr admin initialAdmin

  function setTokenId (id : TokenId) : Unit := do
    setStorage currentTokenId id

  function getTokenId () : Uint256 := do
    let tid ← getStorage currentTokenId
    return tid

  function setAdmin (newAdmin : Owner) : Unit := do
    setStorageAddr admin newAdmin

  function getAdmin () : Address := do
    let a ← getStorageAddr admin
    return a

#check_contract NewtypeStorageSmoke

end Contracts.Smoke

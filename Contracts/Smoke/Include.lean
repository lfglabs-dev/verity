import Contracts.Common
import Compiler.CheckContract

namespace Contracts.Smoke

open Verity hiding pure bind
open Verity.EVM.Uint256

verity_mixin IncludeOwnableMixin where
  storage
    owner : Address := slot 0

  constructor (initialOwner : Address) := do
    setStorageAddr owner initialOwner

  modifier onlyOwner := do
    let sender ← msgSender
    let currentOwner ← getStorageAddr owner
    require (sender == currentOwner) "Caller is not the owner"

  function transferOwnership (newOwner : Address) with onlyOwner modifies(owner) : Unit := do
    setStorageAddr owner newOwner

verity_contract IncludeOwnedCounterHost include IncludeOwnableMixin where
  storage
    count : Uint256 := slot 1

  constructor (initialOwner : Address) IncludeOwnableMixin(initialOwner) := do
    setStorage count 0

  function increment () with onlyOwner modifies(count) : Unit := do
    let current ← getStorage count
    setStorage count (add current 1)

#check_contract IncludeOwnedCounterHost

verity_mixin IncludeNsMixinA where
  storage
    storage_namespace erc7201 "verity.mixin.A"
    flagA : Uint256 := slot 0

  constructor () := do
    setStorage flagA 1

verity_mixin IncludeNsMixinB where
  storage
    storage_namespace erc7201 "verity.mixin.B"
    flagB : Uint256 := slot 0

  constructor () := do
    setStorage flagB 2

verity_contract IncludeTwoNamespaceHost include IncludeNsMixinA, IncludeNsMixinB where
  storage
    extra : Uint256 := slot 1

  constructor IncludeNsMixinA() IncludeNsMixinB() := do
    setStorage extra 3

#check_contract IncludeTwoNamespaceHost

/--
error: include clash: slot 0 from mixin 'Contracts.Smoke.IncludeOwnableMixin' field 'owner' overlaps a host or earlier mixin slot
-/
#guard_msgs in
verity_contract IncludeSlotOverlapRejected include IncludeOwnableMixin where
  storage
    ownerDup : Address := slot 0

  constructor (initialOwner : Address) IncludeOwnableMixin(initialOwner) := do
    pure ()

/--
error: include clash: field 'owner' from mixin 'Contracts.Smoke.IncludeOwnableMixin' duplicates a host or earlier mixin field
-/
#guard_msgs in
verity_contract IncludeNameClashRejected include IncludeOwnableMixin where
  storage
    owner : Address := slot 2

  constructor (initialOwner : Address) IncludeOwnableMixin(initialOwner) := do
    pure ()

/--
error: missing mixin constructor call for 'IncludeOwnableMixin'; add `IncludeOwnableMixin(...)` to the host constructor
-/
#guard_msgs in
verity_contract IncludeMissingCtorRejected include IncludeOwnableMixin where
  storage
    count : Uint256 := slot 1

  constructor (initialOwner : Address) := do
    setStorage count 0

/--
error: duplicate mixin constructor call for 'IncludeOwnableMixin'; each included mixin may be initialized once
-/
#guard_msgs in
verity_contract IncludeDupCtorRejected include IncludeOwnableMixin where
  storage
    count : Uint256 := slot 1

  constructor (initialOwner : Address) IncludeOwnableMixin(initialOwner) IncludeOwnableMixin(initialOwner) := do
    setStorage count 0

/--
error: mixin constructor 'IncludeOwnableMixin' expects 1 argument(s), got 0
-/
#guard_msgs in
verity_contract IncludeCtorArityRejected include IncludeOwnableMixin where
  storage
    count : Uint256 := slot 1

  constructor IncludeOwnableMixin() := do
    setStorage count 0

verity_contract IncludeRenamedCtorArgHost include IncludeOwnableMixin where
  storage
    count : Uint256 := slot 1

  constructor (owner_ : Address) IncludeOwnableMixin(owner_) := do
    setStorage count 0

#check_contract IncludeRenamedCtorArgHost

verity_mixin IncludeErrorMixin where
  storage
    owner : Address := slot 0

  errors
    error NotOwner()

  constructor (initialOwner : Address) := do
    setStorageAddr owner initialOwner

  modifier onlyOwner := do
    let sender ← msgSender
    let currentOwner ← getStorageAddr owner
    requireError (sender == currentOwner) NotOwner()

  function poke () with onlyOwner : Unit := do
    pure ()

verity_contract IncludeErrorHost include IncludeErrorMixin where
  storage
    count : Uint256 := slot 1

  constructor (initialOwner : Address) IncludeErrorMixin(initialOwner) := do
    setStorage count 0

  function increment () with onlyOwner modifies(count) : Unit := do
    let current ← getStorage count
    setStorage count (add current 1)

#check_contract IncludeErrorHost

verity_mixin IncludeImmutableMixin where
  storage

  immutables
    version : Uint256 := seed

  constructor (seed : Uint256) := do
    let _ := seed
    pure ()

  function getVersion () : Uint256 := do
    return version

verity_contract IncludeImmutableHost include IncludeImmutableMixin where
  storage
    count : Uint256 := slot 1

  constructor (seed : Uint256) IncludeImmutableMixin(seed) := do
    setStorage count 0

#check_contract IncludeImmutableHost

/--
error: include clash: slot 0 from mixin 'Contracts.Smoke.IncludeImmutableMixin' immutable 'version' overlaps a host or earlier mixin slot
-/
#guard_msgs in
verity_contract IncludeImmutableSlotClashRejected include IncludeImmutableMixin where
  storage
    count : Uint256 := slot 0

  constructor (seed : Uint256) IncludeImmutableMixin(seed) := do
    setStorage count 0

verity_mixin IncludeOrderMixin where
  storage
    flag : Uint256 := slot 0

  constructor () := do
    setStorage flag 0

  modifier mixinGuard := do
    let current ← getStorage flag
    setStorage flag (add current 1)

verity_contract IncludeModifierOrderHost include IncludeOrderMixin where
  storage
    last : Uint256 := slot 1

  constructor IncludeOrderMixin() := do
    setStorage last 0

  modifier localGuard := do
    setStorage last 7

  function bump () with localGuard, mixinGuard modifies(flag, last) : Unit := do
    pure ()

#check_contract IncludeModifierOrderHost

verity_mixin IncludeHelperMixinA where
  storage
    a : Uint256 := slot 0

  constructor () := do
    setStorage a 1

  function internal helper (x : Uint256) : Uint256 := do
    return x

verity_mixin IncludeHelperMixinB where
  storage
    b : Uint256 := slot 1

  constructor () := do
    setStorage b 2

  function internal helper (x : Uint256) : Uint256 := do
    return x

/--
error: include clash: function 'helper' from mixin 'Contracts.Smoke.IncludeHelperMixinB' duplicates a host or earlier mixin function
-/
#guard_msgs in
verity_contract IncludeInternalClashRejected include IncludeHelperMixinA, IncludeHelperMixinB where
  storage

  constructor IncludeHelperMixinA() IncludeHelperMixinB() := do
    pure ()

end Contracts.Smoke

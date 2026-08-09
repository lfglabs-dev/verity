import Contracts.Common
import Compiler.CheckContract
import Contracts.Counter.Counter
import Contracts.SimpleStorage.SimpleStorage
import Contracts.Owned.Owned
import Contracts.SafeCounter.SafeCounter
import Contracts.OwnedCounter.OwnedCounter
import Contracts.Ledger.Ledger
import Contracts.Vault.Vault
import Contracts.SimpleToken.SimpleToken
import Contracts.ERC20.ERC20
import Contracts.ERC721.ERC721
import Compiler.Modules.Calls
import Compiler.Modules.Callbacks
import Compiler.Modules.Create2SSTORE2
import Compiler.Modules.ERC20
import Compiler.Modules.Oracle
import Compiler.Modules.Precompiles

namespace Contracts.Smoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math

def plusInt256Helper (a : Uint256) (b : Int256) : Uint256 :=
  if b < 0 then sub a (toUint256 (-b)) else add a (toUint256 b)

def eqWordHelper (a : Uint256) (b : Uint256) : Uint256 :=
  if a = b then 1 else 0

verity_contract ModifierInheritanceBase where
  types
    InheritedValue : Uint256
  storage
    owner : Address := slot 0

  constructor (initialOwner : Address) := do
    setStorageAddr owner initialOwner

  modifier onlyOwner := do
    let sender ← msgSender
    let currentOwner ← getStorageAddr owner
    require (sender == currentOwner) "Caller is not the owner"

  function virtual value () : Uint256 := do
    return 1

verity_contract ModifierInheritanceChild is ModifierInheritanceBase where
  storage
    counter : Uint256 := slot 1

  constructor (initialOwner : Address) ModifierInheritanceBase(initialOwner) := do
    setStorage counter 7

  function bump () with onlyOwner : Unit := do
    -- Modifier-local bindings have their own scope and may be reused here.
    let sender ← getStorage counter
    setStorage counter (sender + 1)

  -- Child signatures may use user-defined types declared by the parent.
  function setInherited (next : InheritedValue) : Unit := do
    setStorage counter next

  function override value () : Uint256 := do
    return 2

#check_contract ModifierInheritanceBase
#check_contract ModifierInheritanceChild

-- Constructor arguments are bound lexically: the parameter `owner` in the
-- parent body must not rewrite the storage-field operand with the same name.
verity_contract ConstructorHygieneBase where
  storage
    owner : Address := slot 0

  constructor (owner : Address) := do
    setStorageAddr owner owner

verity_contract ConstructorHygieneChild is ConstructorHygieneBase where
  storage

  constructor (admin : Address) ConstructorHygieneBase(admin) := do
    pure ()

#check_contract ConstructorHygieneChild

/--
error: parent constructor parameter 'owner' conflicts with a child constructor parameter; rename the child parameter
-/
#guard_msgs in
verity_contract ConstructorBindingCollisionRejected is ConstructorHygieneBase where
  storage

  constructor (owner : Address, admin : Address) ConstructorHygieneBase(admin) := do
    pure ()

-- A child with no constructor has an implicit nonpayable constructor even
-- when it runs a zero-argument payable parent initializer.
verity_contract PayableConstructorBase where
  storage

  constructor () payable := do
    pure ()

verity_contract ImplicitConstructorChild is PayableConstructorBase where
  storage

example : ImplicitConstructorChild.spec.constructor.map (·.isPayable) = some false := by
  rfl

-- Overrides may preserve or narrow payability, but may not widen it.
verity_contract NonpayableVirtualBase where
  storage

  function virtual value () : Uint256 := do
    return 1

/--
error: function 'value' cannot widen a nonpayable inherited function to payable
-/
#guard_msgs in
verity_contract PayableOverrideRejected is NonpayableVirtualBase where
  storage

  function payable override value () : Uint256 := do
    return 2

verity_contract ViewVirtualBase where
  storage

  function view virtual value () : Uint256 := do
    return 1

/--
error: function 'value' cannot weaken an inherited view function to state-mutating
-/
#guard_msgs in
verity_contract ViewOverrideRejected is ViewVirtualBase where
  storage

  function override value () : Uint256 := do
    return 2

verity_contract PureVirtualBase where
  storage

  function pure virtual value () : Uint256 := do
    return 1

/--
error: function 'value' cannot weaken an inherited pure function
-/
#guard_msgs in
verity_contract PureOverrideRejected is PureVirtualBase where
  storage

  function view override value () : Uint256 := do
    return 2

-- Overloads introduced on opposite sides of the inheritance boundary receive
-- distinct generated Lean identifiers after flattening.
verity_contract InheritedOverloadBase where
  storage

  function inspect (value : Uint256) : Uint256 := do
    return value

verity_contract InheritedOverloadChild is InheritedOverloadBase where
  storage

  function inspect (value : Address) : Address := do
    return value

#check_contract InheritedOverloadChild

end Contracts.Smoke

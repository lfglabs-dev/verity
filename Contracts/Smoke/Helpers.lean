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

-- An intermediate override may remain virtual for a further derived contract.
verity_contract VirtualOverrideMiddle is ModifierInheritanceBase where
  storage

  constructor (initialOwner : Address) ModifierInheritanceBase(initialOwner) := do
    pure ()

  function virtual override value () : Uint256 := do
    return 2

verity_contract VirtualOverrideLeaf is VirtualOverrideMiddle where
  storage

  constructor (initialOwner : Address) VirtualOverrideMiddle(initialOwner) := do
    pure ()

  function override value () : Uint256 := do
    return 3

#check_contract VirtualOverrideMiddle
#check_contract VirtualOverrideLeaf

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

verity_contract NarrowConstructorBase where
  storage

  constructor (value : Uint8) := do
    pure ()

/--
error: parent constructor parameter 'value' expects Verity.Macro.ValueType.uint8, got Verity.Macro.ValueType.uint256
-/
#guard_msgs in
verity_contract NarrowConstructorMismatchRejected is NarrowConstructorBase where
  storage

  constructor (value : Uint256) NarrowConstructorBase(value) := do
    pure ()

/--
error: parent constructor parameter 'owner' conflicts with a child constructor parameter; rename the child parameter
-/
#guard_msgs in
verity_contract ConstructorBindingCollisionRejected is ConstructorHygieneBase where
  storage

  constructor (owner : Address, admin : Address) ConstructorHygieneBase(admin) := do
    pure ()

verity_contract AncestorConstructorBase where
  storage

  constructor (owner : Address) := do
    pure ()

verity_contract AncestorConstructorMiddle is AncestorConstructorBase where
  storage

  constructor (admin : Address) AncestorConstructorBase(admin) := do
    pure ()

/--
error: ancestor constructor binding 'owner' conflicts with a child constructor parameter; rename the child parameter
-/
#guard_msgs in
verity_contract AncestorConstructorCollisionRejected is AncestorConstructorMiddle where
  storage

  constructor (owner : Address, admin : Address) AncestorConstructorMiddle(admin) := do
    pure ()

verity_contract ConstructorLocalBase where
  storage

  constructor () := do
    let sender ← msgSender
    require (sender == sender) "sender"

/--
error: ancestor constructor binding 'sender' conflicts with a child constructor parameter; rename the child parameter
-/
#guard_msgs in
verity_contract ConstructorLocalCollisionRejected is ConstructorLocalBase where
  storage

  constructor (sender : Address) ConstructorLocalBase() := do
    pure ()

verity_contract ConstructorTupleAliasBase where
  storage

  constructor () := do
    let config_0 ← msgValue
    require (config_0 == config_0) "config"

/--
error: ancestor constructor binding 'config_0' conflicts with a child constructor parameter; rename the child parameter
-/
#guard_msgs in
verity_contract ConstructorTupleAliasCollisionRejected is ConstructorTupleAliasBase where
  storage

  constructor (config : Tuple [Uint256, Uint256]) ConstructorTupleAliasBase() := do
    pure ()

verity_contract InheritedImmutableBase where
  storage

  immutables
    deployer : Address := initialOwner

  constructor (initialOwner : Address) := do
    pure ()

verity_contract InheritedImmutableChild is InheritedImmutableBase where
  storage

  constructor (admin : Address) InheritedImmutableBase(admin) := do
    pure ()

#check_contract InheritedImmutableChild

verity_contract InheritedInterfaceBase where
  storage

  interfaces
    interface IOracle where
      function price() view returns (Uint256)
    end

verity_contract InheritedInterfaceChild is InheritedInterfaceBase where
  storage

  function read (_oracle : IOracle) : Unit := do
    pure ()

#check_contract InheritedInterfaceChild

-- Empty interfaces are valid marker types and must survive inheritance even
-- though they generate no interface-backed external declarations.
verity_contract InheritedEmptyInterfaceBase where
  storage

  interfaces
    interface IMarker where
    end

verity_contract InheritedEmptyInterfaceChild is InheritedEmptyInterfaceBase where
  storage

  function acceptMarker (_marker : IMarker) : Unit := do
    pure ()

#check_contract InheritedEmptyInterfaceChild

verity_contract InheritedTypeNameBase where
  types
    Amount : Uint256
  storage

/--
error: duplicate type name 'Amount'
-/
#guard_msgs in
verity_contract InheritedTypeNameCollisionRejected is InheritedTypeNameBase where
  types
    Amount : Address
  storage

verity_contract NamespacedFieldBase where
  storage_namespace "base"
  storage
    baseValue : Uint256 := slot 0

verity_contract NamespacedFieldChild is NamespacedFieldBase where
  storage_namespace "child"
  storage
    childValue : Uint256 := slot 0

example : NamespacedFieldChild.spec.storageNamespace =
    NamespacedFieldBase.spec.storageNamespace := by
  rfl

verity_contract EmptyNamespacedBase where
  storage_namespace "empty-base"
  storage

verity_contract NamespacedFirstChild is EmptyNamespacedBase where
  storage_namespace "first-child"
  storage
    childValue : Uint256 := slot 0

example : NamespacedFirstChild.spec.storageNamespace = some NamespacedFirstChild.storageNamespace := by
  rfl

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

/--
error: function 'value' must preserve inherited internal/external visibility
-/
#guard_msgs in
verity_contract VisibilityOverrideRejected is NonpayableVirtualBase where
  storage

  function internal override value () : Uint256 := do
    return 2

/--
error: function 'value' must preserve the inherited return type
-/
#guard_msgs in
verity_contract ReturnTypeOverrideRejected is NonpayableVirtualBase where
  storage

  function override value () : Address := do
    return zeroAddress

verity_contract ModifierParameterCollisionBase where
  storage

  modifier captureSender := do
    let sender ← msgSender
    require (sender == sender) "sender"

/--
error: modifier 'captureSender' local 'sender' conflicts with a function parameter; rename one of them
-/
#guard_msgs in
verity_contract ModifierParameterCollisionRejected is ModifierParameterCollisionBase where
  storage

  function check (sender : Address) with captureSender : Unit := do
    pure ()

verity_contract ModifierTupleAliasBase where
  storage

  modifier captureConfig := do
    let config_0 ← msgValue
    require (config_0 == config_0) "config"

/--
error: modifier 'captureConfig' local 'config_0' conflicts with a function parameter; rename one of them
-/
#guard_msgs in
verity_contract ModifierTupleAliasCollisionRejected is ModifierTupleAliasBase where
  storage

  function check (config : Tuple [Uint256, Uint256]) with captureConfig : Unit := do
    pure ()

verity_contract ModifierLoopCollisionBase where
  storage

  modifier loopSender := do
    forEach "sender" 1 (do
      require (sender == 0) "sender")

/--
error: modifier 'loopSender' local 'sender' conflicts with a function parameter; rename one of them
-/
#guard_msgs in
verity_contract ModifierLoopCollisionRejected is ModifierLoopCollisionBase where
  storage

  function check (sender : Uint256) with loopSender : Unit := do
    pure ()

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

verity_contract InheritedRoleBase where
  storage
    owner : Address := slot 0
  roles
    operator := owner

verity_contract InheritedRoleChild is InheritedRoleBase where
  storage
  roles
    auditor := owner

  function audit () requires(auditor) : Unit := do
    pure ()

#check_contract InheritedRoleChild

/--
error: modifier 'earlyExit' contains a terminating return; modifiers must only contain non-terminating precondition statements
-/
#guard_msgs in
verity_contract TerminatingModifierRejected where
  storage

  modifier earlyExit := do
    returnValues [1, 2]

  function pair () with earlyExit : Tuple [Uint256, Uint256] := do
    return (3, 4)

/--
error: cross-namespace inheritance is not supported because inherited bodies must retain the parent's lexical namespace; declare the child in the parent's namespace
-/
#guard_msgs in
verity_contract CrossNamespaceInheritanceRejected is Contracts.Counter where
  storage

/--
error: role 'operator' duplicates an inherited role
-/
#guard_msgs in
verity_contract InheritedRoleCollisionRejected is InheritedRoleBase where
  storage
    admin : Address := slot 0
  roles
    operator := admin

end Contracts.Smoke

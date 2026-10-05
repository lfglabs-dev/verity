import Contracts.Common

/-!
# Executable constructors for ordinary contracts (verity#2465, Pareto G29)

An ordinary `verity_contract` constructor now has an executable
`.constructor` definition (previously only mixins and include hosts did), so a
deployment boundary can run the generated constructor body. Constructors
whose body has no executable lowering still elaborate and keep only the
compilation-model constructor.
-/

namespace Contracts.Smoke.ConstructorExecutable

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256

verity_contract CtorExec where
  storage
    supply : Uint256 := slot 0
    minter : Address := slot 5

  constructor (initial : Uint256) := do
    let sender ← msgSender
    setStorageAddr minter sender
    setStorage supply initial

  function view minterOf () : Address := do
    let m ← getStorageAddr minter
    return m

#check (CtorExec.constructor : Uint256 → Contract Unit)

private def deployer : Address := (0x1234 : Address)

private def deployed : ContractState :=
  ((CtorExec.constructor 77).run { Verity.defaultState with sender := deployer }).getState

example : deployed.readAddrSlot 5 = deployer ∧ deployed.readSlot 0 = 77 := by
  decide +kernel

-- Tranche-shaped constructor with metadata `String` parameters (the strings
-- are accepted as executable parameters; `String` storage stays unsupported).
verity_contract CtorWithStrings where
  storage
    decimalsSlot : Uint256 := slot 0

  constructor (_name : String, _symbol : String) := do
    setStorage decimalsSlot 18

#check (CtorWithStrings.constructor : String → String → Contract Unit)

example :
    (((CtorWithStrings.constructor "AA" "AA_T").run Verity.defaultState).getState).readSlot 0 = 18 := by
  decide +kernel

end Contracts.Smoke.ConstructorExecutable

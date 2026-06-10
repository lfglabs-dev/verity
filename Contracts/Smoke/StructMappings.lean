import Contracts.Smoke.HelperCalls

namespace Contracts.Smoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math

verity_contract StructMappingSmoke where
  storage
    positions : MappingStruct(Address,[
      supplyShares @word 0 packed(0,128),
      borrowShares @word 0 packed(128,128),
      delegate @word 1
    ]) := slot 0
    approvals : MappingStruct2(Address,Address,[
      allowance @word 0 packed(0,128),
      nonce @word 1
    ]) := slot 1

  function setPosition (user : Address, supply : Uint256, borrow : Uint256, delegate_ : Address) : Unit := do
    setStructMember "positions" user "supplyShares" supply
    setStructMember "positions" user "borrowShares" borrow
    setStructMember "positions" user "delegate" delegate_

  function totalPositionShares (user : Address) : Uint256 := do
    let supply ← structMember "positions" user "supplyShares"
    let borrow ← structMember "positions" user "borrowShares"
    return (add supply borrow)

  function delegateOf (user : Address) : Address := do
    let delegate_ ← structMember "positions" user "delegate"
    return delegate_

  function setApproval (owner : Address, spender : Address, amount : Uint256, nextNonce : Uint256) : Unit := do
    setStructMember2 "approvals" owner spender "allowance" amount
    setStructMember2 "approvals" owner spender "nonce" nextNonce

  function approvalOf (owner : Address, spender : Address) : Uint256 := do
    let amount ← structMember2 "approvals" owner spender "allowance"
    return amount

  function approvalNonce (owner : Address, spender : Address) : Uint256 := do
    let nextNonce ← structMember2 "approvals" owner spender "nonce"
    return nextNonce

verity_contract UintKeyStructMappingSmoke where
  storage
    circuits : MappingStruct(Uint256,[
      verifier @word 0 packed(0,160),
      inputCount @word 0 packed(160,16),
      outputCount @word 0 packed(176,16),
      active @word 0 packed(192,8)
    ]) := slot 0

  constants
    TRUE_WORD : Uint256 := 1

  function setCircuit
      (circuitId : Uint256, verifierAddr : Address, inputCount : Uint256,
       outputCount : Uint256) : Unit := do
    setStructMember "circuits" circuitId "verifier" verifierAddr
    setStructMember "circuits" circuitId "inputCount" inputCount
    setStructMember "circuits" circuitId "outputCount" outputCount
    setStructMember "circuits" circuitId "active" TRUE_WORD

  function getCircuit
      (circuitId : Uint256) : Tuple [Address, Uint256, Uint256, Uint256] := do
    let verifierAddr ← structMember "circuits" circuitId "verifier"
    let inputCount ← structMember "circuits" circuitId "inputCount"
    let outputCount ← structMember "circuits" circuitId "outputCount"
    let active ← structMember "circuits" circuitId "active"
    return (verifierAddr, inputCount, outputCount, active)

private def _structMemberExecutableHelper :
    String → Address → String → Contract Uint256 :=
  StructMappingSmoke.structMember
private def _setStructMemberExecutableHelper :
    String → Address → String → Uint256 → Contract Unit :=
  StructMappingSmoke.setStructMember
private def _structMember2ExecutableHelper :
    String → Address → Address → String → Contract Uint256 :=
  StructMappingSmoke.structMember2
private def _setStructMember2ExecutableHelper :
    String → Address → Address → String → Uint256 → Contract Unit :=
  StructMappingSmoke.setStructMember2

end Contracts.Smoke

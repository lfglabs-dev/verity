import Contracts.Common

namespace Contracts.Smoke

open Verity hiding pure bind
open Verity.EVM.Uint256

-- ABI-frame typed-interface calls (#1982 progress): a `Bytes` argument is a forwarded
-- `Bytes` parameter or a payload built in place with `abiEncodeCall`, and a `(Bool, Bytes)`
-- return binds the flag and the returned bytes (`bytesLength`, `bytesWord`, `revertBytes`).
-- The compiled calldata is checked against Solidity's `abi.encodeCall` /
-- `abi.encodeWithSelector` in `test/InterfaceBytesCallSmoke.t.sol`.
verity_contract InterfaceBytesCallSmoke where
  storage

  interfaces
    interface IVenues where
      function counterparty(Uint8, Bytes) view returns (Address)
      function tokens(Uint8, Bytes) view returns (Tuple [Address, Address])
    end
    interface ISafe where
      function execTransactionFromModuleReturnData(Address, Uint256, Bytes, Uint8) returns (Tuple [Bool, Bytes])
      function notify(Bytes)
    end

  -- A forwarded `Bytes` parameter, on a view method with one static return.
  function reentrancy_trusted who (venues : IVenues, kind : Uint8, p : Bytes) : Address := do
    let c ← venues.counterparty kind p
    return c

  -- A view method with two static returns, destructured.
  function reentrancy_trusted tokensOf (venues : IVenues, kind : Uint8, p : Bytes) :
      Tuple [Address, Address] := do
    let (tIn, tOut) ← venues.tokens kind p
    return (tIn, tOut)

  -- A forwarded `Bytes` parameter among words; the `(Bool, Bytes)` return.
  function reentrancy_trusted forward (safe : ISafe, dest : Address, val : Uint256, data : Bytes,
      op : Uint8) : Tuple [Bool, Uint256, Uint256, Uint256] := do
    let (ok, ret) ← safe.execTransactionFromModuleReturnData dest val data op
    return (ok, bytesLength ret, bytesWord ret 0, bytesWord ret 1)

  -- A payload of static words built in place; a failed inner call reverts with its data.
  function reentrancy_trusted transferVia (safe : ISafe, token : Address, recipient : Address,
      amt : Uint256) : Uint256 := do
    let (ok, ret) ← safe.execTransactionFromModuleReturnData token 0
      (abiEncodeCall 0xa9059cbb [recipient, amt]) 0
    if !ok then
      revertBytes ret
    return bytesLength ret

  -- A payload built in place around a forwarded `Bytes` parameter.
  function reentrancy_trusted venueSwapVia (safe : ISafe, venues : Address, kind : Uint8,
      p : Bytes, amt : Uint256) : Uint256 := do
    let (ok, ret) ← safe.execTransactionFromModuleReturnData venues 0
      (abiEncodeCall 0x8c973081 [kind, p, amt]) 0
    if !ok then
      revertBytes ret
    return bytesWord ret 0

  -- A method without returns.
  function reentrancy_trusted notifyVia (safe : ISafe, data : Bytes) : Unit := do
    safe.notify data

/-! ### `abiCallBytes` is Solidity's encoding

Reference bytes from Foundry (`cast calldata`):
`cast calldata "transfer(address,uint256)" 0x…aa 5`,
`cast calldata "swap(uint8,bytes,uint256)" 2 0x0102…21 7` (and `0x`), and
`cast calldata "execTransactionFromModuleReturnData(address,uint256,bytes,uint8)" 0x…bb 0
<transfer calldata> 0`. -/

private def hexNibble (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10

/-- The bytes of a `0x…` hex string. -/
private def hexBytes (s : String) : List Nat :=
  let cs := s.toList.drop 2
  (List.range (cs.length / 2)).map fun i =>
    hexNibble (cs.getD (2 * i) '0') * 16 + hexNibble (cs.getD (2 * i + 1) '0')

private def transferCalldataHex : String :=
  "0xa9059cbb00000000000000000000000000000000000000000000000000000000000000aa" ++
  "0000000000000000000000000000000000000000000000000000000000000005"

#guard abiCallBytes 0xa9059cbb [.word 0xaa, .word 5] == hexBytes transferCalldataHex

#guard abiCallBytes 0x8c973081
    [.word 2, .bytes (byteArrayOfValues (List.range' 1 33)), .word 7] ==
  hexBytes ("0x8c973081" ++
    "0000000000000000000000000000000000000000000000000000000000000002" ++
    "0000000000000000000000000000000000000000000000000000000000000060" ++
    "0000000000000000000000000000000000000000000000000000000000000007" ++
    "0000000000000000000000000000000000000000000000000000000000000021" ++
    "0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20" ++
    "2100000000000000000000000000000000000000000000000000000000000000")

#guard abiCallBytes 0x8c973081 [.word 2, .bytes ByteArray.empty, .word 7] ==
  hexBytes ("0x8c973081" ++
    "0000000000000000000000000000000000000000000000000000000000000002" ++
    "0000000000000000000000000000000000000000000000000000000000000060" ++
    "0000000000000000000000000000000000000000000000000000000000000007" ++
    "0000000000000000000000000000000000000000000000000000000000000000")

#guard abiCallBytes 0x5229073f
    [.word 0xbb, .word 0, .bytes (abiEncodeCall 0xa9059cbb [.word 0xaa, .word 5]), .word 0] ==
  hexBytes ("0x5229073f" ++
    "00000000000000000000000000000000000000000000000000000000000000bb" ++
    "0000000000000000000000000000000000000000000000000000000000000000" ++
    "0000000000000000000000000000000000000000000000000000000000000080" ++
    "0000000000000000000000000000000000000000000000000000000000000000" ++
    "0000000000000000000000000000000000000000000000000000000000000044" ++
    "a9059cbb00000000000000000000000000000000000000000000000000000000" ++
    "000000aa00000000000000000000000000000000000000000000000000000000" ++
    "0000000500000000000000000000000000000000000000000000000000000000")

/-! ### Executables: one journal entry with the ABI bytes, answered by the adversary -/

open Compiler.CompilationModel.DenoteExternalCalls (AdversaryModel)

/-- An adversary answering every call with the ABI words of `abi.encode(flag, data)`. -/
private def boolBytesAdversary (flag : Bool) (data : List Nat) : AdversaryModel :=
  { AdversaryModel.stub with
    result := fun _ _ =>
      .success ([if flag then 1 else 0, 64, data.length] ++ abiBytesDataWords data) }

/-- An adversary answering every call with `words`. -/
private def rawAdversary (words : List Nat) : AdversaryModel :=
  { AdversaryModel.stub with result := fun _ _ => .success words }

private def forwardRun (adv : AdversaryModel) :=
  InterfaceBytesCallSmoke.forward (ExecutableCallContext.ofAdversary adv)
    (Verity.wordToAddress 0x5afe) (Verity.wordToAddress 0xbb) 7 (byteArrayOfValues [1, 2, 3]) 3
    Verity.defaultState

#guard
  match forwardRun (boolBytesAdversary true (List.range' 1 33)) with
  | .success (ok, len, w0, w1) s =>
      ok && len == 33 && w0.val == abiReadWord (List.range' 1 33) 0 &&
        w1.val == 33 * 2 ^ 248 &&
        s.calls.map (·.calldata) ==
          [abiCallBytes 0x5229073f [.word 0xbb, .word 7, .bytes (byteArrayOfValues [1, 2, 3]),
            .word 3]]
  | .revert _ _ => false

-- Malformed returndata (a flag word that is not 0/1, a length past the end) reverts.
#guard
  match forwardRun (rawAdversary [2, 64, 0]), forwardRun (rawAdversary [1, 64, 33, 0]) with
  | .revert _ _, .revert _ _ => true
  | _, _ => false

/-- The 33-byte reason of `testInnerCallFailureRevertsWithItsData`: `_pattern(33, 0xd1)`. -/
private def innerFailureReason : List Nat := (List.range 33).map fun i => (0xd1 + i) % 256

-- A failed inner call (`ok = false`) reverts through `revertBytes` with exactly the
-- returned bytes, as the compiled code does (`testInnerCallFailureRevertsWithItsData`).
#guard
  match InterfaceBytesCallSmoke.transferVia
      (ExecutableCallContext.ofAdversary (boolBytesAdversary false innerFailureReason))
      (Verity.wordToAddress 0x5afe) (Verity.wordToAddress 0x70) (Verity.wordToAddress 0xaa) 5
      Verity.defaultState with
  | .revert payload _ => payload.encode == innerFailureReason.map UInt8.ofNat
  | .success _ _ => false

-- The nested payload is journaled as Solidity's `abi.encodeWithSelector` bytes.
#guard
  match InterfaceBytesCallSmoke.venueSwapVia
      (ExecutableCallContext.ofAdversary (boolBytesAdversary true (abiWordBytes 777)))
      (Verity.wordToAddress 0x5afe) (Verity.wordToAddress 0x7e) 2
      (byteArrayOfValues (List.range' 1 33)) 9 Verity.defaultState with
  | .success w s =>
      w == 777 &&
        s.calls.map (·.calldata) ==
          [abiCallBytes 0x5229073f [.word 0x7e, .word 0,
            .bytes (byteArrayOfValues (hexBytes ("0x8c973081" ++
              "0000000000000000000000000000000000000000000000000000000000000002" ++
              "0000000000000000000000000000000000000000000000000000000000000060" ++
              "0000000000000000000000000000000000000000000000000000000000000009" ++
              "0000000000000000000000000000000000000000000000000000000000000021" ++
              "0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20" ++
              "2100000000000000000000000000000000000000000000000000000000000000"))),
            .word 0]]
  | .revert _ _ => false

end Contracts.Smoke

import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential
import Compiler.SolidityImport.Transactions

namespace SolidityImportSmoke.DynamicSelectorNamedTryEnumArrayChecks
open Compiler.CompilationModel Denote ByteExternalCall
open Compiler.CompilationModel.SolidityImport.Transactions

solidity_profile extProfile where
  evmVersion := "osaka"
  viaIR := true
  optimizerRuns := some 466
  bytecodeHash := "none"

solidity_import imported from "Contracts/SolidityImportSmoke"
  entry "DynamicSelectorNamedTryEnumArray.sol"
  using extProfile
  contract DynamicSelectorNamedTryEnumArray
  function hashSelectorDynMem(bytes4,bytes)
  function hashSelectorDynCalldata(bytes4,bytes)
  function hashSelectorMixed(bytes4,address,uint256,bool,bytes)
  function hashSelectorTwoDyn(bytes4,address,bytes,uint256,bytes)
  function namedExternalQuote(IEndpoint,uint256,bytes32)
  function namedExternalDispatch(IEndpoint,address,uint256,bytes)
  function namedTryVoid(IEndpoint,uint256,bytes32)
  function namedTryReturn(IEndpoint,uint256,bytes32)
  function emptyBytesChecks(bytes4,uint256)
  function callWithNewEmptyBytes(address,uint256)
  function sumCalldataEnumItems(«ActionItem[]»)
  function sumMemoryEnumItems(«ActionItem[]»)
  function sumBatchEnumItems(ActionBatch)
  function buildLocalEnumStructArray(address,uint128)

#guard imported.report.functions.length == 14
#guard imported.report.functions.all (·.denoteCovered)

private def oracle := SolidityImport.Differential.oracle

private def runPure (name : String) (args : List Nat) :
    Option (Bool × Option (List UInt8) × List Nat) := do
  let fn ← imported.model.functions.find? (·.name == name)
  let r := denoteFunction oracle imported.model fn
    { sender := 1, functionSelector := 0, args } Verity.defaultState
  let words := if r.returnWords.isEmpty then r.returnValue.toList else r.returnWords
  return (r.success, r.revertData, words)

private def wordBytes (n : Nat) : List UInt8 :=
  (List.range 32).reverse.map fun i => UInt8.ofNat ((n / (256 ^ i)) % 256)

private def calldataWord (calldata : List UInt8) (offset : Nat) : Nat :=
  (List.range 32).foldl (fun acc lane => acc * 256 + (calldata.getD (offset + lane) 0).toNat) 0

private def goodEp : Nat := 0xa1
private def failEp : Nat := 0xb2

private def outcome (request : Request) : Except (List UInt8) (List UInt8) :=
  if request.target == goodEp then
    -- quote(uint256 amount, bytes32 tag) returns amount * 10 + tag (verifies positional reorder!)
    if request.calldata.length == 68 then
      let amt := calldataWord request.calldata 4
      let tag := calldataWord request.calldata 36
      .ok (wordBytes (amt * 10 + tag))
    else
      .ok []
  else if request.target == failEp then
    .error [0xde, 0xad]
  else
    .ok []

private def env : ByteCallEnvironment :=
  { gas := some 1000000
    adversary := some
      { respond := fun request world => match outcome request with
          | .ok data => .success world data []
          | .error data => .revert data []
        valid := by
          intro request world
          cases outcome request <;> simp [Response.valid] } }

private def observe (name : String) (args : List Nat) : Option (Bool × List UInt8 × Nat) := do
  let fn ← imported.model.functions.find? (·.name == name)
  let tx : DenoteTransaction := { sender := 0x5e, thisAddress := 0xc0de, functionSelector := 0, args }
  let world := [goodEp, failEp].foldl
    (fun world account => world.writeAccount (Verity.Core.Address.ofNat account) { code := [0] })
    (withTransactionContext Verity.defaultState tx)
  let bindings ← bindExternalParams 0 fn.bindingParams args
  match executeBody oracle (effectiveFields imported.model) world
      bindings fn.body imported.model.errors env with
  | .ok r => some (r.success, r.data, (r.world.readSlot 0).val)
  | .error _ => none

-- R3: `abi.encodeWithSelector` with dynamic `bytes memory` and `bytes calldata` produce identical hashes.
-- sel = 0x11223344 (left-aligned in bytes4 word), payload = 3 bytes 0xaabbcc
private def selWord : Nat := 0x11223344 * (2 ^ 224)
private def payloadWord : Nat := 0xaabbcc * (2 ^ 232)

#guard
  match runPure "hashSelectorDynMem" [selWord, 64, 3, payloadWord],
        runPure "hashSelectorDynCalldata" [selWord, 64, 3, payloadWord] with
  | some (true, none, [h1]), some (true, none, [h2]) => h1 != 0 && h1 == h2
  | _, _ => false

-- Mixed static + dynamic `bytes memory` and two dynamic `bytes` arguments succeed with non-zero hash.
#guard
  match runPure "hashSelectorMixed" [selWord, 0x1234, 99, 1, 160, 3, payloadWord] with
  | some (true, none, [h]) => h != 0
  | _ => false

#guard
  match runPure "hashSelectorTwoDyn" [selWord, 0x1234, 160, 99, 224, 3, payloadWord, 2, 0xffee * (2 ^ 240)] with
  | some (true, none, [h]) => h != 0
  | _ => false

-- R5: Named arguments on ordinary typed external calls & external try calls (verifying argument reorder!).
-- quote(amount=5, tag=2) = 52; quote(amount=6, tag=2) = 62 -> 52 + 62 = 114
#guard observe "namedExternalQuote" [goodEp, 5, 2] == some (true, wordBytes 114, 0)
-- Checked arithmetic overflow in reordered named arg `amount: x + 1` panics with Panic(0x11).
#guard observe "namedExternalQuote" [goodEp, 2^256 - 1, 2] == some (false, panicBytes 0x11, 0)
-- Named external dispatch with dynamic bytes argument reordered succeeds.
#guard observe "namedExternalDispatch" [goodEp, 0x1234, 7, 128, 3, payloadWord] == some (true, [], 0)
-- Named external try (void): succeeds on goodEp (lastCount=1, returns 1), catches on failEp (lastCount=0, returns 0).
#guard observe "namedTryVoid" [goodEp, 5, 2] == some (true, wordBytes 1, 1)
#guard observe "namedTryVoid" [failEp, 5, 2] == some (true, wordBytes 0, 0)
-- Named external try (value-returning): returns (5*10 + 2) + 7 = 59 on goodEp, 999 on failEp.
#guard observe "namedTryReturn" [goodEp, 5, 2] == some (true, wordBytes 59, 0)
#guard observe "namedTryReturn" [failEp, 5, 2] == some (true, wordBytes 999, 0)

-- R6-A: `new bytes(0)` produces empty bytes (len = 0, same keccak256 as empty bytes) and works in low-level call.
private def emptyKeccak : Nat :=
  0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470

#guard
  match runPure "emptyBytesChecks" [selWord, 42] with
  | some (true, none, [hEmpty, hEnc, hSel, len]) =>
      hEmpty == emptyKeccak && hEnc != 0 && hSel != 0 && len == 0
  | _ => false

#guard observe "callWithNewEmptyBytes" [goodEp, 0] == some (true, wordBytes 1, 0)
#guard observe "callWithNewEmptyBytes" [failEp, 0] == some (true, wordBytes 0, 0)

-- R6-B: `enum` fields inside `Struct[]` ABI schemas (`calldata`, `memory`, nested dynamic struct, local `new Struct[](n)`).
-- ActionItem has 4 words: (kind: 0..2, asset: address, amount: uint128, active: bool)
-- 2 items: (kind=1, asset=0x10, amt=100, active=1) and (kind=2, asset=0x20, amt=250, active=1)
#guard runPure "sumCalldataEnumItems" [32, 2, 1, 0x10, 100, 1, 2, 0x20, 250, 1] ==
  some (true, none, [350, 3])
#guard runPure "sumMemoryEnumItems" [32, 2, 1, 0x10, 100, 1, 2, 0x20, 250, 1] ==
  some (true, none, [350, 3])
-- Out-of-range enum ordinal (= 3 >= 3) reverts empty on both calldata and memory Struct[]!
#guard runPure "sumCalldataEnumItems" [32, 1, 3, 0x10, 100, 1] ==
  some (false, some [], [])
#guard runPure "sumMemoryEnumItems" [32, 1, 3, 0x10, 100, 1] ==
  some (false, some [], [])

-- Nested dynamic struct `ActionBatch { ActionItem[] items; bytes note; }`:
-- root offset=32; tuple head: [items_off=64, note_off=224]; items: len=1, [2, 0x10, 50, 1]; note: len=3, payloadWord
#guard runPure "sumBatchEnumItems" [32, 64, 224, 1, 2, 0x10, 50, 1, 3, payloadWord] ==
  some (true, none, [250, 3])
-- Out-of-range enum ordinal inside nested ActionBatch.items reverts empty.
#guard runPure "sumBatchEnumItems" [32, 64, 224, 1, 3, 0x10, 50, 1, 3, payloadWord] ==
  some (false, some [], [])

-- Local `new ActionItem[](2)` with enum constructors: Deposit(0) + Rebalance(2)*10 + (100+5) = 125.
#guard runPure "buildLocalEnumStructArray" [0x1234, 100] == some (true, none, [125])

end SolidityImportSmoke.DynamicSelectorNamedTryEnumArrayChecks

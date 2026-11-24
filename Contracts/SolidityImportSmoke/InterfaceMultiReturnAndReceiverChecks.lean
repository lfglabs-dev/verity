import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential
import Verity.Core.Model.DenoteByteExternalCalls

namespace SolidityImportSmoke.InterfaceMultiReturnAndReceiverChecks
open Compiler.CompilationModel Denote DenoteByteExternalCalls ByteExternalCall

solidity_profile callProfile where
  evmVersion := "osaka"
  viaIR := true
  optimizerRuns := some 466
  bytecodeHash := "none"

solidity_import imported from "Contracts/SolidityImportSmoke" entry "InterfaceMultiReturnAndReceiver.sol"
  using callProfile
  contract InterfaceMultiReturnAndReceiver
  function configure(address,uint256,address,address)
  function readStatusDecl(address)
  function readStatusAssign(address)
  function readStatusDirect(address)
  function readStatusElided(address)
  function readStatusDiscarded(address)
  function readQuote(address,uint256)
  function probeViaHelper(uint256,uint256)
  function probeViaFactory(address,uint256,uint256)
  function probeViaState(uint256)
  function probeViaConditional(bool,uint256,uint256)
  function statusViaHelper(uint256)

private def oracle := SolidityImport.Differential.oracle

private def wordBytes (w : Nat) : List UInt8 :=
  (List.range 32).map fun i => UInt8.ofNat ((w / (2 ^ (8 * (31 - i)))) % 256)

private def srcGood : Nat := 0x1001
private def srcDirtyBool : Nat := 0x1002
private def srcShort63 : Nat := 0x1003
private def srcExtra96 : Nat := 0x1004
private def srcReverts : Nat := 0x1005
private def srcEmpty : Nat := 0x1006
private def srcQuoteGood : Nat := 0x1007
private def srcQuoteDirtyU16 : Nat := 0x1008
private def srcQuoteDirtyAddr : Nat := 0x1009
private def targetA : Nat := 0x2001
private def targetB : Nat := 0x2002
private def factoryGood : Nat := 0x3001
private def factoryDirtyAddr : Nat := 0x3002

private def customRevert : List UInt8 := [0xde, 0xad, 0xbe, 0xef]

private def calldataArg0 (calldata : List UInt8) : Nat :=
  (List.range 32).foldl (fun acc i => acc * 256 + (calldata.getD (4 + i) 0).toNat) 0

private def mockCalls : ByteCallEnvironment :=
  { gas := some 30000000
    adversary := some { (staticAdversary fun req _world =>
      if req.kind != .staticcall || req.value != 0 then (false, [], [])
      else if req.target == srcGood then
        (true, wordBytes 42 ++ wordBytes 1, [])
      else if req.target == srcDirtyBool then
        (true, wordBytes 42 ++ wordBytes 2, [])
      else if req.target == srcShort63 then
        (true, (wordBytes 42 ++ wordBytes 1).take 63, [])
      else if req.target == srcExtra96 then
        (true, wordBytes 99 ++ wordBytes 0 ++ wordBytes 777, [])
      else if req.target == srcReverts then
        (false, customRevert, [])
      else if req.target == srcQuoteGood then
        let id := calldataArg0 req.calldata
        (true, wordBytes (id + 100) ++ wordBytes 1 ++ wordBytes targetA, [])
      else if req.target == srcQuoteDirtyU16 then
        (true, wordBytes 0x10000 ++ wordBytes 1 ++ wordBytes targetA, [])
      else if req.target == srcQuoteDirtyAddr then
        (true, wordBytes 5 ++ wordBytes 1 ++ wordBytes (2 ^ 160 + 3), [])
      else if req.target == targetA then
        (true, wordBytes (calldataArg0 req.calldata * 3 + 1), [])
      else if req.target == targetB then
        (true, wordBytes (calldataArg0 req.calldata * 5 + 2), [])
      else if req.target == factoryGood then
        let id := calldataArg0 req.calldata
        (true, wordBytes (if id == 1 then targetA else targetB), [])
      else if req.target == factoryDirtyAddr then
        (true, wordBytes (2 ^ 160 + targetA), [])
      else (true, [], [])) with
        accepts := fun req world =>
          req.kind == .staticcall && req.value == 0 && req.target != world.thisAddress.val } }

private def configuredWorld : Verity.ContractState :=
  ((Verity.defaultState.writePhysicalSlot 3 (.ofNat targetA)).writePhysicalSlot
    (oracle.mappingSlot 4 7) (.ofNat targetB)).writePhysicalSlot
    (oracle.mappingSlot 5 7) (.ofNat srcGood)

private def run (name : String) (args : List Nat) (world := configuredWorld) :
    Option (Bool × Option (List UInt8) × List Nat) := do
  let fn ← imported.model.functions.find? (·.name == name)
  let r := denoteFunction oracle imported.model fn
    { sender := 1, functionSelector := 0, args } world (byteCalls := mockCalls)
  let words := if r.returnWords.isEmpty then r.returnValue.toList else r.returnWords
  return (r.success, r.revertData, words)

-- Multi-return `(uint256, bool)` across declaration, assignment, direct return, elided, discarded.
#guard run "readStatusDecl" [srcGood] == some (true, none, [42, 1])
#guard run "readStatusAssign" [srcGood] == some (true, none, [42, 1])
#guard run "readStatusDirect" [srcGood] == some (true, none, [42, 1])
#guard run "readStatusElided" [srcGood] == some (true, none, [42])
#guard run "readStatusDiscarded" [srcGood] == some (true, none, [7])
#guard run "readStatusDirect" [srcExtra96] == some (true, none, [99, 0])

-- Exact Solidity ABI validation on multi-return staticcalls:
-- dirty bool (= 2), short returndata (< 64 bytes), empty account, and revert-data forwarding.
#guard run "readStatusDecl" [srcDirtyBool] == some (false, some [], [])
#guard run "readStatusElided" [srcDirtyBool] == some (false, some [], [])
#guard run "readStatusDiscarded" [srcDirtyBool] == some (false, some [], [])
#guard run "readStatusDecl" [srcShort63] == some (false, some [], [])
#guard run "readStatusDecl" [srcEmpty] == some (false, some [], [])
#guard run "readStatusDecl" [srcReverts] == some (false, some customRevert, [])

-- 3-tuple `(uint16, bool, address)` with arguments and per-word ABI bounds.
#guard run "readQuote" [srcQuoteGood, 5] == some (true, none, [105, 1, targetA])
#guard run "readQuote" [srcQuoteDirtyU16, 5] == some (false, some [], [])
#guard run "readQuote" [srcQuoteDirtyAddr, 5] == some (false, some [], [])

-- General receiver expressions: internal helper, chained interface call, state var, conditional.
#guard run "probeViaHelper" [7, 10] == some (true, none, [52])
#guard run "probeViaFactory" [factoryGood, 1, 10] == some (true, none, [31])
#guard run "probeViaFactory" [factoryGood, 2, 10] == some (true, none, [52])
#guard run "probeViaFactory" [factoryDirtyAddr, 1, 10] == some (false, some [], [])
#guard run "probeViaState" [10] == some (true, none, [31])
#guard run "probeViaConditional" [1, 7, 10] == some (true, none, [31])
#guard run "probeViaConditional" [0, 7, 10] == some (true, none, [52])
#guard run "statusViaHelper" [7] == some (true, none, [42, 1])

end SolidityImportSmoke.InterfaceMultiReturnAndReceiverChecks

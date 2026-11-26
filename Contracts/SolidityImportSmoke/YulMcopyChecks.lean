import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Transactions

/-!
Yul `mcopy(dst, src, size)` outside the modeled shape (`YulMcopy.sol`).

The model's memory agrees with the EVM's only on the scratch bytes below 0x40 that the same Yul
block wrote on every path, so only a literal copy inside those words, from such bytes, lowers to
word loads and stores (`YulMcopySequence`); a zero size copies nothing. Every other shape is a
located rejection.
-/
namespace SolidityImportSmoke.YulMcopyChecks

solidity_profile yulMcopy where
  evmVersion := "osaka"
  viaIR := true
  optimizerRuns := some 466
  bytecodeHash := "none"

-- No `mstore` before the copy: the source scratch word holds whatever the Solidity code left there.
/--
error: YulMcopy.sol:7:13: YulFunctionCall: [solidity-import:unsupported] Yul mcopy is supported only for a zero size, or a literal range inside the scratch words below 0x40 whose source bytes this Yul block wrote on every path
closure: YulMcopy.unwrittenSource
mcopy(0x20, 0x00, 0x20)
-/
#guard_msgs in
solidity_import unwrittenForm from "Contracts/SolidityImportSmoke" entry "YulMcopy.sol"
  using yulMcopy
  contract YulMcopy
  function unwrittenSource(uint256)

-- A size only known at run time.
/--
error: YulMcopy.sol:14:13: YulFunctionCall: [solidity-import:unsupported] Yul mcopy is supported only for a zero size, or a literal range inside the scratch words below 0x40 whose source bytes this Yul block wrote on every path
closure: YulMcopy.sizedCopy
mcopy(0x20, 0x00, n)
-/
#guard_msgs in
solidity_import sizedForm from "Contracts/SolidityImportSmoke" entry "YulMcopy.sol"
  using yulMcopy
  contract YulMcopy
  function sizedCopy(uint256)

-- The destination runs past the scratch words into the free-memory pointer.
/--
error: YulMcopy.sol:21:13: YulFunctionCall: [solidity-import:unsupported] Yul mcopy is supported only for a zero size, or a literal range inside the scratch words below 0x40 whose source bytes this Yul block wrote on every path
closure: YulMcopy.freePointerDestination
mcopy(0x30, 0x00, 0x20)
-/
#guard_msgs in
solidity_import freePointerDestinationForm from "Contracts/SolidityImportSmoke" entry "YulMcopy.sol"
  using yulMcopy
  contract YulMcopy
  function freePointerDestination(uint256)

-- Every source byte was written, but the range runs past the scratch words into the restored
-- free-memory pointer: solc's pointer, not the model's.
/--
error: YulMcopy.sol:31:13: YulFunctionCall: [solidity-import:unsupported] Yul mcopy is supported only for a zero size, or a literal range inside the scratch words below 0x40 whose source bytes this Yul block wrote on every path
closure: YulMcopy.freePointerSource
mcopy(0x00, 0x20, 0x40)
-/
#guard_msgs in
solidity_import freePointerSourceForm from "Contracts/SolidityImportSmoke" entry "YulMcopy.sol"
  using yulMcopy
  contract YulMcopy
  function freePointerSource(uint256)

-- The source runs from written scratch bytes into the unwritten second scratch word.
/--
error: YulMcopy.sol:38:13: YulFunctionCall: [solidity-import:unsupported] Yul mcopy is supported only for a zero size, or a literal range inside the scratch words below 0x40 whose source bytes this Yul block wrote on every path
closure: YulMcopy.partlyWrittenSource
mcopy(0x00, 0x10, 0x20)
-/
#guard_msgs in
solidity_import partlyWrittenForm from "Contracts/SolidityImportSmoke" entry "YulMcopy.sol"
  using yulMcopy
  contract YulMcopy
  function partlyWrittenSource(uint256)

-- A copy between `bytes memory` payloads whose destination is not proved large enough.
/--
error: YulMcopy.sol:44:13: YulFunctionCall: [solidity-import:unsupported] Yul mcopy between byte buffers requires the copied range to be bounded by both buffers' lengths
closure: YulMcopy.bufferCopy
mcopy(add(target, 0x20), add(source, 0x20), mload(source))
-/
#guard_msgs in
solidity_import bufferForm from "Contracts/SolidityImportSmoke" entry "YulMcopy.sol"
  using yulMcopy
  contract YulMcopy
  function bufferCopy(bytes,bytes)

-- Destination is an arbitrary scalar pointer rather than a modelled byte-buffer payload.
/--
error: YulMcopy.sol:51:13: YulFunctionCall: [solidity-import:unsupported] Yul mcopy with a byte buffer requires both destination and source to be byte-buffer payload addresses (at least 0x20 past the buffer pointer)
closure: YulMcopy.unknownDestinationPointer
mcopy(ptr, add(source, 0x20), 4)
-/
#guard_msgs in
solidity_import unknownDstForm from "Contracts/SolidityImportSmoke" entry "YulMcopy.sol"
  using yulMcopy
  contract YulMcopy
  function unknownDestinationPointer(uint256,bytes)

-- Source is an arbitrary scalar pointer rather than a modelled byte-buffer payload.
/--
error: YulMcopy.sol:58:13: YulFunctionCall: [solidity-import:unsupported] Yul mcopy with a byte buffer requires both destination and source to be byte-buffer payload addresses (at least 0x20 past the buffer pointer)
closure: YulMcopy.unknownSourcePointer
mcopy(add(target, 0x20), ptr, 4)
-/
#guard_msgs in
solidity_import unknownSrcForm from "Contracts/SolidityImportSmoke" entry "YulMcopy.sol"
  using yulMcopy
  contract YulMcopy
  function unknownSourcePointer(bytes,uint256)

-- Destination starts below `add(target, 0x20)` (overwriting the buffer length header).
/--
error: YulMcopy.sol:65:13: YulFunctionCall: [solidity-import:unsupported] Yul mcopy with a byte buffer requires both destination and source to be byte-buffer payload addresses (at least 0x20 past the buffer pointer)
closure: YulMcopy.headerDestination
mcopy(add(target, 0x10), add(source, 0x20), 4)
-/
#guard_msgs in
solidity_import headerDstForm from "Contracts/SolidityImportSmoke" entry "YulMcopy.sol"
  using yulMcopy
  contract YulMcopy
  function headerDestination(bytes,bytes)

-- Destination offset `4 + n` can run two bytes past `out.length == n + 2`.
/--
error: YulMcopy.sol:73:13: YulFunctionCall: [solidity-import:unsupported] Yul mcopy between byte buffers requires the copied range to be bounded by both buffers' lengths
closure: YulMcopy.pastEndDestination
mcopy(add(out, 0x24), add(source, 0x20), n)
-/
#guard_msgs in
solidity_import pastEndDstForm from "Contracts/SolidityImportSmoke" entry "YulMcopy.sol"
  using yulMcopy
  contract YulMcopy
  function pastEndDestination(bytes,uint256)

-- `off + len <= target.length` inside `unchecked` can wrap modulo `2^256`.
/--
error: YulMcopy.sol:88:13: YulFunctionCall: [solidity-import:unsupported] Yul mcopy between byte buffers requires the copied range to be bounded by both buffers' lengths
closure: YulMcopy.uncheckedWrapGuard
mcopy(dst, add(source, 0x20), len)
-/
#guard_msgs in
solidity_import uncheckedWrapForm from "Contracts/SolidityImportSmoke" entry "YulMcopy.sol"
  using yulMcopy
  contract YulMcopy
  function uncheckedWrapGuard(bytes,bytes,uint256,uint256)

-- A Yul cursor over a byte buffer may not leak as a scalar word.
/--
error: YulMcopy.sol:95:18: YulIdentifier: [solidity-import:unsupported] Yul byte-buffer cursor cur may only be used in mcopy
closure: YulMcopy.escapedCursor
cur
-/
#guard_msgs in
solidity_import escapedCursorForm from "Contracts/SolidityImportSmoke" entry "YulMcopy.sol"
  using yulMcopy
  contract YulMcopy
  function escapedCursor(bytes)

-- A standalone single-arm `if (flag != 0) { len = 64; }` must not clamp `len` to boolean `1`.
/--
error: YulMcopy.sol:107:13: YulFunctionCall: [solidity-import:unsupported] Yul mcopy between byte buffers requires the copied range to be bounded by both buffers' lengths
closure: YulMcopy.singleArmIfLengthOverwrite
mcopy(add(dst, 0x20), add(src, 0x20), len)
-/
#guard_msgs in
solidity_import singleArmIfForm from "Contracts/SolidityImportSmoke" entry "YulMcopy.sol"
  using yulMcopy
  contract YulMcopy
  function singleArmIfLengthOverwrite(uint256)

-- A 32-byte `ShortStrings` allocation remains tainted through helper `if`s, `bytes` casts, and
-- local aliases.
/--
error: YulMcopy.sol:127:13: YulFunctionCall: [solidity-import:unsupported] Yul mcopy with a byte buffer requires both destination and source to be byte-buffer payload addresses (at least 0x20 past the buffer pointer)
closure: YulMcopy.branchingShortStringAlias
mcopy(add(out, 0x20), add(b2, 0x20), 64)
-/
#guard_msgs in
solidity_import branchingShortStringForm from "Contracts/SolidityImportSmoke" entry "YulMcopy.sol"
  using yulMcopy
  contract YulMcopy
  function branchingShortStringAlias(uint256,bool)

-- A 32-byte `ShortStrings` reassignment on a loop back-edge after `mcopy` is also rejected.
/--
error: YulMcopy.sol:136:17: YulFunctionCall: [solidity-import:unsupported] Yul mcopy with a byte buffer requires both destination and source to be byte-buffer payload addresses (at least 0x20 past the buffer pointer)
closure: YulMcopy.loopBackEdgeShortStringSource
mcopy(add(out, 0x20), add(cur, 0x20), 64)
-/
#guard_msgs in
solidity_import loopBackEdgeShortStringForm from "Contracts/SolidityImportSmoke" entry "YulMcopy.sol"
  using yulMcopy
  contract YulMcopy
  function loopBackEdgeShortStringSource(uint256)

-- Right-to-left Yul operand evaluation in `mcopy` and Yul buffer-cursor `let`: `staticcall`
-- sets `returndatasize() == 1` before left-hand `and(returndatasize(), 3)` offsets run.
solidity_import rtlOrderForm from "Contracts/SolidityImportSmoke" entry "YulMcopy.sol"
  using yulMcopy
  contract YulMcopy
  function rightToLeftCallOffset(address)
  function rightToLeftCursorOffset(address)

section RightToLeftOrderCheck
open Compiler.CompilationModel
open Compiler.CompilationModel.Denote
open Compiler.CompilationModel.ByteExternalCall
open Compiler.CompilationModel.SolidityImport.Transactions

def oneByteStaticResponse (_request : Request)
    (world : Verity.ContractState) : Response Verity.ContractState Verity.StorageKey :=
  .success world [0xab] []

theorem oneByteStaticResponse_valid (request : Request) (world : Verity.ContractState) :
    (oneByteStaticResponse request world).valid request world := by
  simp [oneByteStaticResponse, Response.valid]

def oneByteCalls : ByteCallEnvironment :=
  { gas := some 100000
    adversary := some
      { respond := oneByteStaticResponse, valid := oneByteStaticResponse_valid } }

def rtlOracle : DenoteOracle :=
  { mappingSlot := fun _ _ => 0, keccakMemorySlice := fun _ _ _ => 0 }

def runRtlSpec (idx : Nat) : Option (Bool × List UInt8) := do
  let fn ← rtlOrderForm.model.functions[idx]?
  let p ← fn.params[0]?
  match executeBody rtlOracle rtlOrderForm.model.fields Verity.defaultState
      [(p.name, 0xbeef)] fn.body (byteCalls := oneByteCalls) with
  | .ok res => some (res.success, res.data.take 3)
  | .error _ => none

#guard runRtlSpec 0 == some (true, [0x00, 0xff, 0x00])
#guard runRtlSpec 1 == some (true, [0x00, 0x00, 0xa5])
end RightToLeftOrderCheck

-- Calling an inline-assembly storage-pointer helper multiple times in one root must not leak
-- `yulDeclaredNames` across helper calls.
solidity_import repeatedStoragePtrForm from "Contracts/SolidityImportSmoke" entry "YulMcopy.sol"
  using yulMcopy
  contract YulMcopyStateful
  function repeatedStoragePointerHelper()

-- `mcopy` overwriting a `create2` initcode template through a pointer alias is rejected.
/--
error: YulMcopy.sol:196:32: YulFunctionCall: [solidity-import:unsupported] create2 initcode must start with a checked deployment-prefix literal
closure: YulMcopyStateful.create2ClobberedViaAlias
add(code, 0x20)
-/
#guard_msgs in
solidity_import create2AliasForm from "Contracts/SolidityImportSmoke" entry "YulMcopy.sol"
  using yulMcopy
  contract YulMcopyStateful
  function create2ClobberedViaAlias(bytes32)

-- `mcopy` overwriting a `create2` initcode template on a loop back-edge after `create2` is rejected.
/--
error: YulMcopy.sol:205:36: YulFunctionCall: [solidity-import:unsupported] create2 initcode must start with a checked deployment-prefix literal
closure: YulMcopyStateful.create2ClobberedViaLoop
add(code, 0x20)
-/
#guard_msgs in
solidity_import create2LoopForm from "Contracts/SolidityImportSmoke" entry "YulMcopy.sol"
  using yulMcopy
  contract YulMcopyStateful
  function create2ClobberedViaLoop(bytes32)

-- `mcopy` overwriting a `create2` initcode template through an inlined helper parameter is rejected.
/--
error: YulMcopy.sol:215:32: YulFunctionCall: [solidity-import:unsupported] create2 initcode must start with a checked deployment-prefix literal
closure: YulMcopyStateful.create2ClobberedViaHelper
add(code, 0x20)
-/
#guard_msgs in
solidity_import create2HelperForm from "Contracts/SolidityImportSmoke" entry "YulMcopy.sol"
  using yulMcopy
  contract YulMcopyStateful
  function create2ClobberedViaHelper(bytes32)

end SolidityImportSmoke.YulMcopyChecks

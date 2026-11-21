import Compiler.SolidityImport.Import

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

-- The source runs past the scratch words into the free-memory pointer, solc's and not the model's.
/--
error: YulMcopy.sol:28:13: YulFunctionCall: [solidity-import:unsupported] Yul mcopy is supported only for a zero size, or a literal range inside the scratch words below 0x40 whose source bytes this Yul block wrote on every path
closure: YulMcopy.freePointerSource
mcopy(0x00, 0x20, 0x40)
-/
#guard_msgs in
solidity_import freePointerSourceForm from "Contracts/SolidityImportSmoke" entry "YulMcopy.sol"
  using yulMcopy
  contract YulMcopy
  function freePointerSource(uint256)

-- A copy between `bytes memory` payloads: heap addresses the model allocates differently (#2620).
/--
error: YulMcopy.sol:34:13: YulFunctionCall: [solidity-import:unsupported] Yul mcopy is supported only for a zero size, or a literal range inside the scratch words below 0x40 whose source bytes this Yul block wrote on every path
closure: YulMcopy.bufferCopy
mcopy(add(target, 0x20), add(source, 0x20), mload(source))
-/
#guard_msgs in
solidity_import bufferForm from "Contracts/SolidityImportSmoke" entry "YulMcopy.sol"
  using yulMcopy
  contract YulMcopy
  function bufferCopy(bytes,bytes)

end SolidityImportSmoke.YulMcopyChecks

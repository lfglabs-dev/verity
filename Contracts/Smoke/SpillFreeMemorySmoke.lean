import Contracts.Common

namespace Contracts.Smoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256

-- More than `defaultMaxStackLocals` live locals force stack spilling to the fixed spill
-- area; the bytes payload is copied to free memory before the call. The spilled locals
-- must survive a payload larger than the gap between the free pointer and the spill area
-- (`test/SpillFreeMemorySmoke.t.sol`).
verity_contract SpillFreeMemorySmoke where
  storage

  function reentrancy_trusted forwardAndSum (target : Address, a : Uint256, b : Uint256,
      c : Uint256, data : Bytes) : Uint256 := do
    let s1 := add a b
    let s2 := add s1 c
    let s3 := add s2 a
    let s4 := add s3 b
    let s5 := add s4 c
    let s6 := add s5 a
    let s7 := add s6 b
    let s8 := add s7 c
    let s9 := add s8 a
    let s10 := add s9 b
    let s11 := add s10 c
    let s12 := add s11 a
    let s13 := add s12 b
    ecmDo (Compiler.Modules.Calls.callWithValueBytesModule "data") [addressToWord target, 0]
    return add s13 (add s1 (add s5 s9))

end Contracts.Smoke

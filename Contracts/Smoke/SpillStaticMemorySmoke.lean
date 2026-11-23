import Contracts.Common

namespace Contracts.Smoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256

-- Functions with more than `defaultMaxStackLocals` locals whose early locals stay live to the
-- end, in a contract whose runtime code touches memory only at literal addresses below the
-- spill words. The runtime section passes the static memory gate, so the CLI compile spills
-- long-lived locals to fixed words from 4096; two dispatch cases share those words
-- (`test/SpillStaticMemorySmoke.t.sol`).
verity_contract SpillStaticMemorySmoke where
  storage
    last : Uint256 := slot 0

  function addChain (a : Uint256, b : Uint256, c : Uint256) : Uint256 := do
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
    setStorage last s13
    return add s13 (add s1 (add s5 s9))

  function xorChain (a : Uint256, b : Uint256, c : Uint256) : Uint256 := do
    let x1 := bitXor a b
    let x2 := add x1 c
    let x3 := bitXor x2 a
    let x4 := add x3 b
    let x5 := bitXor x4 c
    let x6 := add x5 a
    let x7 := bitXor x6 b
    let x8 := add x7 c
    let x9 := bitXor x8 a
    let x10 := add x9 b
    let x11 := bitXor x10 c
    let x12 := add x11 a
    let x13 := bitXor x12 b
    setStorage last x13
    return add x13 (add x1 (add x5 x9))

end Contracts.Smoke

import Contracts.Common

namespace Contracts.Smoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256

-- `copyBytes`/`bytesLength` and `keccak256` over memory: the EDSL hashes the same bytes
-- the compiled code copies from calldata (`test/MemoryHashSmoke.t.sol`).
verity_contract MemoryHashSmoke where
  storage

  function hashBytes (data : Bytes) local_obligations [bytes_hash_scratch := assumed "copies a bytes argument to memory at 0 to hash it"] : Uint256 := do
    copyBytes data 0
    let digest := keccak256 0 (bytesLength data)
    return digest

  function hashWords (a : Uint256, b : Uint256) local_obligations [words_hash_scratch := assumed "writes abi.encode(a, b) to scratch memory at 0 to hash it"] : Uint256 := do
    mstore 0 a
    mstore 32 b
    let digest := keccak256 0 64
    return digest

/-- `copyBytes` + `keccak256` hash a bytes argument as the EVM does: keccak256("abc"). -/
def hashBytesExecutableMatchesKeccak : Bool :=
  match MemoryHashSmoke.hashBytes "abc".toUTF8 Verity.defaultState with
  | .success digest _ =>
      digest.val == 0x4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45
  | .revert _ _ => false

example : hashBytesExecutableMatchesKeccak = true := by native_decide

end Contracts.Smoke

/-
  Contracts.Smoke.KeccakStringSmoke: end-to-end coverage for the
  macro-time `keccakString` literal sugar (#1973).

  Verifies that the digest emitted by the macro matches the published
  Keccak-256 test vector for the empty string, and that it can be used
  inside a `verity_contract` `constants` block to materialise a stable
  Uint256 (e.g. EIP-712 type-hash style constants) without storage reads
  and without per-call runtime hashing.
-/
import Contracts.Common

namespace Contracts.Smoke

open Verity hiding pure bind
open Verity.EVM.Uint256

-- Direct macro use in term position.
example :
    (keccakString "").val =
      0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470 := by
  native_decide

example :
    (keccakString "ERC4337").val =
      KeccakEngine.keccak256_str_nat "ERC4337" := by
  native_decide

-- Macro must agree with the equivalent ordinary Lean def on string literals.
example :
    keccakString "EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)" =
      Verity.keccak256_lit
        "EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)" := by
  native_decide

-- Use inside a `verity_contract constants` block: read the constant back
-- and check it equals the macro-time digest.
verity_contract KeccakStringConstantSmoke where
  storage
  constants
    DOMAIN_HASH : Uint256 := keccakString "ERC4337"

  function readDomainHash () : Uint256 := do
    return DOMAIN_HASH

example :
    (KeccakStringConstantSmoke.readDomainHash.run Verity.defaultState).getValue? =
      some (keccakString "ERC4337") := by
  native_decide

-- Non-literal arguments are rejected by the parser: the `keccakString`
-- syntax form only accepts a `str` literal in its argument position
-- (declared in `Verity.Macro.Syntax` as `"keccakString " str : term`).
-- This guarantees the hash is always known statically; runtime hashing
-- of dynamic strings continues to go through the EVM `keccak256` builtin
-- in the standard way.

end Contracts.Smoke

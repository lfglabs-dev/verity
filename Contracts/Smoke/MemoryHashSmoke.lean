import Contracts.Common
import Contracts.ProofKit

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

open Contracts.ProofKit in
/-- `copyBytes` + `keccak256` hash a bytes argument as the EVM does: `hashBytes data`
returns `keccak256(data)` for every `data`. -/
theorem hashBytes_is_keccak (data : ByteArray) (s : ContractState)
    (hsize : data.size + 32 < 2 ^ 256) :
    ∃ s', MemoryHashSmoke.hashBytes data s =
      .success (Verity.Core.Uint256.ofNat (keccakBytes data.data.toList)) s' := by
  unfold MemoryHashSmoke.hashBytes
  obtain ⟨u, s1, h1⟩ : ∃ u s1, Contracts.copyBytes data 0 s = .success u s1 :=
    ⟨_, _, copyBytes_run _ _ _⟩
  rw [bind_step h1, bind_step (keccak256Live_eq _ _ _),
    keccak_after_copyBytes h1 (by simpa using hsize)]
  exact ⟨_, rfl⟩

open Contracts.ProofKit in
/-- `mstore` + `keccak256`: `hashWords a b` returns `keccak256(abi.encode(a, b))`
(`keccak_after_mstores`). -/
theorem hashWords_is_keccak (a b : Uint256) (s : ContractState) :
    ∃ s', MemoryHashSmoke.hashWords a b s =
      .success (Verity.Core.Uint256.ofNat (keccakBytes (encodeWords [a.val, b.val]))) s' := by
  unfold MemoryHashSmoke.hashWords
  obtain ⟨u0, s1, h0⟩ : ∃ u s1, Contracts.mstore 0 a s = .success u s1 := ⟨_, _, mstore_eq _ _ _⟩
  obtain ⟨u1, s2, h1⟩ : ∃ u s2, Contracts.mstore 32 b s1 = .success u s2 :=
    ⟨_, _, mstore_eq _ _ _⟩
  rw [bind_step h0, bind_step h1, bind_step (keccak256Live_eq _ _ _)]
  have hk := keccak_after_mstores 0 [a, b] (fun i => [s, s1, s2].getD i s) (fun i => 32 * i)
    (by intro i hi; simp at hi; interval_cases i <;> rfl)
    (by intro i hi; simp at hi; interval_cases i <;> assumption)
    (by norm_num)
  exact ⟨s2, by
    rw [show encodeWords [a.val, b.val] = encodeWords ([a, b].map (·.val)) from rfl, ← hk]; rfl⟩

open Contracts.ProofKit in
/-- The digest word `hashWords` returns is the Keccak-256 of `abi.encode(a, b)`, unreduced. -/
theorem hashWords_digest_val (a b : Uint256) (s : ContractState) :
    ∃ d s', MemoryHashSmoke.hashWords a b s = .success d s' ∧
      d.val = keccakBytes (encodeWords [a.val, b.val]) := by
  obtain ⟨s', h⟩ := hashWords_is_keccak a b s
  exact ⟨_, s', h, val_ofNat_keccakBytes _⟩

open Contracts.ProofKit in
/-- `hashWords` only writes memory: it keeps storage, chain id and address. -/
theorem hashWords_keepsStorage (a b : Uint256) (s s' : ContractState) (d : Uint256)
    (h : MemoryHashSmoke.hashWords a b s = .success d s') : KeepsStorage s s' := by
  obtain ⟨u0, s1, h0⟩ : ∃ u s1, Contracts.mstore 0 a s = .success u s1 := ⟨_, _, mstore_eq _ _ _⟩
  obtain ⟨u1, s2, h1⟩ : ∃ u s2, Contracts.mstore 32 b s1 = .success u s2 :=
    ⟨_, _, mstore_eq _ _ _⟩
  unfold MemoryHashSmoke.hashWords at h
  rw [bind_step h0, bind_step h1, bind_step (keccak256Live_eq _ _ _)] at h
  injection h with _ hs
  subst hs
  exact (keepsStorage_of_mstore h0).trans (keepsStorage_of_mstore h1)

end Contracts.Smoke

import Contracts.ProofKit.Memory

/-!
# Stepping through executable contract bodies

A successful run of `x >>= f` is a successful run of `x` followed by one of `f`. Proving a
property of a long `do` block is fastest forward, one bind at a time, keeping each intermediate
state a variable:

```lean
unfold MyContract.f at h
obtain ⟨n, s1, h1, h⟩ := bind_success h      -- h1 : getStorage nonce s = .success n s1
obtain ⟨hc, h⟩ := require_step h              -- hc : cond = true
rw [getStorage_eq] at h1; injection h1 with e1 hs1; subst hs1   -- learn n, s1
```

Rewriting the whole remaining block instead (`rw [...] at h`) re-elaborates it at every step and
gets slow quickly. The `*_eq` lemmas give each executable primitive's result; `mstore_ok` and
`copyBytes_ok` give the state after a memory write. `keccak_after_mstores`: `mstore`s of words at
`b, b + 32, …` then `keccak256` hash `encodeWords` of them; `keccak_after_copyBytes` does the same
for a copied byte string. Storage frames of these steps and of external calls are in
`Contracts.ProofKit.Frames`.
-/

namespace Contracts.ProofKit

open Verity

theorem bind_success {α β : Type} {x : Contract α} {f : α → Contract β} {s s' : ContractState}
    {b : β} (h : (x >>= f) s = .success b s') :
    ∃ a s1, x s = .success a s1 ∧ f a s1 = .success b s' := by
  change Verity.bind x f s = _ at h
  unfold Verity.bind at h
  cases hx : x s with
  | success a s1 => rw [hx] at h; exact ⟨a, s1, rfl, h⟩
  | «revert» _ _ => rw [hx] at h; simp at h

theorem bind_step {α β : Type} {x : Contract α} {f : α → Contract β} {s s1 : ContractState} {a : α}
    (hx : x s = .success a s1) : (x >>= f) s = f a s1 := by
  show Verity.bind x f s = _
  simp [Verity.bind, hx]

theorem require_step {β : Type} {c : Bool} {msg : String} {f : Unit → Contract β}
    {s s' : ContractState} {b : β}
    (h : (Verity.require c msg >>= f) s = .success b s') : c = true ∧ f () s = .success b s' := by
  change Verity.bind (Verity.require c msg) f s = _ at h
  unfold Verity.bind Verity.require at h
  cases c <;> simp_all

/-- A successful `require` checked its condition and left the state unchanged. -/
theorem require_success {c : Bool} {msg : String} {s s' : ContractState} {u : Unit}
    (h : Verity.require c msg s = .success u s') : c = true ∧ s' = s := by
  unfold Verity.require at h
  split at h <;> simp_all

/-! ## Results of the executable primitives -/

theorem getStorage_eq (sl : StorageSlot Uint256) (s : ContractState) :
    Verity.getStorage sl s = .success (s.storage sl.slot) s := rfl
theorem getStorageAddr_eq (sl : StorageSlot Address) (s : ContractState) :
    Verity.getStorageAddr sl s = .success (s.storageAddr sl.slot) s := rfl
theorem setStorage_eq (sl : StorageSlot Uint256) (v : Uint256) (s : ContractState) :
    Verity.setStorage sl v s = .success () (s.writeSlot sl.slot v) := rfl
theorem mloadLive_eq (o : Uint256) (s : ContractState) :
    Contracts.mloadLive o s = .success (s.memory o.val) s := rfl
theorem keccak256Live_eq (o z : Uint256) (s : ContractState) :
    Contracts.keccak256Live o z s = .success (Verity.Core.Uint256.ofNat
      (Compiler.Keccak.MemorySlice.keccak (fun a => (s.memory a).val) o.val z.val)) s := rfl
theorem create2Live_eq (v o z salt : Uint256) (s : ContractState) :
    Contracts.create2Live v o z salt s = .success (Verity.Core.Uint256.ofNat
      (Verity.Core.Model.Create2.create2Address salt (Verity.Core.Uint256.ofNat
        (Compiler.Keccak.MemorySlice.keccak (fun a => (s.memory a).val) o.val z.val))
        s.thisAddress).val) s := rfl
/-- An address widened to a word and narrowed back is unchanged. -/
@[simp] theorem wordToAddress_ofNat_val (a : Address) :
    wordToAddress (Verity.Core.Uint256.ofNat a.val) = a := by
  have h : a.val < 2 ^ 160 := a.isLt
  ext
  simp only [wordToAddress, Verity.Core.Uint256.val_ofNat, Verity.Core.Address.val_ofNat]
  show a.val % 2 ^ 256 % 2 ^ 160 = a.val
  rw [Nat.mod_eq_of_lt (show a.val < 2 ^ 256 by omega), Nat.mod_eq_of_lt h]
theorem chainid_eq (s : ContractState) : Contracts.chainid s = .success s.chainId s := rfl
theorem contractAddress_eq (s : ContractState) :
    Contracts.contractAddress s = .success s.thisAddress s := rfl
theorem msgSender_eq (s : ContractState) : Verity.msgSender s = .success s.sender s := rfl

theorem mstore_eq (o v : Uint256) (st : ContractState) :
    Contracts.mstore o v st =
      .success () { st with memory := fun k => if k = o.val then v else st.memory k } := by
  simp only [Contracts.mstore, Compiler.CompilationModel.DenoteFunctionCalls.writeMemoryWords]
  congr; funext k; split
  · cases v with | mk n hn => simp only [Verity.Core.Uint256.ofNat]; congr; exact Nat.mod_eq_of_lt hn
  · rfl

theorem mstore_ok {o v : Uint256} {s s1 : ContractState} {u : Unit}
    (h : Contracts.mstore o v s = .success u s1) :
    s1 = { s with memory := fun k => if k = o.val then v else s.memory k } := by
  rw [mstore_eq] at h; injection h with _ h; exact h.symm

theorem copyBytes_ok {data : ByteArray} {b : Uint256} {s s1 : ContractState} {u : Unit}
    (h : Contracts.copyBytes data b s = .success u s1) :
    s1 = { s with memory := copyMem data b.val s.memory } := by
  rw [copyBytes_run] at h; injection h with _ h; exact h.symm

theorem bytesLength_val (data : ByteArray) (h : data.size < 2 ^ 256) :
    (Contracts.bytesLength data).val = data.size := by
  show (Verity.Core.Uint256.ofNat data.size).val = _
  rw [Verity.Core.Uint256.val_ofNat]; exact Nat.mod_eq_of_lt h

/-- `copyBytes data b` then `keccak256(b, bytesLength data)` is `keccak256(data)`. -/
theorem keccak_after_copyBytes {data : ByteArray} {b : Uint256} {s0 s1 : ContractState} {u : Unit}
    (h0 : Contracts.copyBytes data b s0 = .success u s1) (hb : b.val + data.size + 32 < 2 ^ 256) :
    Compiler.Keccak.MemorySlice.keccak (fun a => (s1.memory a).val) b.val
        (Contracts.bytesLength data).val = keccakBytes data.data.toList := by
  rw [bytesLength_val data (by omega)]
  apply keccak_eq_keccakBytes
  rw [copyBytes_ok h0]
  exact bytesBE_copyMem data b.val s0.memory hb

/-- Offsets `b + 32 i` and `b + 32 j` differ mod `2^256` when `i < j` and `32 j < 2^256`. -/
theorem word_offsets_ne (b i j : Nat) (hij : i < j) (hj : j * 32 < 2 ^ 256) :
    (b + i * 32) % 2 ^ 256 ≠ (b + j * 32) % 2 ^ 256 := by
  intro h
  have h' : i * 32 = j * 32 := by
    have := Nat.ModEq.add_left_cancel' b h
    unfold Nat.ModEq at this
    rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hj] at this
  omega

/-- After `mstore`s of `ws[0], ws[1], …` at `off 0, off 1, …` (offsets `b + 32 i`), word `i` is
still at `off i` in every later state. -/
theorem memory_after_mstores (b : Uint256) (ws : List Uint256) (st : Nat → ContractState)
    (off : Nat → Uint256)
    (hoff : ∀ i, i < ws.length → (off i).val = (b.val + i * 32) % 2 ^ 256)
    (hstep : ∀ i (hi : i < ws.length),
      Contracts.mstore (off i) ws[i] (st i) = .success () (st (i + 1)))
    (hlen : ws.length * 32 ≤ 2 ^ 256) (i : Nat) (hi : i < ws.length) :
    ∀ j, i < j → j ≤ ws.length → (st j).memory (off i).val = ws[i] := by
  intro j
  induction j with
  | zero => intro h; omega
  | succ j ih =>
    intro hij hj
    rw [mstore_ok (hstep j (by omega))]
    by_cases hji : i = j
    · subst hji; simp
    · have hne : (off i).val ≠ (off j).val := by
        rw [hoff i hi, hoff j (by omega)]
        exact word_offsets_ne b.val i j (by omega) (by omega)
      simp only [hne, if_false]
      exact ih (by omega) (by omega)

/-- `mstore`s of `ws` at `b, b + 32, …`, then `keccak256(b, 32 * ws.length)`, hash
`abi.encode` of the words. -/
theorem keccak_after_mstores (b : Uint256) (ws : List Uint256) (st : Nat → ContractState)
    (off : Nat → Uint256)
    (hoff : ∀ i, i < ws.length → (off i).val = (b.val + i * 32) % 2 ^ 256)
    (hstep : ∀ i (hi : i < ws.length),
      Contracts.mstore (off i) ws[i] (st i) = .success () (st (i + 1)))
    (hlen : ws.length * 32 ≤ 2 ^ 256) :
    Compiler.Keccak.MemorySlice.keccak (fun a => ((st ws.length).memory a).val) b.val
        (32 * ws.length) = keccakBytes (encodeWords (ws.map (·.val))) := by
  rw [show 32 * ws.length = 32 * (ws.map (·.val)).length by simp]
  apply keccak_of_words
  intro i hi
  simp only [List.length_map] at hi
  have hmem := memory_after_mstores b ws st off hoff hstep hlen i hi ws.length hi le_rfl
  rw [show Compiler.Constants.evmModulus = 2 ^ 256 from rfl, ← hoff i hi, hmem]
  simp

end Contracts.ProofKit

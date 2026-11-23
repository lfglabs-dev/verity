import Contracts.Common
import Mathlib.Tactic

/-!
# Memory and hashing facts for the executable EDSL

`keccak256Live offset size` hashes `Compiler.Keccak.MemorySlice.bytesBE mem offset size`: the
words at `offset, offset + 32, …`, serialized big-endian and cut to `size` bytes. These lemmas say
which bytes that is after `copyBytes` and `mstore`, so a theorem can state "this hash is
`keccak256` of these bytes" (`keccakBytes`).

- `toBE n x` / `fromBE`: `n`-byte big-endian encoding of `x mod 256^n` and its inverse, with
  `toBE_append`, `toBE_concat`, `toBE_congr`, `toBE_fromBE`, `getElem_toBE`.
- `getElem_bytesBE`, `length_bytesBE`, `bytesBE_eq_flatMap`: the hashed bytes, byte by byte.
- `bytesBE_copyMem`: after `copyBytes data dest` (memory `copyMem`), the `data.size` bytes at
  `dest` are `data`, provided `dest + data.size + 32 < 2^256`.
- `bytesBE_of_words`: words written at `b, b + 32, …` read back as their concatenation.
- `keccak_eq_keccakBytes`: `MemorySlice.keccak` of a slice equals `keccakBytes` of its bytes.
- `encodeWords ws`: `abi.encode` of words; `keccak_of_words`: words at `b, b + 32, …` hash to
  `keccakBytes (encodeWords ws)`.
- `eip712_pack`: the three aligned words for `"\x19\x01" ‖ a ‖ b` read as 66 bytes are that string.
- Word arithmetic: `add_val`, `shl_val`, `shr_val`, `bitOr_val_of_lt`, `ofNat_val`,
  `val_ofNat_keccakBytes`.

Memory is word-addressed (`Nat → Uint256`, one word per byte offset written); unaligned reads and
writes are outside the model.
-/

namespace Contracts.ProofKit

/-- `n`-byte big-endian encoding of `x mod 256^n`. -/
def toBE : Nat → Nat → List UInt8
  | 0, _ => []
  | n + 1, x => toBE n (x / 256) ++ [UInt8.ofNat (x % 256)]

@[simp] theorem toBE_length (n x : Nat) : (toBE n x).length = n := by
  induction n generalizing x <;> simp [toBE, *]

theorem toBE_append (a b x : Nat) : toBE (a + b) x = toBE a (x / 256 ^ b) ++ toBE b x := by
  induction b generalizing x with
  | zero => simp [toBE]
  | succ b ih =>
    rw [show a + (b + 1) = (a + b) + 1 by omega, toBE, ih, toBE, List.append_assoc,
      Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm (256 ^ b)]

theorem toBE_congr (n : Nat) : ∀ x y, x % 256 ^ n = y % 256 ^ n → toBE n x = toBE n y := by
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro x y h
    simp only [toBE]
    have hd : (x / 256) % 256 ^ n = (y / 256) % 256 ^ n := by
      rw [← Nat.mod_mul_right_div_self, ← Nat.mod_mul_right_div_self, ← pow_succ', h]
    have hm : x % 256 = y % 256 := by
      have hd2 : 256 ∣ 256 ^ (n + 1) := dvd_pow_self 256 (by omega)
      rw [← Nat.mod_mod_of_dvd x hd2, h, Nat.mod_mod_of_dvd y hd2]
    rw [ih _ _ hd, hm]

/-- `wordToBytesBE` is the 32-byte big-endian encoding. -/
theorem range_map_eq_toBE (n x : Nat) :
    (List.range n).map (fun i => UInt8.ofNat (x / 256 ^ (n - 1 - i) % 256)) = toBE n x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.map_append, toBE, ← ih (x / 256)]
    simp only [List.map_cons, List.map_nil, Nat.sub_self, pow_zero, Nat.div_one, Nat.add_sub_cancel]
    congr 1
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    have : n - i = (n - 1 - i) + 1 := by omega
    rw [this, pow_succ', Nat.div_div_eq_div_mul]

theorem wordToBytesBE_data (w : Nat) :
    (Compiler.Keccak.MemorySlice.wordToBytesBE w).data.toList = toBE 32 w := by
  rw [← range_map_eq_toBE]
  simp [Compiler.Keccak.MemorySlice.wordToBytesBE]

theorem toBE_concat (a b x y : Nat) (hy : y < 256 ^ b) :
    toBE a x ++ toBE b y = toBE (a + b) (x * 256 ^ b + y) := by
  rw [toBE_append]
  have hpos : 0 < 256 ^ b := by positivity
  congr 1
  · congr 1
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hy, Nat.zero_add]
  · apply toBE_congr
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hy]

set_option maxRecDepth 20000 in
/-- The three aligned words an EIP-712 digest computation writes for `"\x19\x01" ‖ ds ‖ sh`
(domain separator `ds`, struct hash `sh`), read as 66 bytes, are that byte string. -/
theorem eip712_pack (ds sh : Nat) (hds : ds < 2 ^ 256) (hsh : sh < 2 ^ 256) :
    (toBE 32 (0x1901 * 2 ^ 240 + ds / 2 ^ 16) ++ toBE 32 (ds % 2 ^ 16 * 2 ^ 240 + sh / 2 ^ 16) ++
        toBE 32 (sh % 2 ^ 16 * 2 ^ 240)).take 66 =
      toBE 2 0x1901 ++ toBE 32 ds ++ toBE 32 sh := by
  have h1 : ds % 2 ^ 16 * 2 ^ 240 + sh / 2 ^ 16 < 256 ^ 32 := by
    have := Nat.mod_lt ds (show 2 ^ 16 > 0 by norm_num)
    have := Nat.div_lt_iff_lt_mul (show 2 ^ 16 > 0 by norm_num) |>.mpr (show sh < 2 ^ 240 * 2 ^ 16 by norm_num; omega)
    norm_num at *; omega
  have h2 : sh % 2 ^ 16 * 2 ^ 240 < 256 ^ 32 := by
    have := Nat.mod_lt sh (show 2 ^ 16 > 0 by norm_num)
    clear h1 hds hsh
    norm_num at *; omega
  rw [toBE_concat _ _ _ _ h1, toBE_concat _ _ _ _ h2,
    toBE_concat 2 32 _ _ (by norm_num; omega), toBE_concat _ 32 _ _ (by norm_num; omega)]
  have hx : ((0x1901 * 2 ^ 240 + ds / 2 ^ 16) * 256 ^ 32 + (ds % 2 ^ 16 * 2 ^ 240 + sh / 2 ^ 16)) *
        256 ^ 32 + sh % 2 ^ 16 * 2 ^ 240 =
      ((0x1901 * 256 ^ 32 + ds) * 256 ^ 32 + sh) * 256 ^ 30 := by
    have e1 := Nat.div_add_mod ds (2 ^ 16)
    have e2 := Nat.div_add_mod sh (2 ^ 16)
    norm_num at *
    omega
  rw [hx, show 32 + 32 + 32 = 66 + 30 by rfl, toBE_append, Nat.mul_div_cancel _ (by positivity),
    List.take_left' (by simp)]

open Compiler.Keccak.MemorySlice in
theorem foldl_wordBytes (ws : List Nat) (acc : ByteArray) :
    (ws.foldl (fun acc w => acc ++ wordToBytesBE w) acc).data.toList =
      acc.data.toList ++ ws.flatMap (toBE 32) := by
  induction ws generalizing acc with
  | nil => simp
  | cons w ws ih =>
    rw [List.foldl_cons, ih]
    simp [ByteArray.data_append, wordToBytesBE_data]

open Compiler.Keccak.MemorySlice in
/-- The bytes `keccak256(offset, size)` hashes, as a list. -/
theorem bytesBE_toList (mem : Nat → Nat) (offset size : Nat) :
    (bytesBE mem offset size).data.toList =
      ((words mem offset size).flatMap (toBE 32)).take size := by
  unfold bytesBE
  simp [ByteArray.data_extract, foldl_wordBytes]

/-- Big-endian value of a byte list. -/
def fromBE (l : List UInt8) : Nat := l.foldl (fun acc b => acc * 256 + b.toNat) 0

theorem toBE_fromBE (l : List UInt8) : toBE l.length (fromBE l) = l := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l b ih =>
    rw [List.length_append, List.length_singleton, toBE]
    unfold fromBE at *
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hb := b.toNat_lt
    congr 1
    · rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by norm_num), Nat.div_eq_of_lt hb, Nat.zero_add, ih]
    · simp [Nat.mod_eq_of_lt hb]

theorem getElem_toBE (n x j : Nat) (hj : j < n) :
    (toBE n x)[j]'(by simp [hj]) = UInt8.ofNat (x / 256 ^ (n - 1 - j) % 256) := by
  simp [← range_map_eq_toBE]

theorem length_flatMap_range {α : Type} (f : Nat → List α) (hf : ∀ i, (f i).length = 32)
    (m : Nat) : ((List.range m).flatMap f).length = 32 * m := by
  induction m with
  | zero => simp
  | succ m ih => rw [List.range_succ, List.flatMap_append, List.length_append, ih]; simp [hf]; ring

theorem getElem_flatMap_range {α : Type} (f : Nat → List α) (hf : ∀ i, (f i).length = 32)
    (m k : Nat) (hk : k < ((List.range m).flatMap f).length) :
    ((List.range m).flatMap f)[k] = (f (k / 32))[k % 32]'(by rw [hf]; omega) := by
  induction m with
  | zero => simp at hk
  | succ m ih =>
    have hl := length_flatMap_range f hf
    simp only [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    rw [hl] at hk
    by_cases h : k < 32 * m
    · rw [List.getElem_append_left (by rw [hl]; exact h)]
      exact ih (by rw [hl]; exact h)
    · rw [List.getElem_append_right (by rw [hl]; omega)]
      have hq : k / 32 = m := by omega
      simp only [hl, hq]
      congr 1; omega

open Compiler.Keccak.MemorySlice in
theorem bytesBE_eq_flatMap (mem : Nat → Nat) (offset size : Nat) :
    (bytesBE mem offset size).data.toList =
      ((List.range (byteWordCount size)).flatMap
        (fun i => toBE 32 (mem ((offset + i * 32) % Compiler.Constants.evmModulus)))).take size := by
  rw [bytesBE_toList, words, List.flatMap_map]

open Compiler.Keccak.MemorySlice in
/-- Byte `k` of `keccak256(offset, size)`'s input is byte `k % 32` of the word at
`offset + 32 * (k / 32)`. -/
theorem getElem_bytesBE (mem : Nat → Nat) (offset size k : Nat)
    (hk' : k < (bytesBE mem offset size).data.toList.length) :
    (bytesBE mem offset size).data.toList[k] =
      UInt8.ofNat (mem ((offset + k / 32 * 32) % Compiler.Constants.evmModulus) /
        256 ^ (31 - k % 32) % 256) := by
  simp only [bytesBE_eq_flatMap, List.getElem_take]
  rw [getElem_flatMap_range _ (fun i => toBE_length 32 _), getElem_toBE _ _ _ (by omega)]

open Compiler.Keccak.MemorySlice in
theorem length_bytesBE (mem : Nat → Nat) (offset size : Nat) :
    (bytesBE mem offset size).data.toList.length = size := by
  rw [bytesBE_eq_flatMap, List.length_take, length_flatMap_range _ (fun i => toBE_length 32 _)]
  unfold byteWordCount; omega

theorem fromBE_lt (l : List UInt8) : fromBE l < 256 ^ l.length := by
  induction l using List.reverseRecOn with
  | nil => simp [fromBE]
  | append_singleton l b ih =>
    unfold fromBE at *
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, List.length_append,
      List.length_singleton, pow_succ]
    have := b.toNat_lt
    omega

theorem byteArrayWordBE_eq (data : ByteArray) (start : Nat) :
    Contracts.byteArrayWordBE data start =
      fromBE ((List.range 32).map (fun j => data.get! (start + j))) := by
  unfold Contracts.byteArrayWordBE fromBE
  rw [List.foldl_map]

theorem byteArrayWordBE_lt (data : ByteArray) (start : Nat) :
    Contracts.byteArrayWordBE data start < 2 ^ 256 := by
  rw [byteArrayWordBE_eq]
  have := fromBE_lt ((List.range 32).map (fun j => data.get! (start + j)))
  simp at this
  norm_num at this ⊢
  exact this

theorem digit_byteArrayWordBE (data : ByteArray) (start j : Nat) (hj : j < 32) :
    UInt8.ofNat (Contracts.byteArrayWordBE data start / 256 ^ (31 - j) % 256) =
      data.get! (start + j) := by
  rw [byteArrayWordBE_eq]
  have h := getElem_toBE 32 (fromBE ((List.range 32).map (fun j => data.get! (start + j)))) j hj
  have hl := toBE_fromBE ((List.range 32).map (fun j => data.get! (start + j)))
  simp only [List.length_map, List.length_range] at hl
  simp only [hl, List.getElem_map, List.getElem_range] at h
  rw [← h]

/-- The memory `Contracts.copyBytes data dest` leaves (its definition, verbatim). -/
def copyMem (data : ByteArray) (d : Nat) (mem : Nat → Verity.Core.Uint256) : Nat → Verity.Core.Uint256 :=
  fun offset => Verity.Core.Uint256.ofNat
    (if data.size % 32 ≠ 0 ∧ offset = d + (data.size / 32) * 32 then
      let shift := 8 * (32 - data.size % 32)
      (Contracts.byteArrayWordBE data ((data.size / 32) * 32) / 2 ^ shift) * 2 ^ shift +
        (mem offset).val % 2 ^ shift
    else if d ≤ offset ∧ offset < d + 32 * (data.size / 32) ∧ (offset - d) % 32 = 0 then
      Contracts.byteArrayWordBE data (offset - d)
    else (mem offset).val)

theorem copyBytes_run (data : ByteArray) (dest : Verity.Core.Uint256) (st : Verity.ContractState) :
    Contracts.copyBytes data dest st = .success () { st with memory := copyMem data dest.val st.memory } :=
  rfl

/-- Keeping only the top bytes of a word: a digit above the cut is unchanged. -/
theorem digit_of_truncated (W low sh e : Nat) (hlow : low < 2 ^ sh) (he : sh ≤ e) :
    ((W / 2 ^ sh) * 2 ^ sh + low) / 2 ^ e = W / 2 ^ e := by
  have hP : 0 < 2 ^ sh := by positivity
  have hsplit : 2 ^ e = 2 ^ sh * 2 ^ (e - sh) := by rw [← pow_add]; congr 1; omega
  rw [hsplit, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
  congr 1
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hP, Nat.div_eq_of_lt hlow, Nat.zero_add]

/-- `(W / 2^sh) * 2^sh + low` is still a word when `W` is one and `low < 2^sh`. -/
theorem truncated_add_lt (W low sh : Nat) (hW : W < 2 ^ 256) (hsh : sh ≤ 256)
    (hlow : low < 2 ^ sh) : W / 2 ^ sh * 2 ^ sh + low < 2 ^ 256 := by
  have hdvd : 2 ^ sh ∣ 2 ^ 256 := pow_dvd_pow 2 hsh
  have h1 : W / 2 ^ sh < 2 ^ 256 / 2 ^ sh := Nat.div_lt_div_of_lt_of_dvd hdvd hW
  have h2 : (W / 2 ^ sh + 1) * 2 ^ sh ≤ 2 ^ 256 / 2 ^ sh * 2 ^ sh := Nat.mul_le_mul_right _ h1
  rw [Nat.div_mul_cancel hdvd] at h2
  nlinarith

/-- Byte `k` of the copy, inside a whole 32-byte word of `data`. -/
theorem digit_copyMem_full (data : ByteArray) (d : Nat) (mem : Nat → Verity.Core.Uint256)
    (k : Nat) (hq : k / 32 < data.size / 32) :
    UInt8.ofNat ((copyMem data d mem (d + k / 32 * 32)).val / 256 ^ (31 - k % 32) % 256) =
      data.get! (k / 32 * 32 + k % 32) := by
  have hj : k % 32 < 32 := Nat.mod_lt _ (by norm_num)
  have hlt : Contracts.byteArrayWordBE data (k / 32 * 32) % Verity.Core.Uint256.modulus =
      Contracts.byteArrayWordBE data (k / 32 * 32) := Nat.mod_eq_of_lt (byteArrayWordBE_lt _ _)
  simp only [copyMem, Verity.Core.Uint256.val_ofNat]
  rw [if_neg (by omega), if_pos ⟨by omega, by omega, by omega⟩,
    show d + k / 32 * 32 - d = k / 32 * 32 by omega, hlt, ← digit_byteArrayWordBE _ _ _ hj]

/-- Byte `k` of the copy, inside the final partial word of `data`. -/
theorem digit_copyMem_partial (data : ByteArray) (d : Nat) (mem : Nat → Verity.Core.Uint256)
    (k : Nat) (hk : k < data.size) (hq : ¬k / 32 < data.size / 32) :
    UInt8.ofNat ((copyMem data d mem (d + k / 32 * 32)).val / 256 ^ (31 - k % 32) % 256) =
      data.get! (k / 32 * 32 + k % 32) := by
  have hj : k % 32 < 32 := Nat.mod_lt _ (by norm_num)
  have hqe : k / 32 = data.size / 32 := by omega
  simp only [copyMem, Verity.Core.Uint256.val_ofNat]
  rw [if_pos ⟨by omega, by rw [hqe]⟩]
  set W := Contracts.byteArrayWordBE data (data.size / 32 * 32)
  set sh := 8 * (32 - data.size % 32)
  have hlow : (mem (d + k / 32 * 32)).val % 2 ^ sh < 2 ^ sh := Nat.mod_lt _ (by positivity)
  have hV : W / 2 ^ sh * 2 ^ sh + (mem (d + k / 32 * 32)).val % 2 ^ sh <
      Verity.Core.Uint256.modulus := truncated_add_lt W _ sh (byteArrayWordBE_lt _ _) (by omega) hlow
  rw [Nat.mod_eq_of_lt hV,
    show (256 : Nat) ^ (31 - k % 32) = 2 ^ (8 * (31 - k % 32)) by rw [pow_mul]; norm_num,
    digit_of_truncated _ _ _ _ hlow (by omega),
    show (2 : Nat) ^ (8 * (31 - k % 32)) = 256 ^ (31 - k % 32) by rw [pow_mul]; norm_num,
    ← digit_byteArrayWordBE data (k / 32 * 32) _ hj, hqe]

open Compiler.Keccak.MemorySlice in
/-- `keccak256(dest, data.size)` after `copyBytes data dest` reads exactly `data`. -/
theorem bytesBE_copyMem (data : ByteArray) (d : Nat) (mem : Nat → Verity.Core.Uint256)
    (hd : d + data.size + 32 < 2 ^ 256) :
    (bytesBE (fun a => (copyMem data d mem a).val) d data.size).data.toList = data.data.toList := by
  apply List.ext_getElem
  · rw [length_bytesBE]; simp
  intro k hk _
  rw [getElem_bytesBE]
  rw [length_bytesBE] at hk
  have hkey : (d + k / 32 * 32) % Compiler.Constants.evmModulus = d + k / 32 * 32 := by
    apply Nat.mod_eq_of_lt; unfold Compiler.Constants.evmModulus; omega
  have hget : data.data.toList[k] = data.get! (k / 32 * 32 + k % 32) := by
    rw [show k / 32 * 32 + k % 32 = k by omega]
    simp [ByteArray.get!]
    rw [getElem!_pos data.data k (show k < data.data.size from hk)]
  rw [hkey, hget]
  by_cases hq : k / 32 < data.size / 32
  · exact digit_copyMem_full data d mem k hq
  · exact digit_copyMem_partial data d mem k hk hq

open Compiler.Keccak.MemorySlice in
/-- Words `ws` at `b, b + 32, …` read back as their concatenation, cut to `size`. -/
theorem bytesBE_of_words (mem : Nat → Nat) (b size : Nat) (ws : List Nat)
    (hlen : ws.length = byteWordCount size)
    (h : ∀ i (hi : i < ws.length), mem ((b + i * 32) % Compiler.Constants.evmModulus) = ws[i]) :
    (bytesBE mem b size).data.toList = (ws.flatMap (toBE 32)).take size := by
  rw [bytesBE_eq_flatMap]
  have hws : (List.range (byteWordCount size)).map
      (fun i => mem ((b + i * 32) % Compiler.Constants.evmModulus)) = ws := by
    apply List.ext_getElem
    · simp [hlen]
    · intro i h1 h2; simp only [List.getElem_map, List.getElem_range]; exact h i h2
  rw [← hws, List.flatMap_map]

/-- Keccak-256 of a byte string, as a word: what `keccak256` returns for those bytes. -/
def keccakBytes (bytes : List UInt8) : Nat :=
  KeccakEngine.byteArrayToNatBE (KeccakEngine.keccak256 ⟨bytes.toArray⟩) % 2 ^ 256

theorem keccakBytes_lt (bytes : List UInt8) : keccakBytes bytes < 2 ^ 256 :=
  Nat.mod_lt _ (by norm_num)

open Compiler.Keccak.MemorySlice in
theorem keccak_eq_keccakBytes (mem : Nat → Nat) (o z : Nat) (l : List UInt8)
    (h : (bytesBE mem o z).data.toList = l) : keccak mem o z = keccakBytes l := by
  unfold keccak keccakBytes
  congr 3
  cases hb : bytesBE mem o z with
  | mk d => rw [hb] at h; simp at h; subst h; simp

/-- The ABI encoding of words: each word as 32 big-endian bytes (`abi.encode` of `uint256`s). -/
def encodeWords (ws : List Nat) : List UInt8 := ws.flatMap (toBE 32)

@[simp] theorem length_encodeWords (ws : List Nat) : (encodeWords ws).length = 32 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [encodeWords, List.flatMap_cons, List.length_append, toBE_length] at ih ⊢
    rw [ih, List.length_cons]; ring

open Compiler.Keccak.MemorySlice in
/-- Words `ws` at `b, b + 32, …`, hashed over `32 * ws.length` bytes, give
`keccakBytes (encodeWords ws)`. -/
theorem keccak_of_words (mem : Nat → Nat) (b : Nat) (ws : List Nat)
    (h : ∀ i (hi : i < ws.length), mem ((b + i * 32) % Compiler.Constants.evmModulus) = ws[i]) :
    keccak mem b (32 * ws.length) = keccakBytes (encodeWords ws) := by
  apply keccak_eq_keccakBytes
  rw [bytesBE_of_words mem b _ ws (by simp only [byteWordCount]; omega) h]
  exact List.take_of_length_le (by rw [← encodeWords, length_encodeWords])

/-! ## Word arithmetic -/

theorem ofNat_val (x : Verity.Core.Uint256) : Verity.Core.Uint256.ofNat x.val = x :=
  Verity.Core.Uint256.ext (Nat.mod_eq_of_lt x.isLt)

theorem val_ofNat_keccakBytes (l : List UInt8) :
    (Verity.Core.Uint256.ofNat (keccakBytes l)).val = keccakBytes l :=
  Nat.mod_eq_of_lt (keccakBytes_lt l)

theorem add_val (b : Verity.Core.Uint256) (c : Nat) (hc : c < 2 ^ 256) :
    (Verity.EVM.Uint256.add b (Verity.Core.Uint256.ofNat c)).val = (b.val + c) % 2 ^ 256 := by
  show (Verity.Core.Uint256.ofNat (b.val + (Verity.Core.Uint256.ofNat c).val)).val = _
  rw [Verity.Core.Uint256.val_ofNat, Verity.Core.Uint256.val_ofNat,
    Nat.mod_eq_of_lt (show c < Verity.Core.Uint256.modulus from hc)]
  rfl

theorem shr_val (n x : Verity.Core.Uint256) :
    (Verity.EVM.Uint256.shr n x).val = x.val / 2 ^ n.val := by
  show (Verity.Core.Uint256.ofNat (x.val >>> n.val)).val = _
  rw [Verity.Core.Uint256.val_ofNat, Nat.shiftRight_eq_div_pow]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) x.isLt)

theorem shl_val (k : Nat) (hk : k ≤ 256) (x : Verity.Core.Uint256) :
    (Verity.EVM.Uint256.shl (Verity.Core.Uint256.ofNat k) x).val = x.val % 2 ^ (256 - k) * 2 ^ k := by
  show (Verity.Core.Uint256.ofNat (x.val <<< (Verity.Core.Uint256.ofNat k).val)).val = _
  rw [Verity.Core.Uint256.val_ofNat, Verity.Core.Uint256.val_ofNat,
    Nat.mod_eq_of_lt (show k < Verity.Core.Uint256.modulus from
      Nat.lt_of_le_of_lt hk (by decide)), Nat.shiftLeft_eq]
  show x.val * 2 ^ k % 2 ^ 256 = _
  rw [show (2 : Nat) ^ 256 = 2 ^ (256 - k) * 2 ^ k by rw [← pow_add]; congr 1; omega,
    Nat.mul_mod_mul_right]

/-- `a ||| b` is `a + b` when `a` is a multiple of `2^k` and `b < 2^k`. -/
theorem bitOr_val_of_lt (a b : Verity.Core.Uint256) (k q : Nat) (ha : a.val = q * 2 ^ k)
    (hb : b.val < 2 ^ k) : (Contracts.bitOr a b).val = a.val + b.val := by
  show (Verity.Core.Uint256.ofNat (Nat.lor a.val b.val)).val = _
  rw [Verity.Core.Uint256.val_ofNat, show Nat.lor a.val b.val = a.val ||| b.val from rfl, ha,
    ← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt hb, Nat.shiftLeft_eq, ← ha]
  apply Nat.mod_eq_of_lt
  have haw : a.val < 2 ^ 256 := a.isLt
  have hbw : b.val < 2 ^ 256 := b.isLt
  show a.val + b.val < 2 ^ 256
  rcases Nat.lt_or_ge 256 k with hk | hk
  · have hpow : 2 ^ 256 < 2 ^ k := Nat.pow_lt_pow_right (by norm_num) hk
    have hq : q = 0 := by
      rcases Nat.eq_zero_or_pos q with h0 | h0
      · exact h0
      · exfalso; rw [ha] at haw; nlinarith
    rw [ha, hq]; simpa using hbw
  · have hsplit : (2 : Nat) ^ 256 = 2 ^ (256 - k) * 2 ^ k := by rw [← pow_add]; congr 1; omega
    have hq : q < 2 ^ (256 - k) := by
      rw [ha, hsplit] at haw; exact Nat.lt_of_mul_lt_mul_right haw
    have h2 : (q + 1) * 2 ^ k ≤ 2 ^ (256 - k) * 2 ^ k := Nat.mul_le_mul_right _ hq
    rw [← hsplit] at h2
    rw [ha]; nlinarith

end Contracts.ProofKit

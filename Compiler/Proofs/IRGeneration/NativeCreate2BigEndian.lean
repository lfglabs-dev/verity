import Compiler.Proofs.IRGeneration.NativeCreate2LowBits

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul

private theorem native_from_bytes_append (front suffix : List UInt8) :
    fromBytes' (front ++ suffix) = fromBytes' front + 256 ^ front.length * fromBytes' suffix := by
  induction front with
  | nil => simp only [List.nil_append, fromBytes', List.length_nil, pow_zero, one_mul, Nat.zero_add]
  | cons byte bytes ih =>
    simp only [List.cons_append, fromBytes', List.length_cons, pow_succ, ih]
    ring

private theorem native_fold_loop {α : Type} (f : α → UInt8 → α) (bytes : ByteArray)
    (count index : Nat) (acc : α) (extent : count + index = bytes.size) :
    ByteArray.foldlM.loop (m := Id) (fun a b => pure (f a b)) bytes bytes.size
      (Nat.le_refl _) count index acc =
      (bytes.data.toList.drop index).foldl f acc := by
  induction count generalizing index acc with
  | zero =>
    have ended : ¬ index < bytes.size := by omega
    simp only [ByteArray.foldlM.loop, ended, ↓reduceDIte]
    rw [List.drop_eq_nil_of_le (by simpa only [Array.length_toList] using (show bytes.data.size ≤ index from (show bytes.size ≤ index by omega)))]
    rfl
  | succ count ih =>
    have active : index < bytes.size := by omega
    have activeList : index < bytes.data.toList.length := by
      simpa only [Array.length_toList] using (show index < bytes.data.size from active)
    rw [ByteArray.foldlM.loop, dif_pos active]
    change ByteArray.foldlM.loop (m := Id) (fun a b => pure (f a b)) bytes bytes.size
      (Nat.le_refl _) count (index + 1) (f acc bytes.data[index]) = _
    rw [ih (index + 1) (f acc bytes.data[index]) (by omega)]
    conv_rhs => rw [List.drop_eq_getElem_cons activeList]
    rfl

/-- The actual ByteArray fold traverses precisely the packed bytes. -/
theorem native_bytearray_fold {α : Type} (f : α → UInt8 → α) (bytes : ByteArray) (acc : α) :
    bytes.foldl f acc = bytes.data.toList.foldl f acc := by
  unfold ByteArray.foldl ByteArray.foldlM
  rw [dif_pos (Nat.le_refl _)]
  exact native_fold_loop f bytes bytes.size 0 acc (Nat.add_zero _)

/-- Canonical big-endian list folding equals actual native byte decoding,
with the accumulator contribution retained explicitly. -/
theorem native_big_endian_list_fold (bytes : List UInt8) (acc : Nat) :
    bytes.foldl (fun value byte => value * 256 + byte.toNat) acc =
      acc * 256 ^ bytes.length + fromBytes' bytes.reverse := by
  induction bytes generalizing acc with
  | nil => simp only [List.foldl_nil, List.length_nil, pow_zero, mul_one, List.reverse_nil, fromBytes', Nat.add_zero]
  | cons byte bytes ih =>
    simp only [List.foldl_cons, List.length_cons, List.reverse_cons, ih, native_from_bytes_append,
      fromBytes', Nat.mul_zero, Nat.add_zero, pow_succ]
    change (acc * 256 + byte.toNat) * 256 ^ bytes.length + fromBytes' bytes.reverse =
      acc * (256 ^ bytes.length * 256) + (fromBytes' bytes.reverse + 256 ^ bytes.reverse.length * byte.toNat)
    rw [List.length_reverse]
    ring

/-- Canonical and native decoders agree on every actual byte array. -/
theorem native_big_endian_decoder (bytes : ByteArray) :
    KeccakEngine.byteArrayToNatBE bytes = EvmYul.fromByteArrayBigEndian bytes := by
  unfold KeccakEngine.byteArrayToNatBE
  rw [native_bytearray_fold, native_big_endian_list_fold]
  simp only [Nat.zero_mul, Nat.zero_add, EvmYul.fromByteArrayBigEndian,
    EvmYul.fromBytesBigEndian, Function.comp_apply, native_bytes_list]
end Compiler.Proofs.IRGeneration.NativeMidnightConstructor

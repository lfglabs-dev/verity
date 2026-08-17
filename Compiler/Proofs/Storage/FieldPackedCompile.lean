/-
  C5 step 4 packed compiler-read composition: `fieldPackedExtract` is
  the same Nat as `compiledPackedRead` of the storage word. Packed
  bit-range validity (`offset < 256`, `width < 256`) is explicit.
-/

import Compiler.Proofs.Storage.FieldStorageKey
import Compiler.Proofs.Storage.SolidityStorage

namespace Compiler.Proofs.Storage.FieldPackedCompile

open Verity
open Verity.ContractState
open Compiler.CompilationModel
open Compiler.Proofs.Storage.FieldStorageKey
open Compiler.Proofs.Storage
open Compiler.Proofs.IRGeneration

theorem packedExtract_eq_yulReadPackedWord
    (word : Nat) (offset width : Nat)
    (hword : word < 2 ^ 256) (hwidth : width < 256) :
    packedExtract word { offset := offset, width := width } =
      (yulReadPackedWord (IRStorageWord.ofNat word) offset width).toNat := by
  have hwle : width ≤ 256 := Nat.le_of_lt hwidth
  rw [packedExtract_eq_mod (pb := { offset := offset, width := width }) word hwidth]
  unfold yulReadPackedWord
  rw [IRStorageWord.toNat_ofNat, IRStorageWord.toNat_ofNat]
  have hsize : (2 : Nat) ^ 256 = EvmYul.UInt256.size := by
    unfold EvmYul.UInt256.size; rfl
  have hword' : word % EvmYul.UInt256.size = word := by
    rw [← hsize, Nat.mod_eq_of_lt hword]
  rw [hword']
  have hlt : (word / 2 ^ offset) % 2 ^ width < EvmYul.UInt256.size := by
    have hpow : (2 : Nat) ^ width < 2 ^ 256 :=
      Nat.pow_lt_pow_right (by decide) hwidth
    rw [← hsize]
    exact Nat.lt_trans (Nat.mod_lt _ (Nat.two_pow_pos width)) hpow
  exact (Nat.mod_eq_of_lt hlt).symm

theorem fieldPackedExtract_eq_compiledPackedRead
    {s : ContractState} {f : Field} {slot : Nat} {pb : PackedBits}
    (htr : f.isTransient = false) (hpk : f.packedBits = some pb)
    (hwidth : pb.width < 256) :
    fieldPackedExtract s f slot =
      some (compiledPackedRead
        (IRStorageWord.ofNat (s.storage slot).val) pb.offset pb.width).toNat := by
  have hword : (s.storage slot).val < 2 ^ 256 := (s.storage slot).isLt
  have hwle : pb.width ≤ 256 := Nat.le_of_lt hwidth
  rw [fieldPackedExtract_eq htr hpk,
    packedExtract_eq_yulReadPackedWord _ pb.offset pb.width hword hwidth,
    yulReadPackedWord_eq_compiledExpr _ _ _ hwle]

end Compiler.Proofs.Storage.FieldPackedCompile

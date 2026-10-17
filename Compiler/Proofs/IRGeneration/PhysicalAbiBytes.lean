import Compiler.Proofs.IRGeneration.PhysicalErrorStringExecution

/-! Encoding facts for the compiler's actual UTF-8 chunk and padded-word
constructors. These lemmas do not use the legacy word-only memory model. -/
namespace Compiler.Proofs.IRGeneration.PhysicalAbiBytes
open Compiler.CompilationModel

theorem chunk_length_le :
    ∀ {bytes chunk : List UInt8}, chunk ∈ chunkBytes32 bytes → chunk.length ≤ 32
  | [], chunk, member => by
      unfold chunkBytes32 at member
      simp at member
  | byte :: rest, chunk, member => by
      unfold chunkBytes32 at member
      simp only [List.isEmpty_cons, Bool.false_eq_true, if_false, List.mem_cons] at member
      rcases member with head | tail
      · subst chunk
        exact List.length_take_le 32 (byte :: rest)
      · exact chunk_length_le (bytes := (byte :: rest).drop 32) tail
termination_by bytes => bytes.length
decreasing_by
  simp_wf
  omega

theorem chunks_flatten (bytes : List UInt8) : (chunkBytes32 bytes).flatten = bytes := by
  cases bytes with
  | nil => simp [chunkBytes32]
  | cons byte rest =>
      rw [chunkBytes32]
      simp only [List.isEmpty_cons, Bool.false_eq_true, if_false, List.flatten_cons]
      rw [chunks_flatten ((byte :: rest).drop 32)]
      exact List.take_append_drop 32 (byte :: rest)
termination_by bytes.length
decreasing_by
  simp_wf
  omega

theorem padded_length {bytes : List UInt8} (bound : bytes.length ≤ 32) :
    (bytes ++ List.replicate (32 - bytes.length) (0 : UInt8)).length = 32 := by
  simp [bound]

theorem fold_bound (bytes : List UInt8) (acc : Nat) :
    bytes.foldl (fun acc byte => acc * 256 + byte.toNat) acc <
      (acc + 1) * 256 ^ bytes.length := by
  induction bytes generalizing acc with
  | nil => simp
  | cons byte rest ih =>
      have byteBound : byte.toNat < 256 := UInt8.toNat_lt byte
      have step : acc * 256 + byte.toNat + 1 ≤ (acc + 1) * 256 := by omega
      have scaled := Nat.mul_le_mul_right (256 ^ rest.length) step
      have tail := ih (acc * 256 + byte.toNat)
      simp only [List.foldl_cons, List.length_cons]
      exact lt_of_lt_of_le tail (by simpa [Nat.mul_assoc, Nat.mul_comm,
        Nat.mul_left_comm, pow_succ] using scaled)

theorem word_bounded {bytes : List UInt8} (bound : bytes.length ≤ 32) :
    wordFromBytes bytes < Compiler.Constants.evmModulus := by
  have bounded := fold_bound (bytes ++ List.replicate (32 - bytes.length) (0 : UInt8)) 0
  rw [padded_length bound] at bounded
  simpa [wordFromBytes, Compiler.Constants.evmModulus] using bounded

end Compiler.Proofs.IRGeneration.PhysicalAbiBytes

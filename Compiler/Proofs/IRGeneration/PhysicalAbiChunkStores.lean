import Compiler.Proofs.IRGeneration.PhysicalAbiWordRecovery

/-! Sequential physical chunk placement with explicit nonwrapping addresses. -/
namespace Compiler.Proofs.IRGeneration.PhysicalAbiChunkStores
open Compiler.CompilationModel PhysicalPayloadStores PhysicalAbiWordRecovery

def chunkWrites : Nat → List (List UInt8) → List (Nat × Nat)
  | _, [] => []
  | base, chunk :: tail => (base, wordFromBytes chunk) :: chunkWrites (base + 32) tail

theorem chunkWrites_length (base : Nat) (chunks : List (List UInt8)) :
    (chunkWrites base chunks).length = chunks.length := by
  induction chunks generalizing base with
  | nil => rfl
  | cons chunk tail ih => simp only [chunkWrites, List.length_cons, ih]

theorem chunkWrites_extent (base : Nat) (chunks : List (List UInt8))
    (pair : Nat × Nat) (member : pair ∈ chunkWrites base chunks) :
    base ≤ pair.1 ∧ pair.1 < base + 32 * chunks.length := by
  induction chunks generalizing base with
  | nil => simp [chunkWrites] at member
  | cons chunk tail ih =>
      simp only [chunkWrites, List.mem_cons] at member
      rcases member with head | rest
      · subst pair
        simp only [List.length_cons]
        omega
      · have bounds := ih (base + 32) rest
        simp only [List.length_cons]
        omega

theorem chunkWrites_zipIdx (base start : Nat) (chunks : List (List UInt8)) :
    (chunks.zipIdx start).map (fun pair =>
      (base + pair.2 * 32, wordFromBytes pair.1)) =
      chunkWrites (base + start * 32) chunks := by
  induction chunks generalizing start with
  | nil => rfl
  | cons chunk tail ih =>
      simp only [List.zipIdx_cons, List.map_cons, chunkWrites]
      rw [ih]
      congr 1
      congr 1
      omega

/-- The compiler's actual message data stores are these sequential chunks. -/
theorem dataWrites_eq (message : String) :
    PhysicalErrorStringExecution.dataWrites message =
      chunkWrites 68 (chunkBytes32 (bytesFromString message)) := by
  simpa only [PhysicalErrorStringExecution.dataWrites, Nat.zero_mul, Nat.add_zero]
    using chunkWrites_zipIdx 68 0 (chunkBytes32 (bytesFromString message))

/-- Every full or short chunk is placed at its exact physical byte offset. -/
theorem read_chunk (state : IRState) (base : Nat) (chunks : List (List UInt8))
    (bounded : ∀ chunk ∈ chunks, chunk.length ≤ 32)
    (extent : base + 32 * chunks.length ≤ Verity.Core.Uint256.modulus)
    (index : Nat) (present : index < chunks.length) (byte : Fin 32) :
    (applyStores state (chunkWrites base chunks)).byteMemory.readByte
      (base + 32 * index + byte.val) =
      paddedWord chunks[index] (bounded _ (List.getElem_mem present)) byte := by
  induction chunks generalizing state base index with
  | nil => simp at present
  | cons chunk tail ih =>
      have headBound : chunk.length ≤ 32 := bounded chunk (List.mem_cons_self)
      have tailBound : ∀ entry ∈ tail, entry.length ≤ 32 :=
        fun entry member => bounded entry (List.mem_cons_of_mem _ member)
      have baseBound : base < Verity.Core.Uint256.modulus := by
        simp only [List.length_cons] at extent
        omega
      have normalized : (Verity.Core.Uint256.ofNat base).val = base := by
        simp only [Verity.Core.Uint256.val_ofNat, Nat.mod_eq_of_lt baseBound]
      cases index with
      | zero =>
          simp only [Nat.mul_zero, Nat.add_zero, List.getElem_cons_zero, chunkWrites]
          have outside : ∀ pair ∈ chunkWrites (base + 32) tail,
              (Verity.Core.Uint256.ofNat base).val + byte.val <
                (Verity.Core.Uint256.ofNat pair.1).val ∨
              (Verity.Core.Uint256.ofNat pair.1).val + 32 ≤
                (Verity.Core.Uint256.ofNat base).val + byte.val := by
            intro pair member
            have bounds := chunkWrites_extent (base + 32) tail pair member
            have pairBound : pair.1 < Verity.Core.Uint256.modulus := by
              simp only [List.length_cons] at extent
              omega
            simp only [normalized, Verity.Core.Uint256.val_ofNat,
              Nat.mod_eq_of_lt pairBound]
            left
            have := byte.isLt
            omega
          have result := stored_chunk_byte state chunk headBound base
            (chunkWrites (base + 32) tail) byte outside
          simpa only [normalized] using result
      | succ index =>
          have tailExtent : base + 32 + 32 * tail.length ≤ Verity.Core.Uint256.modulus := by
            simp only [List.length_cons] at extent
            omega
          have tailPresent : index < tail.length := by simpa using present
          have result := ih (state.writePhysicalMemoryValue
            (Verity.Core.Uint256.ofNat base).val (wordFromBytes chunk))
            (base + 32) tailBound tailExtent index tailPresent
          simpa only [chunkWrites, applyStores, List.getElem_cons_succ,
            Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using result

end Compiler.Proofs.IRGeneration.PhysicalAbiChunkStores

import Compiler.Proofs.IRGeneration.NativeSourceMcopy
import EvmYul.EVM.Proof.Memory

namespace Compiler.Proofs.IRGeneration.NativeSourceMcopyWindow
open EvmYul EVM.Proof

theorem write_window (memory : ByteArray) (dest source size : Nat)
    (positive : 0 < size) (input : source + size ≤ memory.size)
    (output : dest + size ≤ memory.size) :
    memory.write source memory dest size =
      ⟨memory.data.extract 0 dest ++ memory.data.extract source (source + size) ++
        memory.data.extract (dest + size) memory.size⟩ := by
  unfold ByteArray.write
  rw [if_neg (by omega), if_neg (by omega)]
  rw [show min size (memory.size - source) = size by omega,
    show min memory.size (dest + size) = dest + size by omega]
  dsimp only
  rw [Nat.sub_self, show dest - memory.size = 0 by omega]
  rw [ByteArray.append_zeroes (by simp), Nat.add_zero]
  ext1
  simp [ByteArray.copySlice, show min size (memory.size - source) = size by omega]

theorem memory_window (fuel gasCost : Nat) (pre post : EVM.State)
    (rest : Stack UInt256) (dest source size : UInt256)
    (popped : pre.stack.pop3 = some (rest, dest, source, size))
    (success : EVM.step (fuel + 1) gasCost (some (.MCOPY, none)) pre = .ok post)
    (positive : 0 < size.toNat) (input : source.toNat + size.toNat ≤ pre.memory.size)
    (output : dest.toNat + size.toNat ≤ pre.memory.size) :
    post.memory = ⟨pre.memory.data.extract 0 dest.toNat ++
      pre.memory.data.extract source.toNat (source.toNat + size.toNat) ++
      pre.memory.data.extract (dest.toNat + size.toNat) pre.memory.size⟩ := by
  rw [NativeSourceMcopy.memory_step_MCOPY fuel gasCost pre post rest dest source size popped success]
  exact write_window pre.memory _ _ _ positive input output

end Compiler.Proofs.IRGeneration.NativeSourceMcopyWindow

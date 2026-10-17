import Compiler.Proofs.IRGeneration.NativeSourcePreludeLength

namespace Compiler.Proofs.IRGeneration.NativeSourcePreludeCopy
open EvmYul EVM.Proof NativeSourcePreludeShuffles

abbrev entry := NativeSourcePreludeLength.loaded
def length (cost : Nat) (pre : EVM.State) (free a b c d e f g h : UInt256) (tail : Stack UInt256) :=
  (result cost pre free a b c d e f g h tail).toMachineState.lookupMemory f

theorem entry_pc (cost loadCost : Nat) (pre : EVM.State) (free a b c d e f g h : UInt256)
    (tail : Stack UInt256) (pc : pre.pc = UInt256.ofNat 636) :
    (entry cost loadCost pre free a b c d e f g h tail).pc = UInt256.ofNat 644 := by
  change ((((((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) +
    UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) = _
  rw [pc]
  decide

def copied (cost loadCost cost1 cost2 cost3 cost4 : Nat) (pre : EVM.State)
    (free a b c d e f g h : UInt256) (tail : Stack UInt256) : EVM.State :=
  NativeSourceFirstCopy.copied (entry cost loadCost pre free a b c d e f g h tail)
    cost1 cost2 cost3 cost4 (length cost pre free a b c d e f g h tail)
    c e a b free d free (free + b) (g :: h :: tail)

theorem copy (fuel cost loadCost cost1 cost2 cost3 cost4 : Nat) (pre : EVM.State)
    (free a b c d e f g h : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 636) :
    ((do
      let one ← EVM.step (fuel + 1) cost1 (some (decodeAt (entry cost loadCost pre free a b c d e f g h tail)))
        (entry cost loadCost pre free a b c d e f g h tail)
      let two ← EVM.step (fuel + 1) cost2 (some (decodeAt one)) one
      EVM.step (fuel + 1) cost3 (some (decodeAt two)) two) >>= fun ready =>
      EVM.step (fuel + 1) cost4 (some (decodeAt ready)) ready) =
      .ok (copied cost loadCost cost1 cost2 cost3 cost4 pre free a b c d e f g h tail) := by
  exact NativeSourceFirstCopy.execute fuel cost1 cost2 cost3 cost4 _
    (length cost pre free a b c d e f g h tail) c e a b free d free (free + b) (g :: h :: tail)
    code (entry_pc cost loadCost pre free a b c d e f g h tail pc)
    (NativeSourcePreludeLength.stack cost loadCost pre free a b c d e f g h tail)

theorem execute (fuel cost loadCost cost1 cost2 cost3 cost4 : Nat) (pre : EVM.State)
    (free a b c d e f g h : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 636)
    (stack : pre.stack = free :: a :: b :: c :: d :: e :: f :: g :: h :: tail) :
    (((run fuel cost [.SWAP5, .DUP6, .SWAP4, .DUP4, .DUP6, .ADD, .SWAP8] pre >>= fun ready =>
      EVM.step (fuel + 1) loadCost (some (.MLOAD, none)) ready) >>= fun loaded => (do
      let one ← EVM.step (fuel + 1) cost1 (some (decodeAt loaded))
        loaded
      let two ← EVM.step (fuel + 1) cost2 (some (decodeAt one)) one
      EVM.step (fuel + 1) cost3 (some (decodeAt two)) two) >>= fun ready =>
      EVM.step (fuel + 1) cost4 (some (decodeAt ready)) ready)) =
      .ok (copied cost loadCost cost1 cost2 cost3 cost4 pre free a b c d e f g h tail) := by
  rw [NativeSourcePreludeLength.execute fuel cost loadCost pre free a b c d e f g h tail stack]
  exact copy fuel cost loadCost cost1 cost2 cost3 cost4 pre free a b c d e f g h tail code pc


theorem bytes (cost loadCost cost1 cost2 cost3 cost4 : Nat) (pre : EVM.State)
    (free a b c d e f g h : UInt256) (tail : Stack UInt256)
    (positive : 0 < (length cost pre free a b c d e f g h tail).toNat)
    (bounded : (length cost pre free a b c d e f g h tail).toNat < 2^64)
    (input : c.toNat + (length cost pre free a b c d e f g h tail).toNat ≤ pre.memory.size)
    (padding : (free + b).toNat - pre.memory.size < 2 ^ System.Platform.numBits) :
    (copied cost loadCost cost1 cost2 cost3 cost4 pre free a b c d e f g h tail).memory.readWithPadding
      (free + b).toNat (length cost pre free a b c d e f g h tail).toNat =
      pre.memory.extract c.toNat (c.toNat + (length cost pre free a b c d e f g h tail).toNat) := by
  exact NativeSourceFirstCopy.bytes _ cost1 cost2 cost3 cost4 _ _ _ _ _ _ _ _ _ _ positive bounded input padding

end Compiler.Proofs.IRGeneration.NativeSourcePreludeCopy

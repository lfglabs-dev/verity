import Compiler.Proofs.IRGeneration.NativeSourcePackingContext

namespace Compiler.Proofs.IRGeneration.NativeSourceFieldLoad
open EvmYul EVM.Proof NativeSourcePreludeDecoded

theorem decode591 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 591) = some (.MLOAD, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 591).toNat = some 81 := by
    have index : (UInt256.ofNat 591).toNat = 591 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem step (fuel cost : Nat) (pre : EVM.State) (address : UInt256) (rest : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 591)
    (stack : pre.stack = address :: rest) :
    EVM.step (fuel + 1) cost (some (decodeAt pre)) pre =
      .ok (NativeSourceLoadStep.loaded cost pre address rest) := by
  have decoded : decodeAt pre = (.MLOAD, none) := by
    unfold decodeAt
    rw [code, pc, decode591]
    rfl
  rw [decoded]
  exact NativeSourceLoadStep.step fuel cost pre address rest stack

theorem run_one (fuel cost : Nat) (pre post : EVM.State)
    (step : EVM.step (fuel + 1) cost (some (decodeAt pre)) pre = .ok post) :
    run fuel cost 1 pre = .ok post := by
  rw [run, step]
  rfl

def loaded (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256) :=
  NativeSourceLoadStep.loaded cost (NativeSourcePackingContext.prepared cost pre a b c d e f g h i j k tail) d
    (e :: f :: a :: g :: a :: b :: c :: UInt256.ofNat 632 :: h :: UInt256.ofNat 32 ::
      i :: UInt256.ofNat 681 :: j :: k :: UInt256.ofNat 0 :: tail)

theorem entry_pc (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 573) :
    (NativeSourcePackingContext.prepared cost pre a b c d e f g h i j k tail).pc = UInt256.ofNat 591 := by
  change ((((((((((((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) +
    UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 2) +
    UInt256.ofNat 1) + UInt256.ofNat 3) + UInt256.ofNat 1) + UInt256.ofNat 1) +
    UInt256.ofNat 3) + UInt256.ofNat 1 = _
  rw [pc]; decide

theorem finish (fuel cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 573) :
    run fuel cost 1 (NativeSourcePackingContext.prepared cost pre a b c d e f g h i j k tail) =
      .ok (loaded cost pre a b c d e f g h i j k tail) := by
  apply run_one
  exact step fuel cost _ d _ code (entry_pc cost pre a b c d e f g h i j k tail pc)
    (NativeSourcePackingContext.stack cost pre a b c d e f g h i j k tail)

theorem execute (fuel cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 573)
    (stack : pre.stack = a :: b :: c :: d :: e :: f :: g :: h :: i :: j :: k :: tail) :
    run fuel cost 14 pre = .ok (loaded cost pre a b c d e f g h i j k tail) := by
  exact NativeSourceSizedPacking.compose fuel cost 13 1 pre _ _
    (NativeSourcePackingContext.execute fuel cost pre a b c d e f g h i j k tail code pc stack)
    (finish fuel cost pre a b c d e f g h i j k tail code pc)

theorem stack (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256) :
    (loaded cost pre a b c d e f g h i j k tail).stack =
      (NativeSourcePackingContext.prepared cost pre a b c d e f g h i j k tail).toMachineState.lookupMemory d ::
      e :: f :: a :: g :: a :: b :: c :: UInt256.ofNat 632 :: h :: UInt256.ofNat 32 ::
      i :: UInt256.ofNat 681 :: j :: k :: UInt256.ofNat 0 :: tail := by rfl

end Compiler.Proofs.IRGeneration.NativeSourceFieldLoad

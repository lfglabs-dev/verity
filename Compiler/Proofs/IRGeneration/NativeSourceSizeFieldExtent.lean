import Compiler.Proofs.IRGeneration.NativeSourceFourthFieldExtent

namespace Compiler.Proofs.IRGeneration.NativeSourceSizeFieldExtent
open EvmYul

theorem ready_words (cost : Nat) (pre : EVM.State) (a b c d e f g h i : UInt256)
    (tail : Stack UInt256) :
    (NativeSourceFieldSize.ready cost pre a b c d e f g h i tail).activeWords = pre.activeWords := by
  rfl

theorem store_words (cost : Nat) (pre : EVM.State) (mask size a b c d e f g : UInt256)
    (tail : Stack UInt256) :
    (NativeSourceFieldRoundingStore.s4 cost pre mask size a b c d e f g tail).activeWords =
      UInt256.ofNat (MachineState.M pre.activeWords.toNat f.toNat 32) := by
  rfl

theorem sized_words (cost : Nat) (pre : EVM.State) (a b c d e f g h i : UInt256)
    (tail : Stack UInt256) :
    (NativeSourceFieldSize.stored cost pre a b c d e f g h i tail).activeWords =
      UInt256.ofNat (MachineState.M pre.activeWords.toNat h.toNat 32) := by
  have frame := store_words cost (NativeSourceFieldSize.ready cost pre a b c d e f g h i tail)
    (UInt256.lnot (UInt256.ofNat 31)) (a - b) c d e f g h i tail
  have words := congrArg
    (fun w : UInt256 => UInt256.ofNat (MachineState.M w.toNat h.toNat 32))
    (ready_words cost pre a b c d e f g h i tail)
  exact frame.trans words

theorem sized_bound (cost : Nat) (pre : EVM.State) (a b c d e f g h i : UInt256)
    (tail : Stack UInt256) (upper : pre.activeWords.toNat < 2 ^ 251) (address : h.toNat < 2 ^ 64) :
    (NativeSourceFieldSize.stored cost pre a b c d e f g h i tail).activeWords.toNat < 2 ^ 251 := by
  rw [sized_words]
  have bound := NativeSourceWordAccessExtent.extent_bound pre.activeWords.toNat h.toNat upper address
  change max pre.activeWords.toNat ((h.toNat + 32 + 31) / 32) % (2 ^ 256) < _
  rw [Nat.mod_eq_of_lt (by omega)]
  exact bound

theorem context_bound (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256)
    (tail : Stack UInt256)
    (upper : (NativeSourceFourthField.stored cost pre a b c d e f g h i j k tail).activeWords.toNat < 2 ^ 251)
    (address : j.toNat < 2 ^ 64) :
    (NativeSourceSizedFields.stored cost pre a b c d e f g h i j k tail).activeWords.toNat < 2 ^ 251 := by
  exact sized_bound cost _ b c (UInt256.ofNat 632) h (UInt256.ofNat 32) i
    (UInt256.ofNat 681) j k (UInt256.ofNat 0 :: tail) upper address

theorem all_fields_bound (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256)
    (tail : Stack UInt256) (upper : pre.activeWords.toNat < 2 ^ 251)
    (sd : d.toNat < 2 ^ 64) (se : e.toNat < 2 ^ 64)
    (sf : f.toNat < 2 ^ 64) (sg : g.toNat < 2 ^ 64)
    (d1 : (c + UInt256.ofNat 192).toNat < 2 ^ 64)
    (d2 : (c + UInt256.ofNat 224).toNat < 2 ^ 64)
    (d3 : (c + UInt256.ofNat 256).toNat < 2 ^ 64)
    (d4 : (c + UInt256.ofNat 288).toNat < 2 ^ 64) (sizeAddress : j.toNat < 2 ^ 64) :
    (NativeSourceSizedFields.stored cost pre a b c d e f g h i j k tail).activeWords.toNat < 2 ^ 251 := by
  have first := NativeSourceFirstFieldExtent.stored_bound cost pre a b c d e f g h i j k tail upper sd d1
  have second := NativeSourceSecondFieldExtent.stored_bound cost pre a b c d e f g h i j k tail first se d2
  have third := NativeSourceThirdFieldExtent.stored_bound cost pre a b c d e f g h i j k tail second sf d3
  have fourth := NativeSourceFourthFieldExtent.stored_bound cost pre a b c d e f g h i j k tail third sg d4
  exact context_bound cost pre a b c d e f g h i j k tail fourth sizeAddress

end Compiler.Proofs.IRGeneration.NativeSourceSizeFieldExtent


import Compiler.Proofs.IRGeneration.NativeSourceLengthCertificate

namespace Compiler.Proofs.IRGeneration.NativeSourceArrayAllocationDecodes
open EvmYul EVM EVM.Proof

theorem immediate273 : NativeSourceAbiWrite.code.extract' 274 275 = ⟨#[64]⟩ := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte0 : NativeSourceAbiWrite.code.data[274]? = some 64 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  apply ByteArray.ext
  simp only [ByteArray.extract', show (274 < 2^64 && 275 < 2^64) = true by decide, if_true, ByteArray.data_extract]
  apply Array.ext
  · simp only [Array.size_extract, size, ByteArray.size_data]; decide
  · intro index left right
    have bound : index < 1 := by simpa using right
    have zero : index = 0 := by omega
    subst index
    simp only [Array.getElem_extract, Nat.add_zero]
    exact Option.some.inj ((Array.getElem?_eq_getElem (by change 274 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte0)

theorem decode273 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 273) = some (.Push .PUSH1, some (UInt256.ofNat 64, 1)) := by
  have byte : NativeSourceAbiWrite.code.get? 273 = some 96 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 273).toNat = 273 by decide, byte]
  change some (Operation.Push Operation.POp.PUSH1, some (uInt256OfByteArray (NativeSourceAbiWrite.code.extract' 274 275), 1)) = _
  rw [immediate273]
  decide

theorem decode275 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 275) = some (.MLOAD, none) := by
  have byte : NativeSourceAbiWrite.code.get? 275 = some 81 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 275).toNat = 275 by decide, byte]
  decide

theorem decode276 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 276) = some (.SWAP3, none) := by
  have byte : NativeSourceAbiWrite.code.get? 276 = some 146 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 276).toNat = 276 by decide, byte]
  decide

theorem immediate277 : NativeSourceAbiWrite.code.extract' 278 280 = ⟨#[1, 36]⟩ := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte0 : NativeSourceAbiWrite.code.data[278]? = some 1 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have byte1 : NativeSourceAbiWrite.code.data[279]? = some 36 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  apply ByteArray.ext
  simp only [ByteArray.extract', show (278 < 2^64 && 280 < 2^64) = true by decide, if_true, ByteArray.data_extract]
  apply Array.ext
  · simp only [Array.size_extract, size, ByteArray.size_data]; decide
  · intro index left right
    have bound : index < 2 := by simpa using right
    have cases : index = 0 ∨ index = 1 := by omega
    rcases cases with rfl | rfl
    · simp only [Array.getElem_extract, Nat.add_zero]
      exact Option.some.inj ((Array.getElem?_eq_getElem (by change 278 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte0)
    · simp only [Array.getElem_extract]
      exact Option.some.inj ((Array.getElem?_eq_getElem (by change 279 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte1)

theorem decode277 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 277) = some (.Push .PUSH2, some (UInt256.ofNat 292, 2)) := by
  have byte : NativeSourceAbiWrite.code.get? 277 = some 97 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 277).toNat = 277 by decide, byte]
  change some (Operation.Push Operation.POp.PUSH2, some (uInt256OfByteArray (NativeSourceAbiWrite.code.extract' 278 280), 2)) = _
  rw [immediate277]
  decide

theorem immediate280 : NativeSourceAbiWrite.code.extract' 281 282 = ⟨#[32]⟩ := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte0 : NativeSourceAbiWrite.code.data[281]? = some 32 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  apply ByteArray.ext
  simp only [ByteArray.extract', show (281 < 2^64 && 282 < 2^64) = true by decide, if_true, ByteArray.data_extract]
  apply Array.ext
  · simp only [Array.size_extract, size, ByteArray.size_data]; decide
  · intro index left right
    have bound : index < 1 := by simpa using right
    have zero : index = 0 := by omega
    subst index
    simp only [Array.getElem_extract, Nat.add_zero]
    exact Option.some.inj ((Array.getElem?_eq_getElem (by change 281 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte0)

theorem decode280 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 280) = some (.Push .PUSH1, some (UInt256.ofNat 32, 1)) := by
  have byte : NativeSourceAbiWrite.code.get? 280 = some 96 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 280).toNat = 280 by decide, byte]
  change some (Operation.Push Operation.POp.PUSH1, some (uInt256OfByteArray (NativeSourceAbiWrite.code.extract' 281 282), 1)) = _
  rw [immediate280]
  decide

theorem decode282 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 282) = some (.DUP4, none) := by
  have byte : NativeSourceAbiWrite.code.get? 282 = some 131 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 282).toNat = 282 by decide, byte]
  decide

theorem immediate283 : NativeSourceAbiWrite.code.extract' 284 285 = ⟨#[5]⟩ := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte0 : NativeSourceAbiWrite.code.data[284]? = some 5 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  apply ByteArray.ext
  simp only [ByteArray.extract', show (284 < 2^64 && 285 < 2^64) = true by decide, if_true, ByteArray.data_extract]
  apply Array.ext
  · simp only [Array.size_extract, size, ByteArray.size_data]; decide
  · intro index left right
    have bound : index < 1 := by simpa using right
    have zero : index = 0 := by omega
    subst index
    simp only [Array.getElem_extract, Nat.add_zero]
    exact Option.some.inj ((Array.getElem?_eq_getElem (by change 284 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte0)

theorem decode283 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 283) = some (.Push .PUSH1, some (UInt256.ofNat 5, 1)) := by
  have byte : NativeSourceAbiWrite.code.get? 283 = some 96 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 283).toNat = 283 by decide, byte]
  change some (Operation.Push Operation.POp.PUSH1, some (uInt256OfByteArray (NativeSourceAbiWrite.code.extract' 284 285), 1)) = _
  rw [immediate283]
  decide

theorem decode285 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 285) = some (.SHL, none) := by
  have byte : NativeSourceAbiWrite.code.get? 285 = some 27 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 285).toNat = 285 by decide, byte]
  decide

theorem decode286 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 286) = some (.ADD, none) := by
  have byte : NativeSourceAbiWrite.code.get? 286 = some 1 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 286).toNat = 286 by decide, byte]
  decide

theorem decode287 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 287) = some (.DUP6, none) := by
  have byte : NativeSourceAbiWrite.code.get? 287 = some 133 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 287).toNat = 287 by decide, byte]
  decide

theorem immediate288 : NativeSourceAbiWrite.code.extract' 289 291 = ⟨#[3, 142]⟩ := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte0 : NativeSourceAbiWrite.code.data[289]? = some 3 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have byte1 : NativeSourceAbiWrite.code.data[290]? = some 142 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  apply ByteArray.ext
  simp only [ByteArray.extract', show (289 < 2^64 && 291 < 2^64) = true by decide, if_true, ByteArray.data_extract]
  apply Array.ext
  · simp only [Array.size_extract, size, ByteArray.size_data]; decide
  · intro index left right
    have bound : index < 2 := by simpa using right
    have cases : index = 0 ∨ index = 1 := by omega
    rcases cases with rfl | rfl
    · simp only [Array.getElem_extract, Nat.add_zero]
      exact Option.some.inj ((Array.getElem?_eq_getElem (by change 289 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte0)
    · simp only [Array.getElem_extract]
      exact Option.some.inj ((Array.getElem?_eq_getElem (by change 290 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte1)

theorem decode288 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 288) = some (.Push .PUSH2, some (UInt256.ofNat 910, 2)) := by
  have byte : NativeSourceAbiWrite.code.get? 288 = some 97 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 288).toNat = 288 by decide, byte]
  change some (Operation.Push Operation.POp.PUSH2, some (uInt256OfByteArray (NativeSourceAbiWrite.code.extract' 289 291), 2)) = _
  rw [immediate288]
  decide

theorem decode291 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 291) = some (.JUMP, none) := by
  have byte : NativeSourceAbiWrite.code.get? 291 = some 86 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 291).toNat = 291 by decide, byte]
  decide

end Compiler.Proofs.IRGeneration.NativeSourceArrayAllocationDecodes

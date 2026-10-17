import Compiler.Proofs.IRGeneration.NativeSourceReturnScannerFirst

namespace Compiler.Proofs.IRGeneration.NativeSourceReturnScannerPart1
open EvmYul

theorem scan0 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 211 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 212 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[211]? = some 144 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 211 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[211] = 144 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan1 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 212 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 214 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[212]? = some 96 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 212 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[212] = 96 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan2 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 214 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 215 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[214]? = some 132 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 214 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[214] = 132 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan3 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 215 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 216 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[215]? = some 1 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 215 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[215] = 1 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan4 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 216 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 217 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[216]? = some 145 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 216 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[216] = 145 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan5 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 217 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 218 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[217]? = some 130 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 217 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[217] = 130 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan6 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 218 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 219 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[218]? = some 82 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 218 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[218] = 82 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan7 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 219 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 221 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[219]? = some 96 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 219 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[219] = 96 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan8 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 221 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 222 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[221]? = some 131 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 221 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[221] = 131 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan9 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 222 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 223 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[222]? = some 1 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 222 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[222] = 1 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan10 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 223 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 224 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[223]? = some 53 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 223 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[223] = 53 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan11 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 224 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 233 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[224]? = some 103 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 224 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[224] = 103 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan12 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 233 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 234 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[233]? = some 129 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 233 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[233] = 129 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan13 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 234 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 235 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[234]? = some 17 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 234 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[234] = 17 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan14 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 235 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 238 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[235]? = some 97 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 235 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[235] = 97 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan15 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 238 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 239 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[238]? = some 87 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 238 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[238] = 87 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan16 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 239 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 240 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[239]? = some 131 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 239 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[239] = 131 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan17 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 240 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 241 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[240]? = some 1 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 240 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[240] = 1 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan18 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 241 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 242 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[241]? = some 144 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 241 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[241] = 144 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan19 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 242 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 243 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[242]? = some 54 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 242 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[242] = 54 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan20 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 243 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 245 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[243]? = some 96 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 243 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[243] = 96 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan21 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 245 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 246 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[245]? = some 131 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 245 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[245] = 131 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan22 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 246 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 247 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[246]? = some 1 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 246 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[246] = 1 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan23 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 247 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 248 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[247]? = some 18 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 247 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[247] = 18 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan24 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 248 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 249 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[248]? = some 21 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 248 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[248] = 21 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan25 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 249 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 252 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[249]? = some 97 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 249 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[249] = 97 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan26 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 252 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 253 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[252]? = some 87 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 252 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[252] = 87 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan27 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 253 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 255 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[253]? = some 96 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 253 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[253] = 96 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan28 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 255 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 256 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[255]? = some 130 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 255 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[255] = 130 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan29 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 256 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 257 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[256]? = some 1 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 256 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[256] = 1 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan30 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 257 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 258 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[257]? = some 53 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 257 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[257] = 53 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan31 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 258 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 267 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[258]? = some 103 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 258 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[258] = 103 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan32 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 267 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 268 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[267]? = some 129 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 267 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[267] = 129 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan33 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 268 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 269 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[268]? = some 17 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 268 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[268] = 17 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan34 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 269 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 272 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[269]? = some 97 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 269 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[269] = 97 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan35 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 272 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 273 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[272]? = some 87 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 272 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[272] = 87 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan36 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 273 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 275 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[273]? = some 96 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 273 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[273] = 96 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan37 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 275 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 276 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[275]? = some 81 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 275 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[275] = 81 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan38 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 276 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 277 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[276]? = some 146 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 276 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[276] = 146 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan39 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 277 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 280 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[277]? = some 97 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 277 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[277] = 97 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan40 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 280 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 282 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[280]? = some 96 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 280 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[280] = 96 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan41 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 282 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 283 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[282]? = some 131 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 282 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[282] = 131 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan42 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 283 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 285 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[283]? = some 96 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 283 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[283] = 96 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan43 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 285 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 286 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[285]? = some 27 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 285 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[285] = 27 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan44 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 286 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 287 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[286]? = some 1 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 286 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[286] = 1 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan45 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 287 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 288 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[287]? = some 133 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 287 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[287] = 133 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan46 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 288 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 291 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[288]? = some 97 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 288 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[288] = 97 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan47 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 291 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 292 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[291]? = some 86 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 291 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[291] = 86 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan48 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 292 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 293 (found.push (UInt256.ofNat 292)) := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[292]? = some 91 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 292 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[292] = 91 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan49 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 293 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 294 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[293]? = some 129 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 293 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[293] = 129 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan50 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 294 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 295 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[294]? = some 132 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 294 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[294] = 132 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan51 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 295 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 296 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[295]? = some 82 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 295 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[295] = 82 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan52 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 296 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 298 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[296]? = some 96 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 296 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[296] = 96 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan53 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 298 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 300 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[298]? = some 96 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 298 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[298] = 96 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan54 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 300 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 301 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[300]? = some 129 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 300 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[300] = 129 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan55 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 301 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 302 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[301]? = some 134 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 301 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[301] = 134 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan56 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 302 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 303 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[302]? = some 1 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 302 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[302] = 1 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan57 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 303 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 304 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[303]? = some 147 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 303 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[303] = 147 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan58 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 304 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 306 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[304]? = some 96 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 304 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[304] = 96 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan59 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 306 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 307 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[306]? = some 27 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 306 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[306] = 27 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scanned_block (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 60) 211 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 307 (found.push (UInt256.ofNat 292)) := by
  rw [scan0, scan1, scan2, scan3, scan4, scan5, scan6]
  rw [scan7, scan8, scan9, scan10, scan11, scan12, scan13]
  rw [scan14, scan15, scan16, scan17, scan18, scan19, scan20]
  rw [scan21, scan22, scan23, scan24, scan25, scan26, scan27]
  rw [scan28, scan29, scan30, scan31, scan32, scan33, scan34]
  rw [scan35, scan36, scan37, scan38, scan39, scan40, scan41]
  rw [scan42, scan43, scan44, scan45, scan46, scan47, scan48]
  rw [scan49, scan50, scan51, scan52, scan53, scan54, scan55]
  rw [scan56, scan57, scan58, scan59]

end Compiler.Proofs.IRGeneration.NativeSourceReturnScannerPart1

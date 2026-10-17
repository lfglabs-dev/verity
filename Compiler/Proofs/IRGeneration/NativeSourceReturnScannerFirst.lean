import Compiler.Proofs.IRGeneration.NativeSourceJumpDestinations

namespace Compiler.Proofs.IRGeneration.NativeSourceReturnScannerFirst
open EvmYul

theorem scan0 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 92 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 93 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[92]? = some 95 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 92 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[92] = 95 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan1 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 93 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 94 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[93]? = some 128 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 93 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[93] = 128 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan2 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 94 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 95 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[94]? = some 253 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 94 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[94] = 253 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan3 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 95 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 96 (found.push (UInt256.ofNat 95)) := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[95]? = some 91 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 95 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[95] = 91 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan4 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 96 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 97 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[96]? = some 52 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 96 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[96] = 52 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan5 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 97 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 100 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[97]? = some 97 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 97 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[97] = 97 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan6 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 100 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 101 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[100]? = some 87 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 100 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[100] = 87 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan7 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 101 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 103 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[101]? = some 96 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 101 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[101] = 96 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan8 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 103 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 104 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[103]? = some 54 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 103 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[103] = 54 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan9 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 104 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 106 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[104]? = some 96 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 104 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[104] = 96 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan10 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 106 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 107 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[106]? = some 25 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 106 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[106] = 25 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan11 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 107 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 108 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[107]? = some 1 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 107 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[107] = 1 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan12 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 108 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 109 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[108]? = some 18 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 108 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[108] = 18 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan13 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 109 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 112 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[109]? = some 97 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 109 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[109] = 97 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan14 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 112 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 113 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[112]? = some 87 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 112 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[112] = 87 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan15 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 113 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 115 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[113]? = some 96 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 113 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[113] = 96 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan16 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 115 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 116 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[115]? = some 53 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 115 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[115] = 53 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan17 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 116 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 125 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[116]? = some 103 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 116 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[116] = 103 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan18 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 125 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 126 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[125]? = some 129 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 125 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[125] = 129 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan19 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 126 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 127 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[126]? = some 17 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 126 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[126] = 17 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan20 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 127 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 130 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[127]? = some 97 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 127 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[127] = 97 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan21 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 130 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 131 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[130]? = some 87 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 130 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[130] = 87 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan22 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 131 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 134 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[131]? = some 97 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 131 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[131] = 97 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan23 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 134 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 136 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[134]? = some 96 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 134 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[134] = 96 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan24 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 136 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 137 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[136]? = some 25 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 136 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[136] = 25 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan25 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 137 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 138 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[137]? = some 130 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 137 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[137] = 130 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan26 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 138 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 139 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[138]? = some 54 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 138 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[138] = 54 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan27 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 139 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 140 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[139]? = some 3 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 139 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[139] = 3 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan28 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 140 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 141 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[140]? = some 1 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 140 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[140] = 1 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan29 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 141 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 142 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[141]? = some 18 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 141 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[141] = 18 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan30 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 142 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 145 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[142]? = some 97 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 142 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[142] = 97 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan31 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 145 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 146 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[145]? = some 87 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 145 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[145] = 87 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan32 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 146 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 149 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[146]? = some 97 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 146 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[146] = 97 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan33 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 149 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 150 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[149]? = some 130 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 149 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[149] = 130 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan34 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 150 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 151 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[150]? = some 1 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 150 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[150] = 1 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan35 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 151 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 152 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[151]? = some 130 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 151 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[151] = 130 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan36 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 152 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 153 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[152]? = some 129 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 152 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[152] = 129 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan37 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 153 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 154 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[153]? = some 16 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 153 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[153] = 16 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan38 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 154 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 163 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[154]? = some 103 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 154 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[154] = 103 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan39 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 163 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 164 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[163]? = some 130 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 163 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[163] = 130 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan40 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 164 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 165 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[164]? = some 17 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 164 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[164] = 17 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan41 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 165 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 166 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[165]? = some 23 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 165 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[165] = 23 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan42 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 166 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 169 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[166]? = some 97 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 166 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[166] = 97 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan43 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 169 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 170 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[169]? = some 87 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 169 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[169] = 87 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan44 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 170 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 172 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[170]? = some 96 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 170 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[170] = 96 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan45 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 172 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 173 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[172]? = some 82 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 172 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[172] = 82 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan46 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 173 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 174 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[173]? = some 128 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 173 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[173] = 128 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan47 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 174 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 176 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[174]? = some 96 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 174 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[174] = 96 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan48 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 176 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 177 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[176]? = some 1 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 176 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[176] = 1 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan49 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 177 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 178 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[177]? = some 53 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 177 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[177] = 53 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan50 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 178 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 179 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[178]? = some 130 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 178 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[178] = 130 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan51 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 179 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 180 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[179]? = some 82 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 179 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[179] = 82 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan52 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 180 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 183 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[180]? = some 97 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 180 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[180] = 97 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan53 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 183 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 185 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[183]? = some 96 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 183 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[183] = 96 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan54 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 185 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 186 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[185]? = some 130 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 185 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[185] = 130 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan55 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 186 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 187 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[186]? = some 1 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 186 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[186] = 1 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan56 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 187 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 190 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[187]? = some 97 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 187 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[187] = 97 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan57 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 190 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 191 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[190]? = some 86 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 190 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[190] = 86 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan58 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 191 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 192 (found.push (UInt256.ofNat 191)) := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[191]? = some 91 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 191 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[191] = 91 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan59 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 192 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 194 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[192]? = some 96 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 192 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[192] = 96 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan60 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 194 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 195 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[194]? = some 131 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 194 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[194] = 131 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan61 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 195 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 196 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[195]? = some 1 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 195 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[195] = 1 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan62 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 196 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 197 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[196]? = some 144 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 196 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[196] = 144 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan63 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 197 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 198 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[197]? = some 129 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 197 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[197] = 129 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan64 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 198 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 199 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[198]? = some 82 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 198 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[198] = 82 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan65 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 199 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 202 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[199]? = some 97 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 199 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[199] = 97 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan66 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 202 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 204 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[202]? = some 96 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 202 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[202] = 96 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan67 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 204 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 205 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[204]? = some 131 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 204 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[204] = 131 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan68 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 205 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 206 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[205]? = some 1 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 205 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[205] = 1 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan69 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 206 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 209 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[206]? = some 97 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 206 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[206] = 97 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan70 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 209 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 210 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[209]? = some 86 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 209 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[209] = 86 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scan71 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 210 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 211 (found.push (UInt256.ofNat 210)) := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[210]? = some 91 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 210 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[210] = 91 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  simp only [EVM.D_J_aux, dif_pos inside, value]
  rfl

theorem scanned_to_191 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 59) 92 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 192 ((found.push (UInt256.ofNat 95)).push (UInt256.ofNat 191)) := by
  rw [scan0, scan1, scan2, scan3, scan4, scan5, scan6]
  rw [scan7, scan8, scan9, scan10, scan11, scan12, scan13]
  rw [scan14, scan15, scan16, scan17, scan18, scan19, scan20]
  rw [scan21, scan22, scan23, scan24, scan25, scan26, scan27]
  rw [scan28, scan29, scan30, scan31, scan32, scan33, scan34]
  rw [scan35, scan36, scan37, scan38, scan39, scan40, scan41]
  rw [scan42, scan43, scan44, scan45, scan46, scan47, scan48]
  rw [scan49, scan50, scan51, scan52, scan53, scan54, scan55]
  rw [scan56, scan57, scan58]

theorem return_191 : UInt256.ofNat 191 ∈ EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0) := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  unfold EVM.D_J
  rw [size]
  change UInt256.ofNat 191 ∈ EVM.D_J_aux NativeSourceAbiWrite.code ((855 + 59) + 63) 0 #[]
  rw [NativeSourceJumpDestinations.scanned_prefix, scanned_to_191]
  apply NativeJumpScannerFrame.preserves
  simp

theorem scanned_to_210 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 72) 92 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 211 (((found.push (UInt256.ofNat 95)).push (UInt256.ofNat 191)).push (UInt256.ofNat 210)) := by
  rw [scan0, scan1, scan2, scan3, scan4, scan5, scan6]
  rw [scan7, scan8, scan9, scan10, scan11, scan12, scan13]
  rw [scan14, scan15, scan16, scan17, scan18, scan19, scan20]
  rw [scan21, scan22, scan23, scan24, scan25, scan26, scan27]
  rw [scan28, scan29, scan30, scan31, scan32, scan33, scan34]
  rw [scan35, scan36, scan37, scan38, scan39, scan40, scan41]
  rw [scan42, scan43, scan44, scan45, scan46, scan47, scan48]
  rw [scan49, scan50, scan51, scan52, scan53, scan54, scan55]
  rw [scan56, scan57, scan58, scan59, scan60, scan61, scan62]
  rw [scan63, scan64, scan65, scan66, scan67, scan68, scan69]
  rw [scan70, scan71]

theorem return_210 : UInt256.ofNat 210 ∈ EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0) := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  unfold EVM.D_J
  rw [size]
  change UInt256.ofNat 210 ∈ EVM.D_J_aux NativeSourceAbiWrite.code ((842 + 72) + 63) 0 #[]
  rw [NativeSourceJumpDestinations.scanned_prefix, scanned_to_210]
  apply NativeJumpScannerFrame.preserves
  simp

end Compiler.Proofs.IRGeneration.NativeSourceReturnScannerFirst

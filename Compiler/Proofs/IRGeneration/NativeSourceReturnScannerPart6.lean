import Compiler.Proofs.IRGeneration.NativeJumpScannerStep
import Compiler.Proofs.IRGeneration.NativeSourceReturnScannerPart5

namespace Compiler.Proofs.IRGeneration.NativeSourceReturnScannerPart6
open EvmYul

theorem scan0 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 637 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 638 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[637]? = some 133 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 637 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[637] = 133 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 133) = some (.DUP6) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 637 found (.DUP6) inside
    (by rw [value]; exact parsed)

theorem scan1 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 638 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 639 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[638]? = some 147 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 638 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[638] = 147 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 147) = some (.SWAP4) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 638 found (.SWAP4) inside
    (by rw [value]; exact parsed)

theorem scan2 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 639 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 640 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[639]? = some 131 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 639 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[639] = 131 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 131) = some (.DUP4) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 639 found (.DUP4) inside
    (by rw [value]; exact parsed)

theorem scan3 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 640 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 641 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[640]? = some 133 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 640 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[640] = 133 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 133) = some (.DUP6) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 640 found (.DUP6) inside
    (by rw [value]; exact parsed)

theorem scan4 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 641 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 642 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[641]? = some 1 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 641 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[641] = 1 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 1) = some (.ADD) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 641 found (.ADD) inside
    (by rw [value]; exact parsed)

theorem scan5 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 642 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 643 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[642]? = some 151 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 642 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[642] = 151 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 151) = some (.SWAP8) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 642 found (.SWAP8) inside
    (by rw [value]; exact parsed)

theorem scan6 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 643 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 644 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[643]? = some 81 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 643 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[643] = 81 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 81) = some (.MLOAD) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 643 found (.MLOAD) inside
    (by rw [value]; exact parsed)

theorem scan7 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 644 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 645 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[644]? = some 128 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 644 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[644] = 128 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 128) = some (.DUP1) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 644 found (.DUP1) inside
    (by rw [value]; exact parsed)

theorem scan8 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 645 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 646 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[645]? = some 145 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 645 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[645] = 145 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 145) = some (.SWAP2) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 645 found (.SWAP2) inside
    (by rw [value]; exact parsed)

theorem scan9 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 646 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 647 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[646]? = some 137 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 646 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[646] = 137 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 137) = some (.DUP10) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 646 found (.DUP10) inside
    (by rw [value]; exact parsed)

theorem scan10 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 647 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 648 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[647]? = some 94 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 647 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[647] = 94 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 94) = some (.MCOPY) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 647 found (.MCOPY) inside
    (by rw [value]; exact parsed)

theorem scan11 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 648 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 649 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[648]? = some 132 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 648 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[648] = 132 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 132) = some (.DUP5) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 648 found (.DUP5) inside
    (by rw [value]; exact parsed)

theorem scan12 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 649 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 650 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[649]? = some 1 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 649 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[649] = 1 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 1) = some (.ADD) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 649 found (.ADD) inside
    (by rw [value]; exact parsed)

theorem scan13 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 650 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 651 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[650]? = some 144 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 650 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[650] = 144 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 144) = some (.SWAP1) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 650 found (.SWAP1) inside
    (by rw [value]; exact parsed)

theorem scan14 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 651 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 652 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[651]? = some 131 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 651 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[651] = 131 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 131) = some (.DUP4) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 651 found (.DUP4) inside
    (by rw [value]; exact parsed)

theorem scan15 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 652 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 653 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[652]? = some 130 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 652 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[652] = 130 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 130) = some (.DUP3) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 652 found (.DUP3) inside
    (by rw [value]; exact parsed)

theorem scan16 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 653 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 654 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[653]? = some 1 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 653 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[653] = 1 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 1) = some (.ADD) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 653 found (.ADD) inside
    (by rw [value]; exact parsed)

theorem scan17 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 654 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 655 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[654]? = some 144 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 654 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[654] = 144 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 144) = some (.SWAP1) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 654 found (.SWAP1) inside
    (by rw [value]; exact parsed)

theorem scan18 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 655 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 656 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[655]? = some 137 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 655 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[655] = 137 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 137) = some (.DUP10) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 655 found (.DUP10) inside
    (by rw [value]; exact parsed)

theorem scan19 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 656 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 657 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[656]? = some 130 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 656 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[656] = 130 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 130) = some (.DUP3) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 656 found (.DUP3) inside
    (by rw [value]; exact parsed)

theorem scan20 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 657 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 658 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[657]? = some 82 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 657 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[657] = 82 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 82) = some (.MSTORE) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 657 found (.MSTORE) inside
    (by rw [value]; exact parsed)

theorem scan21 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 658 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 659 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[658]? = some 81 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 658 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[658] = 81 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 81) = some (.MLOAD) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 658 found (.MLOAD) inside
    (by rw [value]; exact parsed)

theorem scan22 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 659 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 660 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[659]? = some 146 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 659 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[659] = 146 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 146) = some (.SWAP3) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 659 found (.SWAP3) inside
    (by rw [value]; exact parsed)

theorem scan23 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 660 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 661 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[660]? = some 131 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 660 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[660] = 131 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 131) = some (.DUP4) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 660 found (.DUP4) inside
    (by rw [value]; exact parsed)

theorem scan24 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 661 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 662 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[661]? = some 145 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 661 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[661] = 145 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 145) = some (.SWAP2) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 661 found (.SWAP2) inside
    (by rw [value]; exact parsed)

theorem scan25 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 662 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 663 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[662]? = some 94 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 662 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[662] = 94 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 94) = some (.MCOPY) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 662 found (.MCOPY) inside
    (by rw [value]; exact parsed)

theorem scan26 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 663 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 664 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[663]? = some 1 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 663 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[663] = 1 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 1) = some (.ADD) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 663 found (.ADD) inside
    (by rw [value]; exact parsed)

theorem scan27 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 664 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 665 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[664]? = some 1 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 664 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[664] = 1 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 1) = some (.ADD) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 664 found (.ADD) inside
    (by rw [value]; exact parsed)

theorem scan28 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 665 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 666 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[665]? = some 133 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 665 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[665] = 133 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 133) = some (.DUP6) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 665 found (.DUP6) inside
    (by rw [value]; exact parsed)

theorem scan29 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 666 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 667 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[666]? = some 129 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 666 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[666] = 129 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 129) = some (.DUP2) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 666 found (.DUP2) inside
    (by rw [value]; exact parsed)

theorem scan30 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 667 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 668 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[667]? = some 82 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 667 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[667] = 82 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 82) = some (.MSTORE) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 667 found (.MSTORE) inside
    (by rw [value]; exact parsed)

theorem scan31 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 668 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 669 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[668]? = some 3 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 668 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[668] = 3 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 3) = some (.SUB) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 668 found (.SUB) inside
    (by rw [value]; exact parsed)

theorem scan32 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 669 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 671 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[669]? = some 96 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 669 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[669] = 96 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 96) = some (.PUSH1) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 669 found (.PUSH1) inside
    (by rw [value]; exact parsed)

theorem scan33 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 671 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 672 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[671]? = some 25 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 671 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[671] = 25 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 25) = some (.NOT) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 671 found (.NOT) inside
    (by rw [value]; exact parsed)

theorem scan34 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 672 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 673 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[672]? = some 129 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 672 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[672] = 129 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 129) = some (.DUP2) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 672 found (.DUP2) inside
    (by rw [value]; exact parsed)

theorem scan35 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 673 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 674 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[673]? = some 1 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 673 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[673] = 1 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 1) = some (.ADD) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 673 found (.ADD) inside
    (by rw [value]; exact parsed)

theorem scan36 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 674 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 675 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[674]? = some 131 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 674 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[674] = 131 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 131) = some (.DUP4) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 674 found (.DUP4) inside
    (by rw [value]; exact parsed)

theorem scan37 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 675 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 676 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[675]? = some 82 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 675 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[675] = 82 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 82) = some (.MSTORE) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 675 found (.MSTORE) inside
    (by rw [value]; exact parsed)

theorem scan38 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 676 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 677 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[676]? = some 130 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 676 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[676] = 130 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 130) = some (.DUP3) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 676 found (.DUP3) inside
    (by rw [value]; exact parsed)

theorem scan39 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 677 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 680 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[677]? = some 97 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 677 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[677] = 97 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 97) = some (.PUSH2) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 677 found (.PUSH2) inside
    (by rw [value]; exact parsed)

theorem scan40 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 680 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 681 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[680]? = some 86 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 680 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[680] = 86 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 86) = some (.JUMP) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 680 found (.JUMP) inside
    (by rw [value]; exact parsed)

theorem scan41 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 681 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 682 (found.push (UInt256.ofNat 681)) := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[681]? = some 91 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 681 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[681] = 91 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 91) = some (.JUMPDEST) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 681 found (.JUMPDEST) inside
    (by rw [value]; exact parsed)

theorem scan42 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 682 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 683 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[682]? = some 81 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 682 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[682] = 81 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 81) = some (.MLOAD) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 682 found (.MLOAD) inside
    (by rw [value]; exact parsed)

theorem scan43 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 683 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 684 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[683]? = some 144 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 683 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[683] = 144 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 144) = some (.SWAP1) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 683 found (.SWAP1) inside
    (by rw [value]; exact parsed)

theorem scan44 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 684 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 685 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[684]? = some 130 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 684 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[684] = 130 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 130) = some (.DUP3) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 684 found (.DUP3) inside
    (by rw [value]; exact parsed)

theorem scan45 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 685 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 686 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[685]? = some 245 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 685 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[685] = 245 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 245) = some (.CREATE2) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 685 found (.CREATE2) inside
    (by rw [value]; exact parsed)

theorem scan46 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 686 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 687 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[686]? = some 22 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 686 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[686] = 22 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 22) = some (.AND) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 686 found (.AND) inside
    (by rw [value]; exact parsed)

theorem scan47 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 687 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 688 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[687]? = some 128 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 687 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[687] = 128 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 128) = some (.DUP1) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 687 found (.DUP1) inside
    (by rw [value]; exact parsed)

theorem scan48 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 688 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 689 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[688]? = some 21 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 688 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[688] = 21 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 21) = some (.ISZERO) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 688 found (.ISZERO) inside
    (by rw [value]; exact parsed)

theorem scan49 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 689 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 692 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[689]? = some 97 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 689 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[689] = 97 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 97) = some (.PUSH2) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 689 found (.PUSH2) inside
    (by rw [value]; exact parsed)

theorem scan50 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 692 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 693 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[692]? = some 87 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 692 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[692] = 87 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 87) = some (.JUMPI) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 692 found (.JUMPI) inside
    (by rw [value]; exact parsed)

theorem scan51 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 693 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 695 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[693]? = some 96 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 693 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[693] = 96 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 96) = some (.PUSH1) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 693 found (.PUSH1) inside
    (by rw [value]; exact parsed)

theorem scan52 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 695 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 696 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[695]? = some 144 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 695 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[695] = 144 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 144) = some (.SWAP1) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 695 found (.SWAP1) inside
    (by rw [value]; exact parsed)

theorem scan53 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 696 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 698 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[696]? = some 96 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 696 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[696] = 96 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 96) = some (.PUSH1) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 696 found (.PUSH1) inside
    (by rw [value]; exact parsed)

theorem scan54 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 698 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 699 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[698]? = some 81 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 698 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[698] = 81 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 81) = some (.MLOAD) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 698 found (.MLOAD) inside
    (by rw [value]; exact parsed)

theorem scan55 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 699 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 700 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[699]? = some 144 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 699 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[699] = 144 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 144) = some (.SWAP1) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 699 found (.SWAP1) inside
    (by rw [value]; exact parsed)

theorem scan56 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 700 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 701 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[700]? = some 129 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 700 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[700] = 129 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 129) = some (.DUP2) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 700 found (.DUP2) inside
    (by rw [value]; exact parsed)

theorem scan57 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 701 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 702 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[701]? = some 82 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 701 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[701] = 82 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 82) = some (.MSTORE) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 701 found (.MSTORE) inside
    (by rw [value]; exact parsed)

theorem scan58 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 702 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 703 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[702]? = some 243 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 702 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[702] = 243 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 243) = some (.RETURN) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 702 found (.RETURN) inside
    (by rw [value]; exact parsed)

theorem scan59 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 703 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 704 (found.push (UInt256.ofNat 703)) := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[703]? = some 91 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 703 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[703] = 91 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 91) = some (.JUMPDEST) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 703 found (.JUMPDEST) inside
    (by rw [value]; exact parsed)

theorem scanned_block (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 60) 637 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 704 ((found.push (UInt256.ofNat 681)).push (UInt256.ofNat 703)) := by
  rw [scan0, scan1, scan2, scan3, scan4, scan5, scan6]
  rw [scan7, scan8, scan9, scan10, scan11, scan12, scan13]
  rw [scan14, scan15, scan16, scan17, scan18, scan19, scan20]
  rw [scan21, scan22, scan23, scan24, scan25, scan26, scan27]
  rw [scan28, scan29, scan30, scan31, scan32, scan33, scan34]
  rw [scan35, scan36, scan37, scan38, scan39, scan40, scan41]
  rw [scan42, scan43, scan44, scan45, scan46, scan47, scan48]
  rw [scan49, scan50, scan51, scan52, scan53, scan54, scan55]
  rw [scan56, scan57, scan58, scan59]

end Compiler.Proofs.IRGeneration.NativeSourceReturnScannerPart6

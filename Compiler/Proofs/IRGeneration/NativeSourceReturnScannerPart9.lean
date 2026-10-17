import Compiler.Proofs.IRGeneration.NativeJumpScannerStep
import Compiler.Proofs.IRGeneration.NativeSourceReturnScannerPart8

namespace Compiler.Proofs.IRGeneration.NativeSourceReturnScannerPart9
open EvmYul

theorem scan0 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 872 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 873 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[872]? = some 82 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 872 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[872] = 82 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 82) = some (.MSTORE) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 872 found (.MSTORE) inside
    (by rw [value]; exact parsed)

theorem scan1 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 873 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 875 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[873]? = some 96 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 873 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[873] = 96 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 96) = some (.PUSH1) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 873 found (.PUSH1) inside
    (by rw [value]; exact parsed)

theorem scan2 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 875 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 876 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[875]? = some 134 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 875 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[875] = 134 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 134) = some (.DUP7) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 875 found (.DUP7) inside
    (by rw [value]; exact parsed)

theorem scan3 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 876 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 877 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[876]? = some 1 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 876 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[876] = 1 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 1) = some (.ADD) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 876 found (.ADD) inside
    (by rw [value]; exact parsed)

theorem scan4 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 877 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 878 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[877]? = some 53 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 877 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[877] = 53 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 53) = some (.CALLDATALOAD) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 877 found (.CALLDATALOAD) inside
    (by rw [value]; exact parsed)

theorem scan5 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 878 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 880 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[878]? = some 96 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 878 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[878] = 96 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 96) = some (.PUSH1) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 878 found (.PUSH1) inside
    (by rw [value]; exact parsed)

theorem scan6 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 880 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 881 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[880]? = some 130 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 880 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[880] = 130 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 130) = some (.DUP3) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 880 found (.DUP3) inside
    (by rw [value]; exact parsed)

theorem scan7 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 881 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 882 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[881]? = some 1 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 881 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[881] = 1 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 1) = some (.ADD) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 881 found (.ADD) inside
    (by rw [value]; exact parsed)

theorem scan8 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 882 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 883 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[882]? = some 82 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 882 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[882] = 82 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 82) = some (.MSTORE) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 882 found (.MSTORE) inside
    (by rw [value]; exact parsed)

theorem scan9 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 883 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 886 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[883]? = some 97 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 883 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[883] = 97 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 97) = some (.PUSH2) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 883 found (.PUSH2) inside
    (by rw [value]; exact parsed)

theorem scan10 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 886 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 888 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[886]? = some 96 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 886 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[886] = 96 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 96) = some (.PUSH1) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 886 found (.PUSH1) inside
    (by rw [value]; exact parsed)

theorem scan11 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 888 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 889 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[888]? = some 135 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 888 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[888] = 135 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 135) = some (.DUP8) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 888 found (.DUP8) inside
    (by rw [value]; exact parsed)

theorem scan12 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 889 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 890 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[889]? = some 1 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 889 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[889] = 1 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 1) = some (.ADD) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 889 found (.ADD) inside
    (by rw [value]; exact parsed)

theorem scan13 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 890 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 893 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[890]? = some 97 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 890 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[890] = 97 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 97) = some (.PUSH2) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 890 found (.PUSH2) inside
    (by rw [value]; exact parsed)

theorem scan14 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 893 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 894 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[893]? = some 86 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 893 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[893] = 86 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 86) = some (.JUMP) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 893 found (.JUMP) inside
    (by rw [value]; exact parsed)

theorem scan15 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 894 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 895 (found.push (UInt256.ofNat 894)) := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[894]? = some 91 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 894 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[894] = 91 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 91) = some (.JUMPDEST) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 894 found (.JUMPDEST) inside
    (by rw [value]; exact parsed)

theorem scanned_block (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 16) 872 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 895 (found.push (UInt256.ofNat 894)) := by
  rw [scan0, scan1, scan2, scan3, scan4, scan5, scan6]
  rw [scan7, scan8, scan9, scan10, scan11, scan12, scan13]
  rw [scan14, scan15]

end Compiler.Proofs.IRGeneration.NativeSourceReturnScannerPart9

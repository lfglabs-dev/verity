import Compiler.Proofs.IRGeneration.NativeJumpScannerStep
import Compiler.Proofs.IRGeneration.NativeSourceReturnScannerPart7

namespace Compiler.Proofs.IRGeneration.NativeSourceReturnScannerPart8
open EvmYul

theorem scan0 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 780 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 781 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[780]? = some 144 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 780 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[780] = 144 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 144) = some (.SWAP1) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 780 found (.SWAP1) inside
    (by rw [value]; exact parsed)

theorem scan1 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 781 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 782 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[781]? = some 145 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 781 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[781] = 145 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 145) = some (.SWAP2) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 781 found (.SWAP2) inside
    (by rw [value]; exact parsed)

theorem scan2 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 782 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 785 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[782]? = some 97 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 782 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[782] = 97 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 97) = some (.PUSH2) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 782 found (.PUSH2) inside
    (by rw [value]; exact parsed)

theorem scan3 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 785 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 786 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[785]? = some 86 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 785 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[785] = 86 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 86) = some (.JUMP) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 785 found (.JUMP) inside
    (by rw [value]; exact parsed)

theorem scan4 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 786 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 787 (found.push (UInt256.ofNat 786)) := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[786]? = some 91 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 786 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[786] = 91 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 91) = some (.JUMPDEST) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 786 found (.JUMPDEST) inside
    (by rw [value]; exact parsed)

theorem scan5 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 787 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 792 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[787]? = some 99 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 787 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[787] = 99 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 99) = some (.PUSH4) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 787 found (.PUSH4) inside
    (by rw [value]; exact parsed)

theorem scan6 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 792 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 794 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[792]? = some 96 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 792 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[792] = 96 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 96) = some (.PUSH1) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 792 found (.PUSH1) inside
    (by rw [value]; exact parsed)

theorem scan7 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 794 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 795 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[794]? = some 27 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 794 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[794] = 27 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 27) = some (.SHL) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 794 found (.SHL) inside
    (by rw [value]; exact parsed)

theorem scan8 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 795 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 796 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[795]? = some 95 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 795 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[795] = 95 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 95) = some (.PUSH0) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 795 found (.PUSH0) inside
    (by rw [value]; exact parsed)

theorem scan9 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 796 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 797 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[796]? = some 82 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 796 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[796] = 82 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 82) = some (.MSTORE) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 796 found (.MSTORE) inside
    (by rw [value]; exact parsed)

theorem scan10 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 797 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 799 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[797]? = some 96 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 797 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[797] = 96 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 96) = some (.PUSH1) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 797 found (.PUSH1) inside
    (by rw [value]; exact parsed)

theorem scan11 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 799 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 801 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[799]? = some 96 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 799 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[799] = 96 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 96) = some (.PUSH1) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 799 found (.PUSH1) inside
    (by rw [value]; exact parsed)

theorem scan12 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 801 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 802 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[801]? = some 82 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 801 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[801] = 82 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 82) = some (.MSTORE) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 801 found (.MSTORE) inside
    (by rw [value]; exact parsed)

theorem scan13 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 802 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 804 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[802]? = some 96 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 802 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[802] = 96 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 96) = some (.PUSH1) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 802 found (.PUSH1) inside
    (by rw [value]; exact parsed)

theorem scan14 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 804 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 805 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[804]? = some 95 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 804 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[804] = 95 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 95) = some (.PUSH0) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 804 found (.PUSH0) inside
    (by rw [value]; exact parsed)

theorem scan15 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 805 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 806 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[805]? = some 253 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 805 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[805] = 253 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 253) = some (.REVERT) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 805 found (.REVERT) inside
    (by rw [value]; exact parsed)

theorem scan16 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 806 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 807 (found.push (UInt256.ofNat 806)) := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[806]? = some 91 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 806 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[806] = 91 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 91) = some (.JUMPDEST) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 806 found (.JUMPDEST) inside
    (by rw [value]; exact parsed)

theorem scan17 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 807 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 809 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[807]? = some 96 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 807 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[807] = 96 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 96) = some (.PUSH1) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 807 found (.PUSH1) inside
    (by rw [value]; exact parsed)

theorem scan18 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 809 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 810 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[809]? = some 131 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 809 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[809] = 131 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 131) = some (.DUP4) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 809 found (.DUP4) inside
    (by rw [value]; exact parsed)

theorem scan19 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 810 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 811 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[810]? = some 54 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 810 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[810] = 54 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 54) = some (.CALLDATASIZE) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 810 found (.CALLDATASIZE) inside
    (by rw [value]; exact parsed)

theorem scan20 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 811 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 812 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[811]? = some 3 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 811 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[811] = 3 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 3) = some (.SUB) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 811 found (.SUB) inside
    (by rw [value]; exact parsed)

theorem scan21 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 812 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 813 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[812]? = some 18 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 812 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[812] = 18 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 18) = some (.SLT) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 812 found (.SLT) inside
    (by rw [value]; exact parsed)

theorem scan22 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 813 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 816 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[813]? = some 97 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 813 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[813] = 97 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 97) = some (.PUSH2) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 813 found (.PUSH2) inside
    (by rw [value]; exact parsed)

theorem scan23 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 816 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 817 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[816]? = some 87 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 816 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[816] = 87 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 87) = some (.JUMPI) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 816 found (.JUMPI) inside
    (by rw [value]; exact parsed)

theorem scan24 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 817 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 819 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[817]? = some 96 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 817 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[817] = 96 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 96) = some (.PUSH1) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 817 found (.PUSH1) inside
    (by rw [value]; exact parsed)

theorem scan25 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 819 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 820 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[819]? = some 81 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 819 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[819] = 81 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 81) = some (.MLOAD) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 819 found (.MLOAD) inside
    (by rw [value]; exact parsed)

theorem scan26 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 820 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 821 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[820]? = some 144 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 820 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[820] = 144 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 144) = some (.SWAP1) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 820 found (.SWAP1) inside
    (by rw [value]; exact parsed)

theorem scan27 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 821 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 823 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[821]? = some 96 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 821 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[821] = 96 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 96) = some (.PUSH1) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 821 found (.PUSH1) inside
    (by rw [value]; exact parsed)

theorem scan28 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 823 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 824 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[823]? = some 130 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 823 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[823] = 130 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 130) = some (.DUP3) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 823 found (.DUP3) inside
    (by rw [value]; exact parsed)

theorem scan29 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 824 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 825 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[824]? = some 1 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 824 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[824] = 1 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 1) = some (.ADD) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 824 found (.ADD) inside
    (by rw [value]; exact parsed)

theorem scan30 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 825 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 826 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[825]? = some 144 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 825 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[825] = 144 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 144) = some (.SWAP1) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 825 found (.SWAP1) inside
    (by rw [value]; exact parsed)

theorem scan31 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 826 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 827 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[826]? = some 130 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 826 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[826] = 130 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 130) = some (.DUP3) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 826 found (.DUP3) inside
    (by rw [value]; exact parsed)

theorem scan32 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 827 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 828 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[827]? = some 130 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 827 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[827] = 130 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 130) = some (.DUP3) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 827 found (.DUP3) inside
    (by rw [value]; exact parsed)

theorem scan33 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 828 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 829 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[828]? = some 16 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 828 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[828] = 16 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 16) = some (.LT) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 828 found (.LT) inside
    (by rw [value]; exact parsed)

theorem scan34 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 829 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 838 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[829]? = some 103 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 829 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[829] = 103 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 103) = some (.PUSH8) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 829 found (.PUSH8) inside
    (by rw [value]; exact parsed)

theorem scan35 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 838 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 839 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[838]? = some 131 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 838 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[838] = 131 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 131) = some (.DUP4) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 838 found (.DUP4) inside
    (by rw [value]; exact parsed)

theorem scan36 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 839 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 840 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[839]? = some 17 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 839 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[839] = 17 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 17) = some (.GT) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 839 found (.GT) inside
    (by rw [value]; exact parsed)

theorem scan37 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 840 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 841 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[840]? = some 23 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 840 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[840] = 23 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 23) = some (.OR) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 840 found (.OR) inside
    (by rw [value]; exact parsed)

theorem scan38 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 841 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 844 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[841]? = some 97 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 841 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[841] = 97 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 97) = some (.PUSH2) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 841 found (.PUSH2) inside
    (by rw [value]; exact parsed)

theorem scan39 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 844 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 845 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[844]? = some 87 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 844 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[844] = 87 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 87) = some (.JUMPI) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 844 found (.JUMPI) inside
    (by rw [value]; exact parsed)

theorem scan40 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 845 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 847 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[845]? = some 96 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 845 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[845] = 96 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 96) = some (.PUSH1) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 845 found (.PUSH1) inside
    (by rw [value]; exact parsed)

theorem scan41 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 847 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 848 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[847]? = some 146 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 847 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[847] = 146 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 146) = some (.SWAP3) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 847 found (.SWAP3) inside
    (by rw [value]; exact parsed)

theorem scan42 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 848 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 850 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[848]? = some 96 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 848 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[848] = 96 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 96) = some (.PUSH1) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 848 found (.PUSH1) inside
    (by rw [value]; exact parsed)

theorem scan43 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 850 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 851 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[850]? = some 146 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 850 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[850] = 146 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 146) = some (.SWAP3) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 850 found (.SWAP3) inside
    (by rw [value]; exact parsed)

theorem scan44 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 851 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 853 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[851]? = some 96 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 851 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[851] = 96 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 96) = some (.PUSH1) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 851 found (.PUSH1) inside
    (by rw [value]; exact parsed)

theorem scan45 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 853 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 854 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[853]? = some 82 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 853 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[853] = 82 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 82) = some (.MSTORE) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 853 found (.MSTORE) inside
    (by rw [value]; exact parsed)

theorem scan46 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 854 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 857 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[854]? = some 97 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 854 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[854] = 97 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 97) = some (.PUSH2) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 854 found (.PUSH2) inside
    (by rw [value]; exact parsed)

theorem scan47 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 857 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 858 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[857]? = some 134 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 857 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[857] = 134 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 134) = some (.DUP7) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 857 found (.DUP7) inside
    (by rw [value]; exact parsed)

theorem scan48 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 858 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 861 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[858]? = some 97 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 858 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[858] = 97 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 97) = some (.PUSH2) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 858 found (.PUSH2) inside
    (by rw [value]; exact parsed)

theorem scan49 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 861 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 862 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[861]? = some 86 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 861 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[861] = 86 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 86) = some (.JUMP) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 861 found (.JUMP) inside
    (by rw [value]; exact parsed)

theorem scan50 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 862 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 863 (found.push (UInt256.ofNat 862)) := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[862]? = some 91 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 862 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[862] = 91 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 91) = some (.JUMPDEST) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 862 found (.JUMPDEST) inside
    (by rw [value]; exact parsed)

theorem scan51 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 863 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 864 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[863]? = some 129 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 863 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[863] = 129 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 129) = some (.DUP2) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 863 found (.DUP2) inside
    (by rw [value]; exact parsed)

theorem scan52 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 864 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 865 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[864]? = some 82 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 864 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[864] = 82 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 82) = some (.MSTORE) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 864 found (.MSTORE) inside
    (by rw [value]; exact parsed)

theorem scan53 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 865 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 866 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[865]? = some 130 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 865 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[865] = 130 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 130) = some (.DUP3) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 865 found (.DUP3) inside
    (by rw [value]; exact parsed)

theorem scan54 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 866 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 867 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[866]? = some 134 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 866 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[866] = 134 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 134) = some (.DUP7) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 866 found (.DUP7) inside
    (by rw [value]; exact parsed)

theorem scan55 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 867 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 868 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[867]? = some 1 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 867 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[867] = 1 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 1) = some (.ADD) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 867 found (.ADD) inside
    (by rw [value]; exact parsed)

theorem scan56 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 868 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 869 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[868]? = some 53 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 868 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[868] = 53 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 53) = some (.CALLDATALOAD) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 868 found (.CALLDATALOAD) inside
    (by rw [value]; exact parsed)

theorem scan57 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 869 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 870 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[869]? = some 131 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 869 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[869] = 131 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 131) = some (.DUP4) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 869 found (.DUP4) inside
    (by rw [value]; exact parsed)

theorem scan58 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 870 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 871 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[870]? = some 130 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 870 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[870] = 130 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 130) = some (.DUP3) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 870 found (.DUP3) inside
    (by rw [value]; exact parsed)

theorem scan59 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 871 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 872 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[871]? = some 1 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 871 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[871] = 1 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 1) = some (.ADD) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 871 found (.ADD) inside
    (by rw [value]; exact parsed)

theorem scanned_block (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 60) 780 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 872 (((found.push (UInt256.ofNat 786)).push (UInt256.ofNat 806)).push (UInt256.ofNat 862)) := by
  rw [scan0, scan1, scan2, scan3, scan4, scan5, scan6]
  rw [scan7, scan8, scan9, scan10, scan11, scan12, scan13]
  rw [scan14, scan15, scan16, scan17, scan18, scan19, scan20]
  rw [scan21, scan22, scan23, scan24, scan25, scan26, scan27]
  rw [scan28, scan29, scan30, scan31, scan32, scan33, scan34]
  rw [scan35, scan36, scan37, scan38, scan39, scan40, scan41]
  rw [scan42, scan43, scan44, scan45, scan46, scan47, scan48]
  rw [scan49, scan50, scan51, scan52, scan53, scan54, scan55]
  rw [scan56, scan57, scan58, scan59]

end Compiler.Proofs.IRGeneration.NativeSourceReturnScannerPart8

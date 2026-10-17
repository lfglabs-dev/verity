import Compiler.Proofs.IRGeneration.NativeJumpScannerStep
import Compiler.Proofs.IRGeneration.NativeSourceReturnScannerPart3

namespace Compiler.Proofs.IRGeneration.NativeSourceReturnScannerPart4
open EvmYul

theorem scan0 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 483 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 484 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[483]? = some 27 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 483 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[483] = 27 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 27) = some (.SHL) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 483 found (.SHL) inside
    (by rw [value]; exact parsed)

theorem scan1 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 484 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 485 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[484]? = some 3 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 484 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[484] = 3 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 3) = some (.SUB) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 484 found (.SUB) inside
    (by rw [value]; exact parsed)

theorem scan2 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 485 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 487 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[485]? = some 96 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 485 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[485] = 96 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 96) = some (.PUSH1) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 485 found (.PUSH1) inside
    (by rw [value]; exact parsed)

theorem scan3 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 487 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 488 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[487]? = some 81 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 487 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[487] = 81 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 81) = some (.MLOAD) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 487 found (.MLOAD) inside
    (by rw [value]; exact parsed)

theorem scan4 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 488 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 489 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[488]? = some 152 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 488 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[488] = 152 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 152) = some (.SWAP9) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 488 found (.SWAP9) inside
    (by rw [value]; exact parsed)

theorem scan5 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 489 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 490 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[489]? = some 129 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 489 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[489] = 129 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 129) = some (.DUP2) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 489 found (.DUP2) inside
    (by rw [value]; exact parsed)

theorem scan6 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 490 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 492 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[490]? = some 96 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 490 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[490] = 96 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 96) = some (.PUSH1) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 490 found (.PUSH1) inside
    (by rw [value]; exact parsed)

theorem scan7 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 492 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 493 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[492]? = some 139 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 492 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[492] = 139 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 139) = some (.DUP12) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 492 found (.DUP12) inside
    (by rw [value]; exact parsed)

theorem scan8 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 493 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 494 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[493]? = some 1 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 493 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[493] = 1 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 1) = some (.ADD) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 493 found (.ADD) inside
    (by rw [value]; exact parsed)

theorem scan9 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 494 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 495 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[494]? = some 152 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 494 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[494] = 152 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 152) = some (.SWAP9) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 494 found (.SWAP9) inside
    (by rw [value]; exact parsed)

theorem scan10 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 495 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 497 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[495]? = some 96 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 495 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[495] = 96 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 96) = some (.PUSH1) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 495 found (.PUSH1) inside
    (by rw [value]; exact parsed)

theorem scan11 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 497 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 498 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[497]? = some 138 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 497 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[497] = 138 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 138) = some (.DUP11) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 497 found (.DUP11) inside
    (by rw [value]; exact parsed)

theorem scan12 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 498 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 499 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[498]? = some 82 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 498 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[498] = 82 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 82) = some (.MSTORE) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 498 found (.MSTORE) inside
    (by rw [value]; exact parsed)

theorem scan13 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 499 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 502 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[499]? = some 97 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 499 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[499] = 97 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 97) = some (.PUSH2) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 499 found (.PUSH2) inside
    (by rw [value]; exact parsed)

theorem scan14 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 502 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 503 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[502]? = some 140 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 502 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[502] = 140 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 140) = some (.DUP13) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 502 found (.DUP13) inside
    (by rw [value]; exact parsed)

theorem scan15 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 503 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 504 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[503]? = some 1 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 503 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[503] = 1 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 1) = some (.ADD) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 503 found (.ADD) inside
    (by rw [value]; exact parsed)

theorem scan16 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 504 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 505 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[504]? = some 157 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 504 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[504] = 157 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 157) = some (.SWAP14) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 504 found (.SWAP14) inside
    (by rw [value]; exact parsed)

theorem scan17 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 505 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 506 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[505]? = some 81 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 505 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[505] = 81 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 81) = some (.MLOAD) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 505 found (.MLOAD) inside
    (by rw [value]; exact parsed)

theorem scan18 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 506 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 508 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[506]? = some 96 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 506 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[506] = 96 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 96) = some (.PUSH1) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 506 found (.PUSH1) inside
    (by rw [value]; exact parsed)

theorem scan19 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 508 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 509 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[508]? = some 141 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 508 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[508] = 141 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 141) = some (.DUP14) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 508 found (.DUP14) inside
    (by rw [value]; exact parsed)

theorem scan20 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 509 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 510 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[509]? = some 1 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 509 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[509] = 1 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 1) = some (.ADD) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 509 found (.ADD) inside
    (by rw [value]; exact parsed)

theorem scan21 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 510 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 511 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[510]? = some 82 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 510 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[510] = 82 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 82) = some (.MSTORE) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 510 found (.MSTORE) inside
    (by rw [value]; exact parsed)

theorem scan22 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 511 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 512 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[511]? = some 81 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 511 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[511] = 81 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 81) = some (.MLOAD) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 511 found (.MLOAD) inside
    (by rw [value]; exact parsed)

theorem scan23 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 512 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 513 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[512]? = some 22 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 512 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[512] = 22 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 22) = some (.AND) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 512 found (.AND) inside
    (by rw [value]; exact parsed)

theorem scan24 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 513 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 515 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[513]? = some 96 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 513 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[513] = 96 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 96) = some (.PUSH1) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 513 found (.PUSH1) inside
    (by rw [value]; exact parsed)

theorem scan25 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 515 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 516 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[515]? = some 139 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 515 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[515] = 139 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 139) = some (.DUP12) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 515 found (.DUP12) inside
    (by rw [value]; exact parsed)

theorem scan26 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 516 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 517 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[516]? = some 1 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 516 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[516] = 1 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 1) = some (.ADD) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 516 found (.ADD) inside
    (by rw [value]; exact parsed)

theorem scan27 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 517 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 518 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[517]? = some 82 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 517 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[517] = 82 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 82) = some (.MSTORE) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 517 found (.MSTORE) inside
    (by rw [value]; exact parsed)

theorem scan28 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 518 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 519 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[518]? = some 81 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 518 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[518] = 81 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 81) = some (.MLOAD) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 518 found (.MLOAD) inside
    (by rw [value]; exact parsed)

theorem scan29 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 519 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 520 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[519]? = some 22 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 519 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[519] = 22 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 22) = some (.AND) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 519 found (.AND) inside
    (by rw [value]; exact parsed)

theorem scan30 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 520 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 522 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[520]? = some 96 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 520 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[520] = 96 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 96) = some (.PUSH1) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 520 found (.PUSH1) inside
    (by rw [value]; exact parsed)

theorem scan31 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 522 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 523 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[522]? = some 137 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 522 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[522] = 137 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 137) = some (.DUP10) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 522 found (.DUP10) inside
    (by rw [value]; exact parsed)

theorem scan32 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 523 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 524 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[523]? = some 1 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 523 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[523] = 1 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 1) = some (.ADD) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 523 found (.ADD) inside
    (by rw [value]; exact parsed)

theorem scan33 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 524 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 525 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[524]? = some 82 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 524 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[524] = 82 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 82) = some (.MSTORE) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 524 found (.MSTORE) inside
    (by rw [value]; exact parsed)

theorem scan34 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 525 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 526 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[525]? = some 81 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 525 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[525] = 81 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 81) = some (.MLOAD) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 525 found (.MLOAD) inside
    (by rw [value]; exact parsed)

theorem scan35 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 526 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 527 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[526]? = some 152 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 526 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[526] = 152 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 152) = some (.SWAP9) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 526 found (.SWAP9) inside
    (by rw [value]; exact parsed)

theorem scan36 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 527 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 530 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[527]? = some 97 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 527 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[527] = 97 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 97) = some (.PUSH2) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 527 found (.PUSH2) inside
    (by rw [value]; exact parsed)

theorem scan37 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 530 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 532 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[530]? = some 96 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 530 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[530] = 96 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 96) = some (.PUSH1) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 530 found (.PUSH1) inside
    (by rw [value]; exact parsed)

theorem scan38 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 532 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 533 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[532]? = some 137 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 532 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[532] = 137 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 137) = some (.DUP10) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 532 found (.DUP10) inside
    (by rw [value]; exact parsed)

theorem scan39 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 533 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 534 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[533]? = some 1 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 533 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[533] = 1 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 1) = some (.ADD) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 533 found (.ADD) inside
    (by rw [value]; exact parsed)

theorem scan40 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 534 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 535 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[534]? = some 82 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 534 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[534] = 82 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 82) = some (.MSTORE) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 534 found (.MSTORE) inside
    (by rw [value]; exact parsed)

theorem scan41 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 535 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 536 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[535]? = some 137 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 535 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[535] = 137 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 137) = some (.DUP10) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 535 found (.DUP10) inside
    (by rw [value]; exact parsed)

theorem scan42 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 536 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 537 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[536]? = some 81 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 536 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[536] = 81 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 81) = some (.MLOAD) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 536 found (.MLOAD) inside
    (by rw [value]; exact parsed)

theorem scan43 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 537 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 538 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[537]? = some 128 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 537 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[537] = 128 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 128) = some (.DUP1) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 537 found (.DUP1) inside
    (by rw [value]; exact parsed)

theorem scan44 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 538 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 539 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[538]? = some 145 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 538 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[538] = 145 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 145) = some (.SWAP2) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 538 found (.SWAP2) inside
    (by rw [value]; exact parsed)

theorem scan45 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 539 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 540 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[539]? = some 82 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 539 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[539] = 82 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 82) = some (.MSTORE) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 539 found (.MSTORE) inside
    (by rw [value]; exact parsed)

theorem scan46 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 540 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 542 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[540]? = some 96 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 540 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[540] = 96 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 96) = some (.PUSH1) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 540 found (.PUSH1) inside
    (by rw [value]; exact parsed)

theorem scan47 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 542 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 545 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[542]? = some 97 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 542 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[542] = 97 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 97) = some (.PUSH2) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 542 found (.PUSH2) inside
    (by rw [value]; exact parsed)

theorem scan48 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 545 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 546 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[545]? = some 137 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 545 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[545] = 137 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 137) = some (.DUP10) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 545 found (.DUP10) inside
    (by rw [value]; exact parsed)

theorem scan49 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 546 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 547 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[546]? = some 1 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 546 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[546] = 1 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 1) = some (.ADD) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 546 found (.ADD) inside
    (by rw [value]; exact parsed)

theorem scan50 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 547 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 548 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[547]? = some 154 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 547 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[547] = 154 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 154) = some (.SWAP11) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 547 found (.SWAP11) inside
    (by rw [value]; exact parsed)

theorem scan51 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 548 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 549 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[548]? = some 1 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 548 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[548] = 1 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 1) = some (.ADD) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 548 found (.ADD) inside
    (by rw [value]; exact parsed)

theorem scan52 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 549 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 550 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[549]? = some 144 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 549 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[549] = 144 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 144) = some (.SWAP1) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 549 found (.SWAP1) inside
    (by rw [value]; exact parsed)

theorem scan53 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 550 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 551 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[550]? = some 95 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 550 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[550] = 95 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 95) = some (.PUSH0) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 550 found (.PUSH0) inside
    (by rw [value]; exact parsed)

theorem scan54 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 551 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 552 (found.push (UInt256.ofNat 551)) := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[551]? = some 91 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 551 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[551] = 91 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 91) = some (.JUMPDEST) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 551 found (.JUMPDEST) inside
    (by rw [value]; exact parsed)

theorem scan55 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 552 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 553 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[552]? = some 129 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 552 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[552] = 129 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 129) = some (.DUP2) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 552 found (.DUP2) inside
    (by rw [value]; exact parsed)

theorem scan56 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 553 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 554 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[553]? = some 129 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 553 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[553] = 129 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 129) = some (.DUP2) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 553 found (.DUP2) inside
    (by rw [value]; exact parsed)

theorem scan57 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 554 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 555 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[554]? = some 16 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 554 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[554] = 16 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 16) = some (.LT) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 554 found (.LT) inside
    (by rw [value]; exact parsed)

theorem scan58 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 555 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 558 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[555]? = some 97 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 555 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[555] = 97 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 97) = some (.PUSH2) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 555 found (.PUSH2) inside
    (by rw [value]; exact parsed)

theorem scan59 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 558 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 559 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[558]? = some 87 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 558 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[558] = 87 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 87) = some (.JUMPI) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 558 found (.JUMPI) inside
    (by rw [value]; exact parsed)

theorem scanned_block (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 60) 483 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 559 (found.push (UInt256.ofNat 551)) := by
  rw [scan0, scan1, scan2, scan3, scan4, scan5, scan6]
  rw [scan7, scan8, scan9, scan10, scan11, scan12, scan13]
  rw [scan14, scan15, scan16, scan17, scan18, scan19, scan20]
  rw [scan21, scan22, scan23, scan24, scan25, scan26, scan27]
  rw [scan28, scan29, scan30, scan31, scan32, scan33, scan34]
  rw [scan35, scan36, scan37, scan38, scan39, scan40, scan41]
  rw [scan42, scan43, scan44, scan45, scan46, scan47, scan48]
  rw [scan49, scan50, scan51, scan52, scan53, scan54, scan55]
  rw [scan56, scan57, scan58, scan59]

end Compiler.Proofs.IRGeneration.NativeSourceReturnScannerPart4

import Compiler.Proofs.IRGeneration.NativeJumpScannerStep
import Compiler.Proofs.IRGeneration.NativeSourceReturnScannerPart2

namespace Compiler.Proofs.IRGeneration.NativeSourceReturnScannerPart3
open EvmYul

theorem scan0 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 386 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 387 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[386]? = some 1 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 386 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[386] = 1 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 1) = some (.ADD) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 386 found (.ADD) inside
    (by rw [value]; exact parsed)

theorem scan1 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 387 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 388 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[387]? = some 147 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 387 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[387] = 147 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 147) = some (.SWAP4) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 387 found (.SWAP4) inside
    (by rw [value]; exact parsed)

theorem scan2 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 388 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 389 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[388]? = some 132 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 388 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[388] = 132 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 132) = some (.DUP5) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 388 found (.DUP5) inside
    (by rw [value]; exact parsed)

theorem scan3 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 389 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 390 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[389]? = some 82 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 389 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[389] = 82 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 82) = some (.MSTORE) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 389 found (.MSTORE) inside
    (by rw [value]; exact parsed)

theorem scan4 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 390 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 391 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[390]? = some 1 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 390 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[390] = 1 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 1) = some (.ADD) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 390 found (.ADD) inside
    (by rw [value]; exact parsed)

theorem scan5 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 391 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 394 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[391]? = some 97 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 391 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[391] = 97 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 97) = some (.PUSH2) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 391 found (.PUSH2) inside
    (by rw [value]; exact parsed)

theorem scan6 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 394 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 395 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[394]? = some 86 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 394 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[394] = 86 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 86) = some (.JUMP) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 394 found (.JUMP) inside
    (by rw [value]; exact parsed)

theorem scan7 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 395 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 396 (found.push (UInt256.ofNat 395)) := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[395]? = some 91 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 395 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[395] = 91 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 91) = some (.JUMPDEST) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 395 found (.JUMPDEST) inside
    (by rw [value]; exact parsed)

theorem scan8 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 396 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 397 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[396]? = some 145 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 396 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[396] = 145 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 145) = some (.SWAP2) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 396 found (.SWAP2) inside
    (by rw [value]; exact parsed)

theorem scan9 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 397 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 399 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[397]? = some 96 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 397 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[397] = 96 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 96) = some (.PUSH1) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 397 found (.PUSH1) inside
    (by rw [value]; exact parsed)

theorem scan10 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 399 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 400 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[399]? = some 136 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 399 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[399] = 136 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 136) = some (.DUP9) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 399 found (.DUP9) inside
    (by rw [value]; exact parsed)

theorem scan11 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 400 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 401 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[400]? = some 1 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 400 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[400] = 1 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 1) = some (.ADD) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 400 found (.ADD) inside
    (by rw [value]; exact parsed)

theorem scan12 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 401 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 402 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[401]? = some 146 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 401 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[401] = 146 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 146) = some (.SWAP3) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 401 found (.SWAP3) inside
    (by rw [value]; exact parsed)

theorem scan13 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 402 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 403 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[402]? = some 131 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 402 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[402] = 131 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 131) = some (.DUP4) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 402 found (.DUP4) inside
    (by rw [value]; exact parsed)

theorem scan14 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 403 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 404 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[403]? = some 82 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 403 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[403] = 82 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 82) = some (.MSTORE) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 403 found (.MSTORE) inside
    (by rw [value]; exact parsed)

theorem scan15 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 404 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 406 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[404]? = some 96 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 404 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[404] = 96 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 96) = some (.PUSH1) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 404 found (.PUSH1) inside
    (by rw [value]; exact parsed)

theorem scan16 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 406 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 407 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[406]? = some 53 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 406 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[406] = 53 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 53) = some (.CALLDATALOAD) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 406 found (.CALLDATALOAD) inside
    (by rw [value]; exact parsed)

theorem scan17 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 407 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 408 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[407]? = some 95 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 407 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[407] = 95 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 95) = some (.PUSH0) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 407 found (.PUSH0) inside
    (by rw [value]; exact parsed)

theorem scan18 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 408 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 409 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[408]? = some 82 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 408 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[408] = 82 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 82) = some (.MSTORE) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 408 found (.MSTORE) inside
    (by rw [value]; exact parsed)

theorem scan19 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 409 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 410 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[409]? = some 95 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 409 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[409] = 95 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 95) = some (.PUSH0) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 409 found (.PUSH0) inside
    (by rw [value]; exact parsed)

theorem scan20 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 410 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 412 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[410]? = some 96 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 410 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[410] = 96 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 96) = some (.PUSH1) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 410 found (.PUSH1) inside
    (by rw [value]; exact parsed)

theorem scan21 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 412 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 413 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[412]? = some 82 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 412 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[412] = 82 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 82) = some (.MSTORE) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 412 found (.MSTORE) inside
    (by rw [value]; exact parsed)

theorem scan22 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 413 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 415 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[413]? = some 96 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 413 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[413] = 96 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 96) = some (.PUSH1) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 413 found (.PUSH1) inside
    (by rw [value]; exact parsed)

theorem scan23 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 415 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 416 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[415]? = some 53 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 415 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[415] = 53 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 53) = some (.CALLDATALOAD) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 415 found (.CALLDATALOAD) inside
    (by rw [value]; exact parsed)

theorem scan24 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 416 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 418 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[416]? = some 96 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 416 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[416] = 96 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 96) = some (.PUSH1) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 416 found (.PUSH1) inside
    (by rw [value]; exact parsed)

theorem scan25 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 418 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 419 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[418]? = some 95 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 418 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[418] = 95 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 95) = some (.PUSH0) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 418 found (.PUSH0) inside
    (by rw [value]; exact parsed)

theorem scan26 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 419 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 420 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[419]? = some 32 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 419 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[419] = 32 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 32) = some (.KECCAK256) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 419 found (.KECCAK256) inside
    (by rw [value]; exact parsed)

theorem scan27 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 420 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 421 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[420]? = some 85 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 420 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[420] = 85 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 85) = some (.SSTORE) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 420 found (.SSTORE) inside
    (by rw [value]; exact parsed)

theorem scan28 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 421 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 423 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[421]? = some 96 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 421 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[421] = 96 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 96) = some (.PUSH1) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 421 found (.PUSH1) inside
    (by rw [value]; exact parsed)

theorem scan29 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 423 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 424 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[423]? = some 81 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 423 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[423] = 81 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 81) = some (.MLOAD) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 423 found (.MLOAD) inside
    (by rw [value]; exact parsed)

theorem scan30 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 424 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 425 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[424]? = some 150 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 424 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[424] = 150 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 150) = some (.SWAP7) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 424 found (.SWAP7) inside
    (by rw [value]; exact parsed)

theorem scan31 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 425 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 427 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[425]? = some 96 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 425 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[425] = 96 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 96) = some (.PUSH1) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 425 found (.PUSH1) inside
    (by rw [value]; exact parsed)

theorem scan32 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 427 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 428 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[427]? = some 136 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 427 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[427] = 136 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 136) = some (.DUP9) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 427 found (.DUP9) inside
    (by rw [value]; exact parsed)

theorem scan33 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 428 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 429 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[428]? = some 1 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 428 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[428] = 1 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 1) = some (.ADD) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 428 found (.ADD) inside
    (by rw [value]; exact parsed)

theorem scan34 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 429 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 430 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[429]? = some 136 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 429 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[429] = 136 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 136) = some (.DUP9) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 429 found (.DUP9) inside
    (by rw [value]; exact parsed)

theorem scan35 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 430 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 431 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[430]? = some 129 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 430 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[430] = 129 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 129) = some (.DUP2) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 430 found (.DUP2) inside
    (by rw [value]; exact parsed)

theorem scan36 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 431 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 432 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[431]? = some 16 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 431 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[431] = 16 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 16) = some (.LT) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 431 found (.LT) inside
    (by rw [value]; exact parsed)

theorem scan37 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 432 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 441 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[432]? = some 103 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 432 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[432] = 103 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 103) = some (.PUSH8) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 432 found (.PUSH8) inside
    (by rw [value]; exact parsed)

theorem scan38 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 441 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 442 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[441]? = some 130 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 441 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[441] = 130 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 130) = some (.DUP3) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 441 found (.DUP3) inside
    (by rw [value]; exact parsed)

theorem scan39 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 442 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 443 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[442]? = some 17 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 442 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[442] = 17 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 17) = some (.GT) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 442 found (.GT) inside
    (by rw [value]; exact parsed)

theorem scan40 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 443 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 444 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[443]? = some 23 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 443 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[443] = 23 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 23) = some (.OR) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 443 found (.OR) inside
    (by rw [value]; exact parsed)

theorem scan41 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 444 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 447 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[444]? = some 97 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 444 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[444] = 97 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 97) = some (.PUSH2) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 444 found (.PUSH2) inside
    (by rw [value]; exact parsed)

theorem scan42 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 447 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 448 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[447]? = some 87 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 447 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[447] = 87 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 87) = some (.JUMPI) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 447 found (.JUMPI) inside
    (by rw [value]; exact parsed)

theorem scan43 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 448 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 450 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[448]? = some 96 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 448 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[448] = 96 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 96) = some (.PUSH1) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 448 found (.PUSH1) inside
    (by rw [value]; exact parsed)

theorem scan44 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 450 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 451 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[450]? = some 82 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 450 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[450] = 82 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 82) = some (.MSTORE) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 450 found (.MSTORE) inside
    (by rw [value]; exact parsed)

theorem scan45 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 451 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 453 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[451]? = some 96 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 451 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[451] = 96 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 96) = some (.PUSH1) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 451 found (.PUSH1) inside
    (by rw [value]; exact parsed)

theorem scan46 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 453 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 454 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[453]? = some 136 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 453 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[453] = 136 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 136) = some (.DUP9) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 453 found (.DUP9) inside
    (by rw [value]; exact parsed)

theorem scan47 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 454 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 455 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[454]? = some 82 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 454 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[454] = 82 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 82) = some (.MSTORE) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 454 found (.MSTORE) inside
    (by rw [value]; exact parsed)

theorem scan48 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 455 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 457 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[455]? = some 96 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 455 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[455] = 96 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 96) = some (.PUSH1) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 455 found (.PUSH1) inside
    (by rw [value]; exact parsed)

theorem scan49 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 457 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 458 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[457]? = some 136 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 457 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[457] = 136 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 136) = some (.DUP9) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 457 found (.DUP9) inside
    (by rw [value]; exact parsed)

theorem scan50 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 458 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 459 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[458]? = some 1 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 458 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[458] = 1 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 1) = some (.ADD) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 458 found (.ADD) inside
    (by rw [value]; exact parsed)

theorem scan51 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 459 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 460 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[459]? = some 149 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 459 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[459] = 149 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 149) = some (.SWAP6) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 459 found (.SWAP6) inside
    (by rw [value]; exact parsed)

theorem scan52 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 460 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 472 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[460]? = some 106 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 460 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[460] = 106 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 106) = some (.PUSH11) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 460 found (.PUSH11) inside
    (by rw [value]; exact parsed)

theorem scan53 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 472 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 474 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[472]? = some 96 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 472 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[472] = 96 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 96) = some (.PUSH1) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 472 found (.PUSH1) inside
    (by rw [value]; exact parsed)

theorem scan54 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 474 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 475 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[474]? = some 27 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 474 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[474] = 27 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 27) = some (.SHL) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 474 found (.SHL) inside
    (by rw [value]; exact parsed)

theorem scan55 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 475 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 476 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[475]? = some 135 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 475 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[475] = 135 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 135) = some (.DUP8) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 475 found (.DUP8) inside
    (by rw [value]; exact parsed)

theorem scan56 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 476 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 477 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[476]? = some 82 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 476 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[476] = 82 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 82) = some (.MSTORE) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 476 found (.MSTORE) inside
    (by rw [value]; exact parsed)

theorem scan57 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 477 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 479 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[477]? = some 96 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 477 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[477] = 96 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 96) = some (.PUSH1) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 477 found (.PUSH1) inside
    (by rw [value]; exact parsed)

theorem scan58 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 479 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 481 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[479]? = some 96 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 479 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[479] = 96 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 96) = some (.PUSH1) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 479 found (.PUSH1) inside
    (by rw [value]; exact parsed)

theorem scan59 (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 1) 481 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 483 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[481]? = some 96 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have inside : 481 < NativeSourceAbiWrite.code.size := by rw [size]; decide
  have value : NativeSourceAbiWrite.code[481] = 96 := by
    exact Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans byte)
  have parsed : EVM.parseInstr (UInt8.ofNat 96) = some (.PUSH1) := by decide
  exact NativeJumpScannerStep.step NativeSourceAbiWrite.code fuel 481 found (.PUSH1) inside
    (by rw [value]; exact parsed)

theorem scanned_block (fuel : Nat) (found : Array UInt256) :
    EVM.D_J_aux NativeSourceAbiWrite.code (fuel + 60) 386 found =
      EVM.D_J_aux NativeSourceAbiWrite.code fuel 483 (found.push (UInt256.ofNat 395)) := by
  rw [scan0, scan1, scan2, scan3, scan4, scan5, scan6]
  rw [scan7, scan8, scan9, scan10, scan11, scan12, scan13]
  rw [scan14, scan15, scan16, scan17, scan18, scan19, scan20]
  rw [scan21, scan22, scan23, scan24, scan25, scan26, scan27]
  rw [scan28, scan29, scan30, scan31, scan32, scan33, scan34]
  rw [scan35, scan36, scan37, scan38, scan39, scan40, scan41]
  rw [scan42, scan43, scan44, scan45, scan46, scan47, scan48]
  rw [scan49, scan50, scan51, scan52, scan53, scan54, scan55]
  rw [scan56, scan57, scan58, scan59]

end Compiler.Proofs.IRGeneration.NativeSourceReturnScannerPart3

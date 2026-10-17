import Compiler.Proofs.IRGeneration.NativeSourceCheckedOffsetGuard

namespace Compiler.Proofs.IRGeneration.NativeSourceOffsetCertificate
open EvmYul EVM EVM.Proof Compiler.Proofs.YulGeneration.Backends

abbrev loaded := NativeSourceCollateralOffsetLoad.s4

def offset (pre : EVM.State) (a : UInt256) := pre.toState.calldataload (a + UInt256.ofNat 100)

def accepted (pre : EVM.State) (x y a base : UInt256) (tail : Stack UInt256) :=
  NativeSourceCheckedReturn.fallthrough
    (NativeSourceCollateralOffsetGuard.s4 (loaded pre x y a base tail) (offset pre a) (x :: y :: a :: base :: tail))
    (offset pre a :: x :: y :: a :: base :: tail)

theorem load_pc (pre : EVM.State) (x y a base : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 219) : (loaded pre x y a base tail).pc = UInt256.ofNat 224 := by
  simp only [loaded, NativeSourceCollateralOffsetLoad.s4, NativeSourceCollateralOffsetLoad.s3,
    NativeSourceCollateralOffsetLoad.s2, NativeSourceCollateralOffsetLoad.s1, stepPre,
    EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
  rw [pc]; decide

theorem accept (fuel : Nat) (pre : EVM.State) (x y a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 219)
    (stack : pre.stack = x :: y :: a :: base :: tail) (valid : (offset pre a).toNat ≤ 2^64-1)
    (gas : 34 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1017) :
    EVM.X (fuel + 10) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      EVM.X (fuel + 1) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) (accepted pre x y a base tail) := by
  have charged := (NativeSourceCollateralOffsetLoad.gas_chain pre x y a base tail (by omega)).2.2.2
  change (loaded pre x y a base tail).gasAvailable.toNat = _ at charged
  have frame := NativeSourceCollateralOffsetLoad.frame pre x y a base tail
  have codeAfter := (congrArg (fun state : EvmYul.State .EVM => state.executionEnv.code) frame.2.1).trans code
  rw [NativeSourceCollateralOffsetLoad.execute (fuel + 5) _ pre x y a base tail code pc stack (by omega) (by omega)]
  exact NativeSourceCheckedOffsetGuard.accept fuel _ (offset pre a) (x :: y :: a :: base :: tail)
    codeAfter (load_pc pre x y a base tail pc) frame.1 valid (by change 22 ≤ (loaded pre x y a base tail).gasAvailable.toNat; omega)
    (by simp only [List.length_cons]; omega)

theorem reject_exact (fuel : Nat) (pre : EVM.State) (x y a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 219)
    (stack : pre.stack = x :: y :: a :: base :: tail) (invalid : 2^64-1 < (offset pre a).toNat)
    (gas : 40 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1017) :
    EVM.X (fuel + 14) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      .ok (.revert (UInt256.ofNat (pre.gasAvailable.toNat - 40)) ByteArray.empty) := by
  have charged := (NativeSourceCollateralOffsetLoad.gas_chain pre x y a base tail (by omega)).2.2.2
  change (loaded pre x y a base tail).gasAvailable.toNat = _ at charged
  have frame := NativeSourceCollateralOffsetLoad.frame pre x y a base tail
  have codeAfter := (congrArg (fun state : EvmYul.State .EVM => state.executionEnv.code) frame.2.1).trans code
  rw [NativeSourceCollateralOffsetLoad.execute (fuel + 9) _ pre x y a base tail code pc stack (by omega) (by omega)]
  rw [NativeSourceCheckedOffsetGuard.reject_exact fuel (loaded pre x y a base tail) (offset pre a)
    (x :: y :: a :: base :: tail) codeAfter (load_pc pre x y a base tail pc) frame.1 invalid (by omega)
    (by simp only [List.length_cons]; omega), charged]
  congr 3

theorem accepted_gas (pre : EVM.State) (x y a base : UInt256) (tail : Stack UInt256)
    (gas : 34 ≤ pre.gasAvailable.toNat) :
    (accepted pre x y a base tail).gasAvailable.toNat = pre.gasAvailable.toNat - 34 := by
  have loadGas := (NativeSourceCollateralOffsetLoad.gas_chain pre x y a base tail (by omega)).2.2.2
  change (loaded pre x y a base tail).gasAvailable.toNat = _ at loadGas
  have guardGas := NativeSourceCheckedOffsetGuard.accepted_gas (loaded pre x y a base tail)
    (offset pre a) (x :: y :: a :: base :: tail) (by omega)
  change (accepted pre x y a base tail).gasAvailable.toNat = _ at guardGas
  omega

theorem accepted_frame (pre : EVM.State) (x y a base : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 219) :
    (accepted pre x y a base tail).pc = UInt256.ofNat 239 ∧
      (accepted pre x y a base tail).stack = offset pre a :: x :: y :: a :: base :: tail ∧
      (accepted pre x y a base tail).toState = pre.toState ∧
      (accepted pre x y a base tail).memory = pre.memory := by
  have guard := NativeSourceCheckedOffsetGuard.accepted_frame (loaded pre x y a base tail)
    (offset pre a) (x :: y :: a :: base :: tail) (load_pc pre x y a base tail pc)
  have loadFrame := NativeSourceCollateralOffsetLoad.frame pre x y a base tail
  exact ⟨guard.1, guard.2.1, guard.2.2.1.trans loadFrame.2.1, guard.2.2.2.trans loadFrame.2.2⟩

theorem canonical_word (pre : EVM.State) (selector key value : Nat) (market : NativeSourceMarketCalldata.Market)
    (encoded : pre.executionEnv.calldata = StateBridge.calldataToByteArray selector
      (NativeSourceMarketCalldata.arguments market key value)) : offset pre (UInt256.ofNat 96) = UInt256.ofNat 256 := by
  have value := (NativeSourceMarketCalldata.header pre selector key value market encoded).2.2.2.1
  unfold offset
  rw [show UInt256.ofNat 96 + UInt256.ofNat 100 = UInt256.ofNat 196 by decide]
  exact NativeSourceMidnightDecodedStore.word_of_nat _ 256 (value.trans (by decide))

theorem market_accept (fuel : Nat) (pre : EVM.State) (x y base : UInt256) (tail : Stack UInt256)
    (selector key value : Nat) (market : NativeSourceMarketCalldata.Market)
    (encoded : pre.executionEnv.calldata = StateBridge.calldataToByteArray selector
      (NativeSourceMarketCalldata.arguments market key value))
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 219)
    (stack : pre.stack = x :: y :: UInt256.ofNat 96 :: base :: tail)
    (gas : 34 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1017) :
    EVM.X (fuel + 10) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      EVM.X (fuel + 1) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0))
        (accepted pre x y (UInt256.ofNat 96) base tail) := by
  apply accept fuel pre x y _ base tail code pc stack _ gas depth
  rw [canonical_word pre selector key value market encoded]
  decide

end Compiler.Proofs.IRGeneration.NativeSourceOffsetCertificate


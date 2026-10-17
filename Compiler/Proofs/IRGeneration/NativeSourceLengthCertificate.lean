import Compiler.Proofs.IRGeneration.NativeSourceLengthAccept

namespace Compiler.Proofs.IRGeneration.NativeSourceLengthCertificate
open EvmYul EVM EVM.Proof Compiler.Proofs.YulGeneration.Backends

abbrev loaded := NativeSourceCollateralLengthLoad.s4

def lengthWord (pre : EVM.State) (a : UInt256) := pre.toState.calldataload (a + UInt256.ofNat 4)

def accepted (pre : EVM.State) (x y a base : UInt256) (tail : Stack UInt256) :=
  NativeSourceCheckedReturn.fallthrough
    (NativeSourceCollateralLengthGuard.s4 (loaded pre x y a base tail) (lengthWord pre a) (x :: a :: y :: base :: tail))
    (lengthWord pre a :: x :: a :: y :: base :: tail)

theorem load_pc (pre : EVM.State) (x y a base : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 253) : (loaded pre x y a base tail).pc = UInt256.ofNat 258 := by
  simp only [loaded, NativeSourceCollateralLengthLoad.s4, NativeSourceCollateralLengthLoad.s3,
    NativeSourceCollateralLengthLoad.s2, NativeSourceCollateralLengthLoad.s1, stepPre,
    EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
  rw [pc]; decide

theorem accept (fuel : Nat) (pre : EVM.State) (x y a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 253)
    (stack : pre.stack = x :: a :: y :: base :: tail) (valid : (lengthWord pre a).toNat ≤ 2^64-1)
    (gas : 34 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1017) :
    EVM.X (fuel + 10) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      EVM.X (fuel + 1) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) (accepted pre x y a base tail) := by
  have charged := (NativeSourceCollateralLengthLoad.gas_chain pre x y a base tail (by omega)).2.2.2
  change (loaded pre x y a base tail).gasAvailable.toNat = _ at charged
  have frame := NativeSourceCollateralLengthLoad.frame pre x y a base tail
  have codeAfter := (congrArg (fun state : EvmYul.State .EVM => state.executionEnv.code) frame.2.1).trans code
  rw [NativeSourceCollateralLengthLoad.execute (fuel + 5) _ pre x y a base tail code pc stack (by omega) (by omega)]
  exact NativeSourceLengthAccept.accept fuel _ (lengthWord pre a) (x :: a :: y :: base :: tail)
    codeAfter (load_pc pre x y a base tail pc) frame.1 valid (by change 22 ≤ (loaded pre x y a base tail).gasAvailable.toNat; omega)
    (by simp only [List.length_cons]; omega)

theorem accepted_gas (pre : EVM.State) (x y a base : UInt256) (tail : Stack UInt256)
    (gas : 34 ≤ pre.gasAvailable.toNat) :
    (accepted pre x y a base tail).gasAvailable.toNat = pre.gasAvailable.toNat - 34 := by
  have loadGas := (NativeSourceCollateralLengthLoad.gas_chain pre x y a base tail (by omega)).2.2.2
  change (loaded pre x y a base tail).gasAvailable.toNat = _ at loadGas
  have guardGas := NativeSourceLengthAccept.accepted_gas (loaded pre x y a base tail)
    (lengthWord pre a) (x :: a :: y :: base :: tail) (by omega)
  change (accepted pre x y a base tail).gasAvailable.toNat = _ at guardGas
  omega

theorem accepted_frame (pre : EVM.State) (x y a base : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 253) :
    (accepted pre x y a base tail).pc = UInt256.ofNat 273 ∧
      (accepted pre x y a base tail).stack = lengthWord pre a :: x :: a :: y :: base :: tail ∧
      (accepted pre x y a base tail).toState = pre.toState ∧
      (accepted pre x y a base tail).memory = pre.memory := by
  have guard := NativeSourceLengthAccept.accepted_frame (loaded pre x y a base tail)
    (lengthWord pre a) (x :: a :: y :: base :: tail) (load_pc pre x y a base tail pc)
  have loadFrame := NativeSourceCollateralLengthLoad.frame pre x y a base tail
  exact ⟨guard.1, guard.2.1, guard.2.2.1.trans loadFrame.2.1, guard.2.2.2.trans loadFrame.2.2⟩

theorem canonical_word (pre : EVM.State) (selector key value : Nat) (market : NativeSourceMarketCalldata.Market)
    (encoded : pre.executionEnv.calldata = StateBridge.calldataToByteArray selector
      (NativeSourceMarketCalldata.arguments market key value))
    (bound : market.collateral.length ≤ 2^64-1) :
    lengthWord pre (UInt256.ofNat 352) = UInt256.ofNat market.collateral.length := by
  have loaded := (NativeSourceMarketCalldata.header pre selector key value market encoded).2.2.2.2.2.2.2.2
  have modulus : 2^64-1 < Compiler.Constants.evmModulus := by decide
  rw [Nat.mod_eq_of_lt (by omega)] at loaded
  unfold lengthWord
  rw [show UInt256.ofNat 352 + UInt256.ofNat 4 = UInt256.ofNat 356 by decide]
  exact NativeSourceMidnightDecodedStore.word_of_nat _ _ loaded

theorem market_accept (fuel : Nat) (pre : EVM.State) (x y base : UInt256) (tail : Stack UInt256)
    (selector key value : Nat) (market : NativeSourceMarketCalldata.Market)
    (encoded : pre.executionEnv.calldata = StateBridge.calldataToByteArray selector
      (NativeSourceMarketCalldata.arguments market key value))
    (bound : market.collateral.length ≤ 2^64-1)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 253)
    (stack : pre.stack = x :: UInt256.ofNat 352 :: y :: base :: tail)
    (gas : 34 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1017) :
    EVM.X (fuel + 10) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      EVM.X (fuel + 1) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0))
        (accepted pre x y (UInt256.ofNat 352) base tail) := by
  apply accept fuel pre x y _ base tail code pc stack
  · rw [canonical_word pre selector key value market encoded bound]
    exact NativeSourceLengthAccept.canonical_length_bound _ bound
  · exact gas
  · exact depth

end Compiler.Proofs.IRGeneration.NativeSourceLengthCertificate

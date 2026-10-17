import Compiler.Proofs.IRGeneration.NativeSourceAddressCertificate

namespace Compiler.Proofs.IRGeneration.NativeSourceMarketAddressCalls
open EvmYul NativeSourceMarketCalldata Compiler.Proofs.YulGeneration.Backends

theorem midnight_word (pre : EVM.State) (selector key value : Nat) (market : Market)
    (encoded : pre.executionEnv.calldata = StateBridge.calldataToByteArray selector (arguments market key value))
    (canonical : market.midnight < 2 ^ 160) :
    (pre.toState.calldataload (UInt256.ofNat 132)).toNat = market.midnight := by
  have loaded := (header pre selector key value market encoded).2.1
  rw [loaded]
  apply Nat.mod_eq_of_lt
  exact Nat.lt_trans canonical (by decide)

theorem loan_word (pre : EVM.State) (selector key value : Nat) (market : Market)
    (encoded : pre.executionEnv.calldata = StateBridge.calldataToByteArray selector (arguments market key value))
    (canonical : market.loanToken < 2 ^ 160) :
    (pre.toState.calldataload (UInt256.ofNat 164)).toNat = market.loanToken := by
  have loaded := (header pre selector key value market encoded).2.2.1
  rw [loaded]
  apply Nat.mod_eq_of_lt
  exact Nat.lt_trans canonical (by decide)

theorem midnight_call (fuel : Nat) (pre : EVM.State) (tail : Stack UInt256)
    (selector key value : Nat) (market : Market)
    (encoded : pre.executionEnv.calldata = StateBridge.calldataToByteArray selector (arguments market key value))
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 945)
    (stack : pre.stack = UInt256.ofNat 132 :: UInt256.ofNat 191 :: tail)
    (canonical : market.midnight < 2 ^ 160) (gas : 54 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1019) :
    EVM.X (fuel + 15) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      EVM.X (fuel + 1) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0))
        (NativeSourceCheckedCanonical.result pre (UInt256.ofNat 132) (UInt256.ofNat 191) tail) := by
  apply NativeSourceAddressCertificate.canonical fuel pre _ _ tail code pc stack
    (by rw [midnight_word pre selector key value market encoded canonical]; exact canonical) gas depth
  simp

theorem loan_call (fuel : Nat) (pre : EVM.State) (tail : Stack UInt256)
    (selector key value : Nat) (market : Market)
    (encoded : pre.executionEnv.calldata = StateBridge.calldataToByteArray selector (arguments market key value))
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 945)
    (stack : pre.stack = UInt256.ofNat 164 :: UInt256.ofNat 210 :: tail)
    (canonical : market.loanToken < 2 ^ 160) (gas : 54 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1019) :
    EVM.X (fuel + 15) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      EVM.X (fuel + 1) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0))
        (NativeSourceCheckedCanonical.result pre (UInt256.ofNat 164) (UInt256.ofNat 210) tail) := by
  apply NativeSourceAddressCertificate.canonical fuel pre _ _ tail code pc stack
    (by rw [loan_word pre selector key value market encoded canonical]; exact canonical) gas depth
  simp

theorem enter_word (pre : EVM.State) (selector key value : Nat) (market : Market)
    (encoded : pre.executionEnv.calldata = StateBridge.calldataToByteArray selector (arguments market key value))
    (canonical : market.enterGate < 2 ^ 160) :
    (pre.toState.calldataload (UInt256.ofNat 292)).toNat = market.enterGate := by
  have loaded := (header pre selector key value market encoded).2.2.2.2.2.2.1
  rw [loaded]
  apply Nat.mod_eq_of_lt
  exact Nat.lt_trans canonical (by decide)

theorem enter_call (fuel : Nat) (pre : EVM.State) (tail : Stack UInt256)
    (selector key value : Nat) (market : Market)
    (encoded : pre.executionEnv.calldata = StateBridge.calldataToByteArray selector (arguments market key value))
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 945)
    (stack : pre.stack = UInt256.ofNat 292 :: UInt256.ofNat 381 :: tail)
    (canonical : market.enterGate < 2 ^ 160) (gas : 54 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1019) :
    EVM.X (fuel + 15) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      EVM.X (fuel + 1) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0))
        (NativeSourceCheckedCanonical.result pre (UInt256.ofNat 292) (UInt256.ofNat 381) tail) := by
  apply NativeSourceAddressCertificate.canonical fuel pre _ _ tail code pc stack
    (by rw [enter_word pre selector key value market encoded canonical]; exact canonical) gas depth
  simp

theorem liquidator_word (pre : EVM.State) (selector key value : Nat) (market : Market)
    (encoded : pre.executionEnv.calldata = StateBridge.calldataToByteArray selector (arguments market key value))
    (canonical : market.liquidatorGate < 2 ^ 160) :
    (pre.toState.calldataload (UInt256.ofNat 324)).toNat = market.liquidatorGate := by
  have loaded := (header pre selector key value market encoded).2.2.2.2.2.2.2.1
  rw [loaded]
  apply Nat.mod_eq_of_lt
  exact Nat.lt_trans canonical (by decide)

theorem liquidator_call (fuel : Nat) (pre : EVM.State) (tail : Stack UInt256)
    (selector key value : Nat) (market : Market)
    (encoded : pre.executionEnv.calldata = StateBridge.calldataToByteArray selector (arguments market key value))
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 945)
    (stack : pre.stack = UInt256.ofNat 324 :: UInt256.ofNat 395 :: tail)
    (canonical : market.liquidatorGate < 2 ^ 160) (gas : 54 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1019) :
    EVM.X (fuel + 15) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      EVM.X (fuel + 1) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0))
        (NativeSourceCheckedCanonical.result pre (UInt256.ofNat 324) (UInt256.ofNat 395) tail) := by
  apply NativeSourceAddressCertificate.canonical fuel pre _ _ tail code pc stack
    (by rw [liquidator_word pre selector key value market encoded canonical]; exact canonical) gas depth
  simp

end Compiler.Proofs.IRGeneration.NativeSourceMarketAddressCalls

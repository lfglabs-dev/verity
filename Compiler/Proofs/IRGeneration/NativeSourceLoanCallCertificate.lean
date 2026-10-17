import Compiler.Proofs.IRGeneration.NativeSourceLoanCallSetup
import Compiler.Proofs.IRGeneration.NativeSourceHelperScanner

namespace Compiler.Proofs.IRGeneration.NativeSourceLoanCallCertificate
open EvmYul EVM EVM.Proof NativeSourceLoanCallSetup Compiler.Proofs.YulGeneration.Backends

def returned (pre : EVM.State) (x a base : UInt256) (tail : Stack UInt256) :=
  NativeSourceCheckedCanonical.result (NativeSourceAddressEntry.entered (s6 pre x a base tail))
    (a + UInt256.ofNat 68) (UInt256.ofNat 210) (x :: a :: base :: tail)

theorem setup (fuel : Nat) (pre : EVM.State) (x a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 199)
    (stack : pre.stack = x :: a :: base :: tail)
    (gas : 23 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1017) :
    EVM.X (fuel + 7) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      EVM.X (fuel + 1) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) (s6 pre x a base tail) := by
  exact execute fuel _ pre x a base tail code pc stack gas depth NativeSourceHelperScanner.helper_destination

theorem execute_helper (fuel : Nat) (pre : EVM.State) (x a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 199)
    (stack : pre.stack = x :: a :: base :: tail)
    (valid : (pre.toState.calldataload (a + UInt256.ofNat 68)).toNat < 2 ^ 160)
    (gas : 78 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1016) :
    EVM.X (fuel + 22) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      EVM.X (fuel + 1) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) (returned pre x a base tail) := by
  have shape := frame pre x a base tail
  have charged := (gas_chain pre x a base tail (by omega)).2.2.2.2.2
  have codeAfter : (s6 pre x a base tail).executionEnv.code = NativeSourceAbiWrite.code :=
    (congrArg (fun state : EvmYul.State .EVM => state.executionEnv.code) shape.2.2.1).trans code
  rw [setup (fuel + 15) pre x a base tail code pc stack (by omega) (by omega)]
  exact NativeSourceAddressEntryCertificate.canonical fuel _ _ _ (x :: a :: base :: tail)
    codeAfter shape.1 shape.2.1 (by rw [shape.2.2.1]; exact valid) (by omega)
    (by simp only [List.length_cons]; omega) (by simp)

theorem returned_stack (pre : EVM.State) (x a base : UInt256) (tail : Stack UInt256) :
    (returned pre x a base tail).stack =
      pre.toState.calldataload (a + UInt256.ofNat 68) :: x :: a :: base :: tail := by
  have shape := frame pre x a base tail
  exact (NativeSourceAddressEntryCertificate.returned_stack _ _ _ (x :: a :: base :: tail)
    shape.1).trans (by rw [shape.2.2.1])

theorem returned_gas (pre : EVM.State) (x a base : UInt256) (tail : Stack UInt256)
    (gas : 78 ≤ pre.gasAvailable.toNat) :
    (returned pre x a base tail).gasAvailable.toNat = pre.gasAvailable.toNat - 78 := by
  have setupGas := (gas_chain pre x a base tail (by omega)).2.2.2.2.2
  have helperGas := NativeSourceAddressEntry.canonical_gas (s6 pre x a base tail)
    (a + UInt256.ofNat 68) (UInt256.ofNat 210) (x :: a :: base :: tail) (by omega)
  change (returned pre x a base tail).gasAvailable.toNat = _ at helperGas
  omega

theorem market_helper (fuel : Nat) (pre : EVM.State) (x base : UInt256) (tail : Stack UInt256)
    (selector key value : Nat) (market : NativeSourceMarketCalldata.Market)
    (encoded : pre.executionEnv.calldata = StateBridge.calldataToByteArray selector
      (NativeSourceMarketCalldata.arguments market key value))
    (canonical : market.loanToken < 2 ^ 160)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 199)
    (stack : pre.stack = x :: UInt256.ofNat 96 :: base :: tail)
    (gas : 78 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1016) :
    EVM.X (fuel + 22) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      EVM.X (fuel + 1) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0))
        (returned pre x (UInt256.ofNat 96) base tail) := by
  apply execute_helper fuel pre x _ base tail code pc stack _ gas depth
  rw [show UInt256.ofNat 96 + UInt256.ofNat 68 = UInt256.ofNat 164 by decide,
    NativeSourceMarketAddressCalls.loan_word pre selector key value market encoded canonical]
  exact canonical

theorem returned_world (pre : EVM.State) (x a base : UInt256) (tail : Stack UInt256) :
    (returned pre x a base tail).toState = pre.toState := by
  have shape := frame pre x a base tail
  exact (NativeSourceAddressEntryCertificate.returned_world _ _ _ (x :: a :: base :: tail)
    shape.1).trans shape.2.2.1

theorem returned_memory (pre : EVM.State) (x a base : UInt256) (tail : Stack UInt256) :
    (returned pre x a base tail).memory = pre.memory := by
  have shape := frame pre x a base tail
  exact (NativeSourceAddressEntryCertificate.returned_memory _ _ _ (x :: a :: base :: tail)
    shape.1).trans shape.2.2.2

end Compiler.Proofs.IRGeneration.NativeSourceLoanCallCertificate



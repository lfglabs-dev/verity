import Compiler.Proofs.IRGeneration.NativeSourceLoanDecodedStore
import Compiler.Proofs.IRGeneration.NativeSourceMemoryFrame
import Compiler.Proofs.IRGeneration.NativeSourceAddressGeometry

namespace Compiler.Proofs.IRGeneration.NativeSourceAddressPair
open EvmYul EVM EVM.Proof Compiler.Proofs.YulGeneration.Backends

abbrev first := NativeSourceMidnightDecodedStore.stored

def second (pre : EVM.State) (a base : UInt256) (tail : Stack UInt256) :=
  NativeSourceLoanDecodedStore.stored (first pre a base tail) (base + UInt256.ofNat 32) a base tail

def firstExpansion (pre : EVM.State) (a base : UInt256) (tail : Stack UInt256) :=
  memoryExpansionCost (NativeSourceMidnightDecodedStore.prepared pre a base tail) .MSTORE

def secondExpansion (pre : EVM.State) (a base : UInt256) (tail : Stack UInt256) :=
  memoryExpansionCost (NativeSourceLoanDecodedStore.prepared (first pre a base tail)
    (base + UInt256.ofNat 32) a base tail) .MSTORE

theorem first_world (pre : EVM.State) (a base : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 944) : (first pre a base tail).toState = pre.toState := by
  have rawWorld (state : EVM.State) (word : UInt256) :
      (mstorePost 3 (NativeSourceFieldStoreChecks.expanded
        (NativeSourceMidnightFieldStore.s6 state word a base tail))
        ((base + UInt256.ofNat 32) :: a :: base :: tail) (base + UInt256.ofNat 32) word).toState = state.toState := by rfl
  exact (rawWorld _ _).trans (NativeSourceAddressEntryCertificate.returned_world pre _ _ (a :: base :: tail) pc)

theorem first_stack (pre : EVM.State) (a base : UInt256) (tail : Stack UInt256) :
    (first pre a base tail).stack = (base + UInt256.ofNat 32) :: a :: base :: tail := by rfl

theorem first_pc (pre : EVM.State) (a base : UInt256) (tail : Stack UInt256) :
    (first pre a base tail).pc = UInt256.ofNat 199 := by
  have rawPC (state : EVM.State) (word : UInt256) (pc : state.pc = UInt256.ofNat 191) :
      (mstorePost 3 (NativeSourceFieldStoreChecks.expanded
        (NativeSourceMidnightFieldStore.s6 state word a base tail))
        ((base + UInt256.ofNat 32) :: a :: base :: tail) (base + UInt256.ofNat 32) word).pc = UInt256.ofNat 199 := by
    simp only [mstorePost, NativeSourceFieldStoreChecks.expanded, NativeSourceMidnightFieldStore.s6,
      NativeSourceMidnightFieldStore.s5, NativeSourceMidnightFieldStore.s4, NativeSourceMidnightFieldStore.s3,
      NativeSourceMidnightFieldStore.s2, NativeSourceMidnightFieldStore.s1, stepPre,
      EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  exact rawPC _ _ (NativeSourceMidnightDecodedStore.returned_pc pre a base tail)

theorem execute (fuel : Nat) (pre : EVM.State) (a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 944)
    (stack : pre.stack = UInt256.ofNat 132 :: UInt256.ofNat 191 :: a :: base :: tail)
    (midnight : (pre.toState.calldataload (UInt256.ofNat 132)).toNat < 2 ^ 160)
    (loan : (pre.toState.calldataload (a + UInt256.ofNat 68)).toNat < 2 ^ 160)
    (gas : 174 + firstExpansion pre a base tail + secondExpansion pre a base tail ≤ pre.gasAvailable.toNat)
    (depth : tail.length ≤ 1016) :
    EVM.X (fuel + 52) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      EVM.X (fuel + 1) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) (second pre a base tail) := by
  have world := first_world pre a base tail pc
  have charged := NativeSourceMidnightDecodedStore.stored_gas pre a base tail
    (by change 74 + firstExpansion pre a base tail ≤ _; omega)
  change (first pre a base tail).gasAvailable.toNat = pre.gasAvailable.toNat - (74 + firstExpansion pre a base tail) at charged
  have codeAfter := (congrArg (fun state : EvmYul.State .EVM => state.executionEnv.code) world).trans code
  rw [NativeSourceMidnightDecodedStore.execute (fuel + 29) pre a base tail code pc stack midnight
    (by change 74 + firstExpansion pre a base tail ≤ _; omega) depth]
  exact NativeSourceLoanDecodedStore.execute fuel _ _ a base tail codeAfter (first_pc pre a base tail)
    (first_stack pre a base tail) (by change ((first pre a base tail).toState.calldataload _).toNat < _; rw [world]; exact loan)
    (by change 100 + secondExpansion pre a base tail ≤ (first pre a base tail).gasAvailable.toNat; omega) depth

theorem loan_frame (pre : EVM.State) (x a base : UInt256) (tail : Stack UInt256) (start length : Nat)
    (fits : (base + UInt256.ofNat 64).toNat + 32 ≤ pre.memory.size)
    (positive : 0 < length) (bounded : length < 2 ^ 64)
    (below : start + length ≤ (base + UInt256.ofNat 64).toNat) :
    (NativeSourceLoanDecodedStore.stored pre x a base tail).memory.readWithPadding start length =
      pre.memory.readWithPadding start length := by
  have rawFrame (state : EVM.State) (value : UInt256)
      (inside : (base + UInt256.ofNat 64).toNat + 32 ≤ state.memory.size) :
      (mstorePost 3 (NativeSourceFieldStoreChecks.expanded state)
        (x :: (base + UInt256.ofNat 64) :: a :: base :: tail)
        (base + UInt256.ofNat 64) value).memory.readWithPadding start length = state.memory.readWithPadding start length := by
    exact NativeSourceMemoryFrame.read_below (NativeSourceFieldStoreChecks.expanded state).toMachineState
      _ value start length inside positive bounded below
  have memory := NativeSourceLoanDecodedStore.prepared_memory pre x a base tail
  exact (rawFrame (NativeSourceLoanDecodedStore.prepared pre x a base tail)
    (NativeSourceLoanDecodedStore.word pre a) (by rw [memory]; exact fits)).trans (by rw [memory])

theorem midnight_preserved (pre : EVM.State) (a base : UInt256) (tail : Stack UInt256)
    (nonwrap : base.toNat + 64 < 2 ^ 256)
    (fits : (base + UInt256.ofNat 64).toNat + 32 ≤ (first pre a base tail).memory.size) :
    (second pre a base tail).memory.readWithPadding (base + UInt256.ofNat 32).toNat 32 =
      (first pre a base tail).memory.readWithPadding (base + UInt256.ofNat 32).toNat 32 := by
  have small : (UInt256.ofNat 32).toNat = 32 := by decide
  have large : (UInt256.ofNat 64).toNat = 64 := by decide
  have low := NativeSourceAddressGeometry.add_toNat base (UInt256.ofNat 32) (by rw [small]; omega)
  have high := NativeSourceAddressGeometry.add_toNat base (UInt256.ofNat 64) (by rw [large]; exact nonwrap)
  exact loan_frame (first pre a base tail) _ a base tail _ 32 fits (by decide) (by decide)
    (by rw [low, high, small, large])

theorem market_readback (pre : EVM.State) (base : UInt256) (tail : Stack UInt256)
    (selector key value : Nat) (market : NativeSourceMarketCalldata.Market)
    (encoded : pre.executionEnv.calldata = StateBridge.calldataToByteArray selector
      (NativeSourceMarketCalldata.arguments market key value))
    (midnight : market.midnight < 2 ^ 160) (loan : market.loanToken < 2 ^ 160)
    (pc : pre.pc = UInt256.ofNat 944) (nonwrap : base.toNat + 64 < 2 ^ 256)
    (pad : (base + UInt256.ofNat 32).toNat - pre.memory.size < 2 ^ System.Platform.numBits)
    (fits : (base + UInt256.ofNat 64).toNat + 32 ≤ (first pre (UInt256.ofNat 96) base tail).memory.size) :
    (second pre (UInt256.ofNat 96) base tail).memory.readWithPadding (base + UInt256.ofNat 32).toNat 32 =
      (UInt256.ofNat market.midnight).toByteArray ∧
    (second pre (UInt256.ofNat 96) base tail).memory.readWithPadding (base + UInt256.ofNat 64).toNat 32 =
      (UInt256.ofNat market.loanToken).toByteArray := by
  constructor
  · rw [midnight_preserved pre _ base tail nonwrap fits]
    exact NativeSourceMidnightDecodedStore.market_readback pre _ base tail selector key value market encoded midnight pc pad
  · have calldataAfter := congrArg (fun state : EvmYul.State .EVM => state.executionEnv.calldata)
      (first_world pre (UInt256.ofNat 96) base tail pc)
    exact NativeSourceLoanDecodedStore.market_readback (first pre (UInt256.ofNat 96) base tail)
      _ base tail selector key value market (calldataAfter.trans encoded) loan
      (by have zero : (base + UInt256.ofNat 64).toNat - (first pre (UInt256.ofNat 96) base tail).memory.size = 0 := by omega
          rw [zero]; positivity)

theorem gas_exact (pre : EVM.State) (a base : UInt256) (tail : Stack UInt256)
    (gas : 174 + firstExpansion pre a base tail + secondExpansion pre a base tail ≤ pre.gasAvailable.toNat) :
    (second pre a base tail).gasAvailable.toNat = pre.gasAvailable.toNat -
      (174 + firstExpansion pre a base tail + secondExpansion pre a base tail) := by
  have firstGas := NativeSourceMidnightDecodedStore.stored_gas pre a base tail
    (by change 74 + firstExpansion pre a base tail ≤ _; omega)
  change (first pre a base tail).gasAvailable.toNat = pre.gasAvailable.toNat - (74 + firstExpansion pre a base tail) at firstGas
  have secondGas := NativeSourceLoanDecodedStore.stored_gas (first pre a base tail)
    (base + UInt256.ofNat 32) a base tail
    (by change 100 + secondExpansion pre a base tail ≤ (first pre a base tail).gasAvailable.toNat; omega)
  change (second pre a base tail).gasAvailable.toNat =
    (first pre a base tail).gasAvailable.toNat - (100 + secondExpansion pre a base tail) at secondGas
  omega

end Compiler.Proofs.IRGeneration.NativeSourceAddressPair



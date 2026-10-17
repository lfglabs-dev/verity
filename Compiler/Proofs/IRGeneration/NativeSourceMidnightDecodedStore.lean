import Compiler.Proofs.IRGeneration.NativeSourceCheckedFieldPrefix
import Compiler.Proofs.IRGeneration.NativeSourceMarketAddressCalls
import EvmYul.EVM.Proof.Memory

namespace Compiler.Proofs.IRGeneration.NativeSourceMidnightDecodedStore
open EvmYul EVM EVM.Proof NativeSourceMidnightFieldStore Compiler.Proofs.YulGeneration.Backends

def returned (pre : EVM.State) (a base : UInt256) (tail : Stack UInt256) :=
  NativeSourceCheckedCanonical.result (NativeSourceAddressEntry.entered pre)
    (UInt256.ofNat 132) (UInt256.ofNat 191) (a :: base :: tail)

def prepared (pre : EVM.State) (a base : UInt256) (tail : Stack UInt256) :=
  s6 (returned pre a base tail) (pre.toState.calldataload (UInt256.ofNat 132)) a base tail

def stored (pre : EVM.State) (a base : UInt256) (tail : Stack UInt256) :=
  mstorePost 3 (NativeSourceFieldStoreChecks.expanded (prepared pre a base tail))
    ((base + UInt256.ofNat 32) :: a :: base :: tail) (base + UInt256.ofNat 32)
    (pre.toState.calldataload (UInt256.ofNat 132))

theorem returned_code (pre : EVM.State) (a base : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 944) :
    (returned pre a base tail).executionEnv.code = pre.executionEnv.code := by
  exact congrArg (fun state : EvmYul.State .EVM => state.executionEnv.code)
    (NativeSourceAddressEntryCertificate.returned_world pre _ _ (a :: base :: tail) pc)

theorem returned_pc (pre : EVM.State) (a base : UInt256) (tail : Stack UInt256) :
    (returned pre a base tail).pc = UInt256.ofNat 191 := by
  exact (NativeSourceCheckedCanonical.result_frame _ _ _ _).2

theorem execute (fuel : Nat) (pre : EVM.State) (a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 944)
    (stack : pre.stack = UInt256.ofNat 132 :: UInt256.ofNat 191 :: a :: base :: tail)
    (valid : (pre.toState.calldataload (UInt256.ofNat 132)).toNat < 2 ^ 160)
    (gas : 74 + memoryExpansionCost (prepared pre a base tail) .MSTORE ≤ pre.gasAvailable.toNat)
    (depth : tail.length ≤ 1016) :
    EVM.X (fuel + 23) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      EVM.X (fuel + 1) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) (stored pre a base tail) := by
  have charged := NativeSourceAddressEntry.canonical_gas pre (UInt256.ofNat 132)
    (UInt256.ofNat 191) (a :: base :: tail) (by omega)
  have returnedStack := NativeSourceAddressEntryCertificate.returned_stack pre
    (UInt256.ofNat 132) (UInt256.ofNat 191) (a :: base :: tail) pc
  rw [NativeSourceAddressEntryCertificate.canonical (fuel + 7) pre _ _ (a :: base :: tail)
    code pc stack valid (by omega) (by simp only [List.length_cons]; omega) (by simp)]
  exact NativeSourceCheckedFieldPrefix.execute_store fuel _ (returned pre a base tail)
    (pre.toState.calldataload (UInt256.ofNat 132)) a base tail
    ((returned_code pre a base tail pc).trans code) (returned_pc pre a base tail)
    returnedStack (by change 19 + memoryExpansionCost (prepared pre a base tail) .MSTORE ≤
      (returned pre a base tail).gasAvailable.toNat; change (returned pre a base tail).gasAvailable.toNat = _ at charged; omega) (by omega)

theorem prepared_memory (pre : EVM.State) (a base : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 944) :
    (prepared pre a base tail).memory = pre.memory := by
  have prepMemory (state : EVM.State) (word : UInt256) :
      (s6 state word a base tail).memory = state.memory := by rfl
  exact (prepMemory _ _).trans
    (NativeSourceAddressEntryCertificate.returned_memory pre _ _ (a :: base :: tail) pc)

theorem post_readback (state : EVM.State) (offset word : UInt256) (tail : Stack UInt256)
    (pad : offset.toNat - state.memory.size < 2 ^ System.Platform.numBits) :
    (mstorePost 3 (NativeSourceFieldStoreChecks.expanded state) tail offset word).memory.readWithPadding offset.toNat 32 =
      word.toByteArray := by
  exact MachineState.readWithPadding_memory_mstore_of_pad
    (NativeSourceFieldStoreChecks.expanded state).toMachineState offset word pad

theorem store_readback (pre : EVM.State) (a base : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 944)
    (pad : (base + UInt256.ofNat 32).toNat - pre.memory.size < 2 ^ System.Platform.numBits) :
    (stored pre a base tail).memory.readWithPadding (base + UInt256.ofNat 32).toNat 32 =
      (pre.toState.calldataload (UInt256.ofNat 132)).toByteArray := by
  have bytes := prepared_memory pre a base tail pc
  exact post_readback (prepared pre a base tail) _ _ _ (by rw [bytes]; exact pad)

theorem word_of_nat (word : UInt256) (n : Nat) (value : word.toNat = n) :
    word = UInt256.ofNat n := by
  cases word with
  | mk w =>
    apply congrArg UInt256.mk
    apply Fin.ext
    change w.val = n % UInt256.size
    have bound : n < UInt256.size := by rw [← value]; exact w.isLt
    rw [Nat.mod_eq_of_lt bound]
    exact value

theorem market_readback (pre : EVM.State) (a base : UInt256) (tail : Stack UInt256)
    (selector key value : Nat) (market : NativeSourceMarketCalldata.Market)
    (encoded : pre.executionEnv.calldata = StateBridge.calldataToByteArray selector
      (NativeSourceMarketCalldata.arguments market key value))
    (canonical : market.midnight < 2 ^ 160) (pc : pre.pc = UInt256.ofNat 944)
    (pad : (base + UInt256.ofNat 32).toNat - pre.memory.size < 2 ^ System.Platform.numBits) :
    (stored pre a base tail).memory.readWithPadding (base + UInt256.ofNat 32).toNat 32 =
      (UInt256.ofNat market.midnight).toByteArray := by
  rw [store_readback pre a base tail pc pad]
  have value := NativeSourceMarketAddressCalls.midnight_word pre selector key value market encoded canonical
  have word := word_of_nat (pre.toState.calldataload (UInt256.ofNat 132)) market.midnight value
  rw [word]

theorem market_execute (fuel : Nat) (pre : EVM.State) (a base : UInt256) (tail : Stack UInt256)
    (selector key value : Nat) (market : NativeSourceMarketCalldata.Market)
    (encoded : pre.executionEnv.calldata = StateBridge.calldataToByteArray selector
      (NativeSourceMarketCalldata.arguments market key value))
    (canonical : market.midnight < 2 ^ 160)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 944)
    (stack : pre.stack = UInt256.ofNat 132 :: UInt256.ofNat 191 :: a :: base :: tail)
    (gas : 74 + memoryExpansionCost (prepared pre a base tail) .MSTORE ≤ pre.gasAvailable.toNat)
    (depth : tail.length ≤ 1016) :
    EVM.X (fuel + 23) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      EVM.X (fuel + 1) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) (stored pre a base tail) := by
  apply execute fuel pre a base tail code pc stack _ gas depth
  rw [NativeSourceMarketAddressCalls.midnight_word pre selector key value market encoded canonical]
  exact canonical

theorem stored_gas (pre : EVM.State) (a base : UInt256) (tail : Stack UInt256)
    (gas : 74 + memoryExpansionCost (prepared pre a base tail) .MSTORE ≤ pre.gasAvailable.toNat) :
    (stored pre a base tail).gasAvailable.toNat =
      pre.gasAvailable.toNat - (74 + memoryExpansionCost (prepared pre a base tail) .MSTORE) := by
  have helper := NativeSourceAddressEntry.canonical_gas pre (UInt256.ofNat 132)
    (UInt256.ofNat 191) (a :: base :: tail) (by omega)
  change (returned pre a base tail).gasAvailable.toNat = _ at helper
  have prep := (NativeSourceCheckedFieldPrefix.gas_chain (returned pre a base tail)
    (pre.toState.calldataload (UInt256.ofNat 132)) a base tail (by omega)).2.2.2.2.2
  change (prepared pre a base tail).gasAvailable.toNat = _ at prep
  have charged := NativeSourceFieldStoreChecks.expansion_gas (prepared pre a base tail) (by omega)
  have final : (stored pre a base tail).gasAvailable.toNat =
      (NativeSourceFieldStoreChecks.expanded (prepared pre a base tail)).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  omega

end Compiler.Proofs.IRGeneration.NativeSourceMidnightDecodedStore





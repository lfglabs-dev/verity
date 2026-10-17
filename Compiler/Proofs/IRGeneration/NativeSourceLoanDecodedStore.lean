import Compiler.Proofs.IRGeneration.NativeSourceLoanFieldStore

namespace Compiler.Proofs.IRGeneration.NativeSourceLoanDecodedStore
open EvmYul EVM EVM.Proof Compiler.Proofs.YulGeneration.Backends

abbrev returned := NativeSourceLoanCallCertificate.returned

def word (pre : EVM.State) (a : UInt256) := pre.toState.calldataload (a + UInt256.ofNat 68)

def prepared (pre : EVM.State) (x a base : UInt256) (tail : Stack UInt256) :=
  NativeSourceLoanFieldStore.s7 (returned pre x a base tail) (word pre a) x a base tail

def stored (pre : EVM.State) (x a base : UInt256) (tail : Stack UInt256) :=
  NativeSourceLoanFieldStore.stored (returned pre x a base tail) (word pre a) x a base tail

theorem returned_code (pre : EVM.State) (x a base : UInt256) (tail : Stack UInt256) :
    (returned pre x a base tail).executionEnv.code = pre.executionEnv.code := by
  exact congrArg (fun state : EvmYul.State .EVM => state.executionEnv.code)
    (NativeSourceLoanCallCertificate.returned_world pre x a base tail)

theorem returned_pc (pre : EVM.State) (x a base : UInt256) (tail : Stack UInt256) :
    (returned pre x a base tail).pc = UInt256.ofNat 210 := by
  exact (NativeSourceCheckedCanonical.result_frame _ _ _ _).2

theorem execute (fuel : Nat) (pre : EVM.State) (x a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 199)
    (stack : pre.stack = x :: a :: base :: tail)
    (valid : (word pre a).toNat < 2 ^ 160)
    (gas : 100 + memoryExpansionCost (prepared pre x a base tail) .MSTORE ≤ pre.gasAvailable.toNat)
    (depth : tail.length ≤ 1016) :
    EVM.X (fuel + 30) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      EVM.X (fuel + 1) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) (stored pre x a base tail) := by
  have charged := NativeSourceLoanCallCertificate.returned_gas pre x a base tail (by omega)
  change (returned pre x a base tail).gasAvailable.toNat = _ at charged
  have returnedStack := NativeSourceLoanCallCertificate.returned_stack pre x a base tail
  rw [NativeSourceLoanCallCertificate.execute_helper (fuel + 8) pre x a base tail code pc stack
    valid (by omega) depth]
  exact NativeSourceLoanFieldStore.execute fuel _ (returned pre x a base tail) (word pre a) x a base tail
    ((returned_code pre x a base tail).trans code) (returned_pc pre x a base tail) returnedStack
    (by change 22 + memoryExpansionCost (prepared pre x a base tail) .MSTORE ≤
      (returned pre x a base tail).gasAvailable.toNat; omega) depth

theorem prepared_memory (pre : EVM.State) (x a base : UInt256) (tail : Stack UInt256) :
    (prepared pre x a base tail).memory = pre.memory := by
  have prepMemory (state : EVM.State) (value : UInt256) :
      (NativeSourceLoanFieldStore.s7 state value x a base tail).memory = state.memory := by rfl
  exact (prepMemory _ _).trans (NativeSourceLoanCallCertificate.returned_memory pre x a base tail)

theorem store_readback (pre : EVM.State) (x a base : UInt256) (tail : Stack UInt256)
    (pad : (base + UInt256.ofNat 64).toNat - pre.memory.size < 2 ^ System.Platform.numBits) :
    (stored pre x a base tail).memory.readWithPadding (base + UInt256.ofNat 64).toNat 32 =
      (word pre a).toByteArray := by
  have bytes := prepared_memory pre x a base tail
  exact NativeSourceMidnightDecodedStore.post_readback (prepared pre x a base tail) _ _ _
    (by rw [bytes]; exact pad)

theorem market_readback (pre : EVM.State) (x base : UInt256) (tail : Stack UInt256)
    (selector key value : Nat) (market : NativeSourceMarketCalldata.Market)
    (encoded : pre.executionEnv.calldata = StateBridge.calldataToByteArray selector
      (NativeSourceMarketCalldata.arguments market key value))
    (canonical : market.loanToken < 2 ^ 160)
    (pad : (base + UInt256.ofNat 64).toNat - pre.memory.size < 2 ^ System.Platform.numBits) :
    (stored pre x (UInt256.ofNat 96) base tail).memory.readWithPadding (base + UInt256.ofNat 64).toNat 32 =
      (UInt256.ofNat market.loanToken).toByteArray := by
  rw [store_readback pre x (UInt256.ofNat 96) base tail pad]
  have value := NativeSourceMarketAddressCalls.loan_word pre selector key value market encoded canonical
  have loaded : word pre (UInt256.ofNat 96) = pre.toState.calldataload (UInt256.ofNat 164) := by
    unfold word; rw [show UInt256.ofNat 96 + UInt256.ofNat 68 = UInt256.ofNat 164 by decide]
  rw [loaded, NativeSourceMidnightDecodedStore.word_of_nat _ market.loanToken value]

theorem stored_gas (pre : EVM.State) (x a base : UInt256) (tail : Stack UInt256)
    (gas : 100 + memoryExpansionCost (prepared pre x a base tail) .MSTORE ≤ pre.gasAvailable.toNat) :
    (stored pre x a base tail).gasAvailable.toNat =
      pre.gasAvailable.toNat - (100 + memoryExpansionCost (prepared pre x a base tail) .MSTORE) := by
  have helper := NativeSourceLoanCallCertificate.returned_gas pre x a base tail (by omega)
  change (returned pre x a base tail).gasAvailable.toNat = _ at helper
  have prep := (NativeSourceLoanFieldStore.gas_chain (returned pre x a base tail)
    (word pre a) x a base tail (by omega)).2.2.2.2.2.2
  change (prepared pre x a base tail).gasAvailable.toNat = _ at prep
  have charged := NativeSourceFieldStoreChecks.expansion_gas (prepared pre x a base tail) (by omega)
  have final : (stored pre x a base tail).gasAvailable.toNat =
      (NativeSourceFieldStoreChecks.expanded (prepared pre x a base tail)).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub
      (NativeSourceFieldStoreChecks.expanded (prepared pre x a base tail)).gasAvailable 3 (by decide) (by omega)
  omega

theorem market_execute (fuel : Nat) (pre : EVM.State) (x base : UInt256) (tail : Stack UInt256)
    (selector key value : Nat) (market : NativeSourceMarketCalldata.Market)
    (encoded : pre.executionEnv.calldata = StateBridge.calldataToByteArray selector
      (NativeSourceMarketCalldata.arguments market key value))
    (canonical : market.loanToken < 2 ^ 160)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 199)
    (stack : pre.stack = x :: UInt256.ofNat 96 :: base :: tail)
    (gas : 100 + memoryExpansionCost (prepared pre x (UInt256.ofNat 96) base tail) .MSTORE ≤ pre.gasAvailable.toNat)
    (depth : tail.length ≤ 1016) :
    EVM.X (fuel + 30) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      EVM.X (fuel + 1) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0))
        (stored pre x (UInt256.ofNat 96) base tail) := by
  apply execute fuel pre x _ base tail code pc stack _ gas depth
  change (pre.toState.calldataload (UInt256.ofNat 96 + UInt256.ofNat 68)).toNat < _
  rw [show UInt256.ofNat 96 + UInt256.ofNat 68 = UInt256.ofNat 164 by decide,
    NativeSourceMarketAddressCalls.loan_word pre selector key value market encoded canonical]
  exact canonical

theorem stored_stack (pre : EVM.State) (x a base : UInt256) (tail : Stack UInt256) :
    (stored pre x a base tail).stack = x :: (base + UInt256.ofNat 64) :: a :: base :: tail := by rfl

theorem stored_world (pre : EVM.State) (x a base : UInt256) (tail : Stack UInt256) :
    (stored pre x a base tail).toState = pre.toState := by
  have rawWorld (state : EVM.State) (value : UInt256) :
      (NativeSourceLoanFieldStore.stored state value x a base tail).toState = state.toState := by rfl
  exact (rawWorld _ _).trans (NativeSourceLoanCallCertificate.returned_world pre x a base tail)

theorem stored_pc (pre : EVM.State) (x a base : UInt256) (tail : Stack UInt256) :
    (stored pre x a base tail).pc = UInt256.ofNat 219 := by
  have rawPC (state : EVM.State) (value : UInt256) (pc : state.pc = UInt256.ofNat 210) :
      (NativeSourceLoanFieldStore.stored state value x a base tail).pc = UInt256.ofNat 219 := by
    simp only [NativeSourceLoanFieldStore.stored, NativeSourceFieldStoreChecks.expanded, mstorePost,
      NativeSourceLoanFieldStore.s7, NativeSourceLoanFieldStore.s6, NativeSourceLoanFieldStore.s5,
      NativeSourceLoanFieldStore.s4, NativeSourceLoanFieldStore.s3, NativeSourceLoanFieldStore.s2,
      NativeSourceLoanFieldStore.s1, stepPre, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
    rw [pc]; decide
  exact rawPC _ _ (returned_pc pre x a base tail)

end Compiler.Proofs.IRGeneration.NativeSourceLoanDecodedStore



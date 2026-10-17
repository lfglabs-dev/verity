import Compiler.Proofs.IRGeneration.NativeSourceArrayElementBounds

namespace Compiler.Proofs.IRGeneration.NativeSourceArrayElementOutcome
open EvmYul EVM EVM.Proof NativeSourceArrayElementGuard

theorem frame (pre : EVM.State) (a end_ cursor : UInt256) (tail : Stack UInt256) :
    (decided pre a end_ cursor tail).executionEnv = pre.executionEnv ∧
    (decided pre a end_ cursor tail).stack = a :: end_ :: cursor :: tail := by
  exact ⟨rfl, rfl⟩

theorem flag_one (pre : EVM.State) (cursor : UInt256)
    (small : pre.executionEnv.calldata.size < 2^255)
    (inside : cursor.toNat ≤ pre.executionEnv.calldata.size)
    (short : pre.executionEnv.calldata.size < cursor.toNat + 128) :
    flag pre cursor = UInt256.ofNat 1 := by
  have exactRemaining := NativeSourceArrayElementBounds.remaining pre cursor small inside
  exact NativeSourceSpanBounds.signed_less _ _ (by omega) (by decide)
    (by change (size pre - cursor).toNat < 128; omega)

theorem rejected_pc (pre : EVM.State) (a end_ cursor : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 806) (small : pre.executionEnv.calldata.size < 2^255)
    (inside : cursor.toNat ≤ pre.executionEnv.calldata.size)
    (short : pre.executionEnv.calldata.size < cursor.toNat + 128) :
    (decided pre a end_ cursor tail).pc = UInt256.ofNat 91 := by
  change (NativeSourceArrayElementBranch.branched (s7 pre a end_ cursor tail) (flag pre cursor)
    (a :: end_ :: cursor :: tail)).pc = _
  rw [NativeSourceArrayElementBranch.destinations (s7 pre a end_ cursor tail) (flag pre cursor)
    (a :: end_ :: cursor :: tail) (pcs pre a end_ cursor tail pc).2.2.2.2.2.2,
    flag_one pre cursor small inside short]
  rfl

theorem reject_exact (fuel : Nat) (pre : EVM.State) (a end_ cursor : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 806)
    (stack : pre.stack = a :: end_ :: cursor :: tail) (gas : 34 ≤ pre.gasAvailable.toNat)
    (depth : tail.length ≤ 1018) (small : pre.executionEnv.calldata.size < 2^255)
    (inside : cursor.toNat ≤ pre.executionEnv.calldata.size)
    (short : pre.executionEnv.calldata.size < cursor.toNat + 128) :
    EVM.X (fuel + 13) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      .ok (.revert (UInt256.ofNat (pre.gasAvailable.toNat - 34)) ByteArray.empty) := by
  have charged := gas_exact pre a end_ cursor tail (by omega)
  have rejected := rejected_pc pre a end_ cursor tail pc small inside short
  have stateFrame := frame pre a end_ cursor tail
  rw [NativeSourceArrayElementGuard.execute (fuel + 4) pre a end_ cursor tail code pc stack (by omega) depth]
  rw [NativeSourceCheckedRejection.execute_exact fuel _ (decided pre a end_ cursor tail)
    (by rw [stateFrame.1]; exact code) rejected (by omega)
    (by rw [stateFrame.2]; simp only [List.length_cons]; omega)]
  rw [charged, Nat.sub_sub]

theorem canonical_accept (fuel : Nat) (pre : EVM.State) (a end_ : UInt256) (tail : Stack UInt256)
    (selector key value : Nat) (market : NativeSourceMarketCalldata.Market) (index : Nat)
    (encoded : pre.executionEnv.calldata = Compiler.Proofs.YulGeneration.Backends.StateBridge.calldataToByteArray selector
      (NativeSourceMarketCalldata.arguments market key value))
    (inside : index < market.collateral.length) (small : pre.executionEnv.calldata.size < 2^255)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 806)
    (stack : pre.stack = a :: end_ :: NativeSourceMarketArrayCursor.cursor index :: tail)
    (gas : 28 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1018) :
    EVM.X (fuel + 9) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      EVM.X (fuel + 1) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0))
        (decided pre a end_ (NativeSourceMarketArrayCursor.cursor index) tail) ∧
    (decided pre a end_ (NativeSourceMarketArrayCursor.cursor index) tail).pc = UInt256.ofNat 817 ∧
    (decided pre a end_ (NativeSourceMarketArrayCursor.cursor index) tail).gasAvailable.toNat =
      pre.gasAvailable.toNat - 28 := by
  refine ⟨NativeSourceArrayElementGuard.execute fuel pre a end_ _ tail code pc stack gas depth,
    NativeSourceArrayElementBounds.accepted_pc pre a end_ _ tail pc small ?_, gas_exact pre a end_ _ tail gas⟩
  exact NativeSourceArrayElementBounds.canonical_room pre selector key value market index encoded inside small

end Compiler.Proofs.IRGeneration.NativeSourceArrayElementOutcome

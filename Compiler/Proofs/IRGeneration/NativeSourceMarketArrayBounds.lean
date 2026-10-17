import Compiler.Proofs.IRGeneration.NativeSourceArrayLoopAccepted
import Compiler.Proofs.IRGeneration.NativeSourceMarketCalldata

namespace Compiler.Proofs.IRGeneration.NativeSourceMarketArrayBounds
open EvmYul EVM EVM.Proof Compiler.Proofs.YulGeneration.Backends NativeSourceMarketCalldata

def arrayEnd (n : UInt256) :=
  ((UInt256.ofNat 352 + (n <<< UInt256.ofNat 7)) + UInt256.ofNat 4) + UInt256.ofNat 32

theorem calldata_size (pre : EVM.State) (selector key value : Nat) (m : Market)
    (encoded : pre.executionEnv.calldata = StateBridge.calldataToByteArray selector (arguments m key value)) :
    pre.executionEnv.calldata.size = 388 + 128 * m.collateral.length := by
  rw [encoded, StateBridge.calldataToByteArray_size]
  simp only [arguments, List.length_append, List.length_cons, List.length_nil, collateral_length]
  omega

theorem shift_value (n : UInt256) (bound : n.toNat * 128 < UInt256.size) :
    (n <<< UInt256.ofNat 7).toNat = n.toNat * 128 := by
  change (if (UInt256.ofNat 7).val ≥ 256 then (⟨0⟩ : UInt256) else ⟨n.val <<< (UInt256.ofNat 7).val⟩).toNat = _
  rw [if_neg (by decide)]
  change (n.toNat <<< 7) % UInt256.size = _
  rw [Nat.shiftLeft_eq]
  exact Nat.mod_eq_of_lt bound

theorem end_value (n : UInt256) (bound : 388 + 128 * n.toNat < UInt256.size) :
    (arrayEnd n).toNat = 388 + 128 * n.toNat := by
  have shifted := shift_value n (by omega)
  have c352 : (UInt256.ofNat 352).toNat = 352 := by decide
  have c4 : (UInt256.ofNat 4).toNat = 4 := by decide
  have c32 : (UInt256.ofNat 32).toNat = 32 := by decide
  have a := NativeSourceCheckedAllocatorBounds.addition (UInt256.ofNat 352) (n <<< UInt256.ofNat 7) (by omega)
  have b := NativeSourceCheckedAllocatorBounds.addition (UInt256.ofNat 352 + (n <<< UInt256.ofNat 7)) (UInt256.ofNat 4) (by omega)
  have c := NativeSourceCheckedAllocatorBounds.addition ((UInt256.ofNat 352 + (n <<< UInt256.ofNat 7)) + UInt256.ofNat 4) (UInt256.ofNat 32) (by omega)
  change (((UInt256.ofNat 352 + (n <<< UInt256.ofNat 7)) + UInt256.ofNat 4) + UInt256.ofNat 32).toNat = _
  omega

theorem canonical_end (pre : EVM.State) (selector key value : Nat) (m : Market) (n : UInt256)
    (encoded : pre.executionEnv.calldata = StateBridge.calldataToByteArray selector (arguments m key value))
    (length : n.toNat = m.collateral.length)
    (bound : 388 + 128 * m.collateral.length < UInt256.size) :
    (arrayEnd n).toNat = pre.executionEnv.calldata.size := by
  rw [end_value n (by omega), length, calldata_size pre selector key value m encoded]

theorem canonical_flag (pre : EVM.State) (selector key value : Nat) (m : Market) (n : UInt256)
    (encoded : pre.executionEnv.calldata = StateBridge.calldataToByteArray selector (arguments m key value))
    (length : n.toNat = m.collateral.length)
    (bound : 388 + 128 * m.collateral.length < UInt256.size) :
    NativeSourceArrayCalldataGuard.flag pre (arrayEnd n) = UInt256.ofNat 0 := by
  have total := calldata_size pre selector key value m encoded
  have exactEnd := canonical_end pre selector key value m n encoded length bound
  exact NativeSourceArrayCalldataBounds.flag_zero pre (arrayEnd n) (by omega) (by omega)

theorem canonical_execute (fuel : Nat) (pre : EVM.State) (selector key value : Nat) (m : Market)
    (n pointer : UInt256) (tail : Stack UInt256)
    (encoded : pre.executionEnv.calldata = StateBridge.calldataToByteArray selector (arguments m key value))
    (length : n.toNat = m.collateral.length)
    (bound : 388 + 128 * m.collateral.length < UInt256.size)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 312)
    (stack : pre.stack = UInt256.ofNat 352 :: arrayEnd n :: pointer :: tail)
    (gas : 31 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1019) :
    EVM.X (fuel + 10) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      EVM.X (fuel + 1) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0))
        (NativeSourceArrayLoopAccepted.entered pre (UInt256.ofNat 352) (arrayEnd n) pointer tail) := by
  have total := calldata_size pre selector key value m encoded
  have exactEnd := canonical_end pre selector key value m n encoded length bound
  exact NativeSourceArrayLoopAccepted.execute fuel pre (UInt256.ofNat 352) (arrayEnd n) pointer tail
    code pc stack gas depth (by omega) (by omega)

end Compiler.Proofs.IRGeneration.NativeSourceMarketArrayBounds

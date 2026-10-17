import Compiler.Proofs.IRGeneration.NativeSourceReturnMembership
import Compiler.Proofs.IRGeneration.NativeSourceCanonicalFrames

namespace Compiler.Proofs.IRGeneration.NativeSourceAddressCertificate
open EvmYul

/-- The real address helper returns the original word to an actual decoder caller. -/
theorem canonical (fuel : Nat) (pre : EVM.State) (address ret : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 945)
    (stack : pre.stack = address :: ret :: tail) (valid : (pre.toState.calldataload address).toNat < 2 ^ 160)
    (gas : 54 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1019)
    (caller : ret ∈ [UInt256.ofNat 191, UInt256.ofNat 210, UInt256.ofNat 381,
      UInt256.ofNat 395, UInt256.ofNat 862, UInt256.ofNat 894]) :
    EVM.X (fuel + 15) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      EVM.X (fuel + 1) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0))
        (NativeSourceCheckedCanonical.result pre address ret tail) := by
  exact NativeSourceCheckedCanonical.input_return fuel pre address ret tail code pc stack valid gas depth
    (NativeSourceReturnMembership.return_destinations ret caller)

/-- Noncanonical original words take the actual checked empty-revert path. -/
theorem noncanonical (fuel : Nat) (pre : EVM.State) (address ret : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 945)
    (stack : pre.stack = address :: ret :: tail) (invalid : ¬(pre.toState.calldataload address).toNat < 2 ^ 160)
    (gas : 52 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1019) :
    EVM.X (fuel + 18) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      .ok (.revert (UInt256.ofNat (pre.gasAvailable.toNat - 52)) ByteArray.empty) := by
  exact NativeSourceCheckedInputRejection.reject_exact fuel pre address ret tail code pc stack invalid gas depth

theorem returned_observation (pre : EVM.State) (address ret : UInt256) (tail : Stack UInt256)
    (gas : 54 ≤ pre.gasAvailable.toNat) :
    let post := NativeSourceCheckedCanonical.result pre address ret tail
    post.stack = pre.toState.calldataload address :: tail ∧ post.pc = ret ∧
      post.gasAvailable.toNat = pre.gasAvailable.toNat - 54 ∧
      post.toState = pre.toState ∧ post.memory = pre.memory := by
  have frame := NativeSourceCheckedCanonical.result_frame pre address ret tail
  exact ⟨frame.1, frame.2, NativeSourceCheckedCanonical.input_gas pre address ret tail gas,
    NativeSourceCanonicalFrames.input_world pre address ret tail,
    NativeSourceCanonicalFrames.input_memory pre address ret tail⟩

end Compiler.Proofs.IRGeneration.NativeSourceAddressCertificate

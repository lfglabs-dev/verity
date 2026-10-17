import Compiler.Proofs.IRGeneration.NativeSourceAddressEntry
import Compiler.Proofs.IRGeneration.NativeSourceReturnMembership

namespace Compiler.Proofs.IRGeneration.NativeSourceAddressEntryCertificate
open EvmYul NativeSourceAddressEntry

theorem canonical (fuel : Nat) (pre : EVM.State) (address ret : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 944)
    (stack : pre.stack = address :: ret :: tail) (valid : (pre.toState.calldataload address).toNat < 2 ^ 160)
    (gas : 55 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1019)
    (caller : ret ∈ [UInt256.ofNat 191, UInt256.ofNat 210, UInt256.ofNat 381,
      UInt256.ofNat 395, UInt256.ofNat 862, UInt256.ofNat 894]) :
    EVM.X (fuel + 16) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      EVM.X (fuel + 1) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0))
        (NativeSourceCheckedCanonical.result (entered pre) address ret tail) := by
  exact canonical_return fuel pre address ret tail code pc stack valid gas depth
    (NativeSourceReturnMembership.return_destinations ret caller)

theorem returned_stack (pre : EVM.State) (address ret : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 944) :
    (NativeSourceCheckedCanonical.result (entered pre) address ret tail).stack =
      pre.toState.calldataload address :: tail := by
  rw [(NativeSourceCheckedCanonical.result_frame (entered pre) address ret tail).1,
    (entry_frame pre pc).2.2.1]

theorem returned_world (pre : EVM.State) (address ret : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 944) :
    (NativeSourceCheckedCanonical.result (entered pre) address ret tail).toState = pre.toState := by
  exact (NativeSourceCanonicalFrames.input_world (entered pre) address ret tail).trans (entry_frame pre pc).2.2.1

theorem returned_memory (pre : EVM.State) (address ret : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 944) :
    (NativeSourceCheckedCanonical.result (entered pre) address ret tail).memory = pre.memory := by
  exact (NativeSourceCanonicalFrames.input_memory (entered pre) address ret tail).trans (entry_frame pre pc).2.2.2.1

end Compiler.Proofs.IRGeneration.NativeSourceAddressEntryCertificate

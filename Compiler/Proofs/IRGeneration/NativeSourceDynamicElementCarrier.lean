import Compiler.Proofs.IRGeneration.NativeSourceFieldEndpointCarrier

namespace Compiler.Proofs.IRGeneration.NativeSourceDynamicElementCarrier
open EvmYul

/-- Four native stores at the offsets used by the pinned market-array encoder.
This is a memory component, not yet a theorem about executing the loop. -/
def written (machine : MachineState) (pos a b c d : UInt256) : MachineState :=
  (((machine.mstore pos a).mstore (pos + UInt256.ofNat 32) b).mstore
    (pos + UInt256.ofNat 64) c).mstore (pos + UInt256.ofNat 96) d

theorem store_extent (machine : MachineState) (pos value : UInt256)
    (platform : 64 ≤ System.Platform.numBits) (bounded : pos.toNat < 2 ^ 64) :
    (machine.mstore pos value).memory.size = max machine.memory.size (pos.toNat + 32) := by
  have power : 2 ^ 64 ≤ 2 ^ System.Platform.numBits := Nat.pow_le_pow_right (by decide) platform
  exact MachineState.size_memory_mstore_of_pad machine pos value (by omega)

theorem element_extent (machine : MachineState) (pos a b c d : UInt256)
    (platform : 64 ≤ System.Platform.numBits) (bounded : pos.toNat + 96 < 2 ^ 64) :
    (written machine pos a b c d).memory.size = max machine.memory.size (pos.toNat + 128) := by
  have p32 := NativeSourceFieldGeometry.offset_toNat pos 32 (by decide) (by omega)
  have p64 := NativeSourceFieldGeometry.offset_toNat pos 64 (by decide) (by omega)
  have p96 := NativeSourceFieldGeometry.offset_toNat pos 96 (by decide) (by omega)
  have b32 : (pos + UInt256.ofNat 32).toNat < 2 ^ 64 := by rw [p32]; omega
  have b64 : (pos + UInt256.ofNat 64).toNat < 2 ^ 64 := by rw [p64]; omega
  have b96 : (pos + UInt256.ofNat 96).toNat < 2 ^ 64 := by rw [p96]; omega
  unfold written
  rw [store_extent _ _ _ platform b96, store_extent _ _ _ platform b64,
    store_extent _ _ _ platform b32, store_extent _ _ _ platform (by omega), p32, p64, p96]
  omega

end Compiler.Proofs.IRGeneration.NativeSourceDynamicElementCarrier

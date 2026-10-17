import Compiler.Proofs.IRGeneration.NativeSourceStorageBytecode
import EvmYul.EVM.Proof.MemoryStep

namespace Compiler.Proofs.IRGeneration.NativeMappingKeccak
open EvmYul

/-- Two adjacent native reads concatenate to the exact ABI-sized preimage. -/
theorem read_pair (memory : ByteArray) (inside : 64 ≤ memory.size) :
    memory.readWithPadding 0 64 =
      memory.readWithPadding 0 32 ++ memory.readWithPadding 32 32 := by
  rw [ByteArray.readWithPadding_eq_extract _ _ _ (by decide) (by decide) inside,
    ByteArray.readWithPadding_eq_extract _ _ _ (by decide) (by decide) (by omega),
    ByteArray.readWithPadding_eq_extract _ _ _ (by decide) (by decide) (by omega)]
  apply ByteArray.ext
  simp only [ByteArray.data_extract, ByteArray.data_append]
  change memory.data.extract 0 64 = memory.data.extract 0 32 ++ memory.data.extract 32 64
  rw [Array.extract_append_extract]
  rfl

private theorem base_store_pad (machine : MachineState) :
    (UInt256.ofNat 32).toNat - machine.memory.size < 2 ^ System.Platform.numBits := by
  have width : 32 < 2 ^ System.Platform.numBits := by
    rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> omega
  change 32 - machine.memory.size < _
  omega

/-- Store the base first: its write establishes the bounds needed by the key write. -/
theorem base_store_size (machine : MachineState) (base : UInt256) :
    64 ≤ (machine.mstore (UInt256.ofNat 32) base).memory.size := by
  exact MachineState.le_size_memory_mstore machine _ base (base_store_pad machine)

/-- The key store does not disturb the base word at offset 32. -/
theorem key_store_base (machine : MachineState) (base key : UInt256) :
    ((machine.mstore (UInt256.ofNat 32) base).mstore (UInt256.ofNat 0) key).memory.readWithPadding 32 32 =
      base.toByteArray := by
  have inside := base_store_size machine base
  change (ByteArray.write key.toByteArray 0
    (machine.mstore (UInt256.ofNat 32) base).memory 0 32).readWithPadding 32 32 = _
  rw [ByteArray.readWithPadding_write_of_ge _ _ _ _ _ _ (by decide)
    (UInt256.size_toByteArray key) (by omega) (by decide) (by decide) (by omega) (by omega)]
  exact MachineState.readWithPadding_memory_mstore_of_pad machine _ base (base_store_pad machine)

/-- The actual helper writes key first, then base; a growing base store preserves key. -/
theorem base_store_key (machine : MachineState) (base : UInt256)
    (inside : 32 ≤ machine.memory.size) :
    (machine.mstore (UInt256.ofNat 32) base).memory.readWithPadding 0 32 =
      machine.memory.readWithPadding 0 32 := by
  by_cases fits : 64 ≤ machine.memory.size
  · exact ByteArray.readWithPadding_write_of_le base.toByteArray machine.memory 32 32 0 32
      (by decide) (UInt256.size_toByteArray base) fits (by decide) (by decide) (by omega)
  · have grown := base_store_size machine base
    rw [ByteArray.readWithPadding_eq_extract _ _ _ (by decide) (by decide) (by omega),
      ByteArray.readWithPadding_eq_extract _ _ _ (by decide) (by decide) inside]
    change (ByteArray.write base.toByteArray 0 machine.memory 32 32).extract 0 32 = _
    have pad : 32 - machine.memory.size < 2 ^ System.Platform.numBits := base_store_pad machine
    rw [ByteArray.write_eq_of_grows base.toByteArray machine.memory 32 32 (by decide)
      (UInt256.size_toByteArray base) (by omega) pad]
    apply ByteArray.ext
    simp only [ByteArray.data_extract]
    have headSize : (machine.memory.data.extract 0 32).size = 32 := by
      simp only [Array.size_extract, ByteArray.size_data]; omega
    rw [show 32 - machine.memory.size = 0 from by omega, Array.replicate_zero, Array.append_empty]
    have trimmed : (machine.memory.data.extract 0 32).extract 0 32 = machine.memory.data.extract 0 32 := by
      simpa only [headSize] using (Array.extract_size (xs := machine.memory.data.extract 0 32))
    simpa only [headSize, Nat.zero_add, trimmed] using
      (Array.extract_append_left (as := machine.memory.data.extract 0 32) (bs := base.toByteArray.data))

/-- The real helper's two stores materialize exactly key followed by base. -/
theorem mapping_preimage (machine : MachineState) (base key : UInt256) :
    ((machine.mstore (UInt256.ofNat 0) key).mstore (UInt256.ofNat 32) base).memory.readWithPadding 0 64 =
      key.toByteArray ++ base.toByteArray := by
  have keyBounds : 32 ≤ (machine.mstore (UInt256.ofNat 0) key).memory.size :=
    MachineState.le_size_memory_mstore machine (UInt256.ofNat 0) key
      (by change 0 - machine.memory.size < _; simp only [Nat.zero_sub]; positivity)
  rw [read_pair _ (base_store_size _ base), base_store_key _ base keyBounds]
  have keyRead := MachineState.readWithPadding_memory_mstore_of_le machine (UInt256.ofNat 0) key
    (by exact Nat.zero_le _)
  have baseRead := MachineState.readWithPadding_memory_mstore_of_le
    (machine.mstore (UInt256.ofNat 0) key) (UInt256.ofNat 32) base keyBounds
  change (machine.mstore (UInt256.ofNat 0) key).memory.readWithPadding 0 32 = _ at keyRead
  change ((machine.mstore (UInt256.ofNat 0) key).mstore (UInt256.ofNat 32) base).memory.readWithPadding 32 32 = _ at baseRead
  rw [keyRead, baseRead]

/-- Actual native hash of the materialized mapping preimage. -/
theorem mapping_hash (machine : MachineState) (base key : UInt256) :
    (((machine.mstore (UInt256.ofNat 0) key).mstore (UInt256.ofNat 32) base).keccak256
      (UInt256.ofNat 0) (UInt256.ofNat 64)).1 =
      UInt256.ofNat (fromByteArrayBigEndian (ffi.KEC (key.toByteArray ++ base.toByteArray))) := by
  change UInt256.ofNat (fromByteArrayBigEndian (ffi.KEC
    (((machine.mstore (UInt256.ofNat 0) key).mstore (UInt256.ofNat 32) base).memory.readWithPadding 0 64))) = _
  rw [mapping_preimage]

/-- Actual KECCAK256 step, retaining its active-memory update and charged state. -/
theorem step_keccak (machine : EVM.State) (offset size : UInt256)
    (tail : Stack UInt256) (cost : Nat) :
    EVM.step 1 cost (some (.KECCAK256, none)) { machine with stack := offset :: size :: tail } =
      let charged := EVM.Proof.stepPre cost { machine with stack := offset :: size :: tail }
      let result := charged.toMachineState.keccak256 offset size
      .ok ({ charged with toMachineState := result.2 }.replaceStackAndIncrPC (result.1 :: tail)) := by
  rfl

/-- Successful checked hashing derives its result from actual memory, with world frame. -/
theorem checked_keccak (machine after : EVM.State) (offset size : UInt256) (tail : Stack UInt256)
    (stack : machine.stack = offset :: size :: tail)
    (success : CreationCaller.checkedStep machine .KECCAK256 none = .ok after) :
    after.stack = UInt256.ofNat (fromByteArrayBigEndian
      (ffi.KEC (machine.memory.readWithPadding offset.toNat size.toNat))) :: tail ∧
      after.toState = machine.toState ∧ after.memory = machine.memory ∧
      after.pc = machine.pc + UInt256.ofNat 1 := by
  have stepped := NativeCreationStorageOpcodes.checkedStep_delegates machine after .KECCAK256 none success
  let expanded := { machine with
    gasAvailable := machine.gasAvailable - UInt256.ofNat (EVM.memoryExpansionCost machine .KECCAK256) }
  let cost := EVM.C' expanded .KECCAK256
  change EVM.step 1 cost (some (.KECCAK256, none)) expanded = .ok after at stepped
  have expandedStack : expanded.stack = offset :: size :: tail := stack
  have restored : { expanded with stack := offset :: size :: tail } = expanded := by rw [← expandedStack]
  have actual := step_keccak expanded offset size tail cost
  rw [restored] at actual
  rw [actual] at stepped
  cases Except.ok.inj stepped
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- A pointwise FFI/pure agreement at this preimage identifies the model slot. -/
theorem mapping_hash_model (machine : MachineState) (base key : Nat)
    (hash : ffi.KEC (Compiler.Proofs.abiEncodeMappingSlot base key) =
      KeccakEngine.keccak256 (Compiler.Proofs.abiEncodeMappingSlot base key)) :
    (((machine.mstore (UInt256.ofNat 0) (UInt256.ofNat key)).mstore (UInt256.ofNat 32)
      (UInt256.ofNat base)).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 64)).1 =
      UInt256.ofNat (Compiler.Proofs.solidityMappingSlot base key) := by
  rw [mapping_hash]
  change UInt256.ofNat (fromByteArrayBigEndian (ffi.KEC (Compiler.Proofs.abiEncodeMappingSlot base key))) = _
  rw [hash]
  rfl

/-- A real checked MSTORE materializes exactly the primitive memory update. -/
theorem checked_mstore_memory (machine after : EVM.State) (offset value : UInt256) (tail : Stack UInt256)
    (stack : machine.stack = offset :: value :: tail)
    (success : CreationCaller.checkedStep machine .MSTORE none = .ok after) :
    after.memory = (machine.toMachineState.mstore offset value).memory := by
  let expanded := { machine with
    gasAvailable := machine.gasAvailable - UInt256.ofNat (EVM.memoryExpansionCost machine .MSTORE) }
  let cost := EVM.C' expanded .MSTORE
  have stepped := NativeCreationStorageOpcodes.checkedStep_delegates machine after .MSTORE none success
  change EVM.step 1 cost (some (.MSTORE, none)) expanded = .ok after at stepped
  have expandedStack : expanded.stack = offset :: value :: tail := stack
  have actual := EVM.Proof.step_MSTORE 0 cost expanded tail offset value
    (by rw [expandedStack]; rfl)
  have same : after = EVM.Proof.mstorePost cost expanded tail offset value :=
    Except.ok.inj (stepped.symm.trans actual)
  rw [same, EVM.Proof.memory_step_MSTORE_eq]
  rfl

/-- Two real checked MSTOREs, in emitted helper order, derive the ABI preimage. -/
theorem checked_mapping_preimage (initial middle final : EVM.State) (base key : UInt256)
    (keyTail baseTail : Stack UInt256)
    (keyStack : initial.stack = UInt256.ofNat 0 :: key :: keyTail)
    (baseStack : middle.stack = UInt256.ofNat 32 :: base :: baseTail)
    (first : CreationCaller.checkedStep initial .MSTORE none = .ok middle)
    (second : CreationCaller.checkedStep middle .MSTORE none = .ok final) :
    final.memory.readWithPadding 0 64 = key.toByteArray ++ base.toByteArray := by
  have keyMemory := checked_mstore_memory initial middle _ key keyTail keyStack first
  have baseMemory := checked_mstore_memory middle final _ base baseTail baseStack second
  change final.memory = ByteArray.write base.toByteArray 0 middle.memory 32 32 at baseMemory
  rw [keyMemory] at baseMemory
  rw [baseMemory]
  exact mapping_preimage initial.toMachineState base key

/-- The actual checked stores and hash compute the same slot as the pure model.
Only the hash equality at this precise preimage crosses the FFI boundary. -/
theorem checked_mapping_hash (initial middle prepared final : EVM.State) (base key : Nat)
    (keyTail baseTail hashTail : Stack UInt256)
    (keyStack : initial.stack = UInt256.ofNat 0 :: UInt256.ofNat key :: keyTail)
    (baseStack : middle.stack = UInt256.ofNat 32 :: UInt256.ofNat base :: baseTail)
    (hashStack : prepared.stack = UInt256.ofNat 0 :: UInt256.ofNat 64 :: hashTail)
    (first : CreationCaller.checkedStep initial .MSTORE none = .ok middle)
    (second : CreationCaller.checkedStep middle .MSTORE none = .ok prepared)
    (hashed : CreationCaller.checkedStep prepared .KECCAK256 none = .ok final)
    (hash : ffi.KEC (Compiler.Proofs.abiEncodeMappingSlot base key) =
      KeccakEngine.keccak256 (Compiler.Proofs.abiEncodeMappingSlot base key)) :
    final.stack = UInt256.ofNat (Compiler.Proofs.solidityMappingSlot base key) :: hashTail ∧
      final.toState = prepared.toState ∧ final.memory = prepared.memory ∧
      final.pc = prepared.pc + UInt256.ofNat 1 := by
  have preimage := checked_mapping_preimage initial middle prepared _ _ keyTail baseTail
    keyStack baseStack first second
  have result := checked_keccak prepared final _ _ hashTail hashStack hashed
  change final.stack = UInt256.ofNat (fromByteArrayBigEndian
    (ffi.KEC (prepared.memory.readWithPadding 0 64))) :: hashTail ∧ _ at result
  rw [preimage] at result
  change final.stack = UInt256.ofNat (fromByteArrayBigEndian
    (ffi.KEC (Compiler.Proofs.abiEncodeMappingSlot base key))) :: hashTail ∧ _ at result
  rw [hash] at result
  exact result

/-- The actual checked hash has the same native exceptional checks and gas debit. -/
theorem checked_keccak_z (machine after : EVM.State)
    (success : CreationCaller.checkedStep machine .KECCAK256 none = .ok after) :
    EVM.Proof.Z (EVM.D_J machine.executionEnv.code (UInt256.ofNat 0)) .KECCAK256 machine =
      .ok (EVM.Proof.zMid machine .KECCAK256, EVM.C' (EVM.Proof.zMid machine .KECCAK256) .KECCAK256) := by
  have guards := NativePairedCallerChecks.checked_guards machine after .KECCAK256 none success
  have enough : ¬ machine.stack.length < 2 := by
    simpa only [EVM.δ, Option.getD] using guards.stack
  have limit : ¬ machine.stack.length - 2 + 1 > 1024 := by
    simpa only [EVM.δ, EVM.α, Option.getD] using guards.limit
  have instruction := guards.instruction
  dsimp only [EVM.Proof.zMid] at instruction
  simp [EVM.Proof.Z, EVM.Proof.W, EVM.δ, EVM.α, Operation.isCreate,
    enough, limit, guards.memory, instruction]
  rfl

/-- Hashing is fuel-independent at every positive primitive fuel. -/
theorem step_keccak_fuel (fuel cost : Nat) (machine : EVM.State) :
    EVM.step (fuel + 1) cost (some (.KECCAK256, none)) machine =
      EVM.step 1 cost (some (.KECCAK256, none)) machine := by rfl

/-- Byte-authenticated checked hashing continues the actual native iterator.
This theorem does not change the paired caller's opcode admission whitelist. -/
theorem checked_keccak_x (fuel : Nat) (machine after : EVM.State)
    (fetched : machine.executionEnv.code.get? machine.pc.toNat = some 0x20)
    (success : CreationCaller.checkedStep machine .KECCAK256 none = .ok after) :
    EVM.X (fuel + 2) (EVM.D_J machine.executionEnv.code (UInt256.ofNat 0)) machine =
      EVM.X (fuel + 1) (EVM.D_J machine.executionEnv.code (UInt256.ofNat 0)) after := by
  have decoded : EVM.Proof.decodeAt machine = (.KECCAK256, none) := by
    simp only [EVM.Proof.decodeAt, EVM.decode, fetched, Bind.bind, Option.bind]
    rfl
  apply EVM.Proof.X_succ_of_continue decoded (checked_keccak_z machine after success)
  · change EVM.step (fuel + 1) (EVM.C' (EVM.Proof.zMid machine .KECCAK256) .KECCAK256)
      (some (.KECCAK256, none)) (EVM.Proof.zMid machine .KECCAK256) = .ok after
    rw [step_keccak_fuel]
    exact NativeCreationStorageOpcodes.checkedStep_delegates machine after .KECCAK256 none success
  · rfl

end Compiler.Proofs.IRGeneration.NativeMappingKeccak

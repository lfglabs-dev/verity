import Compiler.Proofs.IRGeneration.NativePrefixComposition

namespace Compiler.Proofs.IRGeneration.NativePrefixWorld
open EvmYul NativeCreationWorldCaller NativePrefixComposition
open NativeSourceAbiWrite CapturedMappingHelper

/-- The actual checked paired step, including hashing, retains full world and
warm set whenever its decoded operation is not a storage write. -/
theorem readonly_advance (before after : Frame) (op : Operation .EVM)
    (arg : Option (UInt256 × Nat)) (persistent : op ≠ .SSTORE) (transient : op ≠ .TSTORE)
    (success : NativeHashedWorldCaller.advance before op arg = .ok (.continued after)) :
    after.world = before.world ∧ after.warm = before.warm := by
  by_cases hash : op = .KECCAK256
  · subst op
    exact (NativeHashedWorldCaller.advance_hash_checked before after arg success).2
  · rw [NativeHashedWorldCaller.advance_other before op arg hash] at success
    have allowed := (NativePairedCallerExecution.advance_checked before after op arg success).1
    unfold NativeCreationWorldCaller.advance at success
    simp only [allowed, Bool.not_true, Bool.false_eq_true, ite_false,
      Bind.bind, Except.bind, Pure.pure, Except.pure] at success
    cases step : CreationCaller.checkedStep before.machine op arg with
    | error reason => simp only [step] at success; cases success
    | ok next =>
      simp only [step, worldAfter, persistent, transient, decide_false, Bool.false_or,
        Bool.false_eq_true, ite_false, Bind.bind, Except.bind, Pure.pure, Except.pure] at success
      cases success
      exact ⟨rfl, rfl⟩

private theorem frame_at (initial final : EVM.State) (start finish delta : UInt256)
    (pc : initial.pc = start)
    (frame : final.toState = initial.toState ∧ final.pc = initial.pc + delta)
    (position : start + delta = finish) :
    final.toState = initial.toState ∧ final.pc = finish := by
  exact ⟨frame.1, by rw [frame.2, pc, position]⟩

private theorem push1_frame (initial final : EVM.State) (word : UInt256)
    (success : CreationCaller.checkedStep initial (.Push .PUSH1) (some (word, 1)) = .ok final) :
    final.toState = initial.toState ∧ final.pc = initial.pc + UInt256.ofNat 2 := by
  have actual := checked_push1_shape initial final word success
  exact ⟨actual.2.1, actual.2.2.1⟩

private theorem push0_frame (initial final : EVM.State)
    (success : CreationCaller.checkedStep initial (.Push .PUSH0) none = .ok final) :
    final.toState = initial.toState ∧ final.pc = initial.pc + UInt256.ofNat 1 := by
  have actual := checked_push0_shape initial final success
  exact ⟨actual.2.1, actual.2.2.1⟩

/-- All twelve actual pre-write instructions preserve the native world and move
to the next authenticated source PC, with no supplied stack operands. -/
theorem stage_frame (index : Fin 12) (initial final : EVM.State)
    (pc : initial.pc = UInt256.ofNat instructions[(⟨index.val, by omega⟩ : Fin 13)].1)
    (success : CreationCaller.checkedStep initial instructions[(⟨index.val, by omega⟩ : Fin 13)].2.1
      instructions[(⟨index.val, by omega⟩ : Fin 13)].2.2 = .ok final) :
    final.toState = initial.toState ∧ final.pc = UInt256.ofNat instructions[(⟨index.val + 1, by omega⟩ : Fin 13)].1 := by
  obtain ⟨index, bound⟩ := index
  have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨ index = 5 ∨
    index = 6 ∨ index = 7 ∨ index = 8 ∨ index = 9 ∨ index = 10 ∨ index = 11 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact frame_at initial final _ _ _ pc (push1_frame initial final _ success) (by rfl)
  · exact frame_at initial final _ _ _ pc (checked_calldataload_frame initial final success) (by rfl)
  · exact frame_at initial final _ _ _ pc (push0_frame initial final success) (by rfl)
  · exact frame_at initial final _ _ _ pc (checked_mstore_frame initial final success) (by rfl)
  · exact frame_at initial final _ _ _ pc (push0_frame initial final success) (by rfl)
  · exact frame_at initial final _ _ _ pc (push1_frame initial final _ success) (by rfl)
  · exact frame_at initial final _ _ _ pc (checked_mstore_frame initial final success) (by rfl)
  · exact frame_at initial final _ _ _ pc (push1_frame initial final _ success) (by rfl)
  · exact frame_at initial final _ _ _ pc (checked_calldataload_frame initial final success) (by rfl)
  · exact frame_at initial final _ _ _ pc (push1_frame initial final _ success) (by rfl)
  · exact frame_at initial final _ _ _ pc (push0_frame initial final success) (by rfl)
  · exact frame_at initial final _ _ _ pc (checked_keccak_frame initial final success) (by rfl)

/-- No actual pre-write instruction is a persistent or transient store. -/
theorem stage_readonly (index : Fin 12) :
    instructions[(⟨index.val, by omega⟩ : Fin 13)].2.1 ≠ .SSTORE ∧
      instructions[(⟨index.val, by omega⟩ : Fin 13)].2.1 ≠ .TSTORE := by decide +revert

/-- Every successful actual pre-write fragment retains the entire canonical world,
warm set and native State. The resulting PC is derived, not supplied. -/
theorem prefix_world (count index : Nat) (initial final : Frame)
    (bound : index + count ≤ 12)
    (same : initial.machine.executionEnv.code = code)
    (pc : initial.machine.pc = UInt256.ofNat instructions[(⟨index, by omega⟩ : Fin 13)].1)
    (success : pairedSteps count initial = .ok final) :
    final.world = initial.world ∧ final.warm = initial.warm ∧
      final.machine.toState = initial.machine.toState ∧
      final.machine.pc = UInt256.ofNat instructions[(⟨index + count, by omega⟩ : Fin 13)].1 := by
  induction count generalizing index initial with
  | zero => cases success; exact ⟨rfl, rfl, rfl, pc⟩
  | succ count ih =>
    obtain ⟨op, arg, next, decoded, advanced, rest⟩ := paired_split count initial final success
    have actual := source_decode ⟨index, by omega⟩
    rw [← same, ← pc] at actual
    have instruction := Option.some.inj (decoded.symm.trans actual)
    have opEq := congrArg Prod.fst instruction
    have argEq := congrArg Prod.snd instruction
    dsimp only at opEq argEq
    rw [opEq, argEq] at advanced
    have step := advance_checked initial next _ _ advanced
    have frame := stage_frame ⟨index, by omega⟩ initial.machine next.machine pc step
    have allowed := stage_readonly ⟨index, by omega⟩
    have worlds := readonly_advance initial next _ _ allowed.1 allowed.2 advanced
    have nextCode : next.machine.executionEnv.code = code := by rw [frame.1]; exact same
    have nextBound : index + 1 + count ≤ 12 := by omega
    obtain ⟨world, warm, native, position⟩ := ih (index + 1) next nextBound nextCode frame.2 rest
    refine ⟨world.trans worlds.1, warm.trans worlds.2, native.trans frame.1, ?_⟩
    simpa only [Nat.add_assoc, Nat.add_comm 1 count] using position

/-- The actual thirteen-step paired source fragment performs exactly the one
whole-world write derived from its ORIGINAL calldata. -/
theorem fragment_world (initial final : Frame) (account : Account .EVM)
    (same : initial.machine.executionEnv.code = code) (pc : initial.machine.pc = UInt256.ofNat 404)
    (present : initial.machine.toState.lookupAccount initial.machine.executionEnv.codeOwner = some account)
    (success : pairedSteps 13 initial = .ok final)
    (hash : ffi.KEC (Compiler.Proofs.abiEncodeMappingSlot 0
      (initial.machine.toState.calldataload (UInt256.ofNat 36)).toNat) =
        KeccakEngine.keccak256 (Compiler.Proofs.abiEncodeMappingSlot 0
          (initial.machine.toState.calldataload (UInt256.ofNat 36)).toNat)) :
    final.world = initial.world.writeSlot (Compiler.Proofs.solidityMappingSlot 0
      (initial.machine.toState.calldataload (UInt256.ofNat 36)).toNat)
      (Verity.Core.Uint256.ofNat (initial.machine.toState.calldataload (UInt256.ofNat 68)).toNat) := by
  obtain ⟨middle, firstTwelve, last⟩ := paired_add_split 12 1 initial final success
  obtain ⟨world, warm, native, position⟩ := prefix_world 12 0 initial middle (by decide) same pc firstTwelve
  change middle.machine.pc = UInt256.ofNat 420 at position
  have currentCode : middle.machine.executionEnv.code = code := by rw [native]; exact same
  have expected := source_decode ⟨12, by decide⟩
  change EVM.decode code (UInt256.ofNat 420) = some (.SSTORE, none) at expected
  have actualDecode : EVM.decode middle.machine.executionEnv.code middle.machine.pc = some (.SSTORE, none) := by
    rw [currentCode, position]; exact expected
  obtain ⟨op, arg, next, decoded, advanced, rest⟩ := paired_split 0 middle final last
  have instruction := Option.some.inj (decoded.symm.trans actualDecode)
  cases instruction
  have finalEq : next = final := Except.ok.inj rest
  subst next
  obtain ⟨beforeStore, nativePrefix, stored, effect⟩ := source_paired_write initial.world initial.machine final.machine
    initial.warm account same pc present (paired_native 13 initial final success) hash
  have identity : beforeStore = middle.machine := Except.ok.inj
    (nativePrefix.symm.trans (paired_native 12 initial middle firstTwelve))
  subst beforeStore
  have sameFrame : (⟨initial.world, middle.machine, initial.warm⟩ : Frame) = middle := by
    rw [← world, ← warm]
  rw [sameFrame] at effect
  exact Except.ok.inj ((advance_world middle final .SSTORE none advanced).symm.trans effect)

/-- The complete staged prefix preserves the exact single-write world through
its actual local suffix to CREATE2, with ORIGINAL transaction calldata. -/
theorem execute_world (entryFuel suffixFuel : Nat) (initial final : Frame) (account : Account .EVM)
    (same : initial.machine.executionEnv.code = code)
    (present : initial.machine.toState.lookupAccount initial.machine.executionEnv.codeOwner = some account)
    (success : execute entryFuel suffixFuel initial = .ok (.ready final))
    (hash : ffi.KEC (Compiler.Proofs.abiEncodeMappingSlot 0
      (initial.machine.toState.calldataload (UInt256.ofNat 36)).toNat) =
        KeccakEngine.keccak256 (Compiler.Proofs.abiEncodeMappingSlot 0
          (initial.machine.toState.calldataload (UInt256.ofNat 36)).toNat)) :
    final.world = initial.world.writeSlot (Compiler.Proofs.solidityMappingSlot 0
      (initial.machine.toState.calldataload (UInt256.ofNat 36)).toNat)
      (Verity.Core.Uint256.ofNat (initial.machine.toState.calldataload (UInt256.ofNat 68)).toNat) := by
  obtain ⟨ready, stored, entry, middle, _, world, _⟩ := execute_split entryFuel suffixFuel initial final success
  obtain ⟨position, frame⟩ := NativeSourceEntryWrite.runTo_frame _ entryFuel initial.machine ready entry
  have currentCode : ready.executionEnv.code = code := by rw [frame]; exact same
  have currentAccount : ready.toState.lookupAccount ready.executionEnv.codeOwner = some account := by
    rw [frame]; exact present
  have currentHash : ffi.KEC (Compiler.Proofs.abiEncodeMappingSlot 0
      (ready.toState.calldataload (UInt256.ofNat 36)).toNat) =
        KeccakEngine.keccak256 (Compiler.Proofs.abiEncodeMappingSlot 0
          (ready.toState.calldataload (UInt256.ofNat 36)).toNat) := by rw [frame]; exact hash
  have actual := fragment_world { initial with machine := ready } stored account currentCode position
    currentAccount middle currentHash
  rw [world]
  simpa only [frame] using actual

end Compiler.Proofs.IRGeneration.NativePrefixWorld



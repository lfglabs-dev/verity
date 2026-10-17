import Compiler.Proofs.IRGeneration.NativeCreate2CallerDepth

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul EVM.Proof NativeCreationWorld
open Verity.Core.Model

/-- Exact native exceptional-check order for a structurally valid zero-value CREATE2. -/
theorem caller_create2_checks_order (pre : EVM.State) (jumps : Array UInt256)
    (rest : Stack UInt256) (offset size salt : UInt256)
    (stack : pre.stack = UInt256.ofNat 0 :: offset :: size :: salt :: rest)
    (limit : pre.stack.length ≤ 1024) :
    Z jumps .CREATE2 pre =
      if pre.gasAvailable.toNat < EVM.memoryExpansionCost pre .CREATE2 then .error .OutOfGass
      else if (create2MemoryDebited pre).gasAvailable.toNat < EVM.C' (create2MemoryDebited pre) .CREATE2 then .error .OutOfGass
      else if pre.executionEnv.perm = false then .error .StaticModeViolation
      else if 49152 < size.toNat then .error .OutOfGass
      else .ok (create2MemoryDebited pre, EVM.C' (create2MemoryDebited pre) .CREATE2) := by
  have underflow : ¬ pre.stack.length < 4 := by rw [stack]; simp
  have overflow : ¬ pre.stack.length - 4 + 1 > 1024 := by omega
  have sizeOrder : (size > (⟨49152⟩ : UInt256)) = (49152 < size.toNat) := by rfl
  simp [Z, create2MemoryDebited, EVM.δ, EVM.α, underflow, overflow, Operation.isCreate]
  simp [stack, W, sizeOrder]
  cases pre.executionEnv.perm <;> rfl

/-- A failed first gas gate is an actual interpreter exceptional halt. -/
theorem caller_create2_memory_exhausted (pre : EVM.State) (jumps : Array UInt256) (fuel : Nat)
    (decoded : decodeAt pre = (.CREATE2, none))
    (exhausted : pre.gasAvailable.toNat < EVM.memoryExpansionCost pre .CREATE2) :
    EVM.X (fuel + 1) jumps pre = .error .OutOfGass := by
  apply X_succ_of_Z_error decoded
  simp only [Z, exhausted, if_true, Bind.bind, Except.bind]

/-- Either native gas gate rejects exactly when the combined actual charge is unfunded. -/
theorem caller_create2_unfunded (pre : EVM.State) (jumps : Array UInt256)
    (rest : Stack UInt256) (offset size salt : UInt256)
    (stack : pre.stack = UInt256.ofNat 0 :: offset :: size :: salt :: rest)
    (limit : pre.stack.length ≤ 1024)
    (exhausted : pre.gasAvailable.toNat < EVM.memoryExpansionCost pre .CREATE2 + EVM.C' pre .CREATE2) :
    Z jumps .CREATE2 pre = .error .OutOfGass := by
  rw [caller_create2_checks_order pre jumps rest offset size salt stack limit]
  by_cases memory : pre.gasAvailable.toNat < EVM.memoryExpansionCost pre .CREATE2
  · rw [if_pos memory]
  · have enough := Nat.le_of_not_gt memory
    have debit := gas_sub_toNat pre.gasAvailable (EVM.memoryExpansionCost pre .CREATE2) enough
    have instruction : (create2MemoryDebited pre).gasAvailable.toNat < EVM.C' (create2MemoryDebited pre) .CREATE2 := by
      change (pre.gasAvailable - UInt256.ofNat (EVM.memoryExpansionCost pre .CREATE2)).toNat < EVM.C' pre .CREATE2
      rw [debit]
      omega
    rw [if_neg memory, if_pos instruction]

/-- Native rejection reason preserves gas-before-static-before-size ordering. -/
def callerCreate2Exception (pre : EVM.State) : EVM.ExecutionException :=
  if pre.gasAvailable.toNat < EVM.memoryExpansionCost pre .CREATE2 + EVM.C' pre .CREATE2
  then .OutOfGass else if pre.executionEnv.perm = false then .StaticModeViolation else .OutOfGass

/-- Every supported exceptional input has its precise native rejection reason. -/
theorem caller_create2_exceptional_reason (pre : EVM.State) (jumps : Array UInt256)
    (rest : Stack UInt256) (offset size salt : UInt256)
    (stack : pre.stack = UInt256.ofNat 0 :: offset :: size :: salt :: rest)
    (limit : pre.stack.length ≤ 1024)
    (exceptional : pre.gasAvailable.toNat < EVM.memoryExpansionCost pre .CREATE2 + EVM.C' pre .CREATE2 ∨
      pre.executionEnv.perm = false ∨ 49152 < size.toNat) :
    Z jumps .CREATE2 pre = .error (callerCreate2Exception pre) := by
  by_cases exhausted : pre.gasAvailable.toNat < EVM.memoryExpansionCost pre .CREATE2 + EVM.C' pre .CREATE2
  · rw [callerCreate2Exception, if_pos exhausted]
    exact caller_create2_unfunded pre jumps rest offset size salt stack limit exhausted
  · obtain ⟨memory, instruction⟩ := caller_create2_gas_checks pre (Nat.le_of_not_gt exhausted)
    rw [caller_create2_checks_order pre jumps rest offset size salt stack limit,
      if_neg (Nat.not_lt.mpr memory), if_neg (Nat.not_lt.mpr instruction)]
    rw [callerCreate2Exception, if_neg exhausted]
    by_cases staticMode : pre.executionEnv.perm = false
    · rw [if_pos staticMode, if_pos staticMode]
    · have oversize : 49152 < size.toNat := by rcases exceptional with h | h | h; contradiction; contradiction; exact h
      rw [if_neg staticMode, if_neg staticMode, if_pos oversize]

/-- Canonical preparation rejects the same exceptional inputs with the actual charge. -/
theorem caller_create2_prepare_exceptional (pre : EVM.State)
    (rest : Stack UInt256) (offset size salt : UInt256)
    (stack : pre.stack = UInt256.ofNat 0 :: offset :: size :: salt :: rest)
    (valid : pre.gasAvailable.toNat ≤ Create2Entry.maxGas)
    (exceptional : pre.gasAvailable.toNat < EVM.memoryExpansionCost pre .CREATE2 + EVM.C' pre .CREATE2 ∨
      pre.executionEnv.perm = false ∨ 49152 < size.toNat) :
    Create2Entry.prepare (CreationBytecode.callerMemory pre)
      { gas := pre.gasAvailable.toNat, depth := pre.executionEnv.depth, isStatic := !pre.executionEnv.perm }
      offset.toNat size.toNat = .ok .exceptional := by
  rcases exceptional with exhausted | staticMode | oversize
  · apply Create2Entry.prepare_out_of_gas _ _ _ _ valid
    change pre.gasAvailable.toNat < _
    rw [native_create2_entry_cost pre (UInt256.ofNat 0) offset size salt rest stack
      (native_memory_words_nowrap pre.activeWords offset size)]
    exact exhausted
  · exact Create2Entry.prepare_static _ _ _ _ valid (by simp [staticMode])
  · exact Create2Entry.prepare_oversize _ _ _ _ valid oversize

/-- Canonical exceptional frame retains the opcode-entry snapshot and consumes all gas. -/
def callerExceptionalFinal (world : Verity.ContractState) (pre : EVM.State)
    (warm : Create2Access.WarmAccounts) : Create2Operation.Frame :=
  let boundary := CreationBytecode.atBoundary ⟨world, pre, warm⟩
  { boundary with context := { boundary.context with gas := 0 } }

/-- Full canonical run rejects without inspecting the initcode or computing its hash. -/
theorem caller_create2_exceptional_run (world : Verity.ContractState) (pre : EVM.State)
    (warm : Create2Access.WarmAccounts) (rest : Stack UInt256) (offset size salt : UInt256)
    (stack : pre.stack = UInt256.ofNat 0 :: offset :: size :: salt :: rest)
    (valid : pre.gasAvailable.toNat ≤ Create2Entry.maxGas)
    (exceptional : pre.gasAvailable.toNat < EVM.memoryExpansionCost pre .CREATE2 + EVM.C' pre .CREATE2 ∨
      pre.executionEnv.perm = false ∨ 49152 < size.toNat) :
    Create2Operation.run (CreationBytecode.atBoundary ⟨world, pre, warm⟩)
      (Verity.Core.Uint256.ofNat offset.toNat) (Verity.Core.Uint256.ofNat size.toNat)
      (Verity.Core.Uint256.ofNat salt.toNat) = .ok (.exceptional (callerExceptionalFinal world pre warm)) := by
  apply Create2Operation.run_exceptional
  have offsetValue : (Verity.Core.Uint256.ofNat offset.toNat).val = offset.toNat := Nat.mod_eq_of_lt offset.val.isLt
  have sizeValue : (Verity.Core.Uint256.ofNat size.toNat).val = size.toNat := Nat.mod_eq_of_lt size.val.isLt
  rw [offsetValue, sizeValue]
  exact caller_create2_prepare_exceptional pre rest offset size salt stack valid exceptional

/-- Exceptional canonical preparation preserves all raw account and storage facts. -/
theorem caller_exceptional_agreement (world : Verity.ContractState) (pre : EVM.State)
    (warm : Create2Access.WarmAccounts) (agrees : Agreement world pre warm) :
    Agreement (callerExceptionalFinal world pre warm).world pre warm := by
  exact { agrees with }

/-- Exceptional canonical preparation retains complete initial physical memory. -/
theorem caller_exceptional_physical_memory (world : Verity.ContractState) (pre : EVM.State)
    (warm : Create2Access.WarmAccounts) :
    CallerPhysicalMemoryAgreement (callerExceptionalFinal world pre warm).world pre := by
  exact ⟨rfl, fun _ => rfl⟩

/-- Exceptional canonical preparation preserves every remaining world field. -/
theorem caller_exceptional_world_frame (world : Verity.ContractState) (pre : EVM.State)
    (warm : Create2Access.WarmAccounts) :
    callerWorldFrame (callerExceptionalFinal world pre warm).world = callerWorldFrame world := rfl

/-- Complete exceptional opcode correspondence, retaining the precise native reason. -/
theorem caller_exceptional_operation_completed (world : Verity.ContractState) (pre : EVM.State)
    (warm : Create2Access.WarmAccounts) (agrees : Agreement world pre warm)
    (jumps : Array UInt256) (fuel : Nat) (rest : Stack UInt256) (offset size salt : UInt256)
    (decoded : decodeAt pre = (.CREATE2, none))
    (stack : pre.stack = UInt256.ofNat 0 :: offset :: size :: salt :: rest)
    (limit : pre.stack.length ≤ 1024) (valid : pre.gasAvailable.toNat ≤ Create2Entry.maxGas)
    (exceptional : pre.gasAvailable.toNat < EVM.memoryExpansionCost pre .CREATE2 + EVM.C' pre .CREATE2 ∨
      pre.executionEnv.perm = false ∨ 49152 < size.toNat) :
    Z jumps .CREATE2 pre = .error (callerCreate2Exception pre) ∧
    EVM.X (fuel + 1) jumps pre = .error (callerCreate2Exception pre) ∧
    Create2Operation.run (CreationBytecode.atBoundary ⟨world, pre, warm⟩)
      (Verity.Core.Uint256.ofNat offset.toNat) (Verity.Core.Uint256.ofNat size.toNat)
      (Verity.Core.Uint256.ofNat salt.toNat) = .ok (.exceptional (callerExceptionalFinal world pre warm)) ∧
    (callerExceptionalFinal world pre warm).context.gas = 0 ∧
    Agreement (callerExceptionalFinal world pre warm).world pre warm ∧
    CallerPhysicalMemoryAgreement (callerExceptionalFinal world pre warm).world pre ∧
    callerWorldFrame (callerExceptionalFinal world pre warm).world = callerWorldFrame world ∧
    (callerExceptionalFinal world pre warm).warm = warm ∧
    (callerExceptionalFinal world pre warm).world.storageWords = world.storageWords := by
  have rejected := caller_create2_exceptional_reason pre jumps rest offset size salt stack limit exceptional
  exact ⟨rejected, X_succ_of_Z_error decoded rejected,
    caller_create2_exceptional_run world pre warm rest offset size salt stack valid exceptional, rfl,
    caller_exceptional_agreement world pre warm agrees, caller_exceptional_physical_memory world pre warm,
    caller_exceptional_world_frame world pre warm, rfl, rfl⟩

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor

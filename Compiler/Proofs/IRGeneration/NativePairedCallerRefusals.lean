import Compiler.Proofs.IRGeneration.NativePairedCallerBoundary

namespace Compiler.Proofs.IRGeneration.NativePairedCallerRefusals
open EvmYul EVM.Proof NativeCreationWorld NativeMidnightConstructor
open NativeCreationWorldCaller NativePairedCallerBoundary
open Verity.Core.Model

/-- The actual prefix composes with the complete native/canonical depth result. -/
theorem run_ready_depth (prefixFuel : Nat) (before boundary : Frame)
    (bounded : before.machine.executionEnv.code.size < UInt256.size)
    (agrees : Agreement before.world before.machine before.warm)
    (allocated : CallerAllocated before.machine)
    (ready : run prefixFuel before = .ok (.ready boundary))
    (fuel : Nat) (rest : Stack UInt256) (offset size salt : UInt256)
    (stack : boundary.machine.stack = UInt256.ofNat 0 :: offset :: size :: salt :: rest)
    (limit : boundary.machine.stack.length ≤ 1024) (mutable : boundary.machine.executionEnv.perm = true)
    (cap : size.toNat ≤ 49152) (valid : boundary.machine.gasAvailable.toNat ≤ Create2Entry.maxGas)
    (funded : EVM.memoryExpansionCost boundary.machine .CREATE2 + EVM.C' boundary.machine .CREATE2 ≤ boundary.machine.gasAvailable.toNat)
    (nonce : ¬ ((boundary.machine.accountMap.get? boundary.machine.executionEnv.codeOwner).getD default).nonce.toNat ≥ 2^64 - 1)
    (depth : 1024 ≤ boundary.machine.executionEnv.depth) (target : AccountAddress) :
    ∃ steps next final, steps < prefixFuel ∧
      EVM.step (fuel + 3) (EVM.C' (create2MemoryDebited boundary.machine) .CREATE2)
        (some (.CREATE2, none)) (create2MemoryDebited boundary.machine) = .ok next ∧
      EVM.X (steps + fuel + 4) (EVM.D_J before.machine.executionEnv.code (UInt256.ofNat 0)) before.machine =
        EVM.X (fuel + 3) (EVM.D_J before.machine.executionEnv.code (UInt256.ofNat 0)) next ∧
      Create2Operation.run (CreationBytecode.atBoundary ⟨boundary.world, boundary.machine, boundary.warm⟩)
        (Verity.Core.Uint256.ofNat offset.toNat) (Verity.Core.Uint256.ofNat size.toNat)
        (Verity.Core.Uint256.ofNat salt.toNat) = .ok (.continued 0 final) ∧
      Agreement final.world next final.warm ∧ next.gasAvailable.toNat = final.context.gas ∧
      CallerResultObservations boundary.machine next rest offset size 0 ∧
      CallerPhysicalMemoryAgreement final.world next ∧
      CallerFrameAgreement boundary.world final.world boundary.machine.substate next.substate target ∧
      next.accountMap = boundary.machine.accountMap ∧ next.substate = boundary.machine.substate ∧ final.warm = boundary.warm := by
  obtain ⟨environment, steps, within, continuation⟩ := run_ready_steps prefixFuel before boundary bounded ready
  obtain ⟨agreement, allocation⟩ := NativePairedCallerAllocation.run_ready_boundary prefixFuel before boundary agrees allocated ready
  have decoded := run_ready_decoded prefixFuel before boundary ready
  let jumps := EVM.D_J before.machine.executionEnv.code (UInt256.ofNat 0)
  obtain ⟨next, final, stepped, created, operation, related, gas, observations, physical, frames, accounts, substate, warm⟩ :=
    caller_depth_operation_completed boundary.world boundary.machine boundary.warm agreement allocation jumps fuel rest offset size salt decoded stack limit mutable cap valid funded nonce depth target
  have prefixRun := continuation (fuel + 3)
  have combined : EVM.X (steps + fuel + 4) jumps before.machine = EVM.X (fuel + 3) jumps next := by
    calc
      _ = EVM.X (fuel + 4) jumps boundary.machine := by simpa only [Nat.add_assoc] using prefixRun
      _ = _ := created
  exact ⟨steps, next, final, within, stepped, combined, operation, related, gas, observations, physical, frames, accounts, substate, warm⟩

/-- The actual prefix composes with the complete native/canonical nonce result. -/
theorem run_ready_nonce (prefixFuel : Nat) (before boundary : Frame)
    (bounded : before.machine.executionEnv.code.size < UInt256.size)
    (agrees : Agreement before.world before.machine before.warm)
    (allocated : CallerAllocated before.machine)
    (ready : run prefixFuel before = .ok (.ready boundary))
    (fuel : Nat) (rest : Stack UInt256) (offset size salt : UInt256)
    (stack : boundary.machine.stack = UInt256.ofNat 0 :: offset :: size :: salt :: rest)
    (limit : boundary.machine.stack.length ≤ 1024) (mutable : boundary.machine.executionEnv.perm = true)
    (cap : size.toNat ≤ 49152) (valid : boundary.machine.gasAvailable.toNat ≤ Create2Entry.maxGas)
    (funded : EVM.memoryExpansionCost boundary.machine .CREATE2 + EVM.C' boundary.machine .CREATE2 ≤ boundary.machine.gasAvailable.toNat)
    (depth : boundary.machine.executionEnv.depth < 1024)
    (nonce : ((boundary.machine.accountMap.get? boundary.machine.executionEnv.codeOwner).getD default).nonce.toNat = 2^64 - 1)
    (target : AccountAddress) :
    ∃ steps next final, steps < prefixFuel ∧
      EVM.step (fuel + 3) (EVM.C' (create2MemoryDebited boundary.machine) .CREATE2)
        (some (.CREATE2, none)) (create2MemoryDebited boundary.machine) = .ok next ∧
      EVM.X (steps + fuel + 4) (EVM.D_J before.machine.executionEnv.code (UInt256.ofNat 0)) before.machine =
        EVM.X (fuel + 3) (EVM.D_J before.machine.executionEnv.code (UInt256.ofNat 0)) next ∧
      Create2Operation.run (CreationBytecode.atBoundary ⟨boundary.world, boundary.machine, boundary.warm⟩)
        (Verity.Core.Uint256.ofNat offset.toNat) (Verity.Core.Uint256.ofNat size.toNat)
        (Verity.Core.Uint256.ofNat salt.toNat) = .ok (.continued 0 final) ∧
      Agreement final.world next final.warm ∧ next.gasAvailable.toNat = final.context.gas ∧
      CallerResultObservations boundary.machine next rest offset size 0 ∧
      CallerPhysicalMemoryAgreement final.world next ∧
      CallerFrameAgreement boundary.world final.world boundary.machine.substate next.substate target ∧
      next.accountMap = boundary.machine.accountMap ∧ next.substate = boundary.machine.substate ∧ final.warm = boundary.warm := by
  obtain ⟨environment, steps, within, continuation⟩ := run_ready_steps prefixFuel before boundary bounded ready
  obtain ⟨agreement, allocation⟩ := NativePairedCallerAllocation.run_ready_boundary prefixFuel before boundary agrees allocated ready
  have decoded := run_ready_decoded prefixFuel before boundary ready
  let jumps := EVM.D_J before.machine.executionEnv.code (UInt256.ofNat 0)
  obtain ⟨next, final, stepped, created, operation, related, gas, observations, physical, frames, accounts, substate, warm⟩ :=
    caller_nonce_operation_completed boundary.world boundary.machine boundary.warm agreement allocation jumps fuel rest offset size salt decoded stack limit mutable cap valid funded depth nonce target
  have prefixRun := continuation (fuel + 3)
  have combined : EVM.X (steps + fuel + 4) jumps before.machine = EVM.X (fuel + 3) jumps next := by
    calc
      _ = EVM.X (fuel + 4) jumps boundary.machine := by simpa only [Nat.add_assoc] using prefixRun
      _ = _ := created
  exact ⟨steps, next, final, within, stepped, combined, operation, related, gas, observations, physical, frames, accounts, substate, warm⟩

/-- The actual prefix composes with the complete native/canonical collision result. -/
theorem run_ready_collision (prefixFuel : Nat) (before boundary : Frame)
    (bounded : before.machine.executionEnv.code.size < UInt256.size)
    (agrees : Agreement before.world before.machine before.warm)
    (allocated : CallerAllocated before.machine)
    (ready : run prefixFuel before = .ok (.ready boundary))
    (fuel : Nat) (rest : Stack UInt256) (offset size salt : UInt256)
    (guards : CallerCollisionGuards boundary.machine rest offset size salt)
    (limit : boundary.machine.stack.length ≤ 1024) :
    ∃ steps next final, steps < prefixFuel ∧
      EVM.step (fuel + 4) (EVM.C' (create2MemoryDebited boundary.machine) .CREATE2)
        (some (.CREATE2, none)) (create2MemoryDebited boundary.machine) = .ok next ∧
      EVM.X (steps + fuel + 5) (EVM.D_J before.machine.executionEnv.code (UInt256.ofNat 0)) before.machine =
        EVM.X (fuel + 4) (EVM.D_J before.machine.executionEnv.code (UInt256.ofNat 0)) next ∧
      Create2Operation.run (CreationBytecode.atBoundary ⟨boundary.world, boundary.machine, boundary.warm⟩)
        (Verity.Core.Uint256.ofNat offset.toNat) (Verity.Core.Uint256.ofNat size.toNat)
        (Verity.Core.Uint256.ofNat salt.toNat) = .ok (.continued 0 final) ∧
      Agreement final.world next final.warm ∧ next.gasAvailable.toNat = final.context.gas ∧
      CallerResultObservations boundary.machine next rest offset size 0 ∧
      CallerPhysicalMemoryAgreement final.world next ∧
      CallerFrameAgreement boundary.world final.world boundary.machine.substate next.substate
        (nativeCreate2Target boundary.machine.executionEnv.codeOwner salt.toByteArray
          (boundary.machine.memory.readWithPadding offset.toNat size.toNat)) ∧
      final.world.storageWords = boundary.world.storageWords ∧
      next.substate = boundary.machine.substate.addAccessedAccount (nativeCreate2Target boundary.machine.executionEnv.codeOwner salt.toByteArray
        (boundary.machine.memory.readWithPadding offset.toNat size.toNat)) := by
  obtain ⟨environment, steps, within, continuation⟩ := run_ready_steps prefixFuel before boundary bounded ready
  obtain ⟨agreement, allocation⟩ := NativePairedCallerAllocation.run_ready_boundary prefixFuel before boundary agrees allocated ready
  have decoded := run_ready_decoded prefixFuel before boundary ready
  let jumps := EVM.D_J before.machine.executionEnv.code (UInt256.ofNat 0)
  obtain ⟨next, final, stepped, created, operation, related, gas, observations, physical, frames, storage, substate⟩ :=
    caller_collision_operation_completed boundary.world boundary.machine boundary.warm agreement allocation jumps fuel rest offset size salt guards decoded limit
  have prefixRun := continuation (fuel + 4)
  have combined : EVM.X (steps + fuel + 5) jumps before.machine = EVM.X (fuel + 4) jumps next := by
    calc
      _ = EVM.X (fuel + 5) jumps boundary.machine := by simpa only [Nat.add_assoc] using prefixRun
      _ = _ := created
  exact ⟨steps, next, final, within, stepped, combined, operation, related, gas, observations, physical, frames, storage, substate⟩

/-- Native exceptional reason and all canonical exceptional observations after the real prefix. -/
theorem run_ready_exceptional (prefixFuel : Nat) (before boundary : Frame)
    (bounded : before.machine.executionEnv.code.size < UInt256.size)
    (agrees : Agreement before.world before.machine before.warm)
    (ready : run prefixFuel before = .ok (.ready boundary))
    (fuel : Nat) (rest : Stack UInt256) (offset size salt : UInt256)
    (stack : boundary.machine.stack = UInt256.ofNat 0 :: offset :: size :: salt :: rest)
    (limit : boundary.machine.stack.length ≤ 1024) (valid : boundary.machine.gasAvailable.toNat ≤ Create2Entry.maxGas)
    (exceptional : boundary.machine.gasAvailable.toNat < EVM.memoryExpansionCost boundary.machine .CREATE2 + EVM.C' boundary.machine .CREATE2 ∨
      boundary.machine.executionEnv.perm = false ∨ 49152 < size.toNat) :
    ∃ steps, steps < prefixFuel ∧
    Z (EVM.D_J before.machine.executionEnv.code (UInt256.ofNat 0)) .CREATE2 boundary.machine = .error (callerCreate2Exception boundary.machine) ∧
    EVM.X (steps + fuel + 1) (EVM.D_J before.machine.executionEnv.code (UInt256.ofNat 0)) before.machine = .error (callerCreate2Exception boundary.machine) ∧
    Create2Operation.run (CreationBytecode.atBoundary ⟨boundary.world, boundary.machine, boundary.warm⟩)
      (Verity.Core.Uint256.ofNat offset.toNat) (Verity.Core.Uint256.ofNat size.toNat)
      (Verity.Core.Uint256.ofNat salt.toNat) = .ok (.exceptional (callerExceptionalFinal boundary.world boundary.machine boundary.warm)) ∧
    (callerExceptionalFinal boundary.world boundary.machine boundary.warm).context.gas = 0 ∧
    Agreement (callerExceptionalFinal boundary.world boundary.machine boundary.warm).world boundary.machine boundary.warm ∧
    CallerPhysicalMemoryAgreement (callerExceptionalFinal boundary.world boundary.machine boundary.warm).world boundary.machine ∧
    callerWorldFrame (callerExceptionalFinal boundary.world boundary.machine boundary.warm).world = callerWorldFrame boundary.world ∧
    (callerExceptionalFinal boundary.world boundary.machine boundary.warm).warm = boundary.warm ∧
    (callerExceptionalFinal boundary.world boundary.machine boundary.warm).world.storageWords = boundary.world.storageWords := by
  obtain ⟨environment, steps, within, continuation⟩ := run_ready_steps prefixFuel before boundary bounded ready
  have agreement := NativeCreationWorldCaller.run_ready_agreement prefixFuel before boundary agrees ready
  have decoded := run_ready_decoded prefixFuel before boundary ready
  let jumps := EVM.D_J before.machine.executionEnv.code (UInt256.ofNat 0)
  obtain ⟨checked, failed, operation, gas, related, physical, frames, warm, storage⟩ :=
    caller_exceptional_operation_completed boundary.world boundary.machine boundary.warm agreement jumps fuel rest offset size salt decoded stack limit valid exceptional
  have prefixRun := continuation fuel
  have combined : EVM.X (steps + fuel + 1) jumps before.machine = .error (callerCreate2Exception boundary.machine) :=
    prefixRun.trans failed
  exact ⟨steps, within, checked, combined, operation, gas, related, physical, frames, warm, storage⟩

end Compiler.Proofs.IRGeneration.NativePairedCallerRefusals

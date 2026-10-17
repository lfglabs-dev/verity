import Compiler.Proofs.IRGeneration.NativeConstructorLambdaResult

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul EVM.Proof

/-- The real native guard on INVALID can only reject for gas or invalid code. -/
theorem invalid_checked (jumps : Array UInt256) (pre : EVM.State) :
    Z jumps .INVALID pre = .error .OutOfGass ∨
      Z jumps .INVALID pre = .error .InvalidInstruction := by
  have form : Z jumps .INVALID pre =
      if pre.gasAvailable.toNat < EVM.memoryExpansionCost pre .INVALID then .error .OutOfGass
      else if (pre.gasAvailable - UInt256.ofNat (EVM.memoryExpansionCost pre .INVALID)).toNat <
          EVM.C' { pre with gasAvailable := pre.gasAvailable - UInt256.ofNat (EVM.memoryExpansionCost pre .INVALID) } .INVALID then .error .OutOfGass
      else .error .InvalidInstruction := by rfl
  rw [form]
  split
  · exact Or.inl rfl
  · split
    · exact Or.inl rfl
    · exact Or.inr rfl

/-- Collision initcode really executes INVALID; it is not mapped from an
arbitrary exception or a fuel failure. -/
theorem collision_run (jumps : Array UInt256) (pre : EVM.State)
    (code : pre.executionEnv.code = ⟨#[0xfe]⟩) (pc : pre.pc = UInt256.ofNat 0)
    (fuel : Nat) :
    EVM.X (fuel + 1) jumps pre = .error .OutOfGass ∨
      EVM.X (fuel + 1) jumps pre = .error .InvalidInstruction := by
  have decoded : decodeAt pre = (.INVALID, none) := by
    simp only [decodeAt, code, pc]
    rfl
  rcases invalid_checked jumps pre with gas | invalid
  · exact Or.inl (X_succ_of_Z_error decoded gas)
  · exact Or.inr (X_succ_of_Z_error decoded invalid)

theorem xi_collision (created : Std.TreeSet AccountAddress compare) (genesis : BlockHeader)
    (blocks : ProcessedBlocks) (accounts original : AccountMap .EVM)
    (gas : UInt256) (substate : Substate) (environment : ExecutionEnv .EVM)
    (code : environment.code = ⟨#[0xfe]⟩) (fuel : Nat) :
    EVM.Ξ (fuel + 2) created genesis blocks accounts original gas substate environment =
        .error .OutOfGass ∨
      EVM.Ξ (fuel + 2) created genesis blocks accounts original gas substate environment =
        .error .InvalidInstruction := by
  have failed := collision_run (EVM.D_J environment.code ⟨0⟩)
    (xiInitial created genesis blocks accounts original gas substate environment) code rfl fuel
  rw [show fuel + 2 = (fuel + 1) + 1 by omega, xi_run]
  rcases failed with failed | failed
  · rw [failed]; exact Or.inl rfl
  · rw [failed]; exact Or.inr rfl

/-- Both native collision criteria roll back the account map and consume all
callee gas; no interpreter exhaustion is silently turned into this result. -/
theorem lambda_collision (init : ByteArray)
    (blobs : List ByteArray) (created : Std.TreeSet AccountAddress compare)
    (genesis : BlockHeader) (blocks : ProcessedBlocks)
    (accounts original : AccountMap .EVM) (substate : Substate)
    (sender origin : AccountAddress) (gas price value depth : UInt256)
    (salt : ByteArray) (header : BlockHeader) (permission : Bool)
    (collision : let account := accounts.getD (nativeCreate2Target sender salt init) default
      (decide (account.nonce ≠ (⟨0⟩ : UInt256)) || decide (account.code.size ≠ 0)) = true)
    (fuel : Nat) :
    let target := nativeCreate2Target sender salt init
    EVM.Lambda (fuel + 3) blobs created genesis blocks accounts original substate
      sender origin gas price value init depth (some salt) header permission =
      .ok (target, created, accounts, UInt256.ofNat 0,
        substate.addAccessedAccount target, false, ByteArray.empty) := by
  simp only [EVM.Lambda, EVM.Lambda.L_A]
  dsimp only [liftM, monadLift, MonadLift.monadLift, Option.option, Bind.bind, Except.bind]
  simp only [nativeCreate2Target] at collision
  simp only [Bool.or_eq_true, decide_eq_true_eq] at collision
  have selected : (let account := accounts.getD (nativeCreate2Target sender salt init) default
      account.nonce ≠ (⟨0⟩ : UInt256) ∨ account.code.size ≠ 0) := collision
  simp only [nativeCreate2Target] at selected
  simp only [Bool.or_eq_true, decide_eq_true_eq, selected, if_true]
  generalize executed : EVM.Ξ (fuel + 2) _ _ _ _ _ _ _ _ = result
  have failed : result = .error .OutOfGass ∨ result = .error .InvalidInstruction := by
    rw [← executed]
    apply xi_collision
    rfl
  rcases failed with failed | failed
  · rw [failed]; rfl
  · rw [failed]; rfl

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor

import Compiler.Proofs.IRGeneration.NativePairedCallerAllocation

namespace Compiler.Proofs.IRGeneration.NativePairedCallerFuel
open EvmYul NativeCreationWorldCaller

/-- Unknown bytes parse as INVALID, so the apparent scanner stop is unreachable. -/
theorem parse_instruction_total : ∀ byte : UInt8, (EVM.parseInstr byte).isSome = true := by
  have total : ∀ hi : Fin 8, ∀ lo : Fin 32,
      (EVM.parseInstr (UInt8.ofNat (hi.val * 32 + lo.val))).isSome = true := by
    rintro ⟨hi, bound⟩
    have cases : hi = 0 ∨ hi = 1 ∨ hi = 2 ∨ hi = 3 ∨ hi = 4 ∨ hi = 5 ∨ hi = 6 ∨ hi = 7 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide
  intro byte
  have bound := UInt8.toNat_lt_size byte
  change byte.toNat < 256 at bound
  have checked := total ⟨byte.toNat / 32, by omega⟩ ⟨byte.toNat % 32, Nat.mod_lt _ (by decide)⟩
  have value : byte.toNat / 32 * 32 + byte.toNat % 32 = byte.toNat := by omega
  simpa only [value, UInt8.ofNat_toNat] using checked


/-- Regression: unassigned bytes do not suppress later real JUMPDEST instructions. -/
theorem unknown_opcode_scanners :
    CreationCaller.jumpDestinations ⟨#[0x0c, 0x5b]⟩ = #[UInt256.ofNat 1] ∧
      EVM.D_J ⟨#[0x0c, 0x5b]⟩ (UInt256.ofNat 0) = #[UInt256.ofNat 1] := by decide

/-- Every admitted paired-prefix primitive has identical semantics at positive fuel. -/
theorem paired_step_fuel (fuel : Nat) (op : Operation .EVM)
    (machine : EVM.State) (arg : Option (UInt256 × Nat)) (cost : Nat)
    (admitted : (CreationCaller.supported op || op = .SSTORE || op = .TSTORE) = true) :
    EVM.step (fuel + 1) cost (some (op, arg)) machine = EVM.step 1 cost (some (op, arg)) machine := by
  by_cases store : op = .SSTORE ∨ op = .TSTORE
  · rcases store with rfl | rfl
    all_goals simp only [EVM.step, Bind.bind, Pure.pure, Except.bind, Except.pure]
  · have persistent : op ≠ .SSTORE := fun h => store (.inl h)
    have transient : op ≠ .TSTORE := fun h => store (.inr h)
    have allowed : CreationCaller.supported op = true := by simpa [persistent, transient] using admitted
    exact NativeInitcodeFrames.supported_step_fuel fuel op machine arg cost allowed

/-- Successful checked prefix steps retain their exact native result at all positive fuel. -/
theorem paired_checked_step (fuel : Nat) (op : Operation .EVM)
    (machine after : EVM.State) (arg : Option (UInt256 × Nat))
    (admitted : (CreationCaller.supported op || op = .SSTORE || op = .TSTORE) = true)
    (success : CreationCaller.checkedStep machine op arg = .ok after) :
    let expanded := { machine with gasAvailable := machine.gasAvailable - UInt256.ofNat (EVM.memoryExpansionCost machine op) }
    EVM.step (fuel + 1) (EVM.C' expanded op) (some (op, arg)) expanded = .ok after := by
  dsimp only
  rw [paired_step_fuel fuel op _ arg _ admitted]
  exact NativeCreationStorageOpcodes.checkedStep_delegates machine after op arg success

private theorem decode_scan (code : ByteArray) (pc : Nat) (bounded : pc < UInt256.size)
    (inside : pc < code.size) (op : Operation .EVM) (parsed : EVM.parseInstr code[pc] = some op) :
    (EVM.decode code (UInt256.ofNat pc)).map Prod.fst = some op := by
  have exactPc : (UInt256.ofNat pc).toNat = pc := Nat.mod_eq_of_lt bounded
  change EVM.parseInstr (code.get pc inside) = some op at parsed
  simp only [EVM.decode, exactPc, ByteArray.get?, dif_pos inside,
    Bind.bind, Option.bind, parsed, Option.map]

/-- Both actual scanners agree at every natural index for word-addressable code. -/
theorem jump_scanners_aux (code : ByteArray) (bounded : code.size < UInt256.size)
    (fuel pc : Nat) (found : Array UInt256) :
    CreationCaller.jumpDestinationsAux code fuel pc found = EVM.D_J_aux code fuel pc found := by
  induction fuel generalizing pc found with
  | zero => rfl
  | succ fuel ih =>
    by_cases inside : pc < code.size
    · have wordBound : pc < UInt256.size := Nat.lt_trans inside bounded
      cases parsed : EVM.parseInstr code[pc] with
      | none =>
        have total := parse_instruction_total code[pc]
        rw [parsed] at total
        cases total
      | some op =>
        have decoded := decode_scan code pc wordBound inside op parsed
        cases actual : EVM.decode code (UInt256.ofNat pc) with
        | none => simp only [actual, Option.map_none] at decoded; cases decoded
        | some instruction =>
          rcases instruction with ⟨actualOp, arg⟩
          simp only [actual, Option.map_some, Option.some.injEq] at decoded
          subst actualOp
          simp only [CreationCaller.jumpDestinationsAux, Nat.not_le.mpr inside, if_false,
            actual, EVM.D_J_aux, dif_pos inside, parsed]
          exact ih _ _
    · have outside : pc ≥ code.size := Nat.le_of_not_gt inside
      simp only [CreationCaller.jumpDestinationsAux, outside, if_true, EVM.D_J_aux, dif_neg inside]

/-- The actual jump-destination arrays agree, including PUSH immediate skipping. -/
theorem jump_scanners (code : ByteArray) (bounded : code.size < UInt256.size) :
    CreationCaller.jumpDestinations code = EVM.D_J code (UInt256.ofNat 0) := by
  exact jump_scanners_aux code bounded code.size 0 #[]

end Compiler.Proofs.IRGeneration.NativePairedCallerFuel

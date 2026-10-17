import Compiler.Proofs.IRGeneration.PhysicalMemory
import Compiler.Proofs.IRGeneration.IRInterpreter
import Compiler.Proofs.IRGeneration.FunctionBody.Base

/-! Exact sequential event scratch writes. Every write installs the physical
byte carrier and all overlapping word observations. The lemmas do not replace
the declared-event bridge, which must also establish signature hashing and logs. -/
namespace Compiler.Proofs.IRGeneration

open Compiler Compiler.CompilationModel Compiler.Yul

def writePhysicalScratchSource : List (Nat × Nat) → Verity.ContractState → Verity.ContractState
  | [], world => world
  | (offset, value) :: rest, world =>
      writePhysicalScratchSource rest
        (world.writePhysicalMemoryValue (offset % Constants.evmModulus)
          (Verity.Core.Uint256.ofNat value))

def writePhysicalScratchIR : List (Nat × Nat) → IRState → IRState
  | [], state => state
  | (offset, value) :: rest, state =>
      writePhysicalScratchIR rest
        (state.writePhysicalMemoryValue (offset % Constants.evmModulus) value)

theorem writePhysicalScratch_matches (writes : List (Nat × Nat))
    (world : Verity.ContractState) (state : IRState)
    (hmatch : PhysicalMemoryMatches world state) :
    PhysicalMemoryMatches (writePhysicalScratchSource writes world)
      (writePhysicalScratchIR writes state) := by
  induction writes generalizing world state with
  | nil => exact hmatch
  | cons write rest ih =>
      rcases write with ⟨offset, value⟩
      exact ih _ _ (writePhysicalMemoryValue_matches world state
        (offset % Constants.evmModulus) value hmatch.1)

theorem writePhysicalScratchSource_storageWords
    (writes : List (Nat × Nat)) (world : Verity.ContractState) :
    (writePhysicalScratchSource writes world).storageWords = world.storageWords := by
  induction writes generalizing world with
  | nil => rfl
  | cons write rest ih =>
      rcases write with ⟨offset, value⟩
      rw [writePhysicalScratchSource, ih]
      rfl

theorem writePhysicalScratchSource_events
    (writes : List (Nat × Nat)) (world : Verity.ContractState) :
    (writePhysicalScratchSource writes world).events = world.events := by
  induction writes generalizing world with
  | nil => rfl
  | cons write rest ih =>
      rcases write with ⟨offset, value⟩
      rw [writePhysicalScratchSource, ih]
      rfl

theorem writePhysicalScratchIR_vars
    (writes : List (Nat × Nat)) (state : IRState) :
    (writePhysicalScratchIR writes state).vars = state.vars := by
  induction writes generalizing state with
  | nil => rfl
  | cons write rest ih =>
      rcases write with ⟨offset, value⟩
      rw [writePhysicalScratchIR, ih]
      rfl

/-- Erasing only memory proves a frame for every other source-world field,
including account-qualified storage, arrays, environment, calls and events. -/
theorem writePhysicalScratchSource_frame
    (writes : List (Nat × Nat)) (world : Verity.ContractState) :
    (writePhysicalScratchSource writes world).installPhysicalMemory DenoteMemory.Memory.empty =
      world.installPhysicalMemory DenoteMemory.Memory.empty := by
  induction writes generalizing world with
  | nil => rfl
  | cons write rest ih =>
      rcases write with ⟨offset, value⟩
      rw [writePhysicalScratchSource, ih]
      rfl

theorem writePhysicalScratchIR_frame
    (writes : List (Nat × Nat)) (state : IRState) :
    (writePhysicalScratchIR writes state).installPhysicalMemory DenoteMemory.Memory.empty =
      state.installPhysicalMemory DenoteMemory.Memory.empty := by
  induction writes generalizing state with
  | nil => rfl
  | cons write rest ih =>
      rcases write with ⟨offset, value⟩
      rw [writePhysicalScratchIR, ih]
      rfl

def physicalScratchStoreStmts (writes : List (Nat × Nat)) : List YulStmt :=
  writes.map fun (offset, value) =>
    .exprStmt (.call "mstore" [.lit offset, .hex value])

theorem execIRStmt_physical_mstore_of_eval
    (state : IRState) (offsetExpr valueExpr : YulExpr) (offset value extraFuel : Nat)
    (hoffset : evalIRExpr state offsetExpr = some offset)
    (hvalue : evalIRExpr state valueExpr = some value) :
    execIRStmt (extraFuel + 1) state
      (.exprStmt (.call "mstore" [offsetExpr, valueExpr])) =
      .continue (state.writePhysicalMemoryValue (offset % Constants.evmModulus) value) := by
  simp [execIRStmt, hoffset, hvalue, Constants.evmModulus,
    Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS]

theorem execIRStmts_physicalScratchStoreStmts
    (writes : List (Nat × Nat)) (state : IRState) (extraFuel : Nat) :
    execIRStmts (writes.length + extraFuel + 1) state (physicalScratchStoreStmts writes) =
      .continue (writePhysicalScratchIR writes state) := by
  induction writes generalizing state with
  | nil => simp [physicalScratchStoreStmts, execIRStmts, writePhysicalScratchIR]
  | cons write rest ih =>
      rcases write with ⟨offset, value⟩
      have hhead := execIRStmt_physical_mstore_of_eval state (.lit offset) (.hex value)
        offset value (rest.length + extraFuel) (by simp [evalIRExpr]) (by simp [evalIRExpr])
      have hfuel : ((offset, value) :: rest).length + extraFuel + 1 =
          (rest.length + extraFuel + 1) + 1 := by
        simp only [List.length_cons]
        omega
      rw [hfuel]
      simp only [physicalScratchStoreStmts, List.map_cons, execIRStmts, hhead,
        writePhysicalScratchIR]
      exact ih (state.writePhysicalMemoryValue (offset % Constants.evmModulus) value)

/-- Track the exact final state without reducing an entire fuelled execution. -/
def PhysicalStoresContinueTo (state : IRState) : List YulStmt → IRState → Prop
  | [], final => state = final
  | stmt :: rest, final =>
      ∃ next, (∀ extraFuel, execIRStmt (extraFuel + 1) state stmt = .continue next) ∧
        PhysicalStoresContinueTo next rest final

theorem execIRStmts_of_physicalStoresContinueTo
    {state final : IRState} {stmts : List YulStmt}
    (h : PhysicalStoresContinueTo state stmts final) (extraFuel : Nat) :
    execIRStmts (stmts.length + extraFuel + 1) state stmts = .continue final := by
  induction stmts generalizing state with
  | nil =>
      have hfinal : state = final := h
      subst hfinal
      simp [execIRStmts]
  | cons stmt rest ih =>
      obtain ⟨next, hstep, htail⟩ := h
      have hfuel : (stmt :: rest).length + extraFuel + 1 =
          (rest.length + extraFuel + 1) + 1 := by
        simp only [List.length_cons]
        omega
      rw [hfuel]
      simp only [execIRStmts, hstep (rest.length + extraFuel)]
      exact ih htail

theorem physicalStoresContinueTo_append
    {state middle final : IRState} {front back : List YulStmt}
    (hfront : PhysicalStoresContinueTo state front middle)
    (hback : PhysicalStoresContinueTo middle back final) :
    PhysicalStoresContinueTo state (front ++ back) final := by
  induction front generalizing state with
  | nil =>
      have heq : state = middle := hfront
      subst heq
      exact hback
  | cons stmt rest ih =>
      obtain ⟨next, hstep, htail⟩ := hfront
      exact ⟨next, hstep, ih htail⟩

def physicalSignatureWrites : List Nat → Nat → Nat → List (Nat × Nat)
  | [], _, _ => []
  | word :: rest, ptr, index =>
      (ptr + index * 32, word) :: physicalSignatureWrites rest ptr (index + 1)

def physicalSignatureStoreStmts : List Nat → Nat → List YulStmt
  | [], _ => []
  | word :: rest, index =>
      .exprStmt (.call "mstore" [
        .call "add" [.ident "__evt_ptr", .lit (index * 32)], .hex word]) ::
        physicalSignatureStoreStmts rest (index + 1)

theorem physicalSignatureStoreStmts_continue
    (words : List Nat) (state : IRState) (ptr index : Nat)
    (hptr : state.getVar "__evt_ptr" = some ptr) :
    PhysicalStoresContinueTo state (physicalSignatureStoreStmts words index)
      (writePhysicalScratchIR (physicalSignatureWrites words ptr index) state) := by
  induction words generalizing state index with
  | nil => rfl
  | cons word rest ih =>
      let next := state.writePhysicalMemoryValue
        ((ptr + index * 32) % Constants.evmModulus) word
      have hoff := FunctionBody.evalIRExpr_add_of_eval
        (state := state) (lhs := YulExpr.ident "__evt_ptr")
        (rhs := YulExpr.lit (index * 32)) (a := ptr) (b := index * 32)
        (by simpa [evalIRExpr] using hptr) (by simp [evalIRExpr])
      refine ⟨next, ?_, ?_⟩
      · intro extraFuel
        simpa [next] using execIRStmt_physical_mstore_of_eval state
          (.call "add" [.ident "__evt_ptr", .lit (index * 32)]) (.hex word)
          ((ptr + index * 32) % Constants.evmModulus) word extraFuel
          hoff (by simp [evalIRExpr])
      · exact ih next (index + 1)
          (by simpa [next, IRState.getVar, IRState.writePhysicalMemoryValue,
            IRState.installPhysicalMemory] using hptr)

theorem physicalSignatureWrites_matches
    (words : List Nat) (world : Verity.ContractState) (state : IRState) (ptr index : Nat)
    (hmatch : PhysicalMemoryMatches world state) :
    PhysicalMemoryMatches
      (writePhysicalScratchSource (physicalSignatureWrites words ptr index) world)
      (writePhysicalScratchIR (physicalSignatureWrites words ptr index) state) :=
  writePhysicalScratch_matches _ world state hmatch

/-- Connect the canonical source event writer to the same exact store sequence. -/
theorem sourceEventSignaturePhysical_eq_scratch
    (words : List Nat) (ptr index : Nat) (world : Verity.ContractState) :
    SourceSemantics.writeEventSignaturePhysicalFrom words ptr index world =
      writePhysicalScratchSource (physicalSignatureWrites words ptr index) world := by
  induction words generalizing index world with
  | nil => rfl
  | cons word rest ih =>
      simp only [SourceSemantics.writeEventSignaturePhysicalFrom,
        physicalSignatureWrites, writePhysicalScratchSource, ih]

def physicalUnindexedWrites :
    List EventParam → List Nat → Nat → Nat → Option (List (Nat × Nat))
  | [], [], _, _ => some []
  | param :: params, value :: values, ptr, index =>
      if param.kind == EventParamKind.unindexed then
        (physicalUnindexedWrites params values ptr (index + 1)).map fun rest =>
          (ptr + index * 32, SourceSemantics.normalizeEventValue param.ty value) :: rest
      else
        physicalUnindexedWrites params values ptr index
  | _, _, _, _ => none

theorem sourceUnindexedEventPhysical_eq_scratch
    (params : List EventParam) (values : List Nat) (ptr index : Nat)
    (world : Verity.ContractState) :
    SourceSemantics.writeUnindexedEventPhysicalFrom params values ptr index world =
      (physicalUnindexedWrites params values ptr index).map
        (fun writes => writePhysicalScratchSource writes world) := by
  induction params generalizing values index world with
  | nil => cases values <;> rfl
  | cons param params ih =>
      cases values with
      | nil => rfl
      | cons value values =>
          by_cases hkind : param.kind == EventParamKind.unindexed
          · simp only [SourceSemantics.writeUnindexedEventPhysicalFrom,
              physicalUnindexedWrites, if_pos hkind]
            rw [ih]
            cases physicalUnindexedWrites params values ptr (index + 1) <;> rfl
          · simp only [SourceSemantics.writeUnindexedEventPhysicalFrom,
              physicalUnindexedWrites, if_neg hkind]
            exact ih values index world

theorem sourceEventSignaturePhysical_frame
    (words : List Nat) (ptr index : Nat) (world : Verity.ContractState) :
    (SourceSemantics.writeEventSignaturePhysicalFrom words ptr index world).installPhysicalMemory
        DenoteMemory.Memory.empty = world.installPhysicalMemory DenoteMemory.Memory.empty := by
  rw [sourceEventSignaturePhysical_eq_scratch]
  exact writePhysicalScratchSource_frame _ world

theorem sourceUnindexedEventPhysical_frame
    (params : List EventParam) (values : List Nat) (ptr index : Nat)
    (world next : Verity.ContractState)
    (hwrite : SourceSemantics.writeUnindexedEventPhysicalFrom params values ptr index world =
      some next) :
    next.installPhysicalMemory DenoteMemory.Memory.empty =
      world.installPhysicalMemory DenoteMemory.Memory.empty := by
  rw [sourceUnindexedEventPhysical_eq_scratch] at hwrite
  cases h : physicalUnindexedWrites params values ptr index with
  | none => simp [h] at hwrite
  | some writes =>
      simp only [h, Option.map_some, Option.some.injEq] at hwrite
      rw [← hwrite]
      exact writePhysicalScratchSource_frame writes world

theorem eventScratchWorldAfterEmit_frame
    (events : List EventDef) (eventName : String) (values : List Nat)
    (world next : Verity.ContractState)
    (hscratch : SourceSemantics.eventScratchWorldAfterEmit? events eventName values world =
      some next) :
    next.installPhysicalMemory DenoteMemory.Memory.empty =
      world.installPhysicalMemory DenoteMemory.Memory.empty := by
  cases hfind : events.find? (·.name == eventName) with
  | none =>
      simp [SourceSemantics.eventScratchWorldAfterEmit?, hfind] at hscratch
      rw [← hscratch]
  | some eventDef =>
      by_cases hscalar : eventDefScalarProofSupported eventDef = true
      · simp only [SourceSemantics.eventScratchWorldAfterEmit?, hfind, hscalar,
          ↓reduceIte] at hscratch
        exact (sourceUnindexedEventPhysical_frame _ _ _ _ _ next hscratch).trans
          (sourceEventSignaturePhysical_frame _ _ _ world)
      · simp [SourceSemantics.eventScratchWorldAfterEmit?, hfind, hscalar] at hscratch
        rw [← hscratch]

theorem physicalScratchKey_injective
    {ptr i j : Nat} (hi : i < eventScratchSizeLimit) (hj : j < eventScratchSizeLimit)
    (hkey : (ptr + i * 32) % Constants.evmModulus =
      (ptr + j * 32) % Constants.evmModulus) : i = j := by
  have hptr : ptr + i * 32 ≡ ptr + j * 32 [MOD Constants.evmModulus] := hkey
  have hmul : i * 32 ≡ j * 32 [MOD Constants.evmModulus] :=
    Nat.ModEq.add_left_cancel' ptr hptr
  have hmod : i ≡ j [MOD Constants.evmModulus / Nat.gcd Constants.evmModulus 32] :=
    Nat.ModEq.cancel_right_div_gcd (by norm_num [Constants.evmModulus]) hmul
  have hdiv : Constants.evmModulus / Nat.gcd Constants.evmModulus 32 = 2 ^ 251 := by decide
  have hi' : i < Constants.evmModulus / Nat.gcd Constants.evmModulus 32 := by
    rw [hdiv]
    exact lt_of_lt_of_le hi (by norm_num [eventScratchSizeLimit])
  have hj' : j < Constants.evmModulus / Nat.gcd Constants.evmModulus 32 := by
    rw [hdiv]
    exact lt_of_lt_of_le hj (by norm_num [eventScratchSizeLimit])
  exact Nat.ModEq.eq_of_lt_of_lt hmod hi' hj'

/-- Even when word offsets wrap, distinct scratch cells share the same residue
modulo 32, so their physical byte intervals cannot overlap. -/
theorem physicalScratchKey_disjoint
    {ptr i j : Nat} (hi : i < eventScratchSizeLimit) (hj : j < eventScratchSizeLimit)
    (hne : i ≠ j) :
    (ptr + i * 32) % Constants.evmModulus + 32 ≤ (ptr + j * 32) % Constants.evmModulus ∨
      (ptr + j * 32) % Constants.evmModulus + 32 ≤ (ptr + i * 32) % Constants.evmModulus := by
  have hresidue (index : Nat) :
      ((ptr + index * 32) % Constants.evmModulus) % 32 = ptr % 32 := by
    rw [Nat.mod_mod_of_dvd _ (by norm_num [Constants.evmModulus] : 32 ∣ Constants.evmModulus)]
    simp [Nat.add_mod]
  have hdistinct : (ptr + i * 32) % Constants.evmModulus ≠
      (ptr + j * 32) % Constants.evmModulus :=
    fun heq => hne (physicalScratchKey_injective hi hj heq)
  have hri := hresidue i
  have hrj := hresidue j
  omega

theorem sourceEventSignaturePhysical_preserve_before
    (words : List Nat) (ptr index baseIndex : Nat) (world : Verity.ContractState)
    (hlimit : index + words.length ≤ eventScratchSizeLimit)
    (hbefore : baseIndex < index) (hbase : baseIndex < eventScratchSizeLimit) :
    (SourceSemantics.writeEventSignaturePhysicalFrom words ptr index world).byteMemory.readWord
        ((ptr + baseIndex * 32) % Constants.evmModulus) =
      world.byteMemory.readWord ((ptr + baseIndex * 32) % Constants.evmModulus) := by
  induction words generalizing index world with
  | nil => rfl
  | cons word rest ih =>
      have hindex : index < eventScratchSizeLimit := by simp only [List.length_cons] at hlimit; omega
      rw [SourceSemantics.writeEventSignaturePhysicalFrom,
        ih (index + 1) _ (by simp only [List.length_cons] at hlimit; omega) (by omega)]
      change (world.byteMemory.writeWord ((ptr + index * 32) % Constants.evmModulus)
        (DenoteMemory.valueWord (Verity.Core.Uint256.ofNat word))).readWord _ = _
      exact DenoteMemory.Memory.readWord_writeWord_outside _ _ _ _
        (physicalScratchKey_disjoint hbase hindex (by omega))

theorem sourceEventSignaturePhysical_read_getElem
    (words : List Nat) (ptr index : Nat) (world : Verity.ContractState)
    (hlimit : index + words.length ≤ eventScratchSizeLimit)
    (i : Nat) (hi : i < words.length) :
    (SourceSemantics.writeEventSignaturePhysicalFrom words ptr index world).byteMemory.readWord
        ((ptr + (index + i) * 32) % Constants.evmModulus) =
      DenoteMemory.valueWord (Verity.Core.Uint256.ofNat words[i]) := by
  induction words generalizing index world i with
  | nil => simp at hi
  | cons word rest ih =>
      cases i with
      | zero =>
          simp only [Nat.add_zero, List.getElem_cons_zero]
          rw [SourceSemantics.writeEventSignaturePhysicalFrom,
            sourceEventSignaturePhysical_preserve_before rest ptr (index + 1) index _
              (by simp only [List.length_cons] at hlimit; omega) (by omega)
              (by simp only [List.length_cons] at hlimit; omega)]
          exact DenoteMemory.Memory.readWord_writeWord_at _ _ _
      | succ i =>
          have htail := ih (index + 1)
            (world.writePhysicalMemoryValue ((ptr + index * 32) % Constants.evmModulus)
              (Verity.Core.Uint256.ofNat word))
            (by simp only [List.length_cons] at hlimit; omega) i
            (by simp only [List.length_cons] at hi; omega)
          simpa only [SourceSemantics.writeEventSignaturePhysicalFrom,
            List.getElem_cons_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail

theorem sourceEventSignaturePhysical_coherent
    (words : List Nat) (ptr index : Nat) (world : Verity.ContractState)
    (hcoherent : Compiler.CompilationModel.PhysicalMemory.Coherent world) :
    Compiler.CompilationModel.PhysicalMemory.Coherent
      (SourceSemantics.writeEventSignaturePhysicalFrom words ptr index world) := by
  induction words generalizing index world with
  | nil => exact hcoherent
  | cons word rest ih =>
      exact ih (index + 1) _ (PhysicalMemory.writePhysicalMemoryValue_coherent _ _ _)

theorem sourceEventSignaturePhysical_coherent_of_nonempty
    (words : List Nat) (ptr index : Nat) (world : Verity.ContractState)
    (hne : words ≠ []) :
    Compiler.CompilationModel.PhysicalMemory.Coherent
      (SourceSemantics.writeEventSignaturePhysicalFrom words ptr index world) := by
  cases words with
  | nil => exact False.elim (hne rfl)
  | cons word rest =>
      exact sourceEventSignaturePhysical_coherent rest ptr (index + 1) _
        (PhysicalMemory.writePhysicalMemoryValue_coherent _ _ _)

theorem sourceEventSignaturePhysical_memory_getElem
    (words : List Nat) (ptr index : Nat) (world : Verity.ContractState)
    (hlimit : index + words.length ≤ eventScratchSizeLimit)
    (i : Nat) (hi : i < words.length) :
    (SourceSemantics.writeEventSignaturePhysicalFrom words ptr index world).memory
        ((ptr + (index + i) * 32) % Constants.evmModulus) =
      Verity.Core.Uint256.ofNat words[i] := by
  have hne : words ≠ [] := by intro h; simp [h] at hi
  rw [sourceEventSignaturePhysical_coherent_of_nonempty words ptr index world hne,
    sourceEventSignaturePhysical_read_getElem words ptr index world hlimit i hi]
  exact DenoteMemory.wordValue_valueWord _

end Compiler.Proofs.IRGeneration

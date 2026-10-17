import Compiler.Proofs.IRGeneration.IRInterpreter
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanBridgeLemmas
import Verity.Core.Model.ECM
import Compiler.Proofs.IRGeneration.NonReentrantGuardIR
import Compiler.Proofs.IRGeneration.PhysicalErrorStringBytes
import Compiler.Proofs.IRGeneration.PhysicalErrorStringWords

/-!
# Physical Error(string) payload execution

Literal and pointer-relative mstore blocks update the real byte carrier and
its overlapping word view. The complete payload theorem retains all three
header assertions and adds exact captured bytes under a nonwrapping extent.
The pure applyWrites facts below describe the historical word-map algorithm;
they are not a model of physical mstore and are not used to certify execution.
-/
namespace Compiler.Proofs.IRGeneration

open Compiler.Yul
open Compiler.ECM

/-- Apply a write list left to right (later writes shadow earlier ones). -/
def applyWrites (mem : Nat → Nat) : List (Nat × Nat) → Nat → Nat
  | [] => mem
  | (o, w) :: rest =>
      applyWrites (fun x => if x = o then w else mem x) rest

/-- Unwritten keys read through the write list unchanged. -/
theorem applyWrites_not_written (k : Nat) :
    ∀ (writes : List (Nat × Nat)) (mem : Nat → Nat),
      (∀ ow ∈ writes, ow.1 ≠ k) →
      applyWrites mem writes k = mem k
  | [], _, _ => rfl
  | (o, w) :: rest, mem, hall => by
      have hkey : o ≠ k := hall (o, w) (by simp)
      rw [show applyWrites mem ((o, w) :: rest) k =
        applyWrites (fun x => if x = o then w else mem x) rest k from rfl,
        applyWrites_not_written k rest _ (fun ow hw => hall ow (by simp [hw])),
        if_neg (fun h => hkey h.symm)]

/-- Syntactic characterization: each statement is a literal `mstore` of the
paired write (value given as `lit` or `hex` — both evaluate to the word). -/
inductive MstoreWrites : List YulStmt → List (Nat × Nat) → Prop
  | nil : MstoreWrites [] []
  | consLit {stmts writes} (o w : Nat) :
      MstoreWrites stmts writes →
      MstoreWrites (.exprStmt (.call "mstore" [.lit o, .lit w]) :: stmts)
        ((o, w) :: writes)
  | consHex {stmts writes} (o w : Nat) :
      MstoreWrites stmts writes →
      MstoreWrites (.exprStmt (.call "mstore" [.lit o, .hex w]) :: stmts)
        ((o, w) :: writes)

theorem MstoreWrites.append {xs ys : List YulStmt} {ws vs : List (Nat × Nat)}
    (hx : MstoreWrites xs ws) (hy : MstoreWrites ys vs) :
    MstoreWrites (xs ++ ys) (ws ++ vs) := by
  induction hx with
  | nil => simpa using hy
  | consLit o w _ ih => exact .consLit o w ih
  | consHex o w _ ih => exact .consHex o w ih

theorem MstoreWrites.length_eq {stmts : List YulStmt} {writes : List (Nat × Nat)}
    (h : MstoreWrites stmts writes) : stmts.length = writes.length := by
  induction h with
  | nil => rfl
  | consLit _ _ _ ih => simpa using ih
  | consHex _ _ _ ih => simpa using ih

/-- A block of literal `mstore`s executes to `continue` with exactly its
writes applied. -/
theorem execIRStmts_mstoreWrites :
    ∀ {stmts : List YulStmt} {writes : List (Nat × Nat)},
      MstoreWrites stmts writes → ∀ (fuel : Nat) (state : IRState),
        execIRStmts (stmts.length + fuel + 1) state stmts =
          .continue (PhysicalRevertWrites.applyStores state writes)
  | _, _, .nil, fuel, state => by
      simp [execIRStmts, PhysicalRevertWrites.applyStores]
  | _, _, @MstoreWrites.consLit tail wtail o w htail, fuel, state => by
      rw [show (YulStmt.exprStmt (.call "mstore" [.lit o, .lit w]) :: tail).length +
        fuel + 1 = (tail.length + fuel + 1) + 1 by simp only [List.length_cons]; omega]
      simp only [execIRStmts, execIRStmt, evalIRExpr, PhysicalRevertWrites.applyStores]
      exact execIRStmts_mstoreWrites htail fuel _
  | _, _, @MstoreWrites.consHex tail wtail o w htail, fuel, state => by
      rw [show (YulStmt.exprStmt (.call "mstore" [.lit o, .hex w]) :: tail).length +
        fuel + 1 = (tail.length + fuel + 1) + 1 by simp only [List.length_cons]; omega]
      simp only [execIRStmts, execIRStmt, evalIRExpr, PhysicalRevertWrites.applyStores]
      exact execIRStmts_mstoreWrites htail fuel _

/-- The write list `revertWithMessage` performs: three header words then one
word per 32-byte chunk. -/
def errorStringWrites (message : String) : List (Nat × Nat) :=
  (0, Compiler.Constants.errorStringSelectorWord) :: (4, 32) ::
    (36, (bytesFromString message).length) ::
    ((chunkBytes32 (bytesFromString message)).zipIdx.map fun ci =>
      (68 + ci.2 * 32, wordFromBytes ci.1))

/-- The emitted statements: mixed lit/hex header mstores, the chunk mstores,
then the final `revert`. -/
def errorStringStmts (message : String) : List YulStmt :=
  YulStmt.exprStmt (.call "mstore"
      [.lit 0, .hex Compiler.Constants.errorStringSelectorWord]) ::
    YulStmt.exprStmt (.call "mstore" [.lit 4, .lit 32]) ::
    YulStmt.exprStmt (.call "mstore"
      [.lit 36, .lit (bytesFromString message).length]) ::
    ((chunkBytes32 (bytesFromString message)).zipIdx.map fun ci =>
      YulStmt.exprStmt (.call "mstore"
        [.lit (68 + ci.2 * 32), .hex (wordFromBytes ci.1)]))

theorem revertWithMessage_shape (message : String) :
    revertWithMessage message =
      errorStringStmts message ++
        [YulStmt.exprStmt (.call "revert" [.lit 0,
          .lit (68 + ((bytesFromString message).length + 31) / 32 * 32)])] := by
  simp [revertWithMessage, errorStringStmts]

/-- Any mapped write list is an `MstoreWrites` instance (hex form). -/
theorem MstoreWrites.of_map :
    ∀ (writes : List (Nat × Nat)),
      MstoreWrites
        (writes.map fun ow =>
          YulStmt.exprStmt (.call "mstore" [.lit ow.1, .hex ow.2]))
        writes
  | [] => .nil
  | (o, w) :: rest => .consHex o w (MstoreWrites.of_map rest)

/-- The chunk statements are the mstore block of the chunk writes. -/
theorem chunkStmts_mstoreWrites (message : String) :
    MstoreWrites
      ((chunkBytes32 (bytesFromString message)).zipIdx.map fun ci =>
        YulStmt.exprStmt (.call "mstore"
          [.lit (68 + ci.2 * 32), .hex (wordFromBytes ci.1)]))
      ((chunkBytes32 (bytesFromString message)).zipIdx.map fun ci =>
        (68 + ci.2 * 32, wordFromBytes ci.1)) := by
  rw [show ((chunkBytes32 (bytesFromString message)).zipIdx.map fun ci =>
      YulStmt.exprStmt (.call "mstore"
        [.lit (68 + ci.2 * 32), .hex (wordFromBytes ci.1)])) =
    (((chunkBytes32 (bytesFromString message)).zipIdx.map fun ci =>
      (68 + ci.2 * 32, wordFromBytes ci.1)).map fun ow =>
        YulStmt.exprStmt (.call "mstore" [.lit ow.1, .hex ow.2])) from by
    simp [List.map_map, Function.comp]]
  exact MstoreWrites.of_map _

/-- The statement block is the mstore block of `errorStringWrites`. -/
theorem errorStringStmts_mstoreWrites (message : String) :
    MstoreWrites (errorStringStmts message) (errorStringWrites message) :=
  MstoreWrites.consHex 0 Compiler.Constants.errorStringSelectorWord
    (MstoreWrites.consLit 4 32
      (MstoreWrites.consLit 36 (bytesFromString message).length
        (chunkStmts_mstoreWrites message)))

/-- Data-chunk keys never shadow a header key below 68. -/
theorem errorStringWrites_tail_keys (message : String) (k : Nat) (hk : k < 68) :
    ∀ ow ∈ (chunkBytes32 (bytesFromString message)).zipIdx.map
        (fun ci => (68 + ci.2 * 32, wordFromBytes ci.1)),
      ow.1 ≠ k := by
  intro ow how
  obtain ⟨ci, _, rfl⟩ := List.mem_map.mp how
  omega

theorem errorStringWrites_mem0 (message : String) (mem : Nat → Nat) :
    applyWrites mem (errorStringWrites message) 0 =
      Compiler.Constants.errorStringSelectorWord := by
  rw [show applyWrites mem (errorStringWrites message) 0 =
    applyWrites (fun x => if x = 0 then
      Compiler.Constants.errorStringSelectorWord else mem x)
      ((4, 32) :: (36, (bytesFromString message).length) ::
        ((chunkBytes32 (bytesFromString message)).zipIdx.map fun ci =>
          (68 + ci.2 * 32, wordFromBytes ci.1))) 0 from rfl,
    applyWrites_not_written 0 _ _ ?_]
  · simp
  · intro ow how
    simp at how
    rcases how with h | h | h
    · simp [h]
    · simp [h]
    · exact errorStringWrites_tail_keys message 0 (by omega) ow
        (List.mem_map.mpr (by simpa using h))

theorem errorStringWrites_mem4 (message : String) (mem : Nat → Nat) :
    applyWrites mem (errorStringWrites message) 4 = 32 := by
  rw [show applyWrites mem (errorStringWrites message) 4 =
    applyWrites (fun x => if x = 4 then 32 else
      if x = 0 then Compiler.Constants.errorStringSelectorWord else mem x)
      ((36, (bytesFromString message).length) ::
        ((chunkBytes32 (bytesFromString message)).zipIdx.map fun ci =>
          (68 + ci.2 * 32, wordFromBytes ci.1))) 4 from by
      simp [applyWrites, errorStringWrites],
    applyWrites_not_written 4 _ _ ?_]
  · simp
  · intro ow how
    simp at how
    rcases how with h | h
    · simp [h]
    · exact errorStringWrites_tail_keys message 4 (by omega) ow
        (List.mem_map.mpr (by simpa using h))

theorem errorStringWrites_mem36 (message : String) (mem : Nat → Nat) :
    applyWrites mem (errorStringWrites message) 36 =
      (bytesFromString message).length := by
  rw [show applyWrites mem (errorStringWrites message) 36 =
    applyWrites (fun x => if x = 36 then (bytesFromString message).length
      else if x = 4 then 32 else
      if x = 0 then Compiler.Constants.errorStringSelectorWord else mem x)
      ((chunkBytes32 (bytesFromString message)).zipIdx.map fun ci =>
        (68 + ci.2 * 32, wordFromBytes ci.1)) 36 from by
      simp [applyWrites, errorStringWrites],
    applyWrites_not_written 36 _ _
      (fun ow how => errorStringWrites_tail_keys message 36 (by omega) ow how)]
  simp

theorem MstoreWrites.storeTrace {stmts : List YulStmt} {writes : List (Nat × Nat)}
    (trace : MstoreWrites stmts writes) : PhysicalRevertWrites.StoreTrace stmts writes := by
  induction trace with
  | nil => exact .nil
  | consLit offset value trace ih => exact .consLit offset value ih
  | consHex offset value trace ih => exact .consHex offset value ih

/-- Actual execution retains the complete physical state and captures the
precise REVERT slice, including overlapping header stores. -/
theorem execIRStmts_revertWithMessage_physical (message : String) (fuel : Nat)
    (state : IRState) :
    execIRStmts ((errorStringStmts message).length + fuel + 2) state
      (revertWithMessage message) =
      .revert ((PhysicalRevertWrites.applyStores state (errorStringWrites message)).captureRevert
        0 (68 + ((bytesFromString message).length + 31) / 32 * 32)) := by
  rw [revertWithMessage_shape, (errorStringStmts_mstoreWrites message).length_eq]
  exact PhysicalRevertWrites.exec_trace_revert
    (errorStringStmts_mstoreWrites message).storeTrace state fuel 0 _

private theorem ecm_chunker_eq (bytes : List UInt8) :
    Compiler.ECM.chunkBytes32 bytes = Compiler.CompilationModel.chunkBytes32 bytes := by
  rw [Compiler.ECM.chunkBytes32, Compiler.CompilationModel.chunkBytes32]
  by_cases empty : bytes.isEmpty = true
  · rw [if_pos empty, if_pos empty]
  · rw [if_neg empty, if_neg empty, ecm_chunker_eq (bytes.drop 32)]
termination_by bytes.length
decreasing_by
  simp_wf
  cases bytes with
  | nil => simp at empty
  | cons head tail => simp

private theorem errorStringWrites_physical (message : String) :
    errorStringWrites message = PhysicalErrorStringExecution.writes message := by
  simp only [errorStringWrites, PhysicalErrorStringExecution.writes,
    PhysicalErrorStringExecution.dataWrites, Compiler.ECM.bytesFromString,
    Compiler.CompilationModel.bytesFromString, ecm_chunker_eq]
  rfl

/-- The original header assertions are retained on actual physical memory;
nonwrapping payload extent bounds the unbounded logical length as well. -/
theorem execIRStmts_revertWithMessage (message : String) (fuel : Nat)
    (state : IRState)
    (extent : 68 + 32 * (Compiler.CompilationModel.chunkBytes32
      (Compiler.CompilationModel.bytesFromString message)).length ≤ Verity.Core.Uint256.modulus) :
    ∃ finalState,
      execIRStmts ((errorStringStmts message).length + fuel + 2) state
          (revertWithMessage message) = .revert finalState ∧
      finalState.memory 0 = Compiler.Constants.errorStringSelectorWord ∧
      finalState.memory 4 = 32 ∧
      finalState.memory 36 = (bytesFromString message).length ∧
      finalState.revertBytes = some (Compiler.CompilationModel.Denote.errorStringBytes message) := by
  refine ⟨_, execIRStmts_revertWithMessage_physical message fuel state, ?_, ?_, ?_, ?_⟩
  · change (PhysicalRevertWrites.applyStores state (errorStringWrites message)).memory 0 = _
    rw [errorStringWrites_physical]
    exact PhysicalErrorStringWords.selector_word state message extent
  · change (PhysicalRevertWrites.applyStores state (errorStringWrites message)).memory 4 = _
    rw [errorStringWrites_physical]
    exact PhysicalErrorStringWords.offset_word state message extent
  · change (PhysicalRevertWrites.applyStores state (errorStringWrites message)).memory 36 = _
    rw [errorStringWrites_physical]
    exact PhysicalErrorStringWords.length_word state message extent
  · rw [errorStringWrites_physical]
    exact PhysicalErrorStringBytes.observed_payload state message extent

/-! ## Pointer-based stores

Event payloads and ABI tails write through a base pointer
(`mstore(add(ptr, off), value)`).  The lemmas below extend the block
machinery to that shape: a pointer-offset store with a bound base variable
executes to exactly the offset write, and blocks of them apply their write
lists relative to the pointer. -/

/-- One pointer-offset store executes to the offset write. -/
theorem execIRStmt_mstore_ptr (fuel : Nat) (state : IRState)
    (ptrName : String) (p off w : Nat)
    (hptr : state.getVar ptrName = some p) :
    execIRStmt (fuel + 1) state
        (.exprStmt (.call "mstore"
          [.call "add" [.ident ptrName, .lit off], .hex w])) =
      .continue (state.writePhysicalMemoryValue
        ((p + off) % Compiler.Constants.evmModulus) w) := by
  simp [execIRStmt, evalIRExpr, evalIRCall, evalIRExprs, hptr,
    YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
    Verity.Core.Uint256.val_ofNat, Compiler.Constants.evmModulus,
    Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS, Nat.mod_mod]

/-- A block of pointer-offset stores applies its writes at the pointer. -/
theorem execIRStmts_mstore_ptr_block (ptrName : String) (p : Nat) :
    ∀ (writes : List (Nat × Nat)) (fuel : Nat) (state : IRState),
      state.getVar ptrName = some p →
      execIRStmts (writes.length + fuel + 1) state
          (writes.map fun ow =>
            YulStmt.exprStmt (.call "mstore"
              [.call "add" [.ident ptrName, .lit ow.1], .hex ow.2])) =
        .continue (PhysicalRevertWrites.applyStores state
          (writes.map fun ow =>
            ((p + ow.1) % Compiler.Constants.evmModulus, ow.2)))
  | [], _, state, _ => by simp [execIRStmts, PhysicalRevertWrites.applyStores]
  | (o, w) :: rest, fuel, state, hptr => by
      rw [show ((o, w) :: rest).length + fuel + 1 =
        (rest.length + fuel + 1) + 1 from by simp [List.length]; omega]
      show (match execIRStmt (rest.length + fuel + 1) state
          (.exprStmt (.call "mstore"
            [.call "add" [.ident ptrName, .lit o], .hex w])) with
        | .continue s₁ => execIRStmts (rest.length + fuel + 1) s₁
            (rest.map fun (ow : Nat × Nat) =>
              YulStmt.exprStmt (.call "mstore"
                [.call "add" [.ident ptrName, .lit ow.1], .hex ow.2]))
        | .return v s => .return v s
        | .stop s => .stop s
        | .exceptional s => .exceptional s
        | .interpretationError message => .interpretationError message
        | .revert s => .revert s) = _
      rw [execIRStmt_mstore_ptr (rest.length + fuel) state ptrName p o w hptr]
      have hptr' : (state.writePhysicalMemoryValue
          ((p + o) % Compiler.Constants.evmModulus) w).getVar ptrName = some p := hptr
      change execIRStmts (rest.length + fuel + 1) _ _ = _
      simpa only [List.map_cons, PhysicalRevertWrites.applyStores,
        Verity.Core.Uint256.val_ofNat, Compiler.Constants.evmModulus,
        Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS, Nat.mod_mod] using
        execIRStmts_mstore_ptr_block ptrName p rest fuel _ hptr'

/-- The log observable: a log builtin whose arguments evaluate appends
exactly the encoded event and changes nothing else. -/
theorem execIRStmt_log (fuel : Nat) (state next : IRState) (func : String)
    (args : List YulExpr) (argVals : List Nat)
    (hlog : Compiler.Proofs.YulGeneration.isYulLogName func = true)
    (hargs : evalIRExprs state args = some argVals)
    (happly : applyYulLogCall? state func argVals = some next) :
    execIRStmt (fuel + 1) state (.exprStmt (.call func args)) =
      .continue next := by
  have hcases : func = "log0" ∨ func = "log1" ∨ func = "log2" ∨
      func = "log3" ∨ func = "log4" := by
    simp [Compiler.Proofs.YulGeneration.isYulLogName] at hlog
    tauto
  rcases hcases with rfl | rfl | rfl | rfl | rfl <;>
    simp [execIRStmt, hargs, happly,
      Compiler.Proofs.YulGeneration.isYulLogName]

end Compiler.Proofs.IRGeneration

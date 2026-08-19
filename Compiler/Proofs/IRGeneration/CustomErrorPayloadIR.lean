import Compiler.Proofs.IRGeneration.ErrorStringPayloadIR
import Compiler.CompilationModel.AbiEncoding

/-!
# Proof-side observable for revert payload blocks

Companion to `ErrorStringPayloadIR` (the `Error(string)` observable) and the
`Panic(uint256)` observable.

The generic-induction step lemmas `compiledStmtStep_requireError` and
`compiledStmtStep_revertError` are already proved, but both are stated modulo
the hypothesis

    hrevertExec : ∀ state fuel, ∃ next, execIRStmts fuel state revertStmts = .revert next

which nothing in the tree discharged, leaving those two lemmas without
consumers. This module supplies the machinery for that hypothesis: it
characterizes the statement shapes a revert payload is built from
(`NonEscaping` — statements that can only continue or revert), proves that a
list reaching a `revert` call through such statements deterministically reverts
(`RevertsAlways` / `execIRStmts_revertsAlways`), and lifts that through the
`block` wrapper the typed-error payload uses.

Fuel exhaustion is itself modelled as `.revert` by `execIRStmts`, so these
statements hold at every fuel value, including `0`.
-/

namespace Compiler.Proofs.IRGeneration

open Compiler.Yul
open Compiler.ECM

/-! ## Execution-unfolding helpers -/

theorem execIRStmts_cons_continue'
    (fuel : Nat) (state next : IRState) (stmt : YulStmt) (tail : List YulStmt)
    (hstmt : execIRStmt fuel state stmt = .continue next) :
    execIRStmts (fuel + 1) state (stmt :: tail) = execIRStmts fuel next tail := by
  simp [execIRStmts, hstmt]

theorem execIRStmts_cons_revert
    (fuel : Nat) (state next : IRState) (stmt : YulStmt) (tail : List YulStmt)
    (hstmt : execIRStmt fuel state stmt = .revert next) :
    execIRStmts (fuel + 1) state (stmt :: tail) = .revert next := by
  simp [execIRStmts, hstmt]

theorem execIRStmts_zero_cons (state : IRState) (stmt : YulStmt)
    (tail : List YulStmt) :
    execIRStmts 0 state (stmt :: tail) = .revert state := by
  simp [execIRStmts]

/-- A `revert` expression statement reverts at every fuel value, including the
out-of-fuel case. -/
theorem execIRStmt_revertCall (fuel : Nat) (state : IRState)
    (offset size : YulExpr) :
    execIRStmt fuel state (.exprStmt (.call "revert" [offset, size])) =
      .revert state := by
  cases fuel <;> simp [execIRStmt]

theorem execIRStmt_block' (fuel : Nat) (state : IRState) (body : List YulStmt) :
    execIRStmt (fuel + 1) state (.block body) = execIRStmts fuel state body := by
  simp [execIRStmt]

/-! ## Non-escaping statements -/

/-- A statement whose execution can only `continue` or `revert`: it never
produces a `return`/`stop` observable. Every statement a revert payload is
built from (free-pointer load, `mstore`s, `let`/`assign` temporaries) has this
shape, which is what makes a trailing `revert` unavoidable. -/
def NonEscaping (stmt : YulStmt) : Prop :=
  ∀ (fuel : Nat) (state : IRState),
    (∃ next, execIRStmt fuel state stmt = .continue next) ∨
    (∃ next, execIRStmt fuel state stmt = .revert next)

theorem NonEscaping.let_ (name : String) (value : YulExpr) :
    NonEscaping (.let_ name value) := by
  intro fuel state
  cases fuel with
  | zero => exact Or.inr ⟨state, by simp [execIRStmt]⟩
  | succ f =>
      cases hval : evalIRExpr state value with
      | none => exact Or.inr ⟨state, by simp [execIRStmt, hval]⟩
      | some v => exact Or.inl ⟨state.setVar name v, by simp [execIRStmt, hval]⟩

theorem NonEscaping.assign (name : String) (value : YulExpr) :
    NonEscaping (.assign name value) := by
  intro fuel state
  cases fuel with
  | zero => exact Or.inr ⟨state, by simp [execIRStmt]⟩
  | succ f =>
      cases hval : evalIRExpr state value with
      | none => exact Or.inr ⟨state, by simp [execIRStmt, hval]⟩
      | some v => exact Or.inl ⟨state.setVar name v, by simp [execIRStmt, hval]⟩

theorem NonEscaping.mstore (offset value : YulExpr) :
    NonEscaping (.exprStmt (.call "mstore" [offset, value])) := by
  intro fuel state
  cases fuel with
  | zero => exact Or.inr ⟨state, by simp [execIRStmt]⟩
  | succ f =>
      cases hoff : evalIRExpr state offset with
      | none => exact Or.inr ⟨state, by simp [execIRStmt, hoff]⟩
      | some o =>
          cases hval : evalIRExpr state value with
          | none => exact Or.inr ⟨state, by simp [execIRStmt, hoff, hval]⟩
          | some v =>
              exact Or.inl ⟨{ state with
                memory := fun x => if x = o then v else state.memory x },
                by simp [execIRStmt, hoff, hval]⟩

/-- The list-level counterpart of `NonEscaping`: running the whole list can only
continue or revert. -/
def NonEscapingList (stmts : List YulStmt) : Prop :=
  ∀ (fuel : Nat) (state : IRState),
    (∃ next, execIRStmts fuel state stmts = .continue next) ∨
    (∃ next, execIRStmts fuel state stmts = .revert next)

theorem nonEscapingList_nil : NonEscapingList [] := by
  intro _ state
  exact Or.inl ⟨state, by simp [execIRStmts]⟩

theorem nonEscapingList_cons {stmt : YulStmt} {rest : List YulStmt}
    (hstmt : NonEscaping stmt) (hrest : NonEscapingList rest) :
    NonEscapingList (stmt :: rest) := by
  intro fuel state
  cases fuel with
  | zero => exact Or.inr ⟨state, execIRStmts_zero_cons _ _ _⟩
  | succ f =>
      rcases hstmt f state with ⟨next, hcont⟩ | ⟨next, hrev⟩
      · rcases hrest f next with ⟨final, hfinal⟩ | ⟨final, hfinal⟩
        · exact Or.inl ⟨final, by
            rw [execIRStmts_cons_continue' f state next _ _ hcont]; exact hfinal⟩
        · exact Or.inr ⟨final, by
            rw [execIRStmts_cons_continue' f state next _ _ hcont]; exact hfinal⟩
      · exact Or.inr ⟨next, execIRStmts_cons_revert f state next _ _ hrev⟩

theorem nonEscapingList_of_forall :
    ∀ (stmts : List YulStmt), (∀ stmt ∈ stmts, NonEscaping stmt) → NonEscapingList stmts
  | [], _ => nonEscapingList_nil
  | stmt :: rest, h =>
      nonEscapingList_cons (h stmt (by simp))
        (nonEscapingList_of_forall rest (fun t ht => h t (by simp [ht])))

theorem NonEscaping.block {body : List YulStmt} (h : NonEscapingList body) :
    NonEscaping (.block body) := by
  intro fuel state
  cases fuel with
  | zero => exact Or.inr ⟨state, by simp [execIRStmt]⟩
  | succ f =>
      rcases h f state with ⟨next, hnext⟩ | ⟨next, hnext⟩
      · exact Or.inl ⟨next, by rw [execIRStmt_block' f state body]; exact hnext⟩
      · exact Or.inr ⟨next, by rw [execIRStmt_block' f state body]; exact hnext⟩

/-- `for` loops built from non-escaping pieces are themselves non-escaping.
Needed because the ABI encoder emits a `for` loop for dynamic error arguments.
The induction is on fuel: the interpreter recurs on `.for_ [] cond post body`
with one less fuel, so the structural induction hypothesis applies directly. -/
theorem NonEscaping.for_ {cond : YulExpr} {post body : List YulStmt}
    (hpost : NonEscapingList post) (hbody : NonEscapingList body) :
    ∀ (fuel : Nat) (init : List YulStmt), NonEscapingList init →
      ∀ (state : IRState),
        (∃ next, execIRStmt fuel state (.for_ init cond post body) = .continue next) ∨
        (∃ next, execIRStmt fuel state (.for_ init cond post body) = .revert next) := by
  intro fuel
  induction fuel with
  | zero =>
      intro _ _ state
      exact Or.inr ⟨state, by simp [execIRStmt]⟩
  | succ g ih =>
      intro init hinit state
      rcases hinit g state with ⟨sInit, hI⟩ | ⟨sInit, hI⟩
      · cases hc : evalIRExpr sInit cond with
        | none =>
            exact Or.inr ⟨sInit,
              execIRStmt_for_cond_none g state sInit init post body cond hI hc⟩
        | some v =>
            by_cases hv : v = 0
            · subst hv
              exact Or.inl ⟨sInit,
                execIRStmt_for_init_cond_zero g state sInit init post body cond hI hc⟩
            · rcases hbody g sInit with ⟨sBody, hB⟩ | ⟨sBody, hB⟩
              · rcases hpost g sBody with ⟨sPost, hP⟩ | ⟨sPost, hP⟩
                · rw [execIRStmt_for_one_continue g state sInit sBody sPost init post body
                    cond v hI hc hv hB hP]
                  exact ih [] nonEscapingList_nil sPost
                · exact Or.inr ⟨sPost,
                    execIRStmt_for_post_noncontinue g state sInit sBody init post body cond
                      v (.revert sPost) hI hc hv hB hP (by intro s; simp)⟩
              · exact Or.inr ⟨sBody,
                  execIRStmt_for_body_noncontinue g state sInit init post body cond
                    v (.revert sBody) hI hc hv hB (by intro s; simp)⟩
      · exact Or.inr ⟨sInit,
          execIRStmt_for_init_noncontinue g state init post body cond (.revert sInit)
            hI (by intro s; simp)⟩

/-! ## Statement lists that deterministically revert -/

/-- Statement lists that revert from any state at any fuel: a `revert` call
reached through a prefix of statements that can only continue or revert. -/
inductive RevertsAlways : List YulStmt → Prop
  | revertCall {rest : List YulStmt} (offset size : YulExpr) :
      RevertsAlways (.exprStmt (.call "revert" [offset, size]) :: rest)
  | cons {stmt : YulStmt} {rest : List YulStmt} :
      NonEscaping stmt → RevertsAlways rest → RevertsAlways (stmt :: rest)

/-- The core observable: a `RevertsAlways` list reverts from any state at any
fuel. -/
theorem execIRStmts_revertsAlways {stmts : List YulStmt}
    (h : RevertsAlways stmts) :
    ∀ (fuel : Nat) (state : IRState),
      ∃ next, execIRStmts fuel state stmts = .revert next := by
  induction h with
  | revertCall offset size =>
      intro fuel state
      cases fuel with
      | zero => exact ⟨state, execIRStmts_zero_cons _ _ _⟩
      | succ f =>
          exact ⟨state, execIRStmts_cons_revert f state state _ _
            (execIRStmt_revertCall f state offset size)⟩
  | cons hstmt _ ih =>
      intro fuel state
      cases fuel with
      | zero => exact ⟨state, execIRStmts_zero_cons _ _ _⟩
      | succ f =>
          rcases hstmt f state with ⟨next, hcont⟩ | ⟨next, hrev⟩
          · rcases ih f next with ⟨final, hfinal⟩
            exact ⟨final, by
              rw [execIRStmts_cons_continue' f state next _ _ hcont]; exact hfinal⟩
          · exact ⟨next, execIRStmts_cons_revert f state next _ _ hrev⟩

/-- A non-escaping prefix in front of a reverting list still reverts. -/
theorem RevertsAlways.append_left :
    ∀ (pre : List YulStmt) {post : List YulStmt},
      (∀ stmt ∈ pre, NonEscaping stmt) → RevertsAlways post →
      RevertsAlways (pre ++ post)
  | [], _, _, hpost => by simpa using hpost
  | stmt :: rest, _, hpre, hpost =>
      .cons (hpre stmt (by simp))
        (RevertsAlways.append_left rest
          (fun s hs => hpre s (by simp [hs])) hpost)

/-- A block wrapping a reverting list reverts. -/
theorem execIRStmts_block_revertsAlways {body : List YulStmt}
    (h : RevertsAlways body) :
    ∀ (fuel : Nat) (state : IRState),
      ∃ next, execIRStmts fuel state [YulStmt.block body] = .revert next := by
  intro fuel state
  cases fuel with
  | zero => exact ⟨state, execIRStmts_zero_cons _ _ _⟩
  | succ f =>
      cases f with
      | zero =>
          exact ⟨state, execIRStmts_cons_revert 0 state state _ _
            (by simp [execIRStmt])⟩
      | succ g =>
          rcases execIRStmts_revertsAlways h g state with ⟨next, hnext⟩
          refine ⟨next, execIRStmts_cons_revert (g + 1) state next _ _ ?_⟩
          rw [show execIRStmt (g + 1) state (YulStmt.block body) =
            execIRStmts g state body from by simp [execIRStmt]]
          exact hnext

/-! ## The custom-error payload shape

`revertWithCustomError` emits a single `block` whose body is a prefix of
memory/local writes followed by an unconditional `revert` call. This is the
`hrevertExec` shape that `compiledStmtStep_requireError` and
`compiledStmtStep_revertError` take as a hypothesis. -/

theorem RevertsAlways.prefix_revertCall {pre : List YulStmt} (offset size : YulExpr)
    (hpre : ∀ stmt ∈ pre, NonEscaping stmt) :
    RevertsAlways (pre ++ [YulStmt.exprStmt (.call "revert" [offset, size])]) :=
  RevertsAlways.append_left pre hpre (.revertCall offset size)

/-- Discharges `hrevertExec` for any payload of the shape
`[block (writes ++ [revert ..])]`. -/
theorem execIRStmts_payloadBlock_revert {pre : List YulStmt} (offset size : YulExpr)
    (hpre : ∀ stmt ∈ pre, NonEscaping stmt) :
    ∀ (state : IRState) (fuel : Nat),
      ∃ next,
        execIRStmts fuel state
          [YulStmt.block (pre ++ [YulStmt.exprStmt (.call "revert" [offset, size])])] =
          .revert next :=
  fun state fuel =>
    execIRStmts_block_revertsAlways (RevertsAlways.prefix_revertCall offset size hpre)
      fuel state

/-! ## Application: the `Error(string)` payload always reverts

`revertWithMessage` already has a proved shape lemma, so it is the cheapest
witness that the machinery above discharges a real `hrevertExec` obligation. -/

theorem revertWithMessage_revertsAlways (message : String) :
    RevertsAlways (revertWithMessage message) := by
  rw [revertWithMessage_shape]
  refine RevertsAlways.append_left (errorStringStmts message) ?_ (.revertCall _ _)
  intro stmt hstmt
  have hmstore : ∀ (o v : YulExpr),
      stmt = .exprStmt (.call "mstore" [o, v]) → NonEscaping stmt := by
    rintro o v rfl
    exact NonEscaping.mstore o v
  simp only [errorStringStmts, List.mem_cons, List.mem_map] at hstmt
  rcases hstmt with rfl | rfl | rfl | ⟨ci, _, rfl⟩
  · exact hmstore _ _ rfl
  · exact hmstore _ _ rfl
  · exact hmstore _ _ rfl
  · exact hmstore _ _ rfl

theorem execIRStmts_revertWithMessage_revert (message : String) :
    ∀ (state : IRState) (fuel : Nat),
      ∃ next, execIRStmts fuel state (revertWithMessage message) = .revert next :=
  fun state fuel =>
    execIRStmts_revertsAlways (revertWithMessage_revertsAlways message) fuel state

/-! ## Application: zero-argument custom errors always revert

`revertError E()` / `requireError c E()` compile through
`revertWithCustomError` to a single `block`: free-pointer load, the
signature-word `mstore`s, `keccak256`/`shl`/`shr` selector extraction, the
selector `mstore`, `let __err_tail = 0`, and the trailing `revert`. Every
statement before the `revert` is a `let` or an `mstore`, so the whole payload
is `RevertsAlways` — which is exactly the `hrevertExec` hypothesis of
`compiledStmtStep_requireError` and `compiledStmtStep_revertError`.

Custom errors *with* arguments additionally need `attachOffsets` and
per-parameter ABI encoding reasoning; the statement vocabulary those emit
(`let`/`assign`/`mstore`/`for`) is already covered by the `NonEscaping`
lemmas above, so only the shape computation is missing. -/

section ZeroArgCustomError

open Compiler.CompilationModel

/-- The zero-parameter payload, as emitted by `revertWithCustomError`. -/
private def zeroArgErrorPrefix (errorDef : ErrorDef) : List YulStmt :=
  [YulStmt.let_ "__err_ptr" (YulExpr.call "mload" [YulExpr.lit freeMemoryPointer])] ++
    ((chunkBytes32 (bytesFromString (errorSignature errorDef))).zipIdx.map
      (fun (chunk, idx) =>
        YulStmt.exprStmt (YulExpr.call "mstore" [
          YulExpr.call "add" [YulExpr.ident "__err_ptr", YulExpr.lit (idx * 32)],
          YulExpr.hex (wordFromBytes chunk)]))) ++
    [YulStmt.let_ "__err_hash"
        (YulExpr.call "keccak256" [YulExpr.ident "__err_ptr",
          YulExpr.lit (bytesFromString (errorSignature errorDef)).length]),
      YulStmt.let_ "__err_selector"
        (YulExpr.call "shl" [YulExpr.lit selectorShift,
          YulExpr.call "shr" [YulExpr.lit selectorShift, YulExpr.ident "__err_hash"]]),
      YulStmt.exprStmt (YulExpr.call "mstore"
        [YulExpr.lit 0, YulExpr.ident "__err_selector"]),
      YulStmt.let_ "__err_tail" (YulExpr.lit 0)]

private theorem revertWithCustomError_zero_shape
    (dynamicSource : DynamicDataSource) (errorDef : ErrorDef)
    (hParams : errorDef.params = []) :
    revertWithCustomError dynamicSource errorDef [] [] = .ok
      [YulStmt.block (zeroArgErrorPrefix errorDef ++
        [YulStmt.exprStmt (YulExpr.call "revert"
          [YulExpr.lit 0,
            YulExpr.call "add" [YulExpr.lit 4, YulExpr.ident "__err_tail"]])])] := by
  unfold revertWithCustomError zeroArgErrorPrefix
  simp [hParams]
  rfl

private theorem zeroArgErrorPrefix_nonEscaping (errorDef : ErrorDef) :
    ∀ stmt ∈ zeroArgErrorPrefix errorDef, NonEscaping stmt := by
  intro stmt hMem
  simp only [zeroArgErrorPrefix, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_map] at hMem
  rcases hMem with (rfl | ⟨chunkAndIdx, _, rfl⟩) | (rfl | rfl | rfl | rfl)
  · exact NonEscaping.let_ _ _
  · rcases chunkAndIdx with ⟨chunk, idx⟩
    exact NonEscaping.mstore _ _
  · exact NonEscaping.let_ _ _
  · exact NonEscaping.let_ _ _
  · exact NonEscaping.mstore _ _
  · exact NonEscaping.let_ _ _

/-- `hrevertExec` for a zero-argument custom error: the compiled payload reverts
from every state at every fuel value. -/
theorem execIRStmts_revertWithCustomError_zero_revert
    (dynamicSource : DynamicDataSource) (errorDef : ErrorDef)
    (hParams : errorDef.params = []) {out : List YulStmt}
    (hOk : revertWithCustomError dynamicSource errorDef [] [] = .ok out) :
    ∀ (state : IRState) (fuel : Nat),
      ∃ next, execIRStmts fuel state out = .revert next := by
  rw [revertWithCustomError_zero_shape dynamicSource errorDef hParams] at hOk
  injection hOk with hOk
  subst out
  exact execIRStmts_payloadBlock_revert _ _ (zeroArgErrorPrefix_nonEscaping errorDef)

end ZeroArgCustomError

end Compiler.Proofs.IRGeneration

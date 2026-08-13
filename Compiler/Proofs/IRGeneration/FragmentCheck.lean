import Compiler.Proofs.IRGeneration.SpliceSimulation

/-!
# Decidable membership checker for the splice-simulation fragment

`SpliceSim` is a `Prop` fragment; consumers of the `*_guarded` family need to
discharge membership per concrete compiled body.  This module provides the
executable mirror `spliceSimCheck` with a soundness theorem, so fragment
membership for any concrete compilation output is a `decide`/`native_decide`
obligation — the same per-contract discharge style the rest of the proof
stack uses — with no induction over the source grammar required.
-/
namespace Compiler.Proofs.IRGeneration

open Compiler.Yul

mutual

/-- Executable mirror of `SpliceSim`. -/
def spliceSimCheck : YulStmt → Bool
  | .if_ _ body => spliceSimCheckList body
  | .block stmts => spliceSimCheckList stmts
  | .for_ _ _ _ _ => false
  | .switch _ cases dflt =>
      spliceSimCheckCases cases && spliceSimCheckDflt dflt
  | .exprStmt (.call "return" args) =>
      match args with
      | [.lit _, .lit _] => true
      | _ => false
  | .exprStmt (.call "stop" args) => args.isEmpty
  | .exprStmt (.call "selfdestruct" _) => false
  | _ => true

def spliceSimCheckCases : List (Nat × List YulStmt) → Bool
  | [] => true
  | c :: rest => spliceSimCheckList c.2 && spliceSimCheckCases rest

def spliceSimCheckDflt : Option (List YulStmt) → Bool
  | none => true
  | some stmts => spliceSimCheckList stmts

def spliceSimCheckList : List YulStmt → Bool
  | [] => true
  | s :: rest => spliceSimCheck s && spliceSimCheckList rest

end

mutual

/-- Soundness: a checked statement is in the fragment. -/
theorem spliceSimCheck_sound : ∀ (s : YulStmt), spliceSimCheck s = true →
    SpliceSim s
  | .if_ _ body, h => by
      simp only [SpliceSim]
      exact spliceSimCheckList_sound body (by simpa [spliceSimCheck] using h)
  | .block stmts, h => by
      simp only [SpliceSim]
      exact spliceSimCheckList_sound stmts (by simpa [spliceSimCheck] using h)
  | .for_ _ _ _ _, h => by simp [spliceSimCheck] at h
  | .switch _ cases dflt, h => by
      obtain ⟨hc, hd⟩ : spliceSimCheckCases cases = true ∧
          spliceSimCheckDflt dflt = true := by
        simpa [spliceSimCheck, Bool.and_eq_true] using h
      exact ⟨spliceSimCheckCases_sound cases hc, spliceSimCheckDflt_sound dflt hd⟩
  | .comment _, _ => trivial
  | .let_ _ _, _ => trivial
  | .letMany _ _, _ => trivial
  | .assign _ _, _ => trivial
  | .leave, _ => trivial
  | .funcDef _ _ _ _, _ => trivial
  | .exprStmt e, h => by
      cases e with
      | call f args =>
          by_cases hret : f = "return"
          · subst hret
            simp only [SpliceSim]
            cases args with
            | nil => simp [spliceSimCheck] at h
            | cons a rest =>
                cases rest with
                | nil => cases a <;> simp [spliceSimCheck] at h
                | cons b rest' =>
                    cases rest' with
                    | cons _ _ => cases a <;> cases b <;> simp [spliceSimCheck] at h
                    | nil =>
                        cases a <;> cases b <;>
                          first
                            | exact ⟨_, _, rfl⟩
                            | simp [spliceSimCheck] at h
          · by_cases hstop : f = "stop"
            · subst hstop
              simp only [SpliceSim]
              cases args with
              | nil => rfl
              | cons _ _ => simp [spliceSimCheck] at h
            · by_cases hsd : f = "selfdestruct"
              · subst hsd
                simp [spliceSimCheck] at h
              · rw [SpliceSim.eq_def]
                split <;> simp_all
      | lit _ => trivial
      | hex _ => trivial
      | ident _ => trivial
      | str _ => trivial

theorem spliceSimCheckCases_sound :
    ∀ (cs : List (Nat × List YulStmt)), spliceSimCheckCases cs = true →
      SpliceSimCases cs
  | [], _ => trivial
  | c :: rest, h => by
      obtain ⟨hc, hrest⟩ : spliceSimCheckList c.2 = true ∧
          spliceSimCheckCases rest = true := by
        simpa [spliceSimCheckCases, Bool.and_eq_true] using h
      exact ⟨spliceSimCheckList_sound c.2 hc, spliceSimCheckCases_sound rest hrest⟩

theorem spliceSimCheckDflt_sound :
    ∀ (d : Option (List YulStmt)), spliceSimCheckDflt d = true →
      SpliceSimDflt d
  | none, _ => trivial
  | some stmts, h =>
      spliceSimCheckList_sound stmts (by simpa [spliceSimCheckDflt] using h)

theorem spliceSimCheckList_sound :
    ∀ (xs : List YulStmt), spliceSimCheckList xs = true → SpliceSimList xs
  | [], _ => trivial
  | s :: rest, h => by
      obtain ⟨hs, hrest⟩ : spliceSimCheck s = true ∧
          spliceSimCheckList rest = true := by
        simpa [spliceSimCheckList, Bool.and_eq_true] using h
      exact ⟨spliceSimCheck_sound s hs, spliceSimCheckList_sound rest hrest⟩

end

/-- Executable mirror of `ModeledHalt`. -/
def modeledHaltCheck : YulStmt → Bool
  | .exprStmt (.call "stop" args) => args.isEmpty
  | .exprStmt (.call "return" args) =>
      match args with
      | [.lit _, .lit _] => true
      | _ => false
  | .exprStmt (.call "revert" args) => args.length == 2
  | .exprStmt (.call "invalid" args) => args.isEmpty
  | _ => false

theorem modeledHaltCheck_sound : ∀ (s : YulStmt), modeledHaltCheck s = true →
    ModeledHalt s
  | .exprStmt (.call f args), h => by
      by_cases hstop : f = "stop"
      · subst hstop
        obtain rfl : args = [] := by
          simpa [modeledHaltCheck, List.isEmpty_iff] using h
        exact .stop
      · by_cases hret : f = "return"
        · subst hret
          cases args with
          | nil => simp [modeledHaltCheck] at h
          | cons a rest =>
              cases rest with
              | nil => cases a <;> simp [modeledHaltCheck] at h
              | cons b rest' =>
                  cases rest' with
                  | cons _ _ => cases a <;> cases b <;> simp [modeledHaltCheck] at h
                  | nil =>
                      cases a <;> cases b <;>
                        first
                          | exact ModeledHalt.ret _ _
                          | simp [modeledHaltCheck] at h
        · by_cases hrev : f = "revert"
          · subst hrev
            cases args with
            | nil => simp [modeledHaltCheck] at h
            | cons a rest =>
                cases rest with
                | nil => simp [modeledHaltCheck] at h
                | cons b rest' =>
                    cases rest' with
                    | nil => exact .rev a b
                    | cons _ _ => simp [modeledHaltCheck] at h
          · by_cases hinv : f = "invalid"
            · subst hinv
              obtain rfl : args = [] := by
                simpa [modeledHaltCheck, List.isEmpty_iff] using h
              exact .inv
            · simp [modeledHaltCheck, hstop, hret, hrev, hinv] at h

end Compiler.Proofs.IRGeneration

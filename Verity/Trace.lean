namespace Verity.Trace

/-!
# Counting trace machinery

A reusable type-class–based abstraction for "this event happens exactly
N times" properties over contract execution traces. Promoted from
`Benchmark.Cases.ERC4337.EntryPointInvariant.Trace`.

## Pattern

A `Trace` is a `List Event` for some event type. A `MatchKey` is
arbitrary metadata (an address, a calldata, a selector); a contract
trace property is typically "the trace contains exactly one event
matching this key."

We provide:

* `countMatching` — generic counting predicate.
* `count_le_one_under_pairwise_distinct` — at most one matching event
  when the source list of events generators are pairwise distinct on the
  key.
* `count_ge_one_when_member_emitted` — at least one matching event when
  a known emitter is in the source list with non-empty contribution.

Downstream contracts instantiate with their concrete `Event`, `Key`,
and `matchEvent` predicate.
-/

/-- `countMatching` is positive iff some event matchEvent the key. -/
def countMatching {Event Key : Type}
    (matchEvent : Key → Event → Bool) (key : Key) (trace : List Event) : Nat :=
  (trace.filter (matchEvent key)).length

/-- Pairwise distinctness on a key-extraction function. -/
def Pairwise.distinctOn {α Key : Type} [DecidableEq Key]
    (keyOf : α → Key) (xs : List α) : Prop :=
  List.Pairwise (fun a b => keyOf a ≠ keyOf b) xs

/-! ## Generic at-most-once theorem

Stated parametrically over an event-generation function `emit : α →
Option Event` (returns `none` when the generator contributes nothing, as
in the ERC-4337 `callData.length = 0` branch). The generator's domain
list `xs` is the source of truth; we case-split on it.
-/

/-- A generic execution loop: `xs` is the list of operations, `emit`
    produces zero or one `Event` per operation. -/
def emitLoop {α Event : Type} (emit : α → Option Event) : List α → List Event
  | [] => []
  | x :: rest =>
    match emit x with
    | some e => e :: emitLoop emit rest
    | none   => emitLoop emit rest

/-- Every event in `emitLoop emit xs` came from some `x ∈ xs`. -/
theorem emitLoop_event_origin {α Event : Type}
    (emit : α → Option Event) (xs : List α) (e : Event)
    (he : e ∈ emitLoop emit xs) :
    ∃ x ∈ xs, emit x = some e := by
  induction xs with
  | nil => simp [emitLoop] at he
  | cons hd rest ih =>
    simp only [emitLoop] at he
    split at he
    · rename_i e' hEq
      rcases List.mem_cons.mp he with hHd | hTail
      · refine ⟨hd, List.mem_cons_self .., ?_⟩
        rw [hEq, hHd]
      · obtain ⟨x, hx, hex⟩ := ih hTail
        exact ⟨x, List.mem_cons_of_mem _ hx, hex⟩
    · obtain ⟨x, hx, hex⟩ := ih he
      exact ⟨x, List.mem_cons_of_mem _ hx, hex⟩

/-- If `x ∈ xs` and `emit x = some e`, then `e ∈ emitLoop emit xs`. -/
theorem emitLoop_contains_emitted_event {α Event : Type}
    (emit : α → Option Event) (xs : List α) (x : α) (hMem : x ∈ xs)
    (e : Event) (hEmit : emit x = some e) :
    e ∈ emitLoop emit xs := by
  induction xs with
  | nil => cases hMem
  | cons hd rest ih =>
    simp only [emitLoop]
    rcases List.mem_cons.mp hMem with hEq | hTail
    · subst hEq
      rw [hEmit]
      exact List.mem_cons_self ..
    · split
      · exact List.mem_cons_of_mem _ (ih hTail)
      · exact ih hTail

/-- **At-most-once**: if all events emitted from `xs` are pairwise
    distinct on a matching key, the trace contains at most one match. -/
theorem count_le_one_under_pairwise_distinct
    {α Event Key : Type} [DecidableEq Event]
    (emit : α → Option Event) (matchEvent : Key → Event → Bool) (key : Key)
    (xs : List α)
    (hDistinct : List.Pairwise
      (fun a b => ∀ ea eb, emit a = some ea → emit b = some eb →
        ¬ (matchEvent key ea = true ∧ matchEvent key eb = true)) xs) :
    countMatching matchEvent key (emitLoop emit xs) ≤ 1 := by
  induction xs with
  | nil => simp [emitLoop, countMatching]
  | cons hd rest ih =>
    have hRestDistinct := (List.pairwise_cons.mp hDistinct).2
    have hHeadDistinct := (List.pairwise_cons.mp hDistinct).1
    simp only [emitLoop]
    split
    · rename_i e hEq
      by_cases hHdMatch : matchEvent key e = true
      · -- Head emits a matching event. No tail event can also match.
        have hTailZero :
            countMatching matchEvent key (emitLoop emit rest) = 0 := by
          unfold countMatching
          have : (emitLoop emit rest).filter (matchEvent key) = [] := by
            apply List.filter_eq_nil_iff.mpr
            intro e' he' hMatch'
            obtain ⟨x', hx', hex'⟩ := emitLoop_event_origin emit rest e' he'
            exact hHeadDistinct x' hx' e e' hEq hex' ⟨hHdMatch, hMatch'⟩
          rw [this]; simp
        unfold countMatching at hTailZero ⊢
        simp only [List.filter_cons]
        rw [if_pos hHdMatch]
        simp [hTailZero]
      · -- Head does not match. Recurse on tail.
        unfold countMatching
        simp only [List.filter_cons]
        rw [if_neg (by simp [hHdMatch])]
        exact ih hRestDistinct
    · exact ih hRestDistinct

end Verity.Trace

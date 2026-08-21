import Compiler.Proofs.AbiEventObservable

/-!
# Dynamic event log observables are ABI-encoded (#2082 slice 4)

Slice 3 (`Compiler/Proofs/AbiEventObservable.lean`) proved
`scalarEmitPayload_log_observable`: for an event whose unindexed arguments each
occupy exactly one head word, the compiled `emit` payload appends one LOG
observable whose data is `abiEncodeScalarHeads`.  That statement requires
`eventHeadWordSize` to be `32` for every unindexed parameter, so any payload
with a head/tail split is outside its domain.

This module lifts the result to the dynamic case.  `DynEmitArg` describes an
unindexed emit payload at the IR level — a static scalar, a `bytes`/`string`
value (length word plus packed data words), or a dynamic array of scalars —
and `dynEmitPayloadExprs` lays out the whole payload as one 32-byte-stride
word block: every argument's head first (static heads as normalized words,
dynamic heads as the block-relative byte offset of that argument's tail),
then the tails in argument order.  `dynamicEmitPayload_log_observable` then
proves that running that block followed by the `logN` instruction appends
exactly one observable whose

* `topics = eventSignatureTopic :: abi(indexed arguments)`, and
* `data   = abiEncodeArgs (the slice-2 head/tail encoding)`.

The offsets are *computed* by `dynEmitHeadExprs`, not assumed: the proof that
they agree with `abiEncodeArgHeads` is what pins the ABI head/tail arithmetic
at the IR level.  The chain reuses the slice-3 infrastructure unchanged —
`execIRStmts_mstore_ptr_expr_block` runs the block, `abiBlockWrites_eq_zip`
identifies its writes with an ABI word block, and
`yulLogDataWords_abiBlockWrites` reads the block back.

Two gaps remain and are deliberately *not* claimed here; both are recorded in
`docs/VERIFICATION_STATUS.md`:

* `compileEmit`'s `bytes`/`string` lane materializes tail data with
  `dynamicCopyData` (a `calldatacopy`) and carries dynamic head offsets in the
  mutable `__evt_data_tail` accumulator rather than as literals, so connecting
  `dynEmitPayloadExprs` to that concrete statement list needs:
  (1) a word-granular `calldatacopy` readback lemma — now provided at two
      levels: the floor readback
      `CalldataMemoryLayout.yulLogDataWords_calldatacopyMemory` for
      word-aligned sizes, and the ceiling readback
      `CalldataMemoryLayout.yulLogDataWords_calldatacopyMemoryPadded` for
      arbitrary byte sizes (covering the final partial word with
      zero-padded masking via `calldatacopyMemoryPadded`);
  (2) an accumulator invariant for `__evt_data_tail`; and
  (3) connecting the ceiling-word model `calldatacopyMemoryPadded` to the
      IR interpreter's `calldatacopyMemory` (the base model writes only
      `⌊size/32⌋` full words; the ceiling-word extension is a separate
      composition layer).
* Indexed dynamic arguments are hashed into a topic by `keccak256` over a
  copied region; the observable model has no lemma pinning that hash, so the
  indexed side here stays scalar (`scalarEventIndexedTopicParts`).
-/

namespace Compiler.Proofs.AbiDynamicEventObservable

open Compiler
open Compiler.Yul
open Compiler.CompilationModel
open Compiler.Proofs.AbiEncoding
open Compiler.Proofs.IRGeneration
open Compiler.Proofs.AbiMemoryLayout
open Compiler.Proofs.AbiEventObservable

/-! ## Evaluation plumbing

Two facts about `evalIRExprs` that the scalar slice did not need: it commutes
with `++` (the payload is heads followed by tails), and it commutes with a
`normalizeEventWord` map over a bare expression list (array elements are not
`EventParam` entries, so `evalIRExprs_normalizeEventWord_map` does not apply). -/

theorem evalIRExprs_append :
    ∀ (es fs : List YulExpr) (vs ws : List Nat) (state : IRState),
      evalIRExprs state es = some vs → evalIRExprs state fs = some ws →
      evalIRExprs state (es ++ fs) = some (vs ++ ws)
  | [], fs, vs, ws, state, hes, hfs => by
      have hvs : vs = [] := by simpa [evalIRExprs] using hes.symm
      subst hvs
      simpa using hfs
  | e :: es, fs, vs, ws, state, hes, hfs => by
      simp only [evalIRExprs, Option.bind_eq_bind] at hes
      cases hv : evalIRExpr state e with
      | none => rw [hv] at hes; simp at hes
      | some v =>
          rw [hv] at hes
          cases hvs : evalIRExprs state es with
          | none => rw [hvs] at hes; simp at hes
          | some vs' =>
              rw [hvs] at hes
              obtain rfl : v :: vs' = vs := by simpa using hes
              simp only [List.cons_append, evalIRExprs, Option.bind_eq_bind, hv,
                evalIRExprs_append es fs vs' ws state hvs hfs, List.cons_append]
              rfl

theorem evalIRExprs_map_normalizeEventWord (ty : ParamType)
    (hty : eventParamScalarCompileSupported ty = true) :
    ∀ (es : List YulExpr) (values : List Nat) (state : IRState),
      evalIRExprs state es = some values →
      evalIRExprs state (es.map (normalizeEventWord ty)) =
        some (values.map (abiScalarNormalize ty))
  | [], values, state, hvals => by
      have hv : values = [] := by simpa [evalIRExprs] using hvals.symm
      subst hv
      simp [evalIRExprs]
  | e :: es, values, state, hvals => by
      simp only [evalIRExprs, Option.bind_eq_bind] at hvals
      cases hv : evalIRExpr state e with
      | none => rw [hv] at hvals; simp at hvals
      | some v =>
          rw [hv] at hvals
          cases hvs : evalIRExprs state es with
          | none => rw [hvs] at hvals; simp at hvals
          | some vs =>
              rw [hvs] at hvals
              obtain rfl : v :: vs = values := by simpa using hvals
              have hhead := normalizeEventWord_eval_abiScalarNormalize ty hty state e
              simp only [List.map_cons, evalIRExprs, Option.bind_eq_bind, hhead, hv,
                Option.map_some, evalIRExprs_map_normalizeEventWord ty hty es vs state hvs]
              rfl

/-! ## Unindexed payload arguments at the IR level -/

/-- An unindexed `emit` payload argument, described by the expressions the
payload block stores.  This is the IR-level counterpart of the slice-2
`AbiArg`: a static scalar contributes a single head word, while `bytes` and a
scalar array contribute an offset head plus a length-prefixed tail. -/
inductive DynEmitArg where
  | scalar (ty : ParamType) (expr : YulExpr)
  | bytes (lengthExpr : YulExpr) (dataExprs : List YulExpr)
  | scalarArray (elementType : ParamType) (elemExprs : List YulExpr)

namespace DynEmitArg

/-- The tail words this argument contributes, in ABI order.  Both dynamic
forms are length-prefixed; array elements are ABI-normalized in place. -/
def tailExprs : DynEmitArg → List YulExpr
  | .scalar _ _ => []
  | .bytes lengthExpr dataExprs => lengthExpr :: dataExprs
  | .scalarArray ty elemExprs =>
      YulExpr.lit elemExprs.length :: elemExprs.map (normalizeEventWord ty)

/-- Number of tail words, known statically from the payload shape — this is
what makes the dynamic head offsets computable. -/
def tailWords : DynEmitArg → Nat
  | .scalar _ _ => 0
  | .bytes _ dataExprs => dataExprs.length + 1
  | .scalarArray _ elemExprs => elemExprs.length + 1

/-- The single head word: a normalized value for a static scalar, the
block-relative byte offset of the tail for a dynamic argument. -/
def headExpr : DynEmitArg → Nat → YulExpr
  | .scalar ty expr, _ => normalizeEventWord ty expr
  | .bytes _ _, tailOffset => YulExpr.lit tailOffset
  | .scalarArray _ _, tailOffset => YulExpr.lit tailOffset

end DynEmitArg

/-- What it means for an IR payload argument to denote a slice-2 `AbiArg` in a
given state: its expressions evaluate to that argument's words. -/
def DynEmitArgDenotes (state : IRState) : DynEmitArg → AbiArg → Prop
  | .scalar ty expr, abiArg =>
      eventParamScalarCompileSupported ty = true ∧
        ∃ value, evalIRExpr state expr = some value ∧ abiArg = .scalar ty value
  | .bytes lengthExpr dataExprs, abiArg =>
      ∃ byteLength dataWords, evalIRExpr state lengthExpr = some byteLength ∧
        evalIRExprs state dataExprs = some dataWords ∧
        abiArg = .bytes { byteLength := byteLength, dataWords := dataWords }
  | .scalarArray ty elemExprs, abiArg =>
      eventParamScalarCompileSupported ty = true ∧
        ∃ values, evalIRExprs state elemExprs = some values ∧
          abiArg = .scalarArray ty values

/-- Pointwise denotation of a whole unindexed payload. -/
def DynEmitDenotes (state : IRState) : List DynEmitArg → List AbiArg → Prop
  | [], [] => True
  | arg :: args, abiArg :: abiArgs =>
      DynEmitArgDenotes state arg abiArg ∧ DynEmitDenotes state args abiArgs
  | _, _ => False

theorem DynEmitDenotes_length :
    ∀ (args : List DynEmitArg) (abiArgs : List AbiArg) (state : IRState),
      DynEmitDenotes state args abiArgs → args.length = abiArgs.length
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => absurd h (by simp [DynEmitDenotes])
  | _ :: _, [], _, h => absurd h (by simp [DynEmitDenotes])
  | _ :: args, _ :: abiArgs, state, h => by
      simp only [List.length_cons]
      rw [DynEmitDenotes_length args abiArgs state h.2]

/-- The statically known tail width is the actual tail length of the denoted
argument: the packed data words are exactly the evaluated expressions. -/
theorem tailWords_eq_tail_length (state : IRState) (arg : DynEmitArg) (abiArg : AbiArg)
    (h : DynEmitArgDenotes state arg abiArg) : arg.tailWords = abiArg.tail.length := by
  cases arg with
  | scalar ty expr =>
      obtain ⟨_, value, _, rfl⟩ := h
      simp [DynEmitArg.tailWords]
  | bytes lengthExpr dataExprs =>
      obtain ⟨byteLength, dataWords, _, hdata, rfl⟩ := h
      simp [DynEmitArg.tailWords, evalIRExprs_length dataExprs state dataWords hdata]
  | scalarArray ty elemExprs =>
      obtain ⟨_, values, hvalues, rfl⟩ := h
      simp [DynEmitArg.tailWords, evalIRExprs_length elemExprs state values hvalues]

/-- The tail expressions of a denoted argument evaluate to its ABI tail. -/
theorem tailExprs_eval (state : IRState) (arg : DynEmitArg) (abiArg : AbiArg)
    (h : DynEmitArgDenotes state arg abiArg) :
    evalIRExprs state arg.tailExprs = some abiArg.tail := by
  cases arg with
  | scalar ty expr =>
      obtain ⟨_, value, _, rfl⟩ := h
      simp [DynEmitArg.tailExprs, evalIRExprs]
  | bytes lengthExpr dataExprs =>
      obtain ⟨byteLength, dataWords, hlen, hdata, rfl⟩ := h
      simp [DynEmitArg.tailExprs, evalIRExprs, hlen, hdata]
  | scalarArray ty elemExprs =>
      obtain ⟨hty, values, hvalues, rfl⟩ := h
      have hlen : elemExprs.length = values.length :=
        (evalIRExprs_length elemExprs state values hvalues).symm
      simp only [DynEmitArg.tailExprs, AbiArg.tail_scalarArray, evalIRExprs,
        Option.bind_eq_bind, evalIRExpr, hlen,
        evalIRExprs_map_normalizeEventWord ty hty elemExprs values state hvalues]
      rfl

/-! ## The payload word block -/

/-- Head words of the payload, threading the running tail offset. -/
def dynEmitHeadExprs : List DynEmitArg → Nat → List YulExpr
  | [], _ => []
  | arg :: rest, tailOffset =>
      arg.headExpr tailOffset ::
        dynEmitHeadExprs rest (tailOffset + 32 * arg.tailWords)

/-- **Head/tail arithmetic.**  The computed head expressions evaluate to the
slice-2 ABI heads: static heads are normalized values, and each dynamic head
is the byte offset at which that argument's tail begins. -/
theorem dynEmitHeadExprs_eval :
    ∀ (args : List DynEmitArg) (abiArgs : List AbiArg) (state : IRState) (tailOffset : Nat),
      DynEmitDenotes state args abiArgs →
      evalIRExprs state (dynEmitHeadExprs args tailOffset) =
        some (abiEncodeArgHeads abiArgs tailOffset)
  | [], [], _, _, _ => by simp [dynEmitHeadExprs, abiEncodeArgHeads, evalIRExprs]
  | [], _ :: _, _, _, h => absurd h (by simp [DynEmitDenotes])
  | _ :: _, [], _, _, h => absurd h (by simp [DynEmitDenotes])
  | arg :: args, abiArg :: abiArgs, state, tailOffset, h => by
      have hsize : 32 * arg.tailWords = abiArg.tailSize := by
        rw [tailWords_eq_tail_length state arg abiArg h.1, AbiArg.tailSize, Nat.mul_comm]
      have hrest := dynEmitHeadExprs_eval args abiArgs state
      cases arg with
      | scalar ty expr =>
          obtain ⟨hty, value, hvalue, rfl⟩ := h.1
          have hhead := normalizeEventWord_eval_abiScalarNormalize ty hty state expr
          simp only [dynEmitHeadExprs, DynEmitArg.headExpr, DynEmitArg.tailWords,
            Nat.mul_zero, Nat.add_zero, evalIRExprs, Option.bind_eq_bind, hhead, hvalue,
            Option.map_some, hrest tailOffset h.2, abiEncodeArgHeads, abiEncodeScalarHead]
          rfl
      | bytes lengthExpr dataExprs =>
          obtain ⟨byteLength, dataWords, _, _, rfl⟩ := h.1
          simp only [dynEmitHeadExprs, DynEmitArg.headExpr, evalIRExprs, Option.bind_eq_bind,
            evalIRExpr, hsize, hrest _ h.2, abiEncodeArgHeads]
          rfl
      | scalarArray ty elemExprs =>
          obtain ⟨_, values, _, rfl⟩ := h.1
          simp only [dynEmitHeadExprs, DynEmitArg.headExpr, evalIRExprs, Option.bind_eq_bind,
            evalIRExpr, hsize, hrest _ h.2, abiEncodeArgHeads]
          rfl

/-- The complete unindexed payload as a word list: all heads, then all tails
in argument order — the layout `abiEncodeArgs` specifies. -/
def dynEmitPayloadExprs (args : List DynEmitArg) : List YulExpr :=
  dynEmitHeadExprs args (32 * args.length) ++ args.flatMap DynEmitArg.tailExprs

theorem dynEmitTailExprs_eval :
    ∀ (args : List DynEmitArg) (abiArgs : List AbiArg) (state : IRState),
      DynEmitDenotes state args abiArgs →
      evalIRExprs state (args.flatMap DynEmitArg.tailExprs) =
        some (abiArgs.flatMap AbiArg.tail)
  | [], [], _, _ => by simp [evalIRExprs]
  | [], _ :: _, _, h => absurd h (by simp [DynEmitDenotes])
  | _ :: _, [], _, h => absurd h (by simp [DynEmitDenotes])
  | arg :: args, abiArg :: abiArgs, state, h => by
      simp only [List.flatMap_cons]
      exact evalIRExprs_append _ _ _ _ state (tailExprs_eval state arg abiArg h.1)
        (dynEmitTailExprs_eval args abiArgs state h.2)

/-- **The payload is the ABI encoding.**  Every word the unindexed block
stores, in order, is exactly `abiEncodeArgs` of the denoted arguments. -/
theorem dynEmitPayloadExprs_eval (args : List DynEmitArg) (abiArgs : List AbiArg)
    (state : IRState) (h : DynEmitDenotes state args abiArgs) :
    evalIRExprs state (dynEmitPayloadExprs args) = some (abiEncodeArgs abiArgs) := by
  rw [dynEmitPayloadExprs, abiEncodeArgs, DynEmitDenotes_length args abiArgs state h]
  exact evalIRExprs_append _ _ _ _ state
    (dynEmitHeadExprs_eval args abiArgs state _ h)
    (dynEmitTailExprs_eval args abiArgs state h)

/-! ## Running the block -/

/-- Consecutive 32-byte-stride store offsets for a word list. -/
def abiWordWrites : Nat → List YulExpr → List (Nat × YulExpr)
  | _, [] => []
  | offset, e :: rest => (offset, e) :: abiWordWrites (offset + 32) rest

@[simp] theorem abiWordWrites_snd :
    ∀ (offset : Nat) (es : List YulExpr), (abiWordWrites offset es).map (·.2) = es
  | _, [] => rfl
  | offset, e :: rest => by
      simp only [abiWordWrites, List.map_cons, List.cons.injEq, true_and]
      exact abiWordWrites_snd (offset + 32) rest

@[simp] theorem abiWordWrites_length :
    ∀ (offset : Nat) (es : List YulExpr), (abiWordWrites offset es).length = es.length
  | _, [] => rfl
  | offset, e :: rest => by
      simp only [abiWordWrites, List.length_cons]
      rw [abiWordWrites_length (offset + 32) rest]

/-- The pointer-relative keys of a word-stride block are an `abiBlockWrites`
list based at the pointer. -/
theorem abiWordWrites_zip_eq_abiBlockWrites :
    ∀ (es : List YulExpr) (words : List Nat) (p offset : Nat),
      words.length = es.length →
      ((abiWordWrites offset es).map
          (fun ov => (p + ov.1) % Compiler.Constants.evmModulus)).zip words =
        abiBlockWrites (p + offset) words
  | [], words, p, offset, hlen => by
      have : words = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      subst this; rfl
  | e :: es, words, p, offset, hlen => by
      cases words with
      | nil => simp at hlen
      | cons word rest =>
          have hrest : rest.length = es.length := by simpa using hlen
          simp only [abiWordWrites, List.map_cons, List.zip_cons_cons,
            abiBlockWrites_cons, List.cons.injEq, true_and]
          rw [abiWordWrites_zip_eq_abiBlockWrites es rest p (offset + 32) hrest,
            show p + (offset + 32) = p + offset + 32 from by omega]

/-- The compiled unindexed payload block: one `mstore` per ABI word, at
32-byte stride from `__evt_ptr`. -/
def dynEmitUnindexedStores (args : List DynEmitArg) : List YulStmt :=
  (abiWordWrites 0 (dynEmitPayloadExprs args)).map fun ov =>
    YulStmt.exprStmt (YulExpr.call "mstore"
      [YulExpr.call "add" [YulExpr.ident "__evt_ptr", YulExpr.lit ov.1], ov.2])

theorem dynEmitPayloadExprs_length (args : List DynEmitArg) (abiArgs : List AbiArg)
    (state : IRState) (h : DynEmitDenotes state args abiArgs) :
    (dynEmitPayloadExprs args).length = (abiEncodeArgs abiArgs).length :=
  (evalIRExprs_length _ state _ (dynEmitPayloadExprs_eval args abiArgs state h)).symm

/-- Running the dynamic unindexed block from `__evt_ptr = p` leaves memory
holding the slice-2 ABI head/tail block of the unindexed arguments. -/
theorem dynEmitUnindexedStores_exec (args : List DynEmitArg) (abiArgs : List AbiArg)
    (fuel : Nat) (state : IRState) (p : Nat)
    (hptr : state.getVar "__evt_ptr" = some p)
    (hmi : MemInsensitiveExprs (dynEmitPayloadExprs args))
    (hden : DynEmitDenotes state args abiArgs) :
    execIRStmts ((abiEncodeArgs abiArgs).length + fuel + 1) state
        (dynEmitUnindexedStores args) =
      .continue { state with
        memory := applyWrites state.memory
          (abiBlockWrites p (abiEncodeArgs abiArgs)) } := by
  have hlen := dynEmitPayloadExprs_length args abiArgs state hden
  have hvals : evalIRExprs state ((abiWordWrites 0 (dynEmitPayloadExprs args)).map (·.2)) =
      some (abiEncodeArgs abiArgs) := by
    rw [abiWordWrites_snd]
    exact dynEmitPayloadExprs_eval args abiArgs state hden
  have hblock := execIRStmts_mstore_ptr_expr_block "__evt_ptr" p
    (abiWordWrites 0 (dynEmitPayloadExprs args)) (abiEncodeArgs abiArgs) fuel state hptr
    (by rw [abiWordWrites_snd]; exact hmi) hvals
  rw [dynEmitUnindexedStores,
    show (abiEncodeArgs abiArgs).length + fuel + 1 =
      (abiWordWrites 0 (dynEmitPayloadExprs args)).length + fuel + 1 from by
        rw [abiWordWrites_length, hlen],
    hblock, abiWordWrites_zip_eq_abiBlockWrites _ _ p 0 hlen.symm,
    Nat.add_zero]

/-- The log data payload of the dynamic block is exactly `abiEncodeArgs`. -/
theorem dynEmitUnindexedStores_logDataWords (args : List DynEmitArg) (abiArgs : List AbiArg)
    (fuel : Nat) (state : IRState) (p : Nat) (final : IRState)
    (hptr : state.getVar "__evt_ptr" = some p)
    (hmi : MemInsensitiveExprs (dynEmitPayloadExprs args))
    (hden : DynEmitDenotes state args abiArgs)
    (hfit : p + 32 * (abiEncodeArgs abiArgs).length ≤ Compiler.Constants.evmModulus)
    (hexec : execIRStmts ((abiEncodeArgs abiArgs).length + fuel + 1) state
      (dynEmitUnindexedStores args) = .continue final) :
    yulLogDataWords final.memory p (32 * (abiEncodeArgs abiArgs).length) =
      abiEncodeArgs abiArgs := by
  have hrun := dynEmitUnindexedStores_exec args abiArgs fuel state p hptr hmi hden
  rw [hexec] at hrun
  injection hrun with hstate
  have hmem : final.memory = applyWrites state.memory
      (abiBlockWrites p (abiEncodeArgs abiArgs)) := by rw [hstate]
  rw [hmem]
  exact yulLogDataWords_abiBlockWrites _ p state.memory hfit

/-! ## Threading through the LOG opcodes -/

private theorem evalIRExprs_nil_inv (state : IRState) (values : List Nat)
    (h : evalIRExprs state [] = some values) : values = [] := by
  simpa [evalIRExprs] using h.symm

private theorem evalIRExprs_cons_inv (state : IRState) (e : YulExpr) (es : List YulExpr)
    (values : List Nat) (h : evalIRExprs state (e :: es) = some values) :
    ∃ v vs, evalIRExpr state e = some v ∧ evalIRExprs state es = some vs ∧
      values = v :: vs := by
  simp only [evalIRExprs, Option.bind_eq_bind] at h
  cases he : evalIRExpr state e with
  | none => rw [he] at h; simp at h
  | some v =>
      cases hes : evalIRExprs state es with
      | none => rw [he, hes] at h; simp at h
      | some vs => exact ⟨v, vs, rfl, rfl, by rw [he, hes] at h; simpa using h.symm⟩

/-- `eventLogStmt_exec` with the data size supplied by an arbitrary
expression.  The dynamic lane passes the `__evt_data_tail` accumulator here
instead of a literal, so the size operand must be allowed to be a variable. -/
theorem eventLogStmt_exec_dataExpr
    (indexed : List (EventParam × Expr × YulExpr)) (topics : List Nat)
    (state : IRState) (dataSizeExpr : YulExpr) (p dataSize topic0 fuel : Nat)
    (hptr : state.getVar "__evt_ptr" = some p)
    (htopic0 : state.getVar "__evt_topic0" = some topic0)
    (hsize : evalIRExpr state dataSizeExpr = some dataSize)
    (hindexed : indexed.length ≤ 3)
    (htopics : evalIRExprs state ((scalarEventIndexedTopicParts indexed).map (·.2)) =
      some topics) :
    execIRStmt (fuel + 1) state
        (YulStmt.exprStmt (YulExpr.call (eventLogFunction indexed.length)
          (eventLogArgs dataSizeExpr (scalarEventIndexedTopicParts indexed)))) =
      .continue (state.appendYulLog p dataSize (topic0 :: topics)) := by
  rcases indexed with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩ <;>
    simp only [scalarEventIndexedTopicParts, List.map_cons, List.map_nil] at htopics
  · obtain rfl := evalIRExprs_nil_inv _ _ htopics
    simp [execIRStmt, isYulLogName, eventLogFunction, eventLogArgs,
      scalarEventIndexedTopicParts, evalIRExprs, evalIRExpr, hptr, htopic0, hsize]
  · obtain ⟨ta, _, ha, h0, rfl⟩ := evalIRExprs_cons_inv _ _ _ _ htopics
    obtain rfl := evalIRExprs_nil_inv _ _ h0
    simp [execIRStmt, isYulLogName, eventLogFunction, eventLogArgs,
      scalarEventIndexedTopicParts, evalIRExprs, evalIRExpr, hptr, htopic0, hsize, ha]
  · obtain ⟨ta, _, ha, h1, rfl⟩ := evalIRExprs_cons_inv _ _ _ _ htopics
    obtain ⟨tb, _, hb, h0, rfl⟩ := evalIRExprs_cons_inv _ _ _ _ h1
    obtain rfl := evalIRExprs_nil_inv _ _ h0
    simp [execIRStmt, isYulLogName, eventLogFunction, eventLogArgs,
      scalarEventIndexedTopicParts, evalIRExprs, evalIRExpr, hptr, htopic0, hsize, ha, hb]
  · obtain ⟨ta, _, ha, h2, rfl⟩ := evalIRExprs_cons_inv _ _ _ _ htopics
    obtain ⟨tb, _, hb, h1, rfl⟩ := evalIRExprs_cons_inv _ _ _ _ h2
    obtain ⟨tc, _, hc, h0, rfl⟩ := evalIRExprs_cons_inv _ _ _ _ h1
    obtain rfl := evalIRExprs_nil_inv _ _ h0
    simp [execIRStmt, isYulLogName, eventLogFunction, eventLogArgs,
      scalarEventIndexedTopicParts, evalIRExprs, evalIRExpr, hptr, htopic0, hsize, ha, hb, hc]
  · simp at hindexed

/-- Fuel bookkeeping for a straight-line block followed by one statement. -/
private theorem execIRStmts_block_then_stmt
    (block : List YulStmt) (last : YulStmt) (n fuel : Nat)
    (state mid final result : IRState) (hlen : block.length = n)
    (hblock : execIRStmts (n + fuel + 2) state block = .continue mid)
    (hlast : execIRStmt (fuel + 1) mid last = .continue result)
    (hexec : execIRStmts (n + fuel + 2) state (block ++ [last]) = .continue final) :
    final = result := by
  rw [execIRStmts_append_continue _ block (n + fuel + 2) state mid hblock, hlen,
    show n + fuel + 2 - n = (fuel + 1) + 1 from by omega,
    show execIRStmts ((fuel + 1) + 1) mid [last] =
      (match execIRStmt (fuel + 1) mid last with
        | .continue s => execIRStmts (fuel + 1) s []
        | .return v s => .return v s
        | .stop s => .stop s
        | .revert s => .revert s) from rfl,
    hlast] at hexec
  simp only [execIRStmts] at hexec
  injection hexec with hfinal
  exact hfinal.symm

@[simp] theorem dynEmitUnindexedStores_length (args : List DynEmitArg) :
    (dynEmitUnindexedStores args).length = (dynEmitPayloadExprs args).length := by
  simp [dynEmitUnindexedStores]

/-- **Slice-4 LOG threading.**  Running the compiled dynamic `emit` payload —
the unindexed head/tail `mstore` block followed by the `logN` instruction
whose size operand is the `__evt_data_tail` accumulator — appends exactly one
observable whose topics are `topic0` followed by the ABI encoding of the
indexed arguments, and whose data is the full slice-2 ABI encoding of the
unindexed arguments: static heads, dynamic head offsets, then tails.

This is `scalarEmitPayload_log_observable` with the one-word-per-argument
restriction removed. -/
theorem dynamicEmitPayload_log_observable
    (indexed : List (EventParam × Expr × YulExpr)) (args : List DynEmitArg)
    (abiArgs : List AbiArg) (indexedValues : List Nat)
    (state final : IRState) (p topic0 fuel : Nat)
    (hptr : state.getVar "__evt_ptr" = some p)
    (htopic0 : state.getVar "__evt_topic0" = some topic0)
    (hdataTail : state.getVar "__evt_data_tail" =
      some (32 * (abiEncodeArgs abiArgs).length))
    (hindexedLen : indexed.length ≤ 3)
    (hsupportIndexed : ∀ e ∈ indexed, eventParamScalarCompileSupported e.1.ty = true)
    (hmiIndexed : MemInsensitiveExprs (indexed.map (fun e => e.2.2)))
    (hmiPayload : MemInsensitiveExprs (dynEmitPayloadExprs args))
    (hindexedVals : evalIRExprs state (indexed.map (fun e => e.2.2)) = some indexedValues)
    (hden : DynEmitDenotes state args abiArgs)
    (hfit : p + 32 * (abiEncodeArgs abiArgs).length ≤ Compiler.Constants.evmModulus)
    (hexec : execIRStmts ((abiEncodeArgs abiArgs).length + fuel + 2) state
      (dynEmitUnindexedStores args ++
        [YulStmt.exprStmt (YulExpr.call (eventLogFunction indexed.length)
          (eventLogArgs (YulExpr.ident "__evt_data_tail")
            (scalarEventIndexedTopicParts indexed)))]) = .continue final) :
    final.events = state.events ++
      [(topic0 :: abiEncodeScalarHeads (eventAbiScalarArgs indexed indexedValues)) ++
        abiEncodeArgs abiArgs] := by
  have hlen := dynEmitPayloadExprs_length args abiArgs state hden
  have hrunStores := dynEmitUnindexedStores_exec args abiArgs (fuel + 1) state p hptr
    hmiPayload hden
  obtain ⟨mid, hmid⟩ : ∃ m : IRState, m = { state with
      memory := applyWrites state.memory
        (abiBlockWrites p (abiEncodeArgs abiArgs)) } := ⟨_, rfl⟩
  rw [← hmid] at hrunStores
  have hdata : yulLogDataWords mid.memory p (32 * (abiEncodeArgs abiArgs).length) =
      abiEncodeArgs abiArgs :=
    dynEmitUnindexedStores_logDataWords args abiArgs (fuel + 1) state p mid hptr hmiPayload
      hden hfit hrunStores
  have hrunLog := eventLogStmt_exec_dataExpr indexed
    (abiEncodeScalarHeads (eventAbiScalarArgs indexed indexedValues)) mid
    (YulExpr.ident "__evt_data_tail") p (32 * (abiEncodeArgs abiArgs).length) topic0 fuel
    (by rw [hmid]; exact hptr) (by rw [hmid]; exact htopic0)
    (by rw [hmid]; simpa [evalIRExpr, IRState.getVar] using hdataTail) hindexedLen
    (scalarEventIndexedTopicParts_eval indexed indexedValues mid hsupportIndexed
      (by rw [hmid, evalIRExprs_mem_insensitive _ hmiIndexed state _]; exact hindexedVals))
  rw [execIRStmts_block_then_stmt _ _ _ _ _ _ _ _
    (by rw [dynEmitUnindexedStores_length, hlen]) hrunStores hrunLog hexec]
  simp only [IRState.appendYulLog_events, encodeYulLogEvent, hdata,
    show mid.events = state.events from by rw [hmid]]

end Compiler.Proofs.AbiDynamicEventObservable

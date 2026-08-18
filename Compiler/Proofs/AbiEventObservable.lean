import Compiler.Proofs.AbiMemoryLayout

/-!
# Event log observables are ABI-encoded (#2082 slice 3)

`Compiler/Proofs/AbiMemoryLayout.lean` pins what an ABI word block looks like
once it has been written to memory. This module threads that through the LOG
opcodes: for the scalar `emit` block the compiler actually generates, the log
observable recorded by `log1`–`log4` is

* `topics = eventSignatureTopic :: abi(indexed arguments)`, and
* `data   = abi(non-indexed arguments)`,

where `abi` is the slice-1 scalar head encoder `abiEncodeScalarHeads`.

The chain is: `scalarEventUnindexedStoresFrom_shape` (the emitted block is a
pointer-offset `mstore` block) → `execIRStmts_mstore_ptr_expr_block` (it runs to
its evaluated writes) → `abiBlockWrites_eq_zip` (those writes are an ABI word
block) → `yulLogDataWords_abiBlockWrites` (the log payload reads them back).

Dynamic (`bytes`/`string`/array) event payloads and typed revert payloads are
**not** covered here: `compileEmit`'s dynamic lane writes a separate
`__evt_data_tail` region whose head/tail composition needs the slice-2
`abiEncodeArgs` bridge at the IR level, which is slice 4 work.
-/

namespace Compiler.Proofs.AbiEventObservable

open Compiler
open Compiler.Yul
open Compiler.CompilationModel
open Compiler.Proofs.AbiEncoding
open Compiler.Proofs.IRGeneration
open Compiler.Proofs.AbiMemoryLayout

/-! ## The remaining `normalizeEventWord` evaluation bridges

`Compiler/Proofs/AbiEncoding.lean` already pins `normalizeEventWord` to
`abiScalarNormalize` for the fixed-width scalar types. The parametric ones
(`uintN`, `intN`, `bytesN`) are added here so the bridge covers every type
`eventParamScalarCompileSupported` admits. -/

private theorem land_mod_evm_right (a b : Nat) :
    (a % Compiler.Constants.evmModulus) &&& (b % Compiler.Constants.evmModulus) =
      (a % Compiler.Constants.evmModulus) &&& b := by
  rw [show Compiler.Constants.evmModulus = 2 ^ 256 by rfl]
  rw [← Nat.and_two_pow_sub_one_eq_mod b 256, ← Nat.land_assoc,
    Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt (by
    rw [Nat.land_comm]
    exact Nat.and_lt_two_pow b (Nat.mod_lt a (by positivity)))

private theorem uint256OfNat_mod_evm (n : Nat) :
    Verity.Core.Uint256.ofNat (n % Compiler.Constants.evmModulus) =
      Verity.Core.Uint256.ofNat n := by
  apply Verity.Core.Uint256.ext
  simp [Verity.Core.Uint256.modulus, Compiler.Constants.evmModulus,
    Verity.Core.UINT256_MODULUS]

theorem normalizeEventWord_uintN_eval (bits : Nat) (s : IRState) (e : YulExpr) :
    evalIRExpr s (normalizeEventWord (ParamType.uintN bits) e) =
      (evalIRExpr s e).map (abiScalarNormalize (ParamType.uintN bits)) := by
  cases he : evalIRExpr s e with
  | none =>
      simp [normalizeEventWord, evalIRExpr, evalIRCall, evalIRExprs, he]
  | some v =>
      simp [normalizeEventWord, abiScalarNormalize, evalIRExpr, evalIRCall, evalIRExprs,
        Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
        Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean, he,
        land_mod_evm_right]

theorem normalizeEventWord_bytesN_eval (bytes : Nat) (s : IRState) (e : YulExpr) :
    evalIRExpr s (normalizeEventWord (ParamType.bytesN bytes) e) =
      (evalIRExpr s e).map (abiScalarNormalize (ParamType.bytesN bytes)) := by
  cases he : evalIRExpr s e with
  | none =>
      simp [normalizeEventWord, evalIRExpr, evalIRCall, evalIRExprs, he]
  | some v =>
      simp [normalizeEventWord, abiScalarNormalize, evalIRExpr, evalIRCall, evalIRExprs,
        Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
        Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean, he,
        land_mod_evm_right]

theorem normalizeEventWord_intN_eval (bits : Nat) (s : IRState) (e : YulExpr) :
    evalIRExpr s (normalizeEventWord (ParamType.intN bits) e) =
      (evalIRExpr s e).map (abiScalarNormalize (ParamType.intN bits)) := by
  cases he : evalIRExpr s e with
  | none =>
      simp [normalizeEventWord, evalIRExpr, evalIRCall, evalIRExprs, he]
  | some v =>
      simp [normalizeEventWord, abiScalarNormalize, evalIRExpr, evalIRCall, evalIRExprs,
        Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
        Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean, he,
        uint256OfNat_mod_evm]

/-- Complete bridge: on every scalar event parameter type the compiler accepts,
the emitted `normalizeEventWord` wrapper evaluates to the slice-1 ABI scalar
normalization of the underlying argument. -/
theorem normalizeEventWord_eval_abiScalarNormalize :
    ∀ (ty : ParamType), eventParamScalarCompileSupported ty = true →
      ∀ (s : IRState) (e : YulExpr),
        evalIRExpr s (normalizeEventWord ty e) =
          (evalIRExpr s e).map (abiScalarNormalize ty)
  | .uint256, _, s, e => normalizeEventWord_uint256_eval s e
  | .int256, _, s, e => normalizeEventWord_int256_eval s e
  | .bytes32, _, s, e => normalizeEventWord_bytes32_eval s e
  | .uint8, _, s, e => normalizeEventWord_uint8_eval s e
  | .uint16, _, s, e => normalizeEventWord_uint16_eval s e
  | .address, _, s, e => normalizeEventWord_address_eval s e
  | .bool, _, s, e => normalizeEventWord_bool_eval s e
  | .uintN bits, _, s, e => normalizeEventWord_uintN_eval bits s e
  | .intN bits, _, s, e => normalizeEventWord_intN_eval bits s e
  | .bytesN bytes, _, s, e => normalizeEventWord_bytesN_eval bytes s e
  | .newtypeOf name baseType, hsupport, s, e =>
      normalizeEventWord_newtypeOf_eval s e name baseType
        (normalizeEventWord_eval_abiScalarNormalize baseType
          (by simpa [eventParamScalarCompileSupported] using hsupport) s e)
  | .string, hsupport, _, _ => by
      simp [eventParamScalarCompileSupported] at hsupport
  | .bytes, hsupport, _, _ => by
      simp [eventParamScalarCompileSupported] at hsupport
  | .tuple _, hsupport, _, _ => by
      simp [eventParamScalarCompileSupported] at hsupport
  | .array _, hsupport, _, _ => by
      simp [eventParamScalarCompileSupported] at hsupport
  | .fixedArray _ _, hsupport, _, _ => by
      simp [eventParamScalarCompileSupported] at hsupport
  | .adt _ _, hsupport, _, _ => by
      simp [eventParamScalarCompileSupported] at hsupport

/-! ## Event argument lists as ABI scalar arguments -/

/-- The slice-1 ABI argument list of a zipped event-parameter list evaluated to
`values`: parameter types paired positionally with their argument values. -/
def eventAbiScalarArgs (entries : List (EventParam × Expr × YulExpr))
    (values : List Nat) : List (ParamType × Nat) :=
  (entries.map (fun entry => entry.1.ty)).zip values

@[simp] theorem eventAbiScalarArgs_nil (values : List Nat) :
    eventAbiScalarArgs [] values = [] := by
  simp [eventAbiScalarArgs]

@[simp] theorem eventAbiScalarArgs_cons
    (entry : EventParam × Expr × YulExpr)
    (entries : List (EventParam × Expr × YulExpr)) (value : Nat) (values : List Nat) :
    eventAbiScalarArgs (entry :: entries) (value :: values) =
      (entry.1.ty, value) :: eventAbiScalarArgs entries values := by
  simp [eventAbiScalarArgs]

/-- The normalized head expressions of a zipped event-parameter list evaluate to
exactly the slice-1 ABI scalar heads of the underlying argument values. -/
theorem evalIRExprs_normalizeEventWord_map :
    ∀ (entries : List (EventParam × Expr × YulExpr)) (values : List Nat) (state : IRState),
      (∀ entry ∈ entries, eventParamScalarCompileSupported entry.1.ty = true) →
      evalIRExprs state (entries.map (fun entry => entry.2.2)) = some values →
      evalIRExprs state (entries.map (fun entry => normalizeEventWord entry.1.ty entry.2.2)) =
        some (abiEncodeScalarHeads (eventAbiScalarArgs entries values))
  | [], values, _, _, hvals => by
      have : values = [] := by simpa [evalIRExprs] using hvals.symm
      subst this
      simp [evalIRExprs, abiEncodeScalarHeads]
  | entry :: entries, values, state, hsupport, hvals => by
      simp only [List.map_cons, evalIRExprs, Option.bind_eq_bind] at hvals
      cases hv : evalIRExpr state entry.2.2 with
      | none => rw [hv] at hvals; simp at hvals
      | some v =>
          rw [hv] at hvals
          cases hvs : evalIRExprs state (entries.map (fun e => e.2.2)) with
          | none => rw [hvs] at hvals; simp at hvals
          | some vs =>
              rw [hvs] at hvals
              obtain rfl : v :: vs = values := by simpa using hvals
              have hhead := normalizeEventWord_eval_abiScalarNormalize entry.1.ty
                (hsupport entry (by simp)) state entry.2.2
              have htail := evalIRExprs_normalizeEventWord_map entries vs state
                (fun e he => hsupport e (by simp [he])) hvs
              simp only [List.map_cons, evalIRExprs, Option.bind_eq_bind, hhead, hv,
                Option.map_some, htail, eventAbiScalarArgs_cons, abiEncodeScalarHeads,
                List.map_cons]
              rfl

/-! ## Topics: the indexed arguments -/

theorem scalarEventIndexedTopicParts_snd
    (indexed : List (EventParam × Expr × YulExpr)) :
    (scalarEventIndexedTopicParts indexed).map (·.2) =
      indexed.map (fun entry => normalizeEventWord entry.1.ty entry.2.2) := by
  induction indexed with
  | nil => rfl
  | cons entry rest ih =>
      simp only [scalarEventIndexedTopicParts, List.map_cons] at ih ⊢
      rw [ih]

/-- The `logN` topic operands after `topic0` evaluate to the ABI encoding of the
indexed event arguments. -/
theorem scalarEventIndexedTopicParts_eval
    (indexed : List (EventParam × Expr × YulExpr)) (values : List Nat) (state : IRState)
    (hsupport : ∀ entry ∈ indexed, eventParamScalarCompileSupported entry.1.ty = true)
    (hvals : evalIRExprs state (indexed.map (fun entry => entry.2.2)) = some values) :
    evalIRExprs state ((scalarEventIndexedTopicParts indexed).map (·.2)) =
      some (abiEncodeScalarHeads (eventAbiScalarArgs indexed values)) := by
  rw [scalarEventIndexedTopicParts_snd]
  exact evalIRExprs_normalizeEventWord_map indexed values state hsupport hvals

/-! ## Data: the unindexed arguments -/

theorem scalarEventWrites_snd :
    ∀ (entries : List (EventParam × Expr × YulExpr)) (headOffset : Nat),
      (scalarEventWrites entries headOffset).map (·.2) =
        entries.map (fun entry => normalizeEventWord entry.1.ty entry.2.2)
  | [], _ => rfl
  | entry :: entries, headOffset => by
      simp only [scalarEventWrites, List.map_cons]
      rw [scalarEventWrites_snd entries (headOffset + eventHeadWordSize entry.1.ty)]

theorem scalarEventWrites_fst :
    ∀ (entries : List (EventParam × Expr × YulExpr)) (headOffset : Nat),
      (∀ entry ∈ entries, eventHeadWordSize entry.1.ty = 32) →
      (scalarEventWrites entries headOffset).map (·.1) =
        (List.range entries.length).map (fun i => headOffset + i * 32)
  | [], _, _ => rfl
  | entry :: entries, headOffset, hsize => by
      have hentry : eventHeadWordSize entry.1.ty = 32 := hsize entry (by simp)
      simp only [scalarEventWrites, List.map_cons, List.length_cons]
      rw [scalarEventWrites_fst entries (headOffset + eventHeadWordSize entry.1.ty)
        (fun e he => hsize e (by simp [he])), hentry,
        List.range_succ_eq_map]
      simp only [List.map_cons, List.map_map, Nat.zero_mul, Nat.add_zero, List.cons.injEq,
        true_and]
      apply List.map_congr_left
      intro i _
      simp only [Function.comp_apply]
      omega

theorem scalarEventWrites_memInsensitive :
    ∀ (entries : List (EventParam × Expr × YulExpr)) (headOffset : Nat),
      MemInsensitiveExprs (entries.map (fun entry => entry.2.2)) →
      MemInsensitiveExprs ((scalarEventWrites entries headOffset).map (·.2))
  | [], _, _ => trivial
  | entry :: entries, headOffset, hmi => by
      rw [List.map_cons] at hmi
      obtain ⟨hhead, htail⟩ := hmi
      exact ⟨normalizeEventWord_memInsensitive entry.1.ty entry.2.2 hhead,
        scalarEventWrites_memInsensitive entries
          (headOffset + eventHeadWordSize entry.1.ty) htail⟩

@[simp] theorem scalarEventWrites_length :
    ∀ (entries : List (EventParam × Expr × YulExpr)) (headOffset : Nat),
      (scalarEventWrites entries headOffset).length = entries.length
  | [], _ => rfl
  | entry :: entries, headOffset => by
      simp only [scalarEventWrites, List.length_cons]
      rw [scalarEventWrites_length entries (headOffset + eventHeadWordSize entry.1.ty)]

theorem evalIRExprs_length :
    ∀ (es : List YulExpr) (state : IRState) (values : List Nat),
      evalIRExprs state es = some values → values.length = es.length
  | [], _, values, hvals => by
      have : values = [] := by simpa [evalIRExprs] using hvals.symm
      simp [this]
  | e :: es, state, values, hvals => by
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
              simp [evalIRExprs_length es state vs hvs]

/-- Running the compiled unindexed-store block from `__evt_ptr = p` leaves
memory holding the slice-1 ABI head block of the unindexed arguments. -/
theorem scalarEventUnindexedStores_exec
    (unindexed : List (EventParam × Expr × YulExpr)) (values : List Nat)
    (fuel : Nat) (state : IRState) (p : Nat)
    (hptr : state.getVar "__evt_ptr" = some p)
    (hsupport : ∀ entry ∈ unindexed, eventParamScalarCompileSupported entry.1.ty = true)
    (hsize : ∀ entry ∈ unindexed, eventHeadWordSize entry.1.ty = 32)
    (hmi : MemInsensitiveExprs (unindexed.map (fun entry => entry.2.2)))
    (hvals : evalIRExprs state (unindexed.map (fun entry => entry.2.2)) = some values) :
    execIRStmts (unindexed.length + fuel + 1) state
        (scalarEventUnindexedStores unindexed) =
      .continue { state with
        memory := applyWrites state.memory
          (abiBlockWrites p (abiEncodeScalarHeads (eventAbiScalarArgs unindexed values))) } := by
  have hlen : values.length = unindexed.length :=
    (evalIRExprs_length _ state values hvals).trans (by simp)
  have hheads : (abiEncodeScalarHeads (eventAbiScalarArgs unindexed values)).length =
      unindexed.length := by
    simp [abiEncodeScalarHeads, eventAbiScalarArgs, hlen]
  have hwritesVals : evalIRExprs state ((scalarEventWrites unindexed 0).map (·.2)) =
      some (abiEncodeScalarHeads (eventAbiScalarArgs unindexed values)) := by
    rw [scalarEventWrites_snd]
    exact evalIRExprs_normalizeEventWord_map unindexed values state hsupport hvals
  have hblock := execIRStmts_mstore_ptr_expr_block "__evt_ptr" p (scalarEventWrites unindexed 0)
    (abiEncodeScalarHeads (eventAbiScalarArgs unindexed values)) fuel state hptr
    (scalarEventWrites_memInsensitive unindexed 0 hmi) hwritesVals
  have hwritesEq :
      ((scalarEventWrites unindexed 0).map
          (fun ov => (p + ov.1) % Compiler.Constants.evmModulus)).zip
            (abiEncodeScalarHeads (eventAbiScalarArgs unindexed values)) =
        abiBlockWrites p (abiEncodeScalarHeads (eventAbiScalarArgs unindexed values)) := by
    rw [abiBlockWrites_eq_zip, hheads]
    congr 1
    rw [show ((scalarEventWrites unindexed 0).map
        (fun ov => (p + ov.1) % Compiler.Constants.evmModulus)) =
      ((scalarEventWrites unindexed 0).map (·.1)).map
        (fun o => (p + o) % Compiler.Constants.evmModulus) from by
        rw [List.map_map]; rfl]
    rw [scalarEventWrites_fst unindexed 0 hsize, List.map_map]
    apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply, Nat.zero_add]
  rw [show scalarEventUnindexedStores unindexed =
      (scalarEventWrites unindexed 0).map (fun ov =>
        YulStmt.exprStmt (.call "mstore"
          [.call "add" [.ident "__evt_ptr", .lit ov.1], ov.2])) from
      scalarEventUnindexedStoresFrom_shape unindexed 0,
    show unindexed.length + fuel + 1 = (scalarEventWrites unindexed 0).length + fuel + 1 from by
      rw [scalarEventWrites_length],
    hblock, hwritesEq]

/-- The log data payload of the compiled scalar `emit` block is exactly the
slice-1 ABI encoding of the unindexed arguments. -/
theorem scalarEventUnindexedStores_logDataWords
    (unindexed : List (EventParam × Expr × YulExpr)) (values : List Nat)
    (fuel : Nat) (state : IRState) (p : Nat) (final : IRState)
    (hptr : state.getVar "__evt_ptr" = some p)
    (hsupport : ∀ entry ∈ unindexed, eventParamScalarCompileSupported entry.1.ty = true)
    (hsize : ∀ entry ∈ unindexed, eventHeadWordSize entry.1.ty = 32)
    (hmi : MemInsensitiveExprs (unindexed.map (fun entry => entry.2.2)))
    (hvals : evalIRExprs state (unindexed.map (fun entry => entry.2.2)) = some values)
    (hfit : p + 32 * unindexed.length ≤ Compiler.Constants.evmModulus)
    (hexec : execIRStmts (unindexed.length + fuel + 1) state
      (scalarEventUnindexedStores unindexed) = .continue final) :
    yulLogDataWords final.memory p (32 * unindexed.length) =
      abiEncodeScalarHeads (eventAbiScalarArgs unindexed values) := by
  have hlen : values.length = unindexed.length :=
    (evalIRExprs_length _ state values hvals).trans (by simp)
  have hheads : (abiEncodeScalarHeads (eventAbiScalarArgs unindexed values)).length =
      unindexed.length := by
    simp [abiEncodeScalarHeads, eventAbiScalarArgs, hlen]
  have hrun := scalarEventUnindexedStores_exec unindexed values fuel state p hptr hsupport
    hsize hmi hvals
  rw [hexec] at hrun
  injection hrun with hstate
  have hmem : final.memory = applyWrites state.memory
      (abiBlockWrites p (abiEncodeScalarHeads (eventAbiScalarArgs unindexed values))) := by
    rw [hstate]
  rw [hmem, ← hheads]
  exact yulLogDataWords_abiBlockWrites _ p state.memory (by rw [hheads]; exact hfit)

/-! ## Threading through the LOG opcodes -/

/-- The unindexed head area of a scalar event is one 32-byte word per
argument, so the `logN` data size operand is `32 * n`. -/
theorem eventUnindexedHeadSize_scalar :
    ∀ (unindexed : List (EventParam × Expr × YulExpr)),
      (∀ entry ∈ unindexed, eventHeadWordSize entry.1.ty = 32) →
      eventUnindexedHeadSize unindexed = 32 * unindexed.length := by
  intro unindexed hsize
  have hmap : unindexed.map (fun entry => eventHeadWordSize entry.1.ty) =
      List.replicate unindexed.length 32 := by
    induction unindexed with
    | nil => rfl
    | cons entry rest ih =>
        simp only [List.map_cons, List.length_cons, List.replicate_succ,
          hsize entry (by simp), List.cons.injEq, true_and]
        exact ih (fun e he => hsize e (by simp [he]))
  have hfold : ∀ (n start : Nat),
      (List.replicate n 32).foldl (· + ·) start = start + 32 * n := by
    intro n
    induction n with
    | zero => intro start; simp
    | succ n ih =>
        intro start
        rw [List.replicate_succ, List.foldl_cons, ih]
        omega
  simp only [eventUnindexedHeadSize]
  rw [show (unindexed.map fun entry => eventHeadWordSize entry.1.ty) =
    unindexed.map (fun entry => eventHeadWordSize entry.1.ty) from rfl, hmap, hfold]
  simp

/-- The compiled `logN` statement records `topic0` followed by the evaluated
indexed topics, over the data window `[__evt_ptr, __evt_ptr + dataSize)`. -/
theorem eventLogStmt_exec
    (indexed : List (EventParam × Expr × YulExpr)) (topics : List Nat)
    (state : IRState) (p dataSize topic0 fuel : Nat)
    (hptr : state.getVar "__evt_ptr" = some p)
    (htopic0 : state.getVar "__evt_topic0" = some topic0)
    (hindexed : indexed.length ≤ 3)
    (htopics : evalIRExprs state ((scalarEventIndexedTopicParts indexed).map (·.2)) =
      some topics) :
    execIRStmt (fuel + 1) state
        (YulStmt.exprStmt (YulExpr.call (eventLogFunction indexed.length)
          (eventLogArgs (YulExpr.lit dataSize) (scalarEventIndexedTopicParts indexed)))) =
      .continue (state.appendYulLog p dataSize (topic0 :: topics)) := by
  rcases indexed with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩
  · obtain rfl : topics = [] := by
      simpa [scalarEventIndexedTopicParts, evalIRExprs] using htopics.symm
    simp [execIRStmt, isYulLogName, eventLogFunction, eventLogArgs,
      scalarEventIndexedTopicParts, evalIRExprs, evalIRExpr, hptr, htopic0]
  · simp only [scalarEventIndexedTopicParts, List.map_cons, List.map_nil,
      evalIRExprs, Option.bind_eq_bind] at htopics
    cases ha : evalIRExpr state (normalizeEventWord a.1.ty a.2.2) with
    | none => rw [ha] at htopics; simp at htopics
    | some ta =>
        rw [ha] at htopics
        obtain rfl : topics = [ta] := by
          simpa [evalIRExprs] using htopics.symm
        simp [execIRStmt, isYulLogName, eventLogFunction, eventLogArgs,
          scalarEventIndexedTopicParts, evalIRExprs, evalIRExpr, hptr, htopic0, ha]
  · simp only [scalarEventIndexedTopicParts, List.map_cons, List.map_nil,
      evalIRExprs, Option.bind_eq_bind] at htopics
    cases ha : evalIRExpr state (normalizeEventWord a.1.ty a.2.2) with
    | none => rw [ha] at htopics; simp at htopics
    | some ta =>
        cases hb : evalIRExpr state (normalizeEventWord b.1.ty b.2.2) with
        | none => rw [ha, hb] at htopics; simp at htopics
        | some tb =>
            rw [ha, hb] at htopics
            obtain rfl : topics = [ta, tb] := by
              simpa [evalIRExprs] using htopics.symm
            simp [execIRStmt, isYulLogName, eventLogFunction, eventLogArgs,
              scalarEventIndexedTopicParts, evalIRExprs, evalIRExpr, hptr, htopic0, ha, hb]
  · simp only [scalarEventIndexedTopicParts, List.map_cons, List.map_nil,
      evalIRExprs, Option.bind_eq_bind] at htopics
    cases ha : evalIRExpr state (normalizeEventWord a.1.ty a.2.2) with
    | none => rw [ha] at htopics; simp at htopics
    | some ta =>
        cases hb : evalIRExpr state (normalizeEventWord b.1.ty b.2.2) with
        | none => rw [ha, hb] at htopics; simp at htopics
        | some tb =>
            cases hc : evalIRExpr state (normalizeEventWord c.1.ty c.2.2) with
            | none => rw [ha, hb, hc] at htopics; simp at htopics
            | some tc =>
                rw [ha, hb, hc] at htopics
                obtain rfl : topics = [ta, tb, tc] := by
                  simpa [evalIRExprs] using htopics.symm
                simp [execIRStmt, isYulLogName, eventLogFunction, eventLogArgs,
                  scalarEventIndexedTopicParts, evalIRExprs, evalIRExpr, hptr, htopic0,
                  ha, hb, hc]
  · simp at hindexed

/-- **Slice-3 LOG threading.** Running the compiled scalar `emit` payload —
the unindexed `mstore` block followed by the `logN` instruction — appends
exactly one observable whose topics are `topic0` followed by the ABI encoding
of the indexed arguments, and whose data is the ABI encoding of the unindexed
arguments. -/
theorem scalarEmitPayload_log_observable
    (indexed unindexed : List (EventParam × Expr × YulExpr))
    (indexedValues unindexedValues : List Nat)
    (state final : IRState) (p topic0 fuel : Nat)
    (hptr : state.getVar "__evt_ptr" = some p)
    (htopic0 : state.getVar "__evt_topic0" = some topic0)
    (hindexedLen : indexed.length ≤ 3)
    (hsupportIndexed :
      ∀ entry ∈ indexed, eventParamScalarCompileSupported entry.1.ty = true)
    (hsupportUnindexed :
      ∀ entry ∈ unindexed, eventParamScalarCompileSupported entry.1.ty = true)
    (hsizeUnindexed : ∀ entry ∈ unindexed, eventHeadWordSize entry.1.ty = 32)
    (hmiIndexed : MemInsensitiveExprs (indexed.map (fun entry => entry.2.2)))
    (hmiUnindexed : MemInsensitiveExprs (unindexed.map (fun entry => entry.2.2)))
    (hindexedVals :
      evalIRExprs state (indexed.map (fun entry => entry.2.2)) = some indexedValues)
    (hunindexedVals :
      evalIRExprs state (unindexed.map (fun entry => entry.2.2)) = some unindexedValues)
    (hfit : p + 32 * unindexed.length ≤ Compiler.Constants.evmModulus)
    (hexec : execIRStmts (unindexed.length + fuel + 2) state
      (scalarEventUnindexedStores unindexed ++
        [YulStmt.exprStmt (YulExpr.call (eventLogFunction indexed.length)
          (eventLogArgs (YulExpr.lit (eventUnindexedHeadSize unindexed))
            (scalarEventIndexedTopicParts indexed)))]) = .continue final) :
    final.events = state.events ++
      [(topic0 :: abiEncodeScalarHeads (eventAbiScalarArgs indexed indexedValues)) ++
        abiEncodeScalarHeads (eventAbiScalarArgs unindexed unindexedValues)] := by
  have hstoresLen : (scalarEventUnindexedStores unindexed).length = unindexed.length := by
    rw [show scalarEventUnindexedStores unindexed =
      (scalarEventWrites unindexed 0).map (fun ov =>
        YulStmt.exprStmt (.call "mstore"
          [.call "add" [.ident "__evt_ptr", .lit ov.1], ov.2])) from
      scalarEventUnindexedStoresFrom_shape unindexed 0]
    simp
  have hrunStores : execIRStmts (unindexed.length + fuel + 2) state
      (scalarEventUnindexedStores unindexed) =
        .continue { state with
          memory := applyWrites state.memory
            (abiBlockWrites p
              (abiEncodeScalarHeads
                (eventAbiScalarArgs unindexed unindexedValues))) } :=
    scalarEventUnindexedStores_exec unindexed unindexedValues (fuel + 1) state p hptr
      hsupportUnindexed hsizeUnindexed hmiUnindexed hunindexedVals
  obtain ⟨mid, hmid⟩ : ∃ m : IRState, m = { state with
      memory := applyWrites state.memory
        (abiBlockWrites p
          (abiEncodeScalarHeads (eventAbiScalarArgs unindexed unindexedValues))) } := ⟨_, rfl⟩
  rw [← hmid] at hrunStores
  -- Data words: the ABI block written by the stores, read back at the pointer.
  have hdata : yulLogDataWords mid.memory p (eventUnindexedHeadSize unindexed) =
      abiEncodeScalarHeads (eventAbiScalarArgs unindexed unindexedValues) := by
    rw [eventUnindexedHeadSize_scalar unindexed hsizeUnindexed]
    exact scalarEventUnindexedStores_logDataWords unindexed unindexedValues (fuel + 1) state p
      mid hptr hsupportUnindexed hsizeUnindexed hmiUnindexed hunindexedVals hfit hrunStores
  -- Topics: evaluated in `mid`, which differs from `state` only in memory.
  have hindexedValsMid :
      evalIRExprs mid (indexed.map (fun entry => entry.2.2)) = some indexedValues := by
    rw [hmid, evalIRExprs_mem_insensitive _ hmiIndexed state _]
    exact hindexedVals
  have htopics := scalarEventIndexedTopicParts_eval indexed indexedValues mid
    hsupportIndexed hindexedValsMid
  have hptrMid : mid.getVar "__evt_ptr" = some p := by rw [hmid]; exact hptr
  have htopic0Mid : mid.getVar "__evt_topic0" = some topic0 := by rw [hmid]; exact htopic0
  have hrunLog := eventLogStmt_exec indexed
    (abiEncodeScalarHeads (eventAbiScalarArgs indexed indexedValues)) mid p
    (eventUnindexedHeadSize unindexed) topic0 fuel
    hptrMid htopic0Mid hindexedLen htopics
  rw [execIRStmts_append_continue _ (scalarEventUnindexedStores unindexed)
      (unindexed.length + fuel + 2) state mid hrunStores,
    hstoresLen,
    show unindexed.length + fuel + 2 - unindexed.length = fuel + 2 from by omega,
    show fuel + 2 = (fuel + 1) + 1 from rfl] at hexec
  rw [show execIRStmts ((fuel + 1) + 1) mid
      [YulStmt.exprStmt (YulExpr.call (eventLogFunction indexed.length)
        (eventLogArgs (YulExpr.lit (eventUnindexedHeadSize unindexed))
          (scalarEventIndexedTopicParts indexed)))] =
      (match execIRStmt (fuel + 1) mid
          (YulStmt.exprStmt (YulExpr.call (eventLogFunction indexed.length)
            (eventLogArgs (YulExpr.lit (eventUnindexedHeadSize unindexed))
              (scalarEventIndexedTopicParts indexed)))) with
        | .continue s => execIRStmts (fuel + 1) s []
        | .return v s => .return v s
        | .stop s => .stop s
        | .revert s => .revert s) from rfl,
    hrunLog] at hexec
  simp only [execIRStmts] at hexec
  injection hexec with hfinal
  have hevents : mid.events = state.events := by rw [hmid]
  rw [← hfinal]
  simp only [IRState.appendYulLog_events, encodeYulLogEvent, hdata, hevents]

end Compiler.Proofs.AbiEventObservable

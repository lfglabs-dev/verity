import Verity.Core.Model.Denote

/-!
# Denotation coverage certificate for Solidity slices

The Solidity-slice importer (`Compiler/SolidityImport`) emits only a small,
explicitly listed fragment of the deep `CompilationModel`.  This module is the
machine-checked side of that contract:

* `exprCovered` / `executableStmtCovered` / `executableStmtListCovered` are the decidable
  whitelists of `Expr` / `Stmt` constructors the importer may emit.  A
  constructor is whitelisted only when `Compiler.CompilationModel.Denote`
  gives it a dedicated arm — never the catch-all `none` / `.revert` fallback.
* For every whitelisted constructor, an `*_arm` theorem pins the exact
  denotation equation by `rfl`.  If the corresponding `Denote` arm is removed
  or its meaning changes, the pin stops compiling, so the whitelist cannot
  silently drift away from the semantics.

The importer refuses to register a slice whose body fails `executableStmtListCovered`,
and registers the passing verdict as a theorem proved by `decide`.

This predicate is deliberately *not* `SupportedFunction`: that predicate is
the Denote↔IR raccord boundary (it rejects `panic`, `returnValues`, ...),
while this one characterizes the compiler-free `Denote` execution path only.
-/

namespace Compiler.CompilationModel.SolidityImport

open Compiler.CompilationModel
open Compiler.CompilationModel.Denote

/-! ## Expression whitelist -/

/-- Expressions the slice importer may emit, mirrored against
`Denote.evalExpr`.  Every `true` case has a dedicated arm there; every other
constructor (including `paramDynamicMember*`, `paramDynamicStaticComposite`,
`mulDiv512*`, raw calls, `internalCall`, `intrinsic`, `forkIfAtLeast`, ADTs,
`arrayElementWord`, `mappingChain`, and any future constructor) is rejected. -/
def exprCovered : Expr → Bool
  | .literal _ => true
  | .param _ => true
  | .storage _ => true
  | .localVar _ => true
  | .blockTimestamp => true
  | .blockNumber | .chainid | .caller | .contractAddress => true
  | .structMember _ key _ => exprCovered key
  | .structMember2 _ key1 key2 _ => exprCovered key1 && exprCovered key2
  | .add a b | .sub a b | .mul a b | .div a b
  | .lt a b | .gt a b | .le a b | .ge a b | .eq a b
  | .bitAnd a b | .bitXor a b => exprCovered a && exprCovered b
  | .logicalNot a => exprCovered a
  | _ => false

/-- Every expression in the list is covered. -/
def exprListCovered : List Expr → Bool
  | [] => true
  | e :: es => exprCovered e && exprListCovered es

/-! ## Statement whitelist -/

mutual

/-- Read-only statements, mirrored against `Denote.execStmt`.
Multi-value returns are covered: `Stmt.returnValues` records the resolved words
in `DenoteState.observedReturnWords` and finishes with `.stop`. -/
def stmtCovered : Stmt → Bool
  | .letVar _ value => exprCovered value
  | .assignVar _ value => exprCovered value
  | .ite cond thenBranch elseBranch =>
      exprCovered cond && stmtListCovered thenBranch && stmtListCovered elseBranch
  | .panic _ => true
  | .require condition _ => exprCovered condition
  | .requireError condition _ args => exprCovered condition && exprListCovered args
  | .returnValues args => exprListCovered args
  | _ => false

/-- Every statement in the list is covered. -/
def stmtListCovered : List Stmt → Bool
  | [] => true
  | s :: ss => stmtCovered s && stmtListCovered ss

end

/- Executable coverage includes writes; `stmtCovered` retains its read-only
meaning and its original world-preservation theorems. -/
mutual
  def executableStmtCovered : Stmt → Bool
    | .stop => true
    | .setStorage _ value => exprCovered value
    | .setStructMember _ key _ value => exprCovered key && exprCovered value
    | .setStructMember2 _ key1 key2 _ value =>
        exprCovered key1 && exprCovered key2 && exprCovered value
    | .ite condition yes no =>
        exprCovered condition && executableStmtListCovered yes && executableStmtListCovered no
    | statement => stmtCovered statement
  def executableStmtListCovered : List Stmt → Bool
    | [] => true
    | head :: tail => executableStmtCovered head && executableStmtListCovered tail
end

theorem execStmt_stop_arm (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) :
    execStmt oracle fields state .stop =
      .stop { state with observedStop := true } := rfl

theorem execStmt_setStorage_arm (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (name : String) (value : Expr) :
    execStmt oracle fields state (.setStorage name value) =
      (match findFieldWriteSlots fields name, evalExpr oracle fields state value with
       | some slots, some resolved =>
           .continue { state with world := writeUintFieldSlots fields name state.world slots resolved }
       | _, _ => .revert) := rfl

theorem execStmt_require_arm (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (condition : Expr) (message : String) :
    execStmt oracle fields state (.require condition message) =
      (match evalExpr oracle fields state condition with
       | some value => if value != 0 then .continue state
           else .revertWithData (errorStringBytes message)
       | none => .revert) := rfl

theorem execStmt_requireError_arm (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (condition : Expr) (name : String) (args : List Expr) :
    execStmt oracle fields state (.requireError condition name args) =
      (match evalExpr oracle fields state condition with
       | some value => if value != 0 then .continue state else
           match evalExprList oracle fields state args with
           | none => .revert
           | some values => match customErrorBytes oracle state.errors name values with
               | some bytes => .revertWithData bytes
               | none => .revert
       | none => .revert) := rfl

/-! ## Arm pins: expressions

Each pin restates the dedicated `Denote.evalExpr` arm.  They are proved by
`rfl`, so deleting the arm (falling back to the catch-all `none`) or changing
the arm's meaning breaks the build here. -/

theorem evalExpr_storage_arm (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (name : String) :
    evalExpr oracle fields state (.storage name) =
      (match findFieldWithResolvedSlot fields name with
       | some (field, slot) =>
           let rawWord := (readFieldWord state.world field slot).val
           match field.packedBits with
           | none => some rawWord
           | some packed => some (Verity.Core.Uint256.and
               (Verity.Core.Uint256.shr packed.offset rawWord) (packedMaskNat packed)).val
       | none => none) := rfl

theorem evalExpr_literal_arm (oracle : DenoteOracle) (fields : List Field)
    (s : DenoteState) (n : Nat) :
    evalExpr oracle fields s (.literal n) = some (wordNormalize n) := rfl

theorem evalExpr_param_arm (oracle : DenoteOracle) (fields : List Field)
    (s : DenoteState) (name : String) :
    evalExpr oracle fields s (.param name) = some (lookupValue s.bindings name) := rfl

theorem evalExpr_localVar_arm (oracle : DenoteOracle) (fields : List Field)
    (s : DenoteState) (name : String) :
    evalExpr oracle fields s (.localVar name) = some (lookupValue s.bindings name) := rfl

theorem evalExpr_blockTimestamp_arm (oracle : DenoteOracle) (fields : List Field)
    (s : DenoteState) :
    evalExpr oracle fields s .blockTimestamp = some s.world.blockTimestamp.val := rfl

theorem evalExpr_blockNumber_arm (oracle : DenoteOracle) (fields : List Field)
    (s : DenoteState) :
    evalExpr oracle fields s .blockNumber = some s.world.blockNumber.val := rfl

theorem evalExpr_chainid_arm (oracle : DenoteOracle) (fields : List Field)
    (s : DenoteState) :
    evalExpr oracle fields s .chainid = some s.world.chainId.val := rfl

theorem evalExpr_caller_arm (oracle : DenoteOracle) (fields : List Field)
    (s : DenoteState) :
    evalExpr oracle fields s .caller = some s.world.sender.val := rfl

theorem evalExpr_contractAddress_arm (oracle : DenoteOracle) (fields : List Field)
    (s : DenoteState) :
    evalExpr oracle fields s .contractAddress = some s.world.thisAddress.val := rfl

theorem evalExpr_add_arm (oracle : DenoteOracle) (fields : List Field)
    (s : DenoteState) (a b : Expr) :
    evalExpr oracle fields s (.add a b) =
      (do
        let lhs : Verity.Core.Uint256 := ← evalExpr oracle fields s a
        let rhs : Verity.Core.Uint256 := ← evalExpr oracle fields s b
        pure (lhs + rhs).val) := rfl

theorem evalExpr_sub_arm (oracle : DenoteOracle) (fields : List Field)
    (s : DenoteState) (a b : Expr) :
    evalExpr oracle fields s (.sub a b) =
      (do
        let lhs : Verity.Core.Uint256 := ← evalExpr oracle fields s a
        let rhs : Verity.Core.Uint256 := ← evalExpr oracle fields s b
        pure (lhs - rhs).val) := rfl

theorem evalExpr_mul_arm (oracle : DenoteOracle) (fields : List Field)
    (s : DenoteState) (a b : Expr) :
    evalExpr oracle fields s (.mul a b) =
      (do
        let lhs : Verity.Core.Uint256 := ← evalExpr oracle fields s a
        let rhs : Verity.Core.Uint256 := ← evalExpr oracle fields s b
        pure (lhs * rhs).val) := rfl

theorem evalExpr_div_arm (oracle : DenoteOracle) (fields : List Field)
    (s : DenoteState) (a b : Expr) :
    evalExpr oracle fields s (.div a b) =
      (do
        let lhs : Verity.Core.Uint256 := ← evalExpr oracle fields s a
        let rhs : Verity.Core.Uint256 := ← evalExpr oracle fields s b
        pure (lhs / rhs).val) := rfl

theorem evalExpr_lt_arm (oracle : DenoteOracle) (fields : List Field)
    (s : DenoteState) (a b : Expr) :
    evalExpr oracle fields s (.lt a b) =
      (do
        let lhs ← evalExpr oracle fields s a
        let rhs ← evalExpr oracle fields s b
        pure (boolWord (decide (lhs < rhs)))) := rfl

theorem evalExpr_gt_arm (oracle : DenoteOracle) (fields : List Field)
    (s : DenoteState) (a b : Expr) :
    evalExpr oracle fields s (.gt a b) =
      (do
        let lhs ← evalExpr oracle fields s a
        let rhs ← evalExpr oracle fields s b
        pure (boolWord (decide (rhs < lhs)))) := rfl

theorem evalExpr_le_arm (oracle : DenoteOracle) (fields : List Field)
    (s : DenoteState) (a b : Expr) :
    evalExpr oracle fields s (.le a b) =
      (do
        let lhs ← evalExpr oracle fields s a
        let rhs ← evalExpr oracle fields s b
        pure (boolWord (decide (lhs ≤ rhs)))) := rfl

theorem evalExpr_ge_arm (oracle : DenoteOracle) (fields : List Field)
    (s : DenoteState) (a b : Expr) :
    evalExpr oracle fields s (.ge a b) =
      (do
        let lhs ← evalExpr oracle fields s a
        let rhs ← evalExpr oracle fields s b
        pure (boolWord (decide (rhs ≤ lhs)))) := rfl

theorem evalExpr_eq_arm (oracle : DenoteOracle) (fields : List Field)
    (s : DenoteState) (a b : Expr) :
    evalExpr oracle fields s (.eq a b) =
      (do
        let lhs ← evalExpr oracle fields s a
        let rhs ← evalExpr oracle fields s b
        pure (boolWord (decide (lhs = rhs)))) := rfl

theorem evalExpr_bitAnd_arm (oracle : DenoteOracle) (fields : List Field)
    (s : DenoteState) (a b : Expr) :
    evalExpr oracle fields s (.bitAnd a b) =
      (do
        let lhs ← evalExpr oracle fields s a
        let rhs ← evalExpr oracle fields s b
        pure (Verity.Core.Uint256.and lhs rhs).val) := rfl

theorem evalExpr_bitXor_arm (oracle : DenoteOracle) (fields : List Field)
    (s : DenoteState) (a b : Expr) :
    evalExpr oracle fields s (.bitXor a b) =
      (do
        let lhs ← evalExpr oracle fields s a
        let rhs ← evalExpr oracle fields s b
        pure (Verity.Core.Uint256.xor lhs rhs).val) := rfl

/-- `Expr.logicalOr` and `Expr.logicalAnd` are eager in `evalExpr`, so they are
not slice constructors. `Expr.paramDynamicHeadWord` is an ABI-head read and is
excluded from this certificate; the slice does not claim public ABI decoding. -/
theorem evalExpr_logicalNot_arm (oracle : DenoteOracle) (fields : List Field)
    (s : DenoteState) (a : Expr) :
    evalExpr oracle fields s (.logicalNot a) =
      (do
        let value ← evalExpr oracle fields s a
        pure (boolWord (decide (value = 0)))) := rfl

/-- Struct member reads through a single mapping key are denoted, including
packed sub-word slicing from the field's declared `StructMember` metadata. -/
theorem evalExpr_structMember_arm (oracle : DenoteOracle) (fields : List Field)
    (s : DenoteState) (field : String) (key : Expr) (memberName : String) :
    evalExpr oracle fields s (.structMember field key memberName) =
      (do
        let keyVal ← evalExpr oracle fields s key
        match findFieldWithResolvedSlot fields field, findStructMembers fields field with
        | some (fieldInfo, slot), some members =>
            match findStructMember members memberName with
            | some member =>
                let targetSlot := wordNormalize
                  (oracle.mappingSlot slot keyVal + member.wordOffset)
                let rawWord := (readFieldWord s.world fieldInfo targetSlot).val
                match member.packed with
                | none => some rawWord
                | some packed =>
                    some (Verity.Core.Uint256.and
                      (Verity.Core.Uint256.shr packed.offset rawWord)
                      (packedMaskNat packed)).val
            | none => none
        | _, _ => none) := rfl

/-- Struct member reads through two mapping keys are denoted. -/
theorem evalExpr_structMember2_arm (oracle : DenoteOracle) (fields : List Field)
    (s : DenoteState) (field : String) (key1 key2 : Expr) (memberName : String) :
    evalExpr oracle fields s (.structMember2 field key1 key2 memberName) =
      (do
        let key1Val ← evalExpr oracle fields s key1
        let key2Val ← evalExpr oracle fields s key2
        match findFieldWithResolvedSlot fields field, findStructMembers fields field with
        | some (fieldInfo, slot), some members =>
            match findStructMember members memberName with
            | some member =>
                let innerSlot := oracle.mappingSlot slot key1Val
                let outerSlot := oracle.mappingSlot innerSlot key2Val
                let targetSlot := wordNormalize (outerSlot + member.wordOffset)
                let rawWord := (readFieldWord s.world fieldInfo targetSlot).val
                match member.packed with
                | none => some rawWord
                | some packed =>
                    some (Verity.Core.Uint256.and
                      (Verity.Core.Uint256.shr packed.offset rawWord)
                      (packedMaskNat packed)).val
            | none => none
        | _, _ => none) := rfl

/-! ## Arm pins: statements -/

theorem execStmt_setStructMember_arm (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (fieldName memberName : String) (key value : Expr) :
    execStmt oracle fields state (.setStructMember fieldName key memberName value) =
      (
        match findFieldWriteSlots fields fieldName,
            findStructMembers fields fieldName,
            evalExpr oracle fields state key,
            evalExpr oracle fields state value with
        | some slots@(_ :: _), some members, some resolvedKey, some resolved =>
            match findStructMember members memberName with
            | some { wordOffset := wordOffset, packed := none, .. } =>
                .continue
                  { state with
                      world := writeAddressKeyedMappingWordFieldSlots
                        oracle fields fieldName state.world slots resolvedKey wordOffset resolved }
            | some { wordOffset := wordOffset, packed := some packed, .. } =>
                if packedBitsValid packed then
                  .continue
                    { state with
                        world := writeAddressKeyedMappingPackedWordFieldSlots oracle
                          fields fieldName state.world slots resolvedKey wordOffset packed resolved }
                else
                  .revert
            | _ => .revert
        | _, _, _, _ => .revert) := rfl

theorem execStmt_setStructMember2_arm (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (fieldName memberName : String) (key1 key2 value : Expr) :
    execStmt oracle fields state (.setStructMember2 fieldName key1 key2 memberName value) =
      (
        match findFieldWriteSlots fields fieldName,
            findStructMembers fields fieldName,
            evalExpr oracle fields state key1,
            evalExpr oracle fields state key2,
            evalExpr oracle fields state value with
        | some slots@(_ :: _), some members, some resolvedKey1, some resolvedKey2, some resolved =>
            match findStructMember members memberName with
            | some { wordOffset := wordOffset, packed := none, .. } =>
                .continue
                  { state with
                      world := writeAddressKeyedMapping2WordFieldSlots
                        oracle fields fieldName state.world slots resolvedKey1 resolvedKey2 wordOffset resolved }
            | some { wordOffset := wordOffset, packed := some packed, .. } =>
                if packedBitsValid packed then
                  .continue
                    { state with
                        world := writeAddressKeyedMapping2PackedWordFieldSlots oracle
                          fields fieldName state.world slots resolvedKey1 resolvedKey2 wordOffset packed resolved }
                else
                  .revert
            | _ => .revert
        | _, _, _, _, _ => .revert) := rfl



theorem execStmt_letVar_arm (oracle : DenoteOracle) (fields : List Field)
    (s : DenoteState) (name : String) (value : Expr) :
    execStmt oracle fields s (.letVar name value) =
      (match evalExpr oracle fields s value with
      | some resolved => .continue { s with bindings := bindValue s.bindings name resolved }
      | none => .revert) := rfl

theorem execStmt_assignVar_arm (oracle : DenoteOracle) (fields : List Field)
    (s : DenoteState) (name : String) (value : Expr) :
    execStmt oracle fields s (.assignVar name value) =
      (match evalExpr oracle fields s value with
      | some resolved => .continue { s with bindings := bindValue s.bindings name resolved }
      | none => .revert) := rfl

/-- `Stmt.ite` is lazy in the denotation: only the taken branch executes, so
guards inside an untaken branch cannot introduce a spurious revert. -/
theorem execStmt_ite_arm (oracle : DenoteOracle) (fields : List Field)
    (s : DenoteState) (cond : Expr) (thenBranch elseBranch : List Stmt) :
    execStmt oracle fields s (.ite cond thenBranch elseBranch) =
      (match evalExpr oracle fields s cond with
      | some condVal =>
          if condVal != 0 then
            execStmtList oracle fields s thenBranch
          else
            execStmtList oracle fields s elseBranch
      | none => .revert) := rfl

theorem execStmt_panic_arm (oracle : DenoteOracle) (fields : List Field)
    (s : DenoteState) (code : Verity.Core.PanicCode) :
    execStmt oracle fields s (.panic code) = .revertWithData (panicBytes code.toNat) := rfl

theorem execStmtList_panic_stops (oracle : DenoteOracle) (fields : List Field)
    (s : DenoteState) (code : Verity.Core.PanicCode) (rest : List Stmt) :
    execStmtList oracle fields s (.panic code :: rest) =
      .revertWithData (panicBytes code.toNat) := rfl

theorem execForEachLoop_preserves_revert_bytes (s : DenoteState)
    (name : String) (index remaining : Nat) (data : List UInt8) :
    execForEachLoop name (fun _ => .revertWithData data) s index (remaining + 1) =
      .revertWithData data := rfl

/-- Multi-value returns are denoted: the resolved words are recorded in source
order in `observedReturnWords` and execution stops. -/
theorem execStmt_returnValues_arm (oracle : DenoteOracle) (fields : List Field)
    (s : DenoteState) (args : List Expr) :
    execStmt oracle fields s (.returnValues args) =
      (match evalExprList oracle fields s args with
      | some resolved =>
          .stop { s with observedReturnWords := some (resolved.map wordNormalize), observedStop := false }
      | none => .revert) := rfl

/-- A `returnValues` statement terminates the statement list: later statements
(a `panic` here) never execute, and the recorded words survive in source
order. -/
theorem execStmtList_returnValues_stop_arm (oracle : DenoteOracle) (fields : List Field)
    (s : DenoteState) (a b : Nat) :
    execStmtList oracle fields s
        [.returnValues [.literal a, .literal b], .panic .arithmeticOverflow] =
      .stop { s with observedReturnWords := some [wordNormalize a, wordNormalize b], observedStop := false } := by
  simp [execStmtList, execStmt, evalExprList, evalExpr, wordNormalize]

/-- Every function body of a model is in the slice whitelist. -/
def modelImportCovered (model : CompilationModel) : Bool :=
  model.functions.all fun fn => executableStmtListCovered fn.body

/-- Level A: run a body on scalar bindings. Arguments are Solidity words, not
ABI-decoded calldata. `some` is the source-order return list of a successful
run; `none` is a revert. The panic payload is not returned. -/
def denoteScalarBody
    (oracle : DenoteOracle) (fields : List Field)
    (world : Verity.ContractState) (timestamp : Nat)
    (bindings : Env) (body : List Stmt) : Option (List Nat) :=
  match execStmtList oracle fields
      { world := { world with blockTimestamp := Verity.Core.Uint256.ofNat timestamp }
        bindings := bindings } body with
  | .stop state | .continue state | .return _ state => state.observedReturnWords
  | .revert | .revertWithData _ => none

private theorem boolAnd2 {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all

private theorem boolAnd3 {a b c : Bool} (h : (a && b && c) = true) :
    b = true ∧ c = true := by
  cases a <;> cases b <;> cases c <;> simp_all

/-- `next.world = origin.world` whenever execution continues, stops, or returns.
A revert has no successor state. -/
def preservesWorld (origin : DenoteState) : StmtOutcome → Prop
  | .continue next | .stop next | .return _ next => next.world = origin.world
  | .revert | .revertWithData _ => True

mutual

theorem execStmt_slice_world
    (oracle : DenoteOracle) (fields : List Field) (state : DenoteState) (stmt : Stmt)
    (h : stmtCovered stmt = true) :
    preservesWorld state (execStmt oracle fields state stmt) := by
  unfold stmtCovered at h
  split at h
  · rename_i name value
    cases hEval : evalExpr oracle fields state value <;>
      simp [preservesWorld, execStmt, hEval]
  · rename_i name value
    cases hEval : evalExpr oracle fields state value <;>
      simp [preservesWorld, execStmt, hEval]
  · rename_i cond thenBranch elseBranch
    have ⟨hthen, helse⟩ := boolAnd3 h
    cases hEval : evalExpr oracle fields state cond
    · simp [preservesWorld, execStmt, hEval]
    · rename_i bit
      by_cases hbit : (bit != 0) = true
      · simpa [preservesWorld, execStmt, hEval, hbit] using
          execStmtList_slice_world oracle fields state thenBranch hthen
      · have hnot : (bit != 0) = false := by simpa using hbit
        simpa [preservesWorld, execStmt, hEval, hnot] using
          execStmtList_slice_world oracle fields state elseBranch helse
  · simp [preservesWorld, execStmt]
  · rename_i condition message
    cases hEval : evalExpr oracle fields state condition with
    | none => simp [preservesWorld, execStmt, hEval]
    | some value =>
        by_cases hzero : value = 0 <;>
          simp [preservesWorld, execStmt, hEval, hzero]
  · rename_i condition name args
    cases hEval : evalExpr oracle fields state condition with
    | none => simp [preservesWorld, execStmt, hEval]
    | some value =>
        by_cases hzero : value = 0
        · cases hArgs : evalExprList oracle fields state args with
          | none => simp [preservesWorld, execStmt, hEval, hzero, hArgs]
          | some values =>
              cases hBytes : customErrorBytes oracle state.errors name values <;>
                simp [preservesWorld, execStmt, hEval, hzero, hArgs, hBytes]
        · simp [preservesWorld, execStmt, hEval, hzero]
  · rename_i args
    cases hEval : evalExprList oracle fields state args <;>
      simp [preservesWorld, execStmt, hEval]
  · cases h

theorem execStmtList_slice_world
    (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (stmts : List Stmt) (h : stmtListCovered stmts = true) :
    preservesWorld state (execStmtList oracle fields state stmts) := by
  match stmts with
  | [] => simp [preservesWorld, execStmtList]
  | stmt :: rest =>
      unfold stmtListCovered at h
      have ⟨hstmt, hrest⟩ := boolAnd2 h
      have hone := execStmt_slice_world oracle fields state stmt hstmt
      simp only [execStmtList]
      cases hExec : execStmt oracle fields state stmt
      · rename_i next
        have hworld : next.world = state.world := by
          simpa [preservesWorld, hExec] using hone
        have htail := execStmtList_slice_world oracle fields next rest hrest
        simpa [preservesWorld, hworld] using htail
      · rename_i next
        simpa [preservesWorld, hExec] using hone
      · rename_i value next
        simpa [preservesWorld, hExec] using hone
      · simp [preservesWorld]
      · simp [preservesWorld]

end

/-- A covered slice does not write persistent storage. A revert leaves the
caller's pre-state in place because `denoteScalarBody` discards it. -/
theorem execStmtList_slice_storageWords
    (oracle : DenoteOracle) (fields : List Field)
    (world : Verity.ContractState) (timestamp : Nat)
    (bindings : Env) (body : List Stmt)
    (h : stmtListCovered body = true) :
    let state : DenoteState :=
      { world := { world with blockTimestamp := Verity.Core.Uint256.ofNat timestamp }
        bindings := bindings }
    preservesWorld state (execStmtList oracle fields state body) := by
  intro state
  exact execStmtList_slice_world oracle fields state body h

end Compiler.CompilationModel.SolidityImport

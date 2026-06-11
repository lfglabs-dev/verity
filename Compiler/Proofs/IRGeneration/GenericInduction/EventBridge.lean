import Compiler.Proofs.IRGeneration.GenericInduction.Storage

set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

/-!
# Event emission semantic bridge

Proves that the compiled scalar `.emit` block (free-pointer scratch, signature
stores, `keccak256` topic0, unindexed head stores, `logN`) matches the source
event semantics, discharging `EventHeadStepSemanticBridgeCatalog.bridge`.
-/

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.CompilationModel
open Compiler.Yul

/-! ## Fuel arithmetic helpers -/

private theorem length_le_sizeOf (stmts : List YulStmt) :
    stmts.length ≤ sizeOf stmts := by
  induction stmts with
  | nil => simp
  | cons head tail ih =>
      simp only [List.length_cons, List.cons.sizeOf_spec]
      omega

private theorem eventSingletonBlock_sizeOf_slack (body : List YulStmt) :
    sizeOf [YulStmt.block body] - [YulStmt.block body].length = sizeOf body + 2 := by
  simp [YulStmt.block.sizeOf_spec]
  omega

private theorem eventExecIRStmts_single_block_of_continue
    (fuel : Nat)
    (state next : IRState)
    (body : List YulStmt)
    (hbody : execIRStmts fuel state body = .continue next) :
    execIRStmts (fuel + 2) state [YulStmt.block body] = .continue next := by
  have hblock :
      execIRStmt (fuel + 1) state (YulStmt.block body) = .continue next := by
    simpa [execIRStmt, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hbody
  simpa [execIRStmts, hblock]

/-! ## Source expression-list evaluation -/

private theorem eventEvalExprList_eq_mapM
    (fields : List Field)
    (state : SourceSemantics.RuntimeState)
    (exprs : List Expr) :
    SourceSemantics.evalExprList fields state exprs =
      exprs.mapM (SourceSemantics.evalExpr fields state) := by
  induction exprs with
  | nil => rfl
  | cons expr rest ih =>
      simp [SourceSemantics.evalExprList, ih]

private theorem eventExprList_all_helperSurfaceClosed_of_contractSurfaceClosed
    {exprs : List Expr}
    (hsurface : exprs.any exprTouchesUnsupportedContractSurface = false) :
    exprs.all (fun expr => exprTouchesUnsupportedHelperSurface expr == false) = true := by
  induction exprs with
  | nil =>
      simp
  | cons expr rest ih =>
      simp only [List.any_cons, Bool.or_eq_false_iff] at hsurface
      have hhead :=
        exprTouchesUnsupportedHelperSurface_eq_false_of_contractSurfaceClosed hsurface.1
      simp only [List.all_cons, BEq.rfl, Bool.and_eq_true]
      exact ⟨by simpa [hhead], ih hsurface.2⟩

private theorem eventEvalExprListWithHelpers_eq_evalExprList_of_contractSurfaceClosed
    (spec : CompilationModel)
    (fields : List Field)
    (fuel : Nat)
    (state : SourceSemantics.RuntimeState)
    {exprs : List Expr}
    (hsurface : exprs.any exprTouchesUnsupportedContractSurface = false) :
    SourceSemantics.evalExprListWithHelpers spec fields fuel state exprs =
      SourceSemantics.evalExprList fields state exprs := by
  rw [SourceSemantics.evalExprListWithHelpers_eq_evalExprList_of_helperSurfaceClosed]
  · exact (eventEvalExprList_eq_mapM fields state exprs).symm
  · exact eventExprList_all_helperSurfaceClosed_of_contractSurfaceClosed hsurface

private theorem eventExprList_compile_core_of_contractSurfaceClosed
    {exprs : List Expr}
    (hsurface : exprs.any exprTouchesUnsupportedContractSurface = false) :
    ∀ expr ∈ exprs, FunctionBody.ExprCompileCore expr := by
  intro expr hmem
  have hnotTrue :
      ¬ exprTouchesUnsupportedContractSurface expr = true :=
    (List.any_eq_false.mp hsurface) expr hmem
  have hclosed : exprTouchesUnsupportedContractSurface expr = false := by
    cases h : exprTouchesUnsupportedContractSurface expr <;> simp [h] at hnotTrue ⊢
  exact exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false hclosed

/-! ## Final-state-tracking statement continuation

`StmtsContinueFrom` (IRInterpreter.lean) only yields an existential final
state. The event bridge needs the exact final state, so we track it. -/

private def StmtsContinueFromTo (state : IRState) :
    List YulStmt → IRState → Prop
  | [], final => state = final
  | stmt :: rest, final =>
      ∃ state',
        (∀ extraFuel, execIRStmt (extraFuel + 1) state stmt = .continue state') ∧
        StmtsContinueFromTo state' rest final

private theorem execIRStmts_of_StmtsContinueFromTo
    {state final : IRState}
    {stmts : List YulStmt}
    (h : StmtsContinueFromTo state stmts final)
    (extraFuel : Nat) :
    execIRStmts (stmts.length + extraFuel + 1) state stmts = .continue final := by
  induction stmts generalizing state with
  | nil =>
      have hfinal : state = final := h
      subst hfinal
      simp [execIRStmts]
  | cons stmt rest ih =>
      obtain ⟨state', hstep, htail⟩ := h
      have hlen : (stmt :: rest).length + extraFuel + 1 =
          (rest.length + extraFuel + 1) + 1 := by
        simp [List.length_cons]
        omega
      rw [hlen]
      simp only [execIRStmts, hstep (rest.length + extraFuel)]
      exact ih htail

private theorem StmtsContinueFromTo_append
    {state mid final : IRState}
    {front back : List YulStmt}
    (hfront : StmtsContinueFromTo state front mid)
    (hback : StmtsContinueFromTo mid back final) :
    StmtsContinueFromTo state (front ++ back) final := by
  induction front generalizing state with
  | nil =>
      have hmid : state = mid := hfront
      subst hmid
      simpa using hback
  | cons stmt rest ih =>
      obtain ⟨state', hstep, htail⟩ := hfront
      exact ⟨state', hstep, ih htail⟩

/-! ## Atomic argument IR shapes

Compiling an atomic event argument yields a literal, a scope identifier, or a
zero-argument context builtin. These shapes evaluate independently of block
scratch bindings and memory writes. -/

private def AtomicArgIR (scope : List String) (exprIR : YulExpr) : Prop :=
  (∃ n, exprIR = YulExpr.lit n) ∨
  (∃ name, exprIR = YulExpr.ident name ∧ name ∈ scope) ∨
  (∃ func, exprIR = YulExpr.call func [])

private theorem compileExpr_atomic_shape
    {fields : List Field}
    {scope : List String}
    {expr : Expr}
    {exprIR : YulExpr}
    (hatomic : exprEventArgAtomic expr = true)
    (hinScope : FunctionBody.exprBoundNamesInScope expr scope)
    (hcompile : CompilationModel.compileExpr fields .calldata expr = Except.ok exprIR) :
    AtomicArgIR scope exprIR := by
  cases expr <;> simp [exprEventArgAtomic] at hatomic
  case literal n =>
      refine Or.inl ⟨n % CompilationModel.uint256Modulus, ?_⟩
      simpa [CompilationModel.compileExpr, pure, Except.pure] using hcompile.symm
  case param name =>
      refine Or.inr (Or.inl ⟨name, ?_, ?_⟩)
      · simpa [CompilationModel.compileExpr, pure, Except.pure] using hcompile.symm
      · exact hinScope name (by simp [FunctionBody.exprBoundNames])
  case localVar name =>
      refine Or.inr (Or.inl ⟨name, ?_, ?_⟩)
      · simpa [CompilationModel.compileExpr, pure, Except.pure] using hcompile.symm
      · exact hinScope name (by simp [FunctionBody.exprBoundNames])
  case caller =>
      exact Or.inr (Or.inr ⟨"caller", by simpa [CompilationModel.compileExpr, pure, Except.pure] using hcompile.symm⟩)
  case contractAddress =>
      exact Or.inr (Or.inr ⟨"address", by simpa [CompilationModel.compileExpr, pure, Except.pure] using hcompile.symm⟩)
  case txOrigin =>
      exact Or.inr (Or.inr ⟨"origin", by simpa [CompilationModel.compileExpr, pure, Except.pure] using hcompile.symm⟩)
  case msgValue =>
      exact Or.inr (Or.inr ⟨"callvalue", by simpa [CompilationModel.compileExpr, pure, Except.pure] using hcompile.symm⟩)
  case blockTimestamp =>
      exact Or.inr (Or.inr ⟨"timestamp", by simpa [CompilationModel.compileExpr, pure, Except.pure] using hcompile.symm⟩)
  case blockNumber =>
      exact Or.inr (Or.inr ⟨"number", by simpa [CompilationModel.compileExpr, pure, Except.pure] using hcompile.symm⟩)
  case chainid =>
      exact Or.inr (Or.inr ⟨"chainid", by simpa [CompilationModel.compileExpr, pure, Except.pure] using hcompile.symm⟩)
  case blobbasefee =>
      exact Or.inr (Or.inr ⟨"blobbasefee", by simpa [CompilationModel.compileExpr, pure, Except.pure] using hcompile.symm⟩)
  case calldatasize =>
      exact Or.inr (Or.inr ⟨"calldatasize", by simpa [CompilationModel.compileExpr, pure, Except.pure] using hcompile.symm⟩)

/-! ## Stability of atomic argument IR under scratch effects -/

private theorem evalIRCall_nil_setVar
    (state : IRState) (name : String) (value : Nat) (func : String) :
    evalIRCall (state.setVar name value) func [] = evalIRCall state func [] := by
  simp [evalIRCall, evalIRExprs, IRState.setVar]

private theorem evalIRCall_nil_memory
    (state : IRState) (mem : Nat → Nat) (func : String) :
    evalIRCall { state with memory := mem } func [] = evalIRCall state func [] := by
  simp [evalIRCall, evalIRExprs]

private theorem evalIRExpr_atomic_setVar
    {scope : List String}
    {exprIR : YulExpr}
    (hshape : AtomicArgIR scope exprIR)
    {name : String}
    (hname : name ∉ scope)
    (state : IRState)
    (value : Nat) :
    evalIRExpr (state.setVar name value) exprIR = evalIRExpr state exprIR := by
  rcases hshape with ⟨n, rfl⟩ | ⟨varName, rfl, hmem⟩ | ⟨func, rfl⟩
  · simp [evalIRExpr]
  · have hne : varName ≠ name := fun h => hname (h ▸ hmem)
    simp only [evalIRExpr]
    exact FunctionBody.getVar_setVar_ne state name varName value hne
  · simp only [evalIRExpr]
    exact evalIRCall_nil_setVar state name value func

private theorem evalIRExpr_atomic_memory
    {scope : List String}
    {exprIR : YulExpr}
    (hshape : AtomicArgIR scope exprIR)
    (state : IRState)
    (mem : Nat → Nat) :
    evalIRExpr { state with memory := mem } exprIR = evalIRExpr state exprIR := by
  rcases hshape with ⟨n, rfl⟩ | ⟨varName, rfl, hmem⟩ | ⟨func, rfl⟩
  · simp [evalIRExpr]
  · simp [evalIRExpr, IRState.getVar]
  · simp only [evalIRExpr]
    exact evalIRCall_nil_memory state mem func

/-! ## Per-statement step lemmas -/

private theorem eventExecIRStmt_let_step
    {state : IRState} {valueIR : YulExpr} {value : Nat}
    (name : String)
    (heval : evalIRExpr state valueIR = some value)
    (extraFuel : Nat) :
    execIRStmt (extraFuel + 1) state (YulStmt.let_ name valueIR) =
      .continue (state.setVar name value) := by
  simp [execIRStmt, heval]

private theorem eventExecIRStmt_mstore_step
    {state : IRState} {offsetExpr valExpr : YulExpr} {offset val : Nat}
    (hoff : evalIRExpr state offsetExpr = some offset)
    (hval : evalIRExpr state valExpr = some val)
    (extraFuel : Nat) :
    execIRStmt (extraFuel + 1) state
        (YulStmt.expr (YulExpr.call "mstore" [offsetExpr, valExpr])) =
      .continue { state with
        memory := fun o => if o = offset then val else state.memory o } := by
  simp [execIRStmt, hoff, hval]

/-! ## Event signature scratch stores -/

private theorem eventIRState_set_memory_eq_self
    (state : IRState) {mem : Nat → Nat}
    (hmem : ∀ offset, mem offset = state.memory offset) :
    { state with memory := mem } = state := by
  cases state
  simp only
  congr
  funext offset
  exact hmem offset

private def eventSignatureStoreStmtsFromWords :
    List Nat → Nat → List YulStmt
  | [], _ => []
  | word :: rest, startIdx =>
    YulStmt.expr (YulExpr.call "mstore" [
      YulExpr.call "add" [
        YulExpr.ident "__evt_ptr",
        YulExpr.lit (startIdx * 32)
      ],
      YulExpr.hex word
    ]) :: eventSignatureStoreStmtsFromWords rest (startIdx + 1)

private def eventSignatureStoreStmtsFromChunks
    (chunks : List (List UInt8)) (startIdx : Nat) : List YulStmt :=
  (chunks.zipIdx startIdx).map fun (chunk, idx) =>
    YulStmt.expr (YulExpr.call "mstore" [
      YulExpr.call "add" [
        YulExpr.ident "__evt_ptr",
        YulExpr.lit (idx * 32)
      ],
      YulExpr.hex (wordFromBytes chunk)
    ])

private theorem eventEvalIRExpr_evtPtr_add
    {state : IRState} {ptr idx : Nat}
    (hptr : state.getVar "__evt_ptr" = some ptr) :
    evalIRExpr state
        (YulExpr.call "add" [
          YulExpr.ident "__evt_ptr",
          YulExpr.lit (idx * 32)
        ]) =
      some ((ptr + idx * 32) % Compiler.Constants.evmModulus) := by
  exact FunctionBody.evalIRExpr_add_of_eval
    (state := state)
    (lhs := YulExpr.ident "__evt_ptr")
    (rhs := YulExpr.lit (idx * 32))
    (a := ptr)
    (b := idx * 32)
    (by simpa [evalIRExpr] using hptr)
    (by simp [evalIRExpr])

private theorem eventSignatureStoreStmtsFromWords_cons
    (word : Nat) (words : List Nat) (startIdx : Nat) :
    eventSignatureStoreStmtsFromWords (word :: words) startIdx =
      YulStmt.expr (YulExpr.call "mstore" [
        YulExpr.call "add" [
          YulExpr.ident "__evt_ptr",
          YulExpr.lit (startIdx * 32)
        ],
        YulExpr.hex word
      ]) :: eventSignatureStoreStmtsFromWords words (startIdx + 1) := by
  rfl

private theorem eventSignatureStoreStmtsFromChunks_eq_words
    (chunks : List (List UInt8)) (startIdx : Nat) :
    eventSignatureStoreStmtsFromChunks chunks startIdx =
      eventSignatureStoreStmtsFromWords (chunks.map wordFromBytes) startIdx := by
  induction chunks generalizing startIdx with
  | nil =>
      simp [eventSignatureStoreStmtsFromChunks, eventSignatureStoreStmtsFromWords]
  | cons chunk rest ih =>
      simp [eventSignatureStoreStmtsFromChunks, eventSignatureStoreStmtsFromWords]
      exact ih (startIdx + 1)

private theorem eventSignatureScratchStore_memoryRel
    {state : IRState} {srcMemory : Nat → Verity.Core.Uint256}
    {ptr startIdx word : Nat}
    (hmem : ∀ offset, state.memory offset = (srcMemory offset).val)
    (hword : word < Compiler.Constants.evmModulus) :
    ∀ offset,
      (if offset = (ptr + startIdx * 32) % Compiler.Constants.evmModulus
        then word else state.memory offset) =
      ((fun offset =>
        if offset = (ptr + startIdx * 32) % Compiler.Constants.evmModulus then
          (word : Verity.Core.Uint256)
        else
          srcMemory offset) offset).val := by
  intro offset
  by_cases hkey :
      offset = (ptr + startIdx * 32) % Compiler.Constants.evmModulus
  · simp [hkey, Nat.mod_eq_of_lt hword]
  · simp [hkey, hmem offset]

private theorem eventSignatureScratchStores_continue {state : IRState}
    {srcMemory : Nat → Verity.Core.Uint256} {ptr startIdx : Nat} {words : List Nat}
    (hptr : state.getVar "__evt_ptr" = some ptr)
    (hmem : ∀ offset, state.memory offset = (srcMemory offset).val)
    (hbounded : ∀ word ∈ words, word < Compiler.Constants.evmModulus) :
    StmtsContinueFromTo state (eventSignatureStoreStmtsFromWords words startIdx)
      { state with memory := fun offset =>
          (SourceSemantics.writeEventSignatureScratchFrom words ptr startIdx
            srcMemory offset).val } := by
  induction words generalizing state srcMemory startIdx with
  | nil =>
      simpa [eventSignatureStoreStmtsFromWords,
        SourceSemantics.writeEventSignatureScratchFrom] using
        (eventIRState_set_memory_eq_self state
          (by intro offset; exact (hmem offset).symm)).symm
  | cons word rest ih =>
      rw [eventSignatureStoreStmtsFromWords_cons]
      have hoff := eventEvalIRExpr_evtPtr_add (state := state) (ptr := ptr) (idx := startIdx) hptr
      have hval : evalIRExpr state (YulExpr.hex word) = some word := by simp [evalIRExpr]
      refine ⟨{ state with memory :=
        fun o => if o = (ptr + startIdx * 32) % Compiler.Constants.evmModulus
          then word else state.memory o }, ?_, ?_⟩
      · intro extraFuel
        simpa using eventExecIRStmt_mstore_step hoff hval extraFuel
      · have hptr' :
            ({ state with memory :=
              fun o => if o = (ptr + startIdx * 32) % Compiler.Constants.evmModulus
                then word else state.memory o }).getVar "__evt_ptr" = some ptr := by
          simpa [IRState.getVar] using hptr
        let nextSrcMemory : Nat → Verity.Core.Uint256 := fun offset =>
          if offset = (ptr + startIdx * 32) % Compiler.Constants.evmModulus then
            (word : Verity.Core.Uint256)
          else srcMemory offset
        have hmem' := eventSignatureScratchStore_memoryRel
          (state := state) (srcMemory := srcMemory) (ptr := ptr)
          (startIdx := startIdx) (word := word) hmem (hbounded word (by simp))
        have hbounded' : ∀ w ∈ rest, w < Compiler.Constants.evmModulus := by
          intro w hw
          exact hbounded w (by simp [hw])
        simpa [SourceSemantics.writeEventSignatureScratchFrom, nextSrcMemory]
          using ih (state := { state with memory := (fun o =>
            if o = (ptr + startIdx * 32) % Compiler.Constants.evmModulus
            then word else state.memory o) }) (srcMemory := nextSrcMemory)
            (startIdx := startIdx + 1) hptr' hmem' hbounded'

private theorem eventSignatureTopic_of_memorySliceWords_eq
    {eventDef : EventDef} {memory : Nat → Nat} {ptr : Nat}
    (hslice :
      memorySliceWords memory ptr (bytesFromString (eventSignature eventDef)).length =
        memorySliceWords (SourceSemantics.eventSignatureMemory eventDef) 0
          (bytesFromString (eventSignature eventDef)).length) :
    abstractKeccakMemorySlice memory ptr
        (bytesFromString (eventSignature eventDef)).length =
      SourceSemantics.eventSignatureTopic eventDef := by
  simp [abstractKeccakMemorySlice, SourceSemantics.eventSignatureTopic, hslice]

private theorem eventEvalIRExpr_topic0
    {state : IRState} {eventDef : EventDef} {ptr : Nat}
    (hptr : state.getVar "__evt_ptr" = some ptr)
    (hslice :
      memorySliceWords state.memory ptr (bytesFromString (eventSignature eventDef)).length =
        memorySliceWords (SourceSemantics.eventSignatureMemory eventDef) 0
          (bytesFromString (eventSignature eventDef)).length) :
    evalIRExpr state
        (YulExpr.call "keccak256" [
          YulExpr.ident "__evt_ptr",
          YulExpr.lit (bytesFromString (eventSignature eventDef)).length
        ]) =
      some (SourceSemantics.eventSignatureTopic eventDef) := by
  simp [evalIRExpr, evalIRCall, evalIRExprs, hptr,
    eventSignatureTopic_of_memorySliceWords_eq hslice]

/-! ## Word normalization bridge

The compiled `normalizeEventWord` masking matches the source-side
`normalizeEventValue` on every proof-supported scalar parameter type. -/

private theorem eventEvalIRExpr_normalizeEventWord_uint8
    {state : IRState} {exprIR : YulExpr} {value : Nat}
    (heval : evalIRExpr state exprIR = some value) :
    evalIRExpr state (normalizeEventWord ParamType.uint8 exprIR) =
      some (SourceSemantics.normalizeEventValue ParamType.uint8 value) := by
  have h255 : (255 : Nat) % Compiler.Constants.evmModulus = 255 :=
    Nat.mod_eq_of_lt (by norm_num [Compiler.Constants.evmModulus])
  simp [normalizeEventWord, SourceSemantics.normalizeEventValue,
    SourceSemantics.uint8Modulus, evalIRExpr, evalIRCall, evalIRExprs,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
    heval, h255]

private theorem eventEvalIRExpr_normalizeEventWord_uint16
    {state : IRState} {exprIR : YulExpr} {value : Nat}
    (heval : evalIRExpr state exprIR = some value) :
    evalIRExpr state (normalizeEventWord ParamType.uint16 exprIR) =
      some (SourceSemantics.normalizeEventValue ParamType.uint16 value) := by
  have h65535 : (65535 : Nat) % Compiler.Constants.evmModulus = 65535 :=
    Nat.mod_eq_of_lt (by norm_num [Compiler.Constants.evmModulus])
  simp [normalizeEventWord, SourceSemantics.normalizeEventValue,
    evalIRExpr, evalIRCall, evalIRExprs,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
    heval, h65535]

private theorem eventEvalIRExpr_normalizeEventWord_address
    {state : IRState} {exprIR : YulExpr} {value : Nat}
    (heval : evalIRExpr state exprIR = some value) :
    evalIRExpr state (normalizeEventWord ParamType.address exprIR) =
      some (SourceSemantics.normalizeEventValue ParamType.address value) := by
  have hmask : Compiler.Constants.addressMask % Compiler.Constants.evmModulus =
      Compiler.Constants.addressMask :=
    Nat.mod_eq_of_lt
      (by norm_num [Compiler.Constants.addressMask, Compiler.Constants.evmModulus])
  simp [normalizeEventWord, SourceSemantics.normalizeEventValue,
    evalIRExpr, evalIRCall, evalIRExprs,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
    heval, hmask]

private theorem eventEvalIRExpr_normalizeEventWord_bool
    {state : IRState} {exprIR : YulExpr} {value : Nat}
    (heval : evalIRExpr state exprIR = some value) :
    evalIRExpr state (normalizeEventWord ParamType.bool exprIR) =
      some (SourceSemantics.normalizeEventValue ParamType.bool value) := by
  have hone : (1 : Nat) % Compiler.Constants.evmModulus = 1 :=
    Nat.mod_eq_of_lt (by norm_num [Compiler.Constants.evmModulus])
  by_cases hzero : value % Compiler.Constants.evmModulus = 0 <;>
    simp [normalizeEventWord, CompilationModel.yulToBool,
      SourceSemantics.normalizeEventValue, evalIRExpr, evalIRCall, evalIRExprs,
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
      heval, hzero, hone]

private theorem eventEvalIRExpr_normalizeEventWord :
    ∀ (ty : ParamType) {state : IRState} {exprIR : YulExpr} {value : Nat},
      eventParamScalarProofSupported ty = true →
      evalIRExpr state exprIR = some value →
      value < Compiler.Constants.evmModulus →
      evalIRExpr state (normalizeEventWord ty exprIR) =
        some (SourceSemantics.normalizeEventValue ty value)
  | .uint256, _, _, _, _, heval, hlt => by
      simpa [normalizeEventWord, SourceSemantics.normalizeEventValue,
        Nat.mod_eq_of_lt hlt] using heval
  | .int256, _, _, _, _, heval, hlt => by
      simpa [normalizeEventWord, SourceSemantics.normalizeEventValue,
        Nat.mod_eq_of_lt hlt] using heval
  | .bytes32, _, _, _, _, heval, hlt => by
      simpa [normalizeEventWord, SourceSemantics.normalizeEventValue,
        Nat.mod_eq_of_lt hlt] using heval
  | .uint8, _, _, _, _, heval, _ => by
      exact eventEvalIRExpr_normalizeEventWord_uint8 heval
  | .uint16, _, _, _, _, heval, _ => by
      exact eventEvalIRExpr_normalizeEventWord_uint16 heval
  | .address, _, _, _, _, heval, _ => by
      exact eventEvalIRExpr_normalizeEventWord_address heval
  | .bool, _, _, _, _, heval, _ => by
      exact eventEvalIRExpr_normalizeEventWord_bool heval
  | .newtypeOf _ baseType, _, _, _, hsupport, heval, hlt => by
      have hbase : eventParamScalarProofSupported baseType = true := by
        simpa [eventParamScalarProofSupported, eventParamScalarCompileSupported]
          using hsupport
      simpa [normalizeEventWord, SourceSemantics.normalizeEventValue]
        using eventEvalIRExpr_normalizeEventWord baseType hbase heval hlt
  | .string, _, _, _, hsupport, _, _ => by
      simp [eventParamScalarProofSupported, eventParamScalarCompileSupported] at hsupport
  | .tuple _, _, _, _, hsupport, _, _ => by
      simp [eventParamScalarProofSupported, eventParamScalarCompileSupported] at hsupport
  | .array _, _, _, _, hsupport, _, _ => by
      simp [eventParamScalarProofSupported, eventParamScalarCompileSupported] at hsupport
  | .fixedArray _ _, _, _, _, hsupport, _, _ => by
      simp [eventParamScalarProofSupported, eventParamScalarCompileSupported] at hsupport
  | .bytes, _, _, _, hsupport, _, _ => by
      simp [eventParamScalarProofSupported, eventParamScalarCompileSupported] at hsupport
  | .adt _ _, _, _, _, hsupport, _, _ => by
      simp [eventParamScalarProofSupported, eventParamScalarCompileSupported] at hsupport

end Compiler.Proofs.IRGeneration

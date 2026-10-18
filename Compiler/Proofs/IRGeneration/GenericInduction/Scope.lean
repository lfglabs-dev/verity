import Compiler.Proofs.IRGeneration.GenericInduction.InterfaceAssembly

set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.CompilationModel
open Compiler.Yul

/-- Structural scope discipline for statement prefixes used to justify that the
generic induction scope only contains validated source identifiers. -/
inductive StmtListScopeDiscipline (fieldNames : List String) : List String → List Stmt → Prop where
  | nil {scope : List String} :
      StmtListScopeDiscipline fieldNames scope []
  | letVar {scope : List String} {name : String} {value : Expr} {rest : List Stmt} :
      FunctionBody.ExprCompileCore value →
      FunctionBody.exprBoundNamesInScope value scope →
      StmtListScopeDiscipline fieldNames (stmtNextScope scope (.letVar name value)) rest →
      StmtListScopeDiscipline fieldNames scope (.letVar name value :: rest)
  | assignVar {scope : List String} {name : String} {value : Expr} {rest : List Stmt} :
      FunctionBody.ExprCompileCore value →
      FunctionBody.exprBoundNamesInScope value scope →
      StmtListScopeDiscipline fieldNames (stmtNextScope scope (.assignVar name value)) rest →
      StmtListScopeDiscipline fieldNames scope (.assignVar name value :: rest)
  | require {scope : List String} {cond : Expr} {message : String} {rest : List Stmt} :
      FunctionBody.ExprCompileCore cond →
      FunctionBody.exprBoundNamesInScope cond scope →
      StmtListScopeDiscipline fieldNames (stmtNextScope scope (.require cond message)) rest →
      StmtListScopeDiscipline fieldNames scope (.require cond message :: rest)
  | return_ {scope : List String} {value : Expr} {rest : List Stmt} :
      FunctionBody.ExprCompileCore value →
      FunctionBody.exprBoundNamesInScope value scope →
      StmtListScopeDiscipline fieldNames (stmtNextScope scope (.return value)) rest →
      StmtListScopeDiscipline fieldNames scope (.return value :: rest)
  | stop {scope : List String} {rest : List Stmt} :
      StmtListScopeDiscipline fieldNames scope rest →
      StmtListScopeDiscipline fieldNames scope (.stop :: rest)
  | setStorage {scope : List String} {fieldName : String} {value : Expr} {rest : List Stmt} :
      fieldName ∈ fieldNames →
      FunctionBody.ExprCompileCore value →
      FunctionBody.exprBoundNamesInScope value scope →
      StmtListScopeDiscipline fieldNames (stmtNextScope scope (.setStorage fieldName value)) rest →
      StmtListScopeDiscipline fieldNames scope (.setStorage fieldName value :: rest)
  | setStorageAddr {scope : List String} {fieldName : String} {value : Expr} {rest : List Stmt} :
      fieldName ∈ fieldNames →
      FunctionBody.ExprCompileCore value →
      FunctionBody.exprBoundNamesInScope value scope →
      StmtListScopeDiscipline fieldNames (stmtNextScope scope (.setStorageAddr fieldName value)) rest →
      StmtListScopeDiscipline fieldNames scope (.setStorageAddr fieldName value :: rest)
  | setImmutable {scope : List String} {name : String} {value : Expr} {rest : List Stmt} :
      FunctionBody.ExprCompileCore value →
      FunctionBody.exprBoundNamesInScope value scope →
      StmtListScopeDiscipline fieldNames (stmtNextScope scope (.setImmutable name value)) rest →
      StmtListScopeDiscipline fieldNames scope (.setImmutable name value :: rest)
  | setStorageWord {scope : List String} {fieldName : String} {wordOffset : Nat} {value : Expr}
      {rest : List Stmt} :
      fieldName ∈ fieldNames →
      FunctionBody.ExprCompileCore value →
      FunctionBody.exprBoundNamesInScope value scope →
      StmtListScopeDiscipline fieldNames
        (stmtNextScope scope (.setStorageWord fieldName wordOffset value)) rest →
      StmtListScopeDiscipline fieldNames scope (.setStorageWord fieldName wordOffset value :: rest)
  | mstore {scope : List String} {offset value : Expr} {rest : List Stmt} :
      FunctionBody.ExprCompileCore offset →
      FunctionBody.exprBoundNamesInScope offset scope →
      FunctionBody.ExprCompileCore value →
      FunctionBody.exprBoundNamesInScope value scope →
      StmtListScopeDiscipline fieldNames (stmtNextScope scope (.mstore offset value)) rest →
      StmtListScopeDiscipline fieldNames scope (.mstore offset value :: rest)
  | tstore {scope : List String} {offset value : Expr} {rest : List Stmt} :
      FunctionBody.ExprCompileCore offset →
      FunctionBody.exprBoundNamesInScope offset scope →
      FunctionBody.ExprCompileCore value →
      FunctionBody.exprBoundNamesInScope value scope →
      StmtListScopeDiscipline fieldNames (stmtNextScope scope (.tstore offset value)) rest →
      StmtListScopeDiscipline fieldNames scope (.tstore offset value :: rest)
  | calldatacopy {scope : List String} {destOffset sourceOffset size : Expr} {rest : List Stmt} :
      FunctionBody.ExprCompileCore destOffset →
      FunctionBody.exprBoundNamesInScope destOffset scope →
      FunctionBody.ExprCompileCore sourceOffset →
      FunctionBody.exprBoundNamesInScope sourceOffset scope →
      FunctionBody.ExprCompileCore size →
      FunctionBody.exprBoundNamesInScope size scope →
      StmtListScopeDiscipline fieldNames
        (stmtNextScope scope (.calldatacopy destOffset sourceOffset size)) rest →
      StmtListScopeDiscipline fieldNames scope (.calldatacopy destOffset sourceOffset size :: rest)
  | returndataCopy {scope : List String} {destOffset sourceOffset size : Expr}
      {rest : List Stmt} :
      FunctionBody.ExprCompileCore destOffset →
      FunctionBody.exprBoundNamesInScope destOffset scope →
      FunctionBody.ExprCompileCore sourceOffset →
      FunctionBody.exprBoundNamesInScope sourceOffset scope →
      FunctionBody.ExprCompileCore size →
      FunctionBody.exprBoundNamesInScope size scope →
      StmtListScopeDiscipline fieldNames
        (stmtNextScope scope (.returndataCopy destOffset sourceOffset size)) rest →
      StmtListScopeDiscipline fieldNames scope (.returndataCopy destOffset sourceOffset size :: rest)
  | revertEmpty {scope : List String} {rest : List Stmt} :
      StmtListScopeDiscipline fieldNames scope rest →
      StmtListScopeDiscipline fieldNames scope (.revertEmpty :: rest)
  | revertReturndata {scope : List String} {rest : List Stmt} :
      StmtListScopeDiscipline fieldNames scope rest →
      StmtListScopeDiscipline fieldNames scope (.revertReturndata :: rest)
  | ite {scope : List String} {cond : Expr} {thenBranch elseBranch rest : List Stmt} :
      FunctionBody.ExprCompileCore cond →
      FunctionBody.exprBoundNamesInScope cond scope →
      StmtListScopeDiscipline fieldNames scope thenBranch →
      StmtListScopeDiscipline fieldNames scope elseBranch →
      StmtListScopeDiscipline fieldNames (stmtNextScope scope (.ite cond thenBranch elseBranch)) rest →
      StmtListScopeDiscipline fieldNames scope (.ite cond thenBranch elseBranch :: rest)
  | forEachLiteralZero {scope : List String} {varName : String} {body rest : List Stmt} :
      StmtListScopeDiscipline fieldNames (varName :: scope) body →
      StmtListScopeDiscipline fieldNames (stmtNextScope scope (.forEach varName (.literal 0) body)) rest →
      StmtListScopeDiscipline fieldNames scope (.forEach varName (.literal 0) body :: rest)
  | forEachLiteralEmpty {scope : List String} {varName : String} {n : Nat} {rest : List Stmt} :
      StmtListScopeDiscipline fieldNames (stmtNextScope scope (.forEach varName (.literal n) [])) rest →
      StmtListScopeDiscipline fieldNames scope (.forEach varName (.literal n) [] :: rest)

/-- Syntax-side witness for the current generic statement fragment, before the
scope obligations are discharged from identifier validation. -/
inductive StmtListScopeCore (fieldNames : List String) : List Stmt → Prop where
  | nil :
      StmtListScopeCore fieldNames []
  | letVar {name : String} {value : Expr} {rest : List Stmt} :
      FunctionBody.ExprCompileCore value →
      StmtListScopeCore fieldNames rest →
      StmtListScopeCore fieldNames (.letVar name value :: rest)
  | assignVar {name : String} {value : Expr} {rest : List Stmt} :
      FunctionBody.ExprCompileCore value →
      StmtListScopeCore fieldNames rest →
      StmtListScopeCore fieldNames (.assignVar name value :: rest)
  | require {cond : Expr} {message : String} {rest : List Stmt} :
      FunctionBody.ExprCompileCore cond →
      StmtListScopeCore fieldNames rest →
      StmtListScopeCore fieldNames (.require cond message :: rest)
  | return_ {value : Expr} {rest : List Stmt} :
      FunctionBody.ExprCompileCore value →
      StmtListScopeCore fieldNames rest →
      StmtListScopeCore fieldNames (.return value :: rest)
  | stop {rest : List Stmt} :
      StmtListScopeCore fieldNames rest →
      StmtListScopeCore fieldNames (.stop :: rest)
  | setStorage {fieldName : String} {value : Expr} {rest : List Stmt} :
      fieldName ∈ fieldNames →
      FunctionBody.ExprCompileCore value →
      StmtListScopeCore fieldNames rest →
      StmtListScopeCore fieldNames (.setStorage fieldName value :: rest)
  | setStorageAddr {fieldName : String} {value : Expr} {rest : List Stmt} :
      fieldName ∈ fieldNames →
      FunctionBody.ExprCompileCore value →
      StmtListScopeCore fieldNames rest →
      StmtListScopeCore fieldNames (.setStorageAddr fieldName value :: rest)
  | setImmutable {name : String} {value : Expr} {rest : List Stmt} :
      FunctionBody.ExprCompileCore value →
      StmtListScopeCore fieldNames rest →
      StmtListScopeCore fieldNames (.setImmutable name value :: rest)
  | setStorageWord {fieldName : String} {wordOffset : Nat} {value : Expr} {rest : List Stmt} :
      fieldName ∈ fieldNames →
      FunctionBody.ExprCompileCore value →
      StmtListScopeCore fieldNames rest →
      StmtListScopeCore fieldNames (.setStorageWord fieldName wordOffset value :: rest)
  | mstore {offset value : Expr} {rest : List Stmt} :
      FunctionBody.ExprCompileCore offset →
      FunctionBody.ExprCompileCore value →
      StmtListScopeCore fieldNames rest →
      StmtListScopeCore fieldNames (.mstore offset value :: rest)
  | tstore {offset value : Expr} {rest : List Stmt} :
      FunctionBody.ExprCompileCore offset →
      FunctionBody.ExprCompileCore value →
      StmtListScopeCore fieldNames rest →
      StmtListScopeCore fieldNames (.tstore offset value :: rest)
  | calldatacopy {destOffset sourceOffset size : Expr} {rest : List Stmt} :
      FunctionBody.ExprCompileCore destOffset →
      FunctionBody.ExprCompileCore sourceOffset →
      FunctionBody.ExprCompileCore size →
      StmtListScopeCore fieldNames rest →
      StmtListScopeCore fieldNames (.calldatacopy destOffset sourceOffset size :: rest)
  | returndataCopy {destOffset sourceOffset size : Expr} {rest : List Stmt} :
      FunctionBody.ExprCompileCore destOffset →
      FunctionBody.ExprCompileCore sourceOffset →
      FunctionBody.ExprCompileCore size →
      StmtListScopeCore fieldNames rest →
      StmtListScopeCore fieldNames (.returndataCopy destOffset sourceOffset size :: rest)
  | revertEmpty {rest : List Stmt} :
      StmtListScopeCore fieldNames rest →
      StmtListScopeCore fieldNames (.revertEmpty :: rest)
  | revertReturndata {rest : List Stmt} :
      StmtListScopeCore fieldNames rest →
      StmtListScopeCore fieldNames (.revertReturndata :: rest)
  | ite {cond : Expr} {thenBranch elseBranch rest : List Stmt} :
      FunctionBody.ExprCompileCore cond →
      StmtListScopeCore fieldNames thenBranch →
      StmtListScopeCore fieldNames elseBranch →
      StmtListScopeCore fieldNames rest →
      StmtListScopeCore fieldNames (.ite cond thenBranch elseBranch :: rest)
  | forEachLiteralZero {varName : String} {body rest : List Stmt} :
      StmtListScopeCore fieldNames body →
      StmtListScopeCore fieldNames rest →
      StmtListScopeCore fieldNames (.forEach varName (.literal 0) body :: rest)
  | forEachLiteralEmpty {varName : String} {n : Nat} {rest : List Stmt} :
      StmtListScopeCore fieldNames rest →
      StmtListScopeCore fieldNames (.forEach varName (.literal n) [] :: rest)

theorem exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false
    {expr : Expr}
    (hsurface : exprTouchesUnsupportedContractSurface expr = false) :
    FunctionBody.ExprCompileCore expr := by
  match expr, hsurface with
  | .literal _, _ => exact .literal _
  | .param _, _ => exact .param _
  | .constructorArg idx, _ => exact .constructorArg idx
  | .localVar _, _ => exact .localVar _
  | .immutable _, hsurface => simp [exprTouchesUnsupportedContractSurface] at hsurface
  | .caller, _ => exact .caller
  | .contractAddress, _ => exact .contractAddress
  | .txOrigin, _ => exact .txOrigin
  | .msgValue, _ => exact .msgValue
  | .blockTimestamp, _ => exact .blockTimestamp
  | .blockNumber, _ => exact .blockNumber
  | .chainid, _ => exact .chainid
  | .blobbasefee, _ => exact .blobbasefee
  | .calldatasize, _ => exact .calldatasize
  | .returndataSize, _ => exact .returndataSize
  | .add a b, hsurface | .sub a b, hsurface | .mul a b, hsurface
  | .div a b, hsurface | .mod a b, hsurface
  | .bitAnd a b, hsurface | .bitOr a b, hsurface | .bitXor a b, hsurface
  | .eq a b, hsurface | .ge a b, hsurface | .gt a b, hsurface
  | .lt a b, hsurface | .le a b, hsurface
  | .logicalAnd a b, hsurface | .logicalOr a b, hsurface
  | .shl a b, hsurface | .shr a b, hsurface | .slt a b, hsurface | .sgt a b, hsurface
  | .sdiv a b, hsurface | .smod a b, hsurface | .sar a b, hsurface
  | .byte a b, hsurface | .signextend a b, hsurface | .min a b, hsurface | .max a b, hsurface
  | .ceilDiv a b, hsurface =>
      simp only [exprTouchesUnsupportedContractSurface, Bool.or_eq_false_iff] at hsurface
      constructor
      · exact exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false hsurface.1
      · exact exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false hsurface.2
  | .wMulDown a b, hsurface | .wDivUp a b, hsurface =>
      simp only [exprTouchesUnsupportedContractSurface, Bool.or_eq_false_iff] at hsurface
      constructor
      · exact exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false hsurface.1
      · exact exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false hsurface.2
  | .logicalNot a, hsurface | .bitNot a, hsurface =>
      simp only [exprTouchesUnsupportedContractSurface] at hsurface
      constructor
      exact exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false hsurface
  | .tload a, hsurface =>
      simp only [exprTouchesUnsupportedContractSurface] at hsurface
      exact .tload
        (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false hsurface)
  | .calldataload a, hsurface =>
      simp only [exprTouchesUnsupportedContractSurface] at hsurface
      exact .calldataload
        (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false hsurface)
  | .mload a, hsurface =>
      simp only [exprTouchesUnsupportedContractSurface] at hsurface
      exact .mload
        (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false hsurface)
  | .extcodesize a, hsurface =>
      simp only [exprTouchesUnsupportedContractSurface] at hsurface
      exact .extcodesize
        (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false hsurface)
  | .returndataOptionalBoolAt a, hsurface =>
      simp only [exprTouchesUnsupportedContractSurface] at hsurface
      exact .returndataOptionalBoolAt
        (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false hsurface)
  | .keccak256 offset size, hsurface =>
      simp only [exprTouchesUnsupportedContractSurface, Bool.or_eq_false_iff] at hsurface
      exact .keccak256
        (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false hsurface.1)
        (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false hsurface.2)
  | .ite cond thenVal elseVal, hsurface =>
      simp only [exprTouchesUnsupportedContractSurface, Bool.or_eq_false_iff] at hsurface
      exact .ite
        (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false hsurface.1.1)
        (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false hsurface.1.2)
        (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false hsurface.2)
  | .mulDivDown a b c, hsurface =>
      simp only [exprTouchesUnsupportedContractSurface, Bool.or_eq_false_iff] at hsurface
      exact .mulDivDown
        (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false hsurface.1.1)
        (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false hsurface.1.2)
        (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false hsurface.2)
  | .mulDivUp a b c, hsurface =>
      simp only [exprTouchesUnsupportedContractSurface, Bool.or_eq_false_iff] at hsurface
      exact .mulDivUp
        (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false hsurface.1.1)
        (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false hsurface.1.2)
        (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false hsurface.2)
  | .forkIfAtLeast _ _ _, hsurface =>
      -- Unspecialized fork conditionals are rejected by source semantics and
      -- expression compilation. They must be specialized by the compile driver
      -- before reaching the generic proof surface.
      simp [exprTouchesUnsupportedContractSurface] at hsurface
  | .mulDiv512Down _ _ _, hsurface | .mulDiv512Up _ _ _, hsurface =>
      -- `mulDiv512Down/Up` is unsupported by the contract surface (verity#1761
      -- codegen-only; no `ExprCompileCore` constructor), so this branch is
      -- vacuous.
      simp [exprTouchesUnsupportedContractSurface] at hsurface
  | .paramDynamicHeadWord _ _, hsurface =>
      -- Same vacuous handling for `paramDynamicHeadWord` (verity#1832
      -- codegen-only).
      simp [exprTouchesUnsupportedContractSurface] at hsurface
  | .externalCall name args, hsurface =>
      -- Only the reserved two-operand `exp` builtin lane is inside the contract
      -- surface; every other `externalCall` shape makes `hsurface` vacuous.
      cases args with
      | nil => simp [exprTouchesUnsupportedContractSurface] at hsurface
      | cons base tl =>
        cases tl with
        | nil => simp [exprTouchesUnsupportedContractSurface] at hsurface
        | cons exponent tl' =>
          cases tl' with
          | cons _ _ => simp [exprTouchesUnsupportedContractSurface] at hsurface
          | nil =>
            by_cases hname : name = builtinExpName
            · subst hname
              simp only [exprTouchesUnsupportedContractSurface, beq_self_eq_true, if_true,
                Bool.or_eq_false_iff] at hsurface
              exact .builtinExp
                (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false hsurface.1)
                (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false hsurface.2)
            · simp [exprTouchesUnsupportedContractSurface, hname] at hsurface

private theorem fieldName_mem_fields_of_findFieldWithResolvedSlot_some
    {fields : List Field}
    {fieldName : String}
    {f : Field}
    {slot : Nat}
    (hfind : findFieldWithResolvedSlot fields fieldName = some (f, slot)) :
    fieldName ∈ fields.map (·.name) := by
  have hmem := field_mem_of_findFieldWithResolvedSlot_eq_some hfind
  have hname := fieldName_eq_of_findFieldWithResolvedSlot_eq_some hfind
  rw [List.mem_map]
  exact ⟨f, hmem, hname⟩

private theorem fieldName_mem_fields_of_compileSetStorage_ok
    {fields : List Field}
    {fieldName : String}
    {value : Expr}
    {requireAddressField : Bool}
    {compiledIR : List YulStmt}
    (hcompile :
      CompilationModel.compileSetStorage
        fields
        .calldata
        fieldName
        value
        requireAddressField = Except.ok compiledIR) :
    fieldName ∈ fields.map (·.name) := by
  simp only [CompilationModel.compileSetStorage] at hcompile
  split at hcompile
  · simp at hcompile
  · rename_i hnotMapping
    split at hcompile
    · rename_i f slot hfind
      exact fieldName_mem_fields_of_findFieldWithResolvedSlot_some hfind
    · simp at hcompile

private theorem isMapping_false_of_compileSetStorage_ok
    {fields : List Field}
    {fieldName : String}
    {value : Expr}
    {requireAddressField : Bool}
    {compiledIR : List YulStmt}
    (hcompile :
      CompilationModel.compileSetStorage
        fields .calldata fieldName value requireAddressField = Except.ok compiledIR) :
    isMapping fields fieldName = false := by
  by_cases h : isMapping fields fieldName
  · simp [CompilationModel.compileSetStorage, h] at hcompile
  · simpa using h

theorem compileStmt_ok_of_compileStmtList_append_cons
    {fields : List Field}
    {scope : List String}
    {«prefix» : List Stmt}
    {stmt : Stmt}
    {«suffix» : List Stmt}
    {bodyIR : List YulStmt}
    (hcompile :
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false scope [] («prefix» ++ stmt :: «suffix») =
          Except.ok bodyIR) :
    ∃ stmtIR,
      CompilationModel.compileStmt
        fields [] [] .calldata [] false
          (List.foldl (fun acc s => collectStmtBindNames s ++ acc) scope «prefix»)
          [] stmt = Except.ok stmtIR := by
  induction «prefix» generalizing scope bodyIR with
  | nil => rcases FunctionBody.compileStmtList_cons_ok_inv hcompile with ⟨hd, _, hstmt, _⟩; exact ⟨hd, hstmt⟩
  | cons s rest ih =>
      rcases FunctionBody.compileStmtList_cons_ok_inv hcompile with ⟨_, _, _, htail, _⟩
      exact ih htail

theorem isMapping_false_of_compileStmt_setStorage_ok
    {fields : List Field}
    {scope : List String}
    {fieldName : String}
    {value : Expr}
    {compiledIR : List YulStmt}
    (hcompile :
      CompilationModel.compileStmt
        fields [] [] .calldata [] false scope [] (.setStorage fieldName value) =
          Except.ok compiledIR) :
    isMapping fields fieldName = false := by
  simp only [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork] at hcompile
  exact isMapping_false_of_compileSetStorage_ok hcompile

private theorem compileStmt_ite_ok_inv
    {fields : List Field}
    {scope : List String}
    {cond : Expr}
    {thenBranch elseBranch : List Stmt}
    {compiledIR : List YulStmt}
    (hcompile :
      CompilationModel.compileStmt
        fields [] [] .calldata [] false scope [] (.ite cond thenBranch elseBranch) =
          Except.ok compiledIR) :
    ∃ condIR thenIR elseIR,
      CompilationModel.compileExpr fields .calldata cond = Except.ok condIR ∧
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false scope [] thenBranch = Except.ok thenIR ∧
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false scope [] elseBranch = Except.ok elseIR := by
  unfold CompilationModel.compileStmt CompilationModel.compileStmtWithFork at hcompile
  rcases hcond : CompilationModel.compileExprWithInternals fields .calldata [] cond with _ | condIR
  · simp [hcond] at hcompile
    cases hcompile
  · simp [hcond] at hcompile
    rcases hthen : CompilationModel.compileStmtList
        fields [] [] .calldata [] false scope [] thenBranch with _ | thenIR
    · simp [FunctionBody.compileStmtListWithFork_cancun_eq_compileStmtList, hthen] at hcompile
      cases hcompile
    · simp [FunctionBody.compileStmtListWithFork_cancun_eq_compileStmtList, hthen] at hcompile
      rcases helse : CompilationModel.compileStmtList
          fields [] [] .calldata [] false scope [] elseBranch with _ | elseIR
      · simp [FunctionBody.compileStmtListWithFork_cancun_eq_compileStmtList, helse] at hcompile
        cases hcompile
      ·
        have hcondPublic :
            CompilationModel.compileExpr fields .calldata cond = Except.ok condIR := by
          simpa [CompilationModel.compileExprWithInternals_nil_eq] using hcond
        simpa [hcondPublic, hthen, helse] using
          (show ∃ condIR thenIR elseIR,
              Except.ok condIR = Except.ok condIR ∧
              Except.ok thenIR = Except.ok thenIR ∧
              Except.ok elseIR = Except.ok elseIR from
            ⟨condIR, thenIR, elseIR, rfl, rfl, rfl⟩)

private theorem stmtListScopeCore_of_unsupportedContractSurface_eq_false
    (fields : List Field)
    (scope : List String)
    (stmts : List Stmt)
    (bodyIR : List YulStmt)
    (hsurface : stmtListTouchesUnsupportedContractSurface stmts = false)
    (hcompile :
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false scope [] stmts = Except.ok bodyIR) :
    StmtListScopeCore (fields.map (·.name)) stmts := by
  match stmts with
  | [] => exact StmtListScopeCore.nil
  | stmt :: rest =>
      rcases FunctionBody.compileStmtList_cons_ok_inv hcompile with
        ⟨headIR, tailIR, hhead, htail, rfl⟩
      have hstmtSurface :
          stmtTouchesUnsupportedContractSurface stmt = false := by
        simpa [stmtListTouchesUnsupportedContractSurface] using
          (Bool.or_eq_false_iff.mp hsurface).1
      have hrestSurface :
          stmtListTouchesUnsupportedContractSurface rest = false := by
        simpa [stmtListTouchesUnsupportedContractSurface] using
          (Bool.or_eq_false_iff.mp hsurface).2
      have ihRest := stmtListScopeCore_of_unsupportedContractSurface_eq_false
        fields _ rest _ hrestSurface htail
      cases stmt with
      | letVar _ value =>
          exact .letVar (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false
            (by simpa [stmtTouchesUnsupportedContractSurface] using hstmtSurface)) ihRest
      | assignVar _ value =>
          exact .assignVar (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false
            (by simpa [stmtTouchesUnsupportedContractSurface] using hstmtSurface)) ihRest
      | setStorage fieldName value =>
          exact .setStorage
            (by simp [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork] at hhead
                exact fieldName_mem_fields_of_compileSetStorage_ok hhead)
            (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false
              (by simpa [stmtTouchesUnsupportedContractSurface] using hstmtSurface)) ihRest
      | setStorageAddr fieldName value =>
          exact .setStorageAddr
            (by simp [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork] at hhead
                exact fieldName_mem_fields_of_compileSetStorage_ok hhead)
            (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false
              (by simpa [stmtTouchesUnsupportedContractSurface] using hstmtSurface)) ihRest
      | setImmutable name value =>
          exact .setImmutable
            (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false
              (by simpa [stmtTouchesUnsupportedContractSurface] using hstmtSurface)) ihRest
      | setStorageWord fieldName wordOffset value =>
          exact .setStorageWord
            (by
              simp only [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
                bind, Except.bind] at hhead
              rcases hfind : findFieldWithResolvedSlot fields fieldName with _ | ⟨f, slot⟩
              · simp [hfind] at hhead
              · exact fieldName_mem_fields_of_findFieldWithResolvedSlot_some hfind)
            (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false
              (by simpa [stmtTouchesUnsupportedContractSurface] using hstmtSurface)) ihRest
      | require cond message =>
          exact .require (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false
            (by simpa [stmtTouchesUnsupportedContractSurface] using hstmtSurface)) ihRest
      | «return» value =>
          exact .return_ (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false
            (by simpa [stmtTouchesUnsupportedContractSurface] using hstmtSurface)) ihRest
      | stop => exact .stop ihRest
      | mstore offset value =>
          have hor := Bool.or_eq_false_iff.mp hstmtSurface
          exact .mstore (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false
            (by simpa [stmtTouchesUnsupportedContractSurface] using hor.1))
            (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false
              (by simpa [stmtTouchesUnsupportedContractSurface] using hor.2)) ihRest
      | tstore offset value =>
          have hor := Bool.or_eq_false_iff.mp hstmtSurface
          exact .tstore (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false
            (by simpa [stmtTouchesUnsupportedContractSurface] using hor.1))
            (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false
              (by simpa [stmtTouchesUnsupportedContractSurface] using hor.2)) ihRest
      | calldatacopy destOffset sourceOffset size =>
          simp only [stmtTouchesUnsupportedContractSurface,
            Bool.or_eq_false_iff] at hstmtSurface
          exact .calldatacopy
            (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false hstmtSurface.1.1)
            (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false hstmtSurface.1.2)
            (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false hstmtSurface.2)
            ihRest
      | returndataCopy destOffset sourceOffset size =>
          simp only [stmtTouchesUnsupportedContractSurface,
            Bool.or_eq_false_iff] at hstmtSurface
          exact .returndataCopy
            (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false hstmtSurface.1.1)
            (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false hstmtSurface.1.2)
            (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false hstmtSurface.2)
            ihRest
      | revertEmpty =>
          exact .revertEmpty ihRest
      | revertReturndata =>
          exact .revertReturndata ihRest
      | ite cond thenBranch elseBranch =>
          simp only [stmtTouchesUnsupportedContractSurface,
            Bool.or_eq_false_iff] at hstmtSurface
          rcases compileStmt_ite_ok_inv hhead with
            ⟨_, thenIR, elseIR, _, hthenCompile, helseCompile⟩
          exact .ite (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false
              hstmtSurface.1.1)
            (stmtListScopeCore_of_unsupportedContractSurface_eq_false
              fields scope thenBranch thenIR hstmtSurface.1.2 hthenCompile)
            (stmtListScopeCore_of_unsupportedContractSurface_eq_false
              fields scope elseBranch elseIR hstmtSurface.2 helseCompile) ihRest
      | forEach varName count body =>
          cases count with
          | literal n =>
              cases n with
              | zero =>
                  have hbodySurface :
                      stmtListTouchesUnsupportedContractSurface body = false := by
                    cases body with
                    | nil =>
                        simp [stmtListTouchesUnsupportedContractSurface]
                    | cons stmt rest =>
                        simp only [stmtTouchesUnsupportedContractSurface,
                          stmtListTouchesUnsupportedContractSurface,
                          Bool.or_eq_false_iff] at hstmtSurface
                        exact Bool.or_eq_false_iff.mpr hstmtSurface
                  simp only [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
                    bind, Except.bind] at hhead
                  cases hbody :
                      CompilationModel.compileStmtList fields [] [] .calldata [] false
                        (CompilationModel.forEachBodyScope scope varName (Expr.literal 0) body) [] body with
                  | error e =>
                      simp [FunctionBody.compileStmtListWithFork_cancun_eq_compileStmtList,
                        CompilationModel.compileExprWithInternals, pure, Except.pure, hbody] at hhead
                  | ok loopBodyIR =>
                      exact .forEachLiteralZero
                        (stmtListScopeCore_of_unsupportedContractSurface_eq_false
                          fields (CompilationModel.forEachBodyScope scope varName (Expr.literal 0) body)
                            body loopBodyIR hbodySurface hbody)
                        ihRest
              | succ n =>
                  cases body with
                  | nil =>
                      exact .forEachLiteralEmpty ihRest
                  | cons _ _ =>
                      simp [stmtTouchesUnsupportedContractSurface] at hstmtSurface
          | _ =>
              simp [stmtTouchesUnsupportedContractSurface] at hstmtSurface
      | _ => simp [stmtTouchesUnsupportedContractSurface] at hstmtSurface
termination_by sizeOf stmts

theorem stmtListScopeCore_prefix_of_compileStmtList_ok_of_stmtListTouchesUnsupportedContractSurface
    {fields : List Field}
    {scope : List String}
    {«prefix» «suffix» : List Stmt}
    {bodyIR : List YulStmt}
    (hsurface :
      stmtListTouchesUnsupportedContractSurface («prefix» ++ «suffix») = false)
    (hcompile :
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false scope [] («prefix» ++ «suffix») =
          Except.ok bodyIR) :
    StmtListScopeCore (fields.map (·.name)) «prefix» := by
  induction «prefix» generalizing scope «suffix» bodyIR with
  | nil => exact StmtListScopeCore.nil
  | cons stmt rest ih =>
      rcases FunctionBody.compileStmtList_cons_ok_inv hcompile with
        ⟨headIR, tailIR, hhead, htail, rfl⟩
      have hstmtSurface :
          stmtTouchesUnsupportedContractSurface stmt = false := by
        simpa [stmtListTouchesUnsupportedContractSurface] using
          (Bool.or_eq_false_iff.mp hsurface).1
      have hrestSurface :
          stmtListTouchesUnsupportedContractSurface (rest ++ «suffix») = false := by
        simpa [stmtListTouchesUnsupportedContractSurface] using
          (Bool.or_eq_false_iff.mp hsurface).2
      cases stmt with
      | letVar name value =>
          exact StmtListScopeCore.letVar
            (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false
              (by simpa [stmtTouchesUnsupportedContractSurface] using hstmtSurface))
            (ih hrestSurface htail)
      | assignVar name value =>
          exact StmtListScopeCore.assignVar
            (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false
              (by simpa [stmtTouchesUnsupportedContractSurface] using hstmtSurface))
            (ih hrestSurface htail)
      | setStorage fieldName value =>
          exact StmtListScopeCore.setStorage
            (by simp [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork] at hhead
                exact fieldName_mem_fields_of_compileSetStorage_ok hhead)
            (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false
              (by simpa [stmtTouchesUnsupportedContractSurface] using hstmtSurface))
            (ih hrestSurface htail)
      | setStorageAddr fieldName value =>
          exact StmtListScopeCore.setStorageAddr
            (by simp [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork] at hhead
                exact fieldName_mem_fields_of_compileSetStorage_ok hhead)
            (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false
              (by simpa [stmtTouchesUnsupportedContractSurface] using hstmtSurface))
            (ih hrestSurface htail)
      | setImmutable name value =>
          exact StmtListScopeCore.setImmutable
            (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false
              (by simpa [stmtTouchesUnsupportedContractSurface] using hstmtSurface))
            (ih hrestSurface htail)
      | setStorageWord fieldName wordOffset value =>
          exact StmtListScopeCore.setStorageWord
            (by
              simp only [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
                bind, Except.bind] at hhead
              rcases hfind : findFieldWithResolvedSlot fields fieldName with _ | ⟨f, slot⟩
              · simp [hfind] at hhead
              · exact fieldName_mem_fields_of_findFieldWithResolvedSlot_some hfind)
            (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false
              (by simpa [stmtTouchesUnsupportedContractSurface] using hstmtSurface))
            (ih hrestSurface htail)
      | require cond message =>
          exact StmtListScopeCore.require
            (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false
              (by simpa [stmtTouchesUnsupportedContractSurface] using hstmtSurface))
            (ih hrestSurface htail)
      | «return» value =>
          exact StmtListScopeCore.return_
            (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false
              (by simpa [stmtTouchesUnsupportedContractSurface] using hstmtSurface))
            (ih hrestSurface htail)
      | stop => exact StmtListScopeCore.stop (ih hrestSurface htail)
      | mstore offset value =>
          have hor := Bool.or_eq_false_iff.mp hstmtSurface
          exact StmtListScopeCore.mstore
            (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false
              (by simpa [stmtTouchesUnsupportedContractSurface] using hor.1))
            (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false
              (by simpa [stmtTouchesUnsupportedContractSurface] using hor.2))
            (ih hrestSurface htail)
      | tstore offset value =>
          have hor := Bool.or_eq_false_iff.mp hstmtSurface
          exact StmtListScopeCore.tstore
            (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false
              (by simpa [stmtTouchesUnsupportedContractSurface] using hor.1))
            (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false
              (by simpa [stmtTouchesUnsupportedContractSurface] using hor.2))
            (ih hrestSurface htail)
      | calldatacopy destOffset sourceOffset size =>
          simp only [stmtTouchesUnsupportedContractSurface,
            Bool.or_eq_false_iff] at hstmtSurface
          exact StmtListScopeCore.calldatacopy
            (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false hstmtSurface.1.1)
            (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false hstmtSurface.1.2)
            (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false hstmtSurface.2)
            (ih hrestSurface htail)
      | returndataCopy destOffset sourceOffset size =>
          simp only [stmtTouchesUnsupportedContractSurface,
            Bool.or_eq_false_iff] at hstmtSurface
          exact StmtListScopeCore.returndataCopy
            (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false hstmtSurface.1.1)
            (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false hstmtSurface.1.2)
            (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false hstmtSurface.2)
            (ih hrestSurface htail)
      | revertEmpty =>
          exact StmtListScopeCore.revertEmpty (ih hrestSurface htail)
      | revertReturndata =>
          exact StmtListScopeCore.revertReturndata (ih hrestSurface htail)
      | ite cond thenBranch elseBranch =>
          simp only [stmtTouchesUnsupportedContractSurface,
            Bool.or_eq_false_iff] at hstmtSurface
          rcases compileStmt_ite_ok_inv hhead with
            ⟨_, thenIR, elseIR, _, hthenCompile, helseCompile⟩
          exact StmtListScopeCore.ite
            (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false
              hstmtSurface.1.1)
            (stmtListScopeCore_of_unsupportedContractSurface_eq_false
              fields scope thenBranch thenIR hstmtSurface.1.2 hthenCompile)
            (stmtListScopeCore_of_unsupportedContractSurface_eq_false
              fields scope elseBranch elseIR hstmtSurface.2 helseCompile)
            (ih hrestSurface htail)
      | forEach varName count body =>
          cases count with
          | literal n =>
              cases n with
              | zero =>
                  have hbodySurface :
                      stmtListTouchesUnsupportedContractSurface body = false := by
                    cases body with
                    | nil =>
                        simp [stmtListTouchesUnsupportedContractSurface]
                    | cons stmt rest =>
                        simp only [stmtTouchesUnsupportedContractSurface,
                          stmtListTouchesUnsupportedContractSurface,
                          Bool.or_eq_false_iff] at hstmtSurface
                        exact Bool.or_eq_false_iff.mpr hstmtSurface
                  simp only [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
                    bind, Except.bind] at hhead
                  cases hbody :
                      CompilationModel.compileStmtList fields [] [] .calldata [] false
                        (CompilationModel.forEachBodyScope scope varName (Expr.literal 0) body) [] body with
                  | error e =>
                      simp [FunctionBody.compileStmtListWithFork_cancun_eq_compileStmtList,
                        CompilationModel.compileExprWithInternals, pure, Except.pure, hbody] at hhead
                  | ok loopBodyIR =>
                      exact StmtListScopeCore.forEachLiteralZero
                        (stmtListScopeCore_of_unsupportedContractSurface_eq_false
                          fields (CompilationModel.forEachBodyScope scope varName (Expr.literal 0) body)
                            body loopBodyIR hbodySurface hbody)
                        (ih hrestSurface htail)
              | succ n =>
                  cases body with
                  | nil =>
                      exact StmtListScopeCore.forEachLiteralEmpty (ih hrestSurface htail)
                  | cons _ _ =>
                      simp [stmtTouchesUnsupportedContractSurface] at hstmtSurface
          | _ =>
              simp [stmtTouchesUnsupportedContractSurface] at hstmtSurface
      | setMapping _ _ _ | setMappingWord _ _ _ _ | setMappingPackedWord _ _ _ _ _
      | setMapping2 _ _ _ _ | setMapping2Word _ _ _ _ _ | setMappingUint _ _ _
      | setMappingChain _ _ _ | forEachSetBit _ _ _
      | setStructMember _ _ _ _ | setStructMember2 _ _ _ _ _
      | storageArrayPush _ _ | storageArrayPop _ | setStorageArrayElement _ _ _
      | requireError _ _ _ | revertError _ _ | panicCode _ | panic _ | returnValues _ | returnArray _
      | returnBytes _ | returnStorageWords _ | returnCodeData _
      | emit _ _ | internalCall _ _ | internalCallAssign _ _ _
      | rawLog _ _ _ | externalCallBind _ _ _ | tryExternalCallBind _ _ _ _ | ecm _ _
      | unsafeBlock _ _ | unsafeYul _ | matchAdt _ _ _ =>
          simp [stmtTouchesUnsupportedContractSurface] at hstmtSurface

theorem stmtTouchesUnsupportedContractSurface_of_stmtListTouchesUnsupportedContractSurface_append_cons
    {«prefix» «suffix» : List Stmt}
    {stmt : Stmt}
    (hsurface :
      stmtListTouchesUnsupportedContractSurface («prefix» ++ stmt :: «suffix») = false) :
    stmtTouchesUnsupportedContractSurface stmt = false := by
  induction «prefix» with
  | nil =>
      simpa [stmtListTouchesUnsupportedContractSurface] using
        (Bool.or_eq_false_iff.mp hsurface).1
  | cons head rest ih =>
      simp [stmtListTouchesUnsupportedContractSurface] at hsurface
      exact ih hsurface.2

theorem mem_stmtNextScope_of_mem_scope
    {scope : List String}
    {stmt : Stmt}
    {name : String}
    (hmem : name ∈ scope) :
    name ∈ stmtNextScope scope stmt :=
  List.mem_append.mpr <| Or.inr hmem

private theorem mem_stmtNextScopeList_of_mem_scope
    {scope : List String}
    {stmts : List Stmt}
    {name : String}
    (hmem : name ∈ scope) :
    name ∈ List.foldl stmtNextScope scope stmts := by
  induction stmts generalizing scope with
  | nil =>
      simpa using hmem
  | cons stmt rest ih =>
      exact ih (mem_stmtNextScope_of_mem_scope hmem)

private def ConstructorArgsInScope
    (constructorArgCount : Option Nat)
    (scope : List String) : Prop :=
  ∀ idx count, constructorArgCount = some count → idx < count → s!"arg{idx}" ∈ scope

private theorem constructorArgsInScope_stmtNextScope
    {constructorArgCount : Option Nat}
    {scope : List String}
    {stmt : Stmt}
    (hscope : ConstructorArgsInScope constructorArgCount scope) :
    ConstructorArgsInScope constructorArgCount (stmtNextScope scope stmt) := by
  intro idx count hcount hidx
  exact mem_stmtNextScope_of_mem_scope (hscope idx count hcount hidx)

private theorem constructorArgsInScope_cons
    {constructorArgCount : Option Nat}
    {scope : List String}
    {name : String}
    (hscope : ConstructorArgsInScope constructorArgCount scope) :
    ConstructorArgsInScope constructorArgCount (name :: scope) := by
  intro idx count hcount hidx
  exact List.mem_cons_of_mem name (hscope idx count hcount hidx)

private theorem constructorArgsInScope_foldl_stmtNextScope
    {constructorArgCount : Option Nat}
    {scope : List String}
    {stmts : List Stmt}
    (hscope : ConstructorArgsInScope constructorArgCount scope) :
    ConstructorArgsInScope constructorArgCount (List.foldl stmtNextScope scope stmts) := by
  induction stmts generalizing scope with
  | nil =>
      exact hscope
  | cons stmt rest ih =>
      exact ih (constructorArgsInScope_stmtNextScope hscope)

private theorem constructorArgsInScope_none
    {scope : List String} :
    ConstructorArgsInScope none scope := by
  intro idx count hcount hidx
  cases hcount

section ScopedIdentifierValidation

variable {context : String} {params : List Param}
  {paramScope dynamicParams immutableNames localScope scope : List String}
  {constructorArgCount : Option Nat}

/-- A successful `Except` bind after a `Unit`-valued action exposes both halves. -/
private theorem except_bind_ok_inv {ε α : Type} {m : Except ε Unit} {k : Unit → Except ε α}
    {a : α} (h : (m >>= k) = Except.ok a) : m = Except.ok () ∧ k () = Except.ok a := by
  cases m with
  | error e => cases h
  | ok u => exact ⟨rfl, h⟩

private theorem exprBoundNamesInScope_of_exprBoundNames_eq {expr inner : Expr}
    (hinner : FunctionBody.exprBoundNamesInScope inner scope)
    (hnames : FunctionBody.exprBoundNames expr = FunctionBody.exprBoundNames inner) :
    FunctionBody.exprBoundNamesInScope expr scope := by
  intro name hmem
  exact hinner name (hnames ▸ hmem)

private theorem exprBoundNamesInScope_of_append {expr lhs rhs : Expr}
    (hlhs : FunctionBody.exprBoundNamesInScope lhs scope)
    (hrhs : FunctionBody.exprBoundNamesInScope rhs scope)
    (hnames : FunctionBody.exprBoundNames expr =
      FunctionBody.exprBoundNames lhs ++ FunctionBody.exprBoundNames rhs) :
    FunctionBody.exprBoundNamesInScope expr scope := by
  intro name hmem
  rw [hnames] at hmem
  rcases List.mem_append.mp hmem with h | h
  · exact hlhs name h
  · exact hrhs name h

private theorem exprBoundNamesInScope_of_append3 {expr a b c : Expr}
    (ha : FunctionBody.exprBoundNamesInScope a scope)
    (hb : FunctionBody.exprBoundNamesInScope b scope)
    (hc : FunctionBody.exprBoundNamesInScope c scope)
    (hnames : FunctionBody.exprBoundNames expr = FunctionBody.exprBoundNames a ++
      FunctionBody.exprBoundNames b ++ FunctionBody.exprBoundNames c) :
    FunctionBody.exprBoundNamesInScope expr scope := by
  intro name hmem
  rw [hnames] at hmem
  rcases List.mem_append.mp hmem with hab | h
  · rcases List.mem_append.mp hab with h | h
    · exact ha name h
    · exact hb name h
  · exact hc name h

private theorem exprBoundNamesInScope_of_pair_ok {expr lhs rhs : Expr}
    (hvalidate : (do
      validateScopedExprIdentifiers context params paramScope dynamicParams
        immutableNames localScope constructorArgCount lhs
      validateScopedExprIdentifiers context params paramScope dynamicParams
        immutableNames localScope constructorArgCount rhs) = Except.ok ())
    (ihL : validateScopedExprIdentifiers context params paramScope dynamicParams
      immutableNames localScope constructorArgCount lhs = Except.ok () →
      FunctionBody.exprBoundNamesInScope lhs scope)
    (ihR : validateScopedExprIdentifiers context params paramScope dynamicParams
      immutableNames localScope constructorArgCount rhs = Except.ok () →
      FunctionBody.exprBoundNamesInScope rhs scope)
    (hnames : FunctionBody.exprBoundNames expr =
      FunctionBody.exprBoundNames lhs ++ FunctionBody.exprBoundNames rhs) :
    FunctionBody.exprBoundNamesInScope expr scope :=
  have h := except_bind_ok_inv hvalidate
  exprBoundNamesInScope_of_append (ihL h.1) (ihR h.2) hnames

private theorem exprBoundNamesInScope_of_triple_ok {expr a b c : Expr}
    (hvalidate : (do
      validateScopedExprIdentifiers context params paramScope dynamicParams
        immutableNames localScope constructorArgCount a
      validateScopedExprIdentifiers context params paramScope dynamicParams
        immutableNames localScope constructorArgCount b
      validateScopedExprIdentifiers context params paramScope dynamicParams
        immutableNames localScope constructorArgCount c) = Except.ok ())
    (ihA : validateScopedExprIdentifiers context params paramScope dynamicParams
      immutableNames localScope constructorArgCount a = Except.ok () →
      FunctionBody.exprBoundNamesInScope a scope)
    (ihB : validateScopedExprIdentifiers context params paramScope dynamicParams
      immutableNames localScope constructorArgCount b = Except.ok () →
      FunctionBody.exprBoundNamesInScope b scope)
    (ihC : validateScopedExprIdentifiers context params paramScope dynamicParams
      immutableNames localScope constructorArgCount c = Except.ok () →
      FunctionBody.exprBoundNamesInScope c scope)
    (hnames : FunctionBody.exprBoundNames expr = FunctionBody.exprBoundNames a ++
      FunctionBody.exprBoundNames b ++ FunctionBody.exprBoundNames c) :
    FunctionBody.exprBoundNamesInScope expr scope :=
  have h := except_bind_ok_inv hvalidate
  have h' := except_bind_ok_inv h.2
  exprBoundNamesInScope_of_append3 (ihA h.1) (ihB h'.1) (ihC h'.2) hnames

private theorem exprBoundNamesInScope_param {name : String}
    (hvalidate : validateScopedExprIdentifiers context params paramScope dynamicParams
      immutableNames localScope constructorArgCount (.param name) = Except.ok ())
    (hparamsInScope : ∀ name, name ∈ paramScope → name ∈ scope) :
    FunctionBody.exprBoundNamesInScope (.param name) scope := by
  have hparam : name ∈ paramScope := by
    by_cases hname : name ∈ paramScope
    · exact hname
    · simp [validateScopedExprIdentifiers, hname] at hvalidate
  intro other hmem
  simp [FunctionBody.exprBoundNames] at hmem
  subst other
  exact hparamsInScope name hparam

private theorem exprBoundNamesInScope_localVar {name : String}
    (hvalidate : validateScopedExprIdentifiers context params paramScope dynamicParams
      immutableNames localScope constructorArgCount (.localVar name) = Except.ok ())
    (hlocalsInScope : ∀ name, name ∈ localScope → name ∈ scope) :
    FunctionBody.exprBoundNamesInScope (.localVar name) scope := by
  have hlocal : name ∈ localScope := by
    by_cases hname : name ∈ localScope
    · exact hname
    · simp [validateScopedExprIdentifiers, hname] at hvalidate
  intro other hmem
  simp [FunctionBody.exprBoundNames] at hmem
  subst other
  exact hlocalsInScope name hlocal

private theorem exprBoundNamesInScope_constructorArg {idx : Nat}
    (hvalidate : validateScopedExprIdentifiers context params paramScope dynamicParams
      immutableNames localScope constructorArgCount (.constructorArg idx) = Except.ok ())
    (hconstructorArgsInScope : ConstructorArgsInScope constructorArgCount scope) :
    FunctionBody.exprBoundNamesInScope (.constructorArg idx) scope := by
  have harg : ∃ count, constructorArgCount = some count ∧ idx < count := by
    cases constructorArgCount with
    | none => simp [validateScopedExprIdentifiers] at hvalidate
    | some count =>
        by_cases hidx : idx < count
        · exact ⟨count, rfl, hidx⟩
        · simp [validateScopedExprIdentifiers, hidx] at hvalidate
  rcases harg with ⟨count, hcount, hidx⟩
  intro name hmem
  simp [FunctionBody.exprBoundNames] at hmem
  subst name
  exact hconstructorArgsInScope idx count hcount hidx

private theorem exprBoundNamesInScope_of_validateScopedExprIdentifiers_core {expr : Expr}
    (hcore : FunctionBody.ExprCompileCore expr)
    (hvalidate : validateScopedExprIdentifiers context params paramScope dynamicParams
      immutableNames localScope constructorArgCount expr = Except.ok ())
    (hparamsInScope : ∀ name, name ∈ paramScope → name ∈ scope)
    (hlocalsInScope : ∀ name, name ∈ localScope → name ∈ scope)
    (hconstructorArgsInScope : ConstructorArgsInScope constructorArgCount scope) :
    FunctionBody.exprBoundNamesInScope expr scope := by
  induction hcore with
  | literal | caller | contractAddress | txOrigin | msgValue | blockTimestamp | blockNumber
  | chainid | blobbasefee | calldatasize | returndataSize =>
      exact fun _ hmem => by simp [FunctionBody.exprBoundNames] at hmem
  | param => exact exprBoundNamesInScope_param hvalidate hparamsInScope
  | localVar => exact exprBoundNamesInScope_localVar hvalidate hlocalsInScope
  | constructorArg => exact exprBoundNamesInScope_constructorArg hvalidate hconstructorArgsInScope
  | add _ _ ihL ihR | sub _ _ ihL ihR | mul _ _ ihL ihR | div _ _ ihL ihR | mod _ _ ihL ihR
  | eq _ _ ihL ihR | lt _ _ ihL ihR | gt _ _ ihL ihR | ge _ _ ihL ihR | le _ _ ihL ihR
  | bitAnd _ _ ihL ihR | bitOr _ _ ihL ihR | bitXor _ _ ihL ihR | keccak256 _ _ ihL ihR
  | slt _ _ ihL ihR | sgt _ _ ihL ihR | sdiv _ _ ihL ihR | smod _ _ ihL ihR | sar _ _ ihL ihR
  | byte _ _ ihL ihR | signextend _ _ ihL ihR | shl _ _ ihL ihR | shr _ _ ihL ihR
  | wMulDown _ _ ihL ihR =>
      exact exprBoundNamesInScope_of_pair_ok (by simpa only [validateScopedExprIdentifiers]
        using hvalidate) ihL ihR (by simp [FunctionBody.exprBoundNames])
  | min _ _ ihL ihR | max _ _ ihL ihR | ceilDiv _ _ ihL ihR | wDivUp _ _ ihL ihR
  | logicalAnd _ _ ihL ihR | logicalOr _ _ ihL ihR =>
      simp only [validateScopedExprIdentifiers] at hvalidate
      exact exprBoundNamesInScope_of_pair_ok (except_bind_ok_inv hvalidate).2 ihL ihR
        (by simp [FunctionBody.exprBoundNames])
  | builtinExp _ _ ihL ihR =>
      simp only [validateScopedExprIdentifiers, validateScopedExprIdentifiersList] at hvalidate
      have h := except_bind_ok_inv hvalidate
      exact exprBoundNamesInScope_of_append (ihL h.1) (ihR (except_bind_ok_inv h.2).1)
        (by simp [FunctionBody.exprBoundNames, FunctionBody.exprListBoundNames])
  | logicalNot _ ih | bitNot _ ih | tload _ ih | calldataload _ ih | mload _ ih
  | extcodesize _ ih | returndataOptionalBoolAt _ ih =>
      exact exprBoundNamesInScope_of_exprBoundNames_eq (ih (by simpa only
        [validateScopedExprIdentifiers] using hvalidate)) (by simp [FunctionBody.exprBoundNames])
  | mulDivDown _ _ _ ihA ihB ihC =>
      exact exprBoundNamesInScope_of_triple_ok (by simpa only [validateScopedExprIdentifiers]
        using hvalidate) ihA ihB ihC (by simp [FunctionBody.exprBoundNames])
  | mulDivUp _ _ _ ihA ihB ihC =>
      simp only [validateScopedExprIdentifiers] at hvalidate
      exact exprBoundNamesInScope_of_triple_ok (except_bind_ok_inv hvalidate).2 ihA ihB ihC
        (by simp [FunctionBody.exprBoundNames])
  | ite _ _ _ ihA ihB ihC =>
      simp only [validateScopedExprIdentifiers] at hvalidate
      split at hvalidate
      · cases hvalidate
      · exact exprBoundNamesInScope_of_triple_ok (except_bind_ok_inv hvalidate).2 ihA ihB ihC
          (by simp [FunctionBody.exprBoundNames])

/-- A successful `Except` bind ending in `pure` pins the returned value. -/
private theorem except_bind_pure_ok_inv {ε α : Type} {m : Except ε Unit} {a b : α}
    (h : (m >>= fun _ => pure a) = Except.ok b) : m = Except.ok () ∧ b = a := by
  cases m with
  | error e => cases h
  | ok u => cases h; exact ⟨rfl, rfl⟩

private theorem except_bind_ok_exists_inv {ε α β : Type} {m : Except ε β}
    {k : β → Except ε α} {a : α} (h : (m >>= k) = Except.ok a) :
    ∃ b, m = Except.ok b ∧ k b = Except.ok a := by
  cases m with
  | error e => cases h
  | ok b => exact ⟨b, rfl, h⟩

private theorem except_bind_bind_pure_ok_inv {ε α : Type} {m₁ m₂ : Except ε Unit} {a b : α}
    (h : (m₁ >>= fun _ => m₂ >>= fun _ => pure a) = Except.ok b) :
    m₁ = Except.ok () ∧ m₂ = Except.ok () ∧ b = a :=
  have h₁ := except_bind_ok_inv h
  ⟨h₁.1, except_bind_pure_ok_inv h₁.2⟩

private theorem except_bind_bind_bind_pure_ok_inv {ε α : Type} {m₁ m₂ m₃ : Except ε Unit}
    {a b : α} (h : (m₁ >>= fun _ => m₂ >>= fun _ => m₃ >>= fun _ => pure a) = Except.ok b) :
    m₁ = Except.ok () ∧ m₂ = Except.ok () ∧ m₃ = Except.ok () ∧ b = a :=
  have h₁ := except_bind_ok_inv h
  ⟨h₁.1, except_bind_bind_pure_ok_inv h₁.2⟩

private theorem validateScopedStmtIdentifiers_letVar_ok_inv {name : String} {value : Expr}
    {next : List String}
    (h : validateScopedStmtIdentifiers context params paramScope dynamicParams immutableNames
      localScope constructorArgCount (.letVar name value) = Except.ok next) :
    validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames
      localScope constructorArgCount value = Except.ok () ∧ next = name :: localScope := by
  simp only [validateScopedStmtIdentifiers] at h
  have h₁ := except_bind_ok_inv h
  refine ⟨h₁.1, ?_⟩
  have h₂ := h₁.2
  split at h₂
  · cases h₂
  · split at h₂
    · cases h₂
    · cases h₂; rfl

private theorem validateScopedStmtIdentifiers_assignVar_ok_inv {name : String} {value : Expr}
    {next : List String}
    (h : validateScopedStmtIdentifiers context params paramScope dynamicParams immutableNames
      localScope constructorArgCount (.assignVar name value) = Except.ok next) :
    validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames
      localScope constructorArgCount value = Except.ok () ∧ next = localScope := by
  simp only [validateScopedStmtIdentifiers] at h
  split at h
  · cases h
  · exact except_bind_pure_ok_inv (except_bind_ok_inv h).2

private theorem validateScopedStmtIdentifiers_setImmutable_ok_inv {name : String}
    {value : Expr} {next : List String}
    (h : validateScopedStmtIdentifiers context params paramScope dynamicParams immutableNames
      localScope constructorArgCount (.setImmutable name value) = Except.ok next) :
    validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames
      localScope constructorArgCount value = Except.ok () ∧ next = localScope := by
  unfold validateScopedStmtIdentifiers at h
  simp only at h
  split at h
  · split at h
    · exact except_bind_pure_ok_inv (except_bind_ok_inv h).2
    · cases h
  · cases h

private theorem validateScopedStmtIdentifiers_ite_ok_inv {cond : Expr}
    {thenBranch elseBranch : List Stmt} {next : List String}
    (h : validateScopedStmtIdentifiers context params paramScope dynamicParams immutableNames
      localScope constructorArgCount (.ite cond thenBranch elseBranch) = Except.ok next) :
    validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames
      localScope constructorArgCount cond = Except.ok () ∧
    (∃ thenScope, validateScopedStmtListIdentifiers context params paramScope dynamicParams
      immutableNames localScope constructorArgCount thenBranch = Except.ok thenScope) ∧
    (∃ elseScope, validateScopedStmtListIdentifiers context params paramScope dynamicParams
      immutableNames localScope constructorArgCount elseBranch = Except.ok elseScope) ∧
    next = localScope := by
  simp only [validateScopedStmtIdentifiers] at h
  obtain ⟨hcond, h⟩ := except_bind_ok_inv h
  obtain ⟨thenScope, hthen, h⟩ := except_bind_ok_exists_inv h
  obtain ⟨elseScope, helse, h⟩ := except_bind_ok_exists_inv h
  cases h
  exact ⟨hcond, ⟨thenScope, hthen⟩, ⟨elseScope, helse⟩, rfl⟩

private theorem validateScopedStmtIdentifiers_forEach_ok_inv {varName : String}
    {count : Expr} {body : List Stmt} {next : List String}
    (h : validateScopedStmtIdentifiers context params paramScope dynamicParams immutableNames
      localScope constructorArgCount (.forEach varName count body) = Except.ok next) :
    (∃ bodyScope, validateScopedStmtListIdentifiers context params paramScope dynamicParams
      immutableNames (varName :: localScope) constructorArgCount body = Except.ok bodyScope) ∧
    next = localScope := by
  simp only [validateScopedStmtIdentifiers] at h
  obtain ⟨bodyScope, hbody, h⟩ := except_bind_ok_exists_inv (except_bind_ok_inv h).2
  cases h
  exact ⟨⟨bodyScope, hbody⟩, rfl⟩

/-- Induction motive shared by the statement-list scope proofs: validating `stmts` from a local
scope covered by `scope` yields the scope discipline and covers the final local scope. -/
private def ScopedStmtListInvariant (fieldNames : List String) (context : String)
    (params : List Param) (paramScope dynamicParams immutableNames : List String)
    (constructorArgCount : Option Nat) (stmts : List Stmt) : Prop :=
  ∀ {localScope scope finalScope : List String},
    validateScopedStmtListIdentifiers context params paramScope dynamicParams immutableNames
      localScope constructorArgCount stmts = Except.ok finalScope →
    (∀ name, name ∈ paramScope → name ∈ scope) →
    (∀ name, name ∈ localScope → name ∈ scope) →
    ConstructorArgsInScope constructorArgCount scope →
    StmtListScopeDiscipline fieldNames scope stmts ∧
      ∀ name, name ∈ finalScope → name ∈ List.foldl stmtNextScope scope stmts

/-- Per-statement step of `ScopedStmtListInvariant`: a validated head statement extends the
tail's discipline and keeps its next local scope inside `stmtNextScope`. -/
private def ScopedStmtStep (fieldNames : List String) (context : String) (params : List Param)
    (paramScope dynamicParams immutableNames : List String) (constructorArgCount : Option Nat)
    (stmt : Stmt) (rest : List Stmt) : Prop :=
  ∀ {localScope scope next : List String},
    validateScopedStmtIdentifiers context params paramScope dynamicParams immutableNames
      localScope constructorArgCount stmt = Except.ok next →
    (∀ name, name ∈ paramScope → name ∈ scope) →
    (∀ name, name ∈ localScope → name ∈ scope) →
    ConstructorArgsInScope constructorArgCount scope →
    (StmtListScopeDiscipline fieldNames (stmtNextScope scope stmt) rest →
      StmtListScopeDiscipline fieldNames scope (stmt :: rest)) ∧
    ∀ name, name ∈ next → name ∈ stmtNextScope scope stmt

variable {fieldNames : List String}

local notation "StmtListInvariant" =>
  ScopedStmtListInvariant fieldNames context params paramScope dynamicParams immutableNames
    constructorArgCount

local notation "StmtStep" =>
  ScopedStmtStep fieldNames context params paramScope dynamicParams immutableNames
    constructorArgCount

private theorem scopedStmtListInvariant_nil : StmtListInvariant [] := by
  intro localScope scope finalScope hvalidate _ hlocalsInScope _
  simp only [validateScopedStmtListIdentifiers, pure, Except.pure] at hvalidate
  cases hvalidate
  exact ⟨StmtListScopeDiscipline.nil, hlocalsInScope⟩

private theorem scopedStmtListInvariant_cons {stmt : Stmt} {rest : List Stmt}
    (hstep : StmtStep stmt rest) (ih : StmtListInvariant rest) :
    StmtListInvariant (stmt :: rest) := by
  intro localScope scope finalScope hvalidate hparamsInScope hlocalsInScope hconstructorArgs
  obtain ⟨next, hstmt, hrest⟩ := validateScopedStmtListIdentifiers_cons_ok_inv hvalidate
  obtain ⟨hmk, hnext⟩ := hstep hstmt hparamsInScope hlocalsInScope hconstructorArgs
  obtain ⟨hdisc, hnames⟩ := ih hrest
    (fun name hname => mem_stmtNextScope_of_mem_scope (hparamsInScope name hname)) hnext
    (constructorArgsInScope_stmtNextScope hconstructorArgs)
  exact ⟨hmk hdisc, hnames⟩

/-- Steps whose head validates a single expression and keeps the local scope. -/
private theorem scopedStmtStep_of_expr {stmt : Stmt} {value : Expr} {rest : List Stmt}
    (hcore : FunctionBody.ExprCompileCore value)
    (hinv : ∀ {localScope next : List String},
      validateScopedStmtIdentifiers context params paramScope dynamicParams immutableNames
        localScope constructorArgCount stmt = Except.ok next →
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames
        localScope constructorArgCount value = Except.ok () ∧ next = localScope)
    (hmk : ∀ {scope : List String}, FunctionBody.exprBoundNamesInScope value scope →
      StmtListScopeDiscipline fieldNames (stmtNextScope scope stmt) rest →
      StmtListScopeDiscipline fieldNames scope (stmt :: rest)) :
    StmtStep stmt rest := by
  intro localScope scope next hstmt hparamsInScope hlocalsInScope hconstructorArgs
  obtain ⟨hvalue, rfl⟩ := hinv hstmt
  exact ⟨hmk (exprBoundNamesInScope_of_validateScopedExprIdentifiers_core
      hcore hvalue hparamsInScope hlocalsInScope hconstructorArgs),
    fun name hname => mem_stmtNextScope_of_mem_scope (hlocalsInScope name hname)⟩

/-- Steps whose head validates two expressions and keeps the local scope. -/
private theorem scopedStmtStep_of_expr2 {stmt : Stmt} {a b : Expr} {rest : List Stmt}
    (hcoreA : FunctionBody.ExprCompileCore a) (hcoreB : FunctionBody.ExprCompileCore b)
    (hinv : ∀ {localScope next : List String},
      validateScopedStmtIdentifiers context params paramScope dynamicParams immutableNames
        localScope constructorArgCount stmt = Except.ok next →
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames
        localScope constructorArgCount a = Except.ok () ∧
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames
        localScope constructorArgCount b = Except.ok () ∧ next = localScope)
    (hmk : ∀ {scope : List String}, FunctionBody.exprBoundNamesInScope a scope →
      FunctionBody.exprBoundNamesInScope b scope →
      StmtListScopeDiscipline fieldNames (stmtNextScope scope stmt) rest →
      StmtListScopeDiscipline fieldNames scope (stmt :: rest)) :
    StmtStep stmt rest := by
  intro localScope scope next hstmt hparamsInScope hlocalsInScope hconstructorArgs
  obtain ⟨ha, hb, rfl⟩ := hinv hstmt
  exact ⟨hmk
      (exprBoundNamesInScope_of_validateScopedExprIdentifiers_core
        hcoreA ha hparamsInScope hlocalsInScope hconstructorArgs)
      (exprBoundNamesInScope_of_validateScopedExprIdentifiers_core
        hcoreB hb hparamsInScope hlocalsInScope hconstructorArgs),
    fun name hname => mem_stmtNextScope_of_mem_scope (hlocalsInScope name hname)⟩

/-- Steps whose head validates three expressions and keeps the local scope. -/
private theorem scopedStmtStep_of_expr3 {stmt : Stmt} {a b c : Expr} {rest : List Stmt}
    (hcoreA : FunctionBody.ExprCompileCore a) (hcoreB : FunctionBody.ExprCompileCore b)
    (hcoreC : FunctionBody.ExprCompileCore c)
    (hinv : ∀ {localScope next : List String},
      validateScopedStmtIdentifiers context params paramScope dynamicParams immutableNames
        localScope constructorArgCount stmt = Except.ok next →
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames
        localScope constructorArgCount a = Except.ok () ∧
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames
        localScope constructorArgCount b = Except.ok () ∧
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames
        localScope constructorArgCount c = Except.ok () ∧ next = localScope)
    (hmk : ∀ {scope : List String}, FunctionBody.exprBoundNamesInScope a scope →
      FunctionBody.exprBoundNamesInScope b scope → FunctionBody.exprBoundNamesInScope c scope →
      StmtListScopeDiscipline fieldNames (stmtNextScope scope stmt) rest →
      StmtListScopeDiscipline fieldNames scope (stmt :: rest)) :
    StmtStep stmt rest := by
  intro localScope scope next hstmt hparamsInScope hlocalsInScope hconstructorArgs
  obtain ⟨ha, hb, hc, rfl⟩ := hinv hstmt
  exact ⟨hmk
      (exprBoundNamesInScope_of_validateScopedExprIdentifiers_core
        hcoreA ha hparamsInScope hlocalsInScope hconstructorArgs)
      (exprBoundNamesInScope_of_validateScopedExprIdentifiers_core
        hcoreB hb hparamsInScope hlocalsInScope hconstructorArgs)
      (exprBoundNamesInScope_of_validateScopedExprIdentifiers_core
        hcoreC hc hparamsInScope hlocalsInScope hconstructorArgs),
    fun name hname => mem_stmtNextScope_of_mem_scope (hlocalsInScope name hname)⟩

/-- Steps whose head validates nothing, binds nothing, and keeps the local scope. -/
private theorem scopedStmtStep_of_pure {stmt : Stmt} {rest : List Stmt}
    (hinv : ∀ {localScope next : List String},
      validateScopedStmtIdentifiers context params paramScope dynamicParams immutableNames
        localScope constructorArgCount stmt = Except.ok next → next = localScope)
    (hbind : collectStmtBindNames stmt = [])
    (hmk : ∀ {scope : List String}, StmtListScopeDiscipline fieldNames scope rest →
      StmtListScopeDiscipline fieldNames scope (stmt :: rest)) :
    StmtStep stmt rest := by
  intro localScope scope next hstmt _ hlocalsInScope _
  cases hinv hstmt
  simp only [stmtNextScope, hbind, List.nil_append]
  exact ⟨hmk, hlocalsInScope⟩

private theorem scopedStmtListInvariant_letVar {name : String} {value : Expr}
    {rest : List Stmt} (hcore : FunctionBody.ExprCompileCore value)
    (ih : StmtListInvariant rest) : StmtListInvariant (.letVar name value :: rest) := by
  refine scopedStmtListInvariant_cons ?_ ih
  intro localScope scope next hstmt hparamsInScope hlocalsInScope hconstructorArgs
  obtain ⟨hvalue, rfl⟩ := validateScopedStmtIdentifiers_letVar_ok_inv hstmt
  refine ⟨StmtListScopeDiscipline.letVar hcore
    (exprBoundNamesInScope_of_validateScopedExprIdentifiers_core
      hcore hvalue hparamsInScope hlocalsInScope hconstructorArgs), ?_⟩
  intro other hmem
  rcases List.mem_cons.mp hmem with rfl | hmem
  · simp [stmtNextScope, collectStmtBindNames]
  · exact mem_stmtNextScope_of_mem_scope (hlocalsInScope other hmem)

private theorem scopedStmtListInvariant_assignVar {name : String} {value : Expr}
    {rest : List Stmt} (hcore : FunctionBody.ExprCompileCore value)
    (ih : StmtListInvariant rest) : StmtListInvariant (.assignVar name value :: rest) :=
  scopedStmtListInvariant_cons (scopedStmtStep_of_expr hcore
    validateScopedStmtIdentifiers_assignVar_ok_inv (StmtListScopeDiscipline.assignVar hcore)) ih

private theorem scopedStmtListInvariant_require {cond : Expr} {message : String}
    {rest : List Stmt} (hcore : FunctionBody.ExprCompileCore cond)
    (ih : StmtListInvariant rest) : StmtListInvariant (.require cond message :: rest) :=
  scopedStmtListInvariant_cons (scopedStmtStep_of_expr hcore
    (fun h => except_bind_pure_ok_inv (by simpa only [validateScopedStmtIdentifiers] using h))
    (StmtListScopeDiscipline.require hcore)) ih

private theorem scopedStmtListInvariant_return {value : Expr} {rest : List Stmt}
    (hcore : FunctionBody.ExprCompileCore value)
    (ih : StmtListInvariant rest) : StmtListInvariant (.return value :: rest) :=
  scopedStmtListInvariant_cons (scopedStmtStep_of_expr hcore
    (fun h => except_bind_pure_ok_inv (by simpa only [validateScopedStmtIdentifiers] using h))
    (StmtListScopeDiscipline.return_ hcore)) ih

private theorem scopedStmtListInvariant_setStorage {fieldName : String} {value : Expr}
    {rest : List Stmt} (hfield : fieldName ∈ fieldNames)
    (hcore : FunctionBody.ExprCompileCore value) (ih : StmtListInvariant rest) :
    StmtListInvariant (.setStorage fieldName value :: rest) :=
  scopedStmtListInvariant_cons (scopedStmtStep_of_expr hcore
    (fun h => except_bind_pure_ok_inv (by simpa only [validateScopedStmtIdentifiers] using h))
    (StmtListScopeDiscipline.setStorage hfield hcore)) ih

private theorem scopedStmtListInvariant_setStorageAddr {fieldName : String} {value : Expr}
    {rest : List Stmt} (hfield : fieldName ∈ fieldNames)
    (hcore : FunctionBody.ExprCompileCore value) (ih : StmtListInvariant rest) :
    StmtListInvariant (.setStorageAddr fieldName value :: rest) :=
  scopedStmtListInvariant_cons (scopedStmtStep_of_expr hcore
    (fun h => except_bind_pure_ok_inv (by simpa only [validateScopedStmtIdentifiers] using h))
    (StmtListScopeDiscipline.setStorageAddr hfield hcore)) ih

private theorem scopedStmtListInvariant_setStorageWord {fieldName : String}
    {wordOffset : Nat} {value : Expr} {rest : List Stmt} (hfield : fieldName ∈ fieldNames)
    (hcore : FunctionBody.ExprCompileCore value) (ih : StmtListInvariant rest) :
    StmtListInvariant (.setStorageWord fieldName wordOffset value :: rest) :=
  scopedStmtListInvariant_cons (scopedStmtStep_of_expr hcore
    (fun h => except_bind_pure_ok_inv (by simpa only [validateScopedStmtIdentifiers] using h))
    (StmtListScopeDiscipline.setStorageWord hfield hcore)) ih

private theorem scopedStmtListInvariant_setImmutable {name : String} {value : Expr}
    {rest : List Stmt} (hcore : FunctionBody.ExprCompileCore value)
    (ih : StmtListInvariant rest) : StmtListInvariant (.setImmutable name value :: rest) :=
  scopedStmtListInvariant_cons (scopedStmtStep_of_expr hcore
    validateScopedStmtIdentifiers_setImmutable_ok_inv
    (StmtListScopeDiscipline.setImmutable hcore)) ih

private theorem scopedStmtListInvariant_mstore {offset value : Expr} {rest : List Stmt}
    (hcoreOffset : FunctionBody.ExprCompileCore offset)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (ih : StmtListInvariant rest) : StmtListInvariant (.mstore offset value :: rest) :=
  scopedStmtListInvariant_cons (scopedStmtStep_of_expr2 hcoreOffset hcoreValue
    (fun h => except_bind_bind_pure_ok_inv (by
      simpa only [validateScopedStmtIdentifiers] using h))
    (fun hoffset hvalue => StmtListScopeDiscipline.mstore hcoreOffset hoffset hcoreValue hvalue))
    ih

private theorem scopedStmtListInvariant_tstore {offset value : Expr} {rest : List Stmt}
    (hcoreOffset : FunctionBody.ExprCompileCore offset)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (ih : StmtListInvariant rest) : StmtListInvariant (.tstore offset value :: rest) :=
  scopedStmtListInvariant_cons (scopedStmtStep_of_expr2 hcoreOffset hcoreValue
    (fun h => except_bind_bind_pure_ok_inv (by
      simpa only [validateScopedStmtIdentifiers] using h))
    (fun hoffset hvalue => StmtListScopeDiscipline.tstore hcoreOffset hoffset hcoreValue hvalue))
    ih

private theorem scopedStmtListInvariant_calldatacopy {destOffset sourceOffset size : Expr}
    {rest : List Stmt} (hcoreDest : FunctionBody.ExprCompileCore destOffset)
    (hcoreSource : FunctionBody.ExprCompileCore sourceOffset)
    (hcoreSize : FunctionBody.ExprCompileCore size) (ih : StmtListInvariant rest) :
    StmtListInvariant (.calldatacopy destOffset sourceOffset size :: rest) :=
  scopedStmtListInvariant_cons (scopedStmtStep_of_expr3 hcoreDest hcoreSource hcoreSize
    (fun h => except_bind_bind_bind_pure_ok_inv (by
      simpa only [validateScopedStmtIdentifiers] using h))
    (fun hdest hsource hsize => StmtListScopeDiscipline.calldatacopy
      hcoreDest hdest hcoreSource hsource hcoreSize hsize)) ih

private theorem scopedStmtListInvariant_returndataCopy {destOffset sourceOffset size : Expr}
    {rest : List Stmt} (hcoreDest : FunctionBody.ExprCompileCore destOffset)
    (hcoreSource : FunctionBody.ExprCompileCore sourceOffset)
    (hcoreSize : FunctionBody.ExprCompileCore size) (ih : StmtListInvariant rest) :
    StmtListInvariant (.returndataCopy destOffset sourceOffset size :: rest) :=
  scopedStmtListInvariant_cons (scopedStmtStep_of_expr3 hcoreDest hcoreSource hcoreSize
    (fun h => except_bind_bind_bind_pure_ok_inv (by
      simpa only [validateScopedStmtIdentifiers] using h))
    (fun hdest hsource hsize => StmtListScopeDiscipline.returndataCopy
      hcoreDest hdest hcoreSource hsource hcoreSize hsize)) ih

private theorem scopedStmtListInvariant_stop {rest : List Stmt}
    (ih : StmtListInvariant rest) : StmtListInvariant (.stop :: rest) :=
  scopedStmtListInvariant_cons (scopedStmtStep_of_pure
    (fun h => by simp only [validateScopedStmtIdentifiers, pure, Except.pure] at h; cases h; rfl)
    (by simp [collectStmtBindNames]) StmtListScopeDiscipline.stop) ih

private theorem scopedStmtListInvariant_revertEmpty {rest : List Stmt}
    (ih : StmtListInvariant rest) : StmtListInvariant (.revertEmpty :: rest) :=
  scopedStmtListInvariant_cons (scopedStmtStep_of_pure
    (fun h => by simp only [validateScopedStmtIdentifiers, pure, Except.pure] at h; cases h; rfl)
    (by simp [collectStmtBindNames]) StmtListScopeDiscipline.revertEmpty) ih

private theorem scopedStmtListInvariant_revertReturndata {rest : List Stmt}
    (ih : StmtListInvariant rest) : StmtListInvariant (.revertReturndata :: rest) :=
  scopedStmtListInvariant_cons (scopedStmtStep_of_pure
    (fun h => by simp only [validateScopedStmtIdentifiers, pure, Except.pure] at h; cases h; rfl)
    (by simp [collectStmtBindNames]) StmtListScopeDiscipline.revertReturndata) ih

private theorem scopedStmtListInvariant_ite {cond : Expr} {thenBranch elseBranch rest : List Stmt}
    (hcore : FunctionBody.ExprCompileCore cond) (ihThen : StmtListInvariant thenBranch)
    (ihElse : StmtListInvariant elseBranch) (ih : StmtListInvariant rest) :
    StmtListInvariant (.ite cond thenBranch elseBranch :: rest) := by
  refine scopedStmtListInvariant_cons ?_ ih
  intro localScope scope next hstmt hparamsInScope hlocalsInScope hconstructorArgs
  obtain ⟨hcond, ⟨_, hthen⟩, ⟨_, helse⟩, rfl⟩ := validateScopedStmtIdentifiers_ite_ok_inv hstmt
  exact ⟨StmtListScopeDiscipline.ite hcore
      (exprBoundNamesInScope_of_validateScopedExprIdentifiers_core
        hcore hcond hparamsInScope hlocalsInScope hconstructorArgs)
      (ihThen hthen hparamsInScope hlocalsInScope hconstructorArgs).1
      (ihElse helse hparamsInScope hlocalsInScope hconstructorArgs).1,
    fun name hname => mem_stmtNextScope_of_mem_scope (hlocalsInScope name hname)⟩

private theorem scopedStmtListInvariant_forEachLiteralZero {varName : String}
    {body rest : List Stmt} (ihBody : StmtListInvariant body) (ih : StmtListInvariant rest) :
    StmtListInvariant (.forEach varName (.literal 0) body :: rest) := by
  refine scopedStmtListInvariant_cons ?_ ih
  intro localScope scope next hstmt hparamsInScope hlocalsInScope hconstructorArgs
  obtain ⟨⟨_, hbody⟩, rfl⟩ := validateScopedStmtIdentifiers_forEach_ok_inv hstmt
  exact ⟨StmtListScopeDiscipline.forEachLiteralZero (ihBody hbody
      (fun name hname => List.mem_cons_of_mem varName (hparamsInScope name hname))
      (fun name hname => List.cons_subset_cons varName hlocalsInScope hname)
      (constructorArgsInScope_cons hconstructorArgs)).1,
    fun name hname => mem_stmtNextScope_of_mem_scope (hlocalsInScope name hname)⟩

private theorem scopedStmtListInvariant_forEachLiteralEmpty {varName : String} {n : Nat}
    {rest : List Stmt} (ih : StmtListInvariant rest) :
    StmtListInvariant (.forEach varName (.literal n) [] :: rest) := by
  refine scopedStmtListInvariant_cons ?_ ih
  intro localScope scope next hstmt _ hlocalsInScope _
  obtain ⟨-, rfl⟩ := validateScopedStmtIdentifiers_forEach_ok_inv hstmt
  exact ⟨StmtListScopeDiscipline.forEachLiteralEmpty,
    fun name hname => mem_stmtNextScope_of_mem_scope (hlocalsInScope name hname)⟩

private theorem scopedStmtListInvariant_of_core {stmts : List Stmt}
    (hcore : StmtListScopeCore fieldNames stmts) : StmtListInvariant stmts := by
  induction hcore with
  | nil => exact scopedStmtListInvariant_nil
  | letVar hv _ ih => exact scopedStmtListInvariant_letVar hv ih
  | assignVar hv _ ih => exact scopedStmtListInvariant_assignVar hv ih
  | require hc _ ih => exact scopedStmtListInvariant_require hc ih
  | return_ hv _ ih => exact scopedStmtListInvariant_return hv ih
  | stop _ ih => exact scopedStmtListInvariant_stop ih
  | setStorage hf hv _ ih => exact scopedStmtListInvariant_setStorage hf hv ih
  | setStorageAddr hf hv _ ih => exact scopedStmtListInvariant_setStorageAddr hf hv ih
  | setImmutable hv _ ih => exact scopedStmtListInvariant_setImmutable hv ih
  | setStorageWord hf hv _ ih => exact scopedStmtListInvariant_setStorageWord hf hv ih
  | mstore ho hv _ ih => exact scopedStmtListInvariant_mstore ho hv ih
  | tstore ho hv _ ih => exact scopedStmtListInvariant_tstore ho hv ih
  | calldatacopy hd hs hz _ ih => exact scopedStmtListInvariant_calldatacopy hd hs hz ih
  | returndataCopy hd hs hz _ ih => exact scopedStmtListInvariant_returndataCopy hd hs hz ih
  | revertEmpty _ ih => exact scopedStmtListInvariant_revertEmpty ih
  | revertReturndata _ ih => exact scopedStmtListInvariant_revertReturndata ih
  | ite hc _ _ _ ihT ihE ih => exact scopedStmtListInvariant_ite hc ihT ihE ih
  | forEachLiteralZero _ _ ihB ih => exact scopedStmtListInvariant_forEachLiteralZero ihB ih
  | forEachLiteralEmpty _ ih => exact scopedStmtListInvariant_forEachLiteralEmpty ih

private theorem stmtListScopeDiscipline_of_validateScopedStmtListIdentifiers
    {stmts : List Stmt} {finalScope : List String}
    (hcore : StmtListScopeCore fieldNames stmts)
    (hvalidate : validateScopedStmtListIdentifiers context params paramScope dynamicParams
      immutableNames localScope constructorArgCount stmts = Except.ok finalScope)
    (hparamsInScope : ∀ name, name ∈ paramScope → name ∈ scope)
    (hlocalsInScope : ∀ name, name ∈ localScope → name ∈ scope)
    (hconstructorArgsInScope : ConstructorArgsInScope constructorArgCount scope) :
    StmtListScopeDiscipline fieldNames scope stmts :=
  (scopedStmtListInvariant_of_core hcore hvalidate
    hparamsInScope hlocalsInScope hconstructorArgsInScope).1

private theorem scopeNamesPresent_foldl_stmtNextScope_of_validateScopedStmtListIdentifiers
    {stmts : List Stmt} {finalScope : List String}
    (hcore : StmtListScopeCore fieldNames stmts)
    (hvalidate : validateScopedStmtListIdentifiers context params paramScope dynamicParams
      immutableNames localScope constructorArgCount stmts = Except.ok finalScope)
    (hparamsInScope : ∀ name, name ∈ paramScope → name ∈ scope)
    (hlocalsInScope : ∀ name, name ∈ localScope → name ∈ scope)
    (hconstructorArgsInScope : ConstructorArgsInScope constructorArgCount scope) :
    ∀ name, name ∈ finalScope → name ∈ List.foldl stmtNextScope scope stmts :=
  (scopedStmtListInvariant_of_core hcore hvalidate
    hparamsInScope hlocalsInScope hconstructorArgsInScope).2
end ScopedIdentifierValidation

theorem stmtListScopeDiscipline_of_validateFunctionIdentifierReferences_prefix
    {spec : FunctionSpec}
    {fieldNames : List String}
    {«prefix» «suffix» : List Stmt}
    (hcore : StmtListScopeCore fieldNames «prefix»)
    (hvalidate : validateFunctionIdentifierReferences spec = Except.ok ())
    (hparamScope : paramScopeNames spec.params = spec.params.map (·.name))
    (hbody : spec.body = «prefix» ++ «suffix») :
    StmtListScopeDiscipline fieldNames (spec.params.map (·.name)) «prefix» := by
  rcases validateFunctionIdentifierReferences_prefix_ok hvalidate hbody with
    ⟨finalLocalScope, hprefixValidate⟩
  apply stmtListScopeDiscipline_of_validateScopedStmtListIdentifiers
    (paramScope := paramScopeNames spec.params)
    (dynamicParams := dynamicParamBases spec.params)
    (localScope := [])
    (finalScope := finalLocalScope)
    hcore
    hprefixValidate
  · intro name hmem
    rw [hparamScope] at hmem
    simpa using hmem
  · intro name hmem
    simp at hmem
  · exact constructorArgsInScope_none

theorem exprBoundNamesInScope_setStorage_of_validateFunctionIdentifierReferences
    {spec : FunctionSpec}
    {fieldNames : List String}
    {«prefix» «suffix» : List Stmt}
    {fieldName : String}
    {value : Expr}
    (hprefixCore : StmtListScopeCore fieldNames «prefix»)
    (hvalueCore : FunctionBody.ExprCompileCore value)
    (hvalidate : validateFunctionIdentifierReferences spec = Except.ok ())
    (hparamScope : paramScopeNames spec.params = spec.params.map (·.name))
    (hbody : spec.body = «prefix» ++ .setStorage fieldName value :: «suffix») :
    FunctionBody.exprBoundNamesInScope
      value
      (List.foldl stmtNextScope (spec.params.map (·.name)) «prefix») := by
  rcases validateFunctionIdentifierReferences_prefix_stmt_ok hvalidate hbody with
    ⟨localScope, nextScope, hprefixValidate, hstmtValidate⟩
  have hstmt' := hstmtValidate
  unfold validateScopedStmtIdentifiers at hstmt'
  revert hstmt'
  rcases hExprVal : validateScopedExprIdentifiers _ _ _ _ [] localScope _ value with _ | _
  · intro h; simp [bind, Except.bind] at h
  · simp only [bind, Except.bind, pure, Except.pure]
    intro h; cases h
    apply exprBoundNamesInScope_of_validateScopedExprIdentifiers_core
      (paramScope := paramScopeNames spec.params)
      (dynamicParams := dynamicParamBases spec.params)
      (localScope := localScope)
      (scope := List.foldl stmtNextScope (spec.params.map (·.name)) «prefix»)
      hvalueCore hExprVal
    · intro name hname
      rw [hparamScope] at hname
      exact mem_stmtNextScopeList_of_mem_scope hname
    · intro name hname
      exact scopeNamesPresent_foldl_stmtNextScope_of_validateScopedStmtListIdentifiers
        hprefixCore hprefixValidate
        (by intro other hmem; rw [hparamScope] at hmem; simpa using hmem)
        (by intro other hmem; simp at hmem)
        constructorArgsInScope_none name hname
    · exact constructorArgsInScope_foldl_stmtNextScope constructorArgsInScope_none

/-- `collectExprNames` skips the reserved `builtinExpName` sentinel, so the exp
lane contributes exactly the names of its two operands. -/
private theorem collectExprNames_builtinExp_split
    {base exponent : Expr} {name : String}
    (hmem : name ∈ collectExprNames (.externalCall builtinExpName [base, exponent])) :
    name ∈ collectExprNames base ∨ name ∈ collectExprNames exponent := by
  simp only [collectExprNames, collectExprListNames, beq_self_eq_true, if_true,
    List.append_nil] at hmem
  exact List.mem_append.mp hmem

theorem collectExprNames_mem_exprBoundNames_of_core
    {expr : Expr}
    (hcore : FunctionBody.ExprCompileCore expr) :
    ∀ name, name ∈ collectExprNames expr → name ∈ FunctionBody.exprBoundNames expr := by
  induction hcore with
  | literal _ | caller | contractAddress | txOrigin | msgValue | blockTimestamp | blockNumber | chainid
  | blobbasefee | calldatasize | returndataSize | constructorArg _ =>
      intro name hmem; simp [collectExprNames] at hmem
  | param _ | localVar _ =>
      intro name hmem; simpa [collectExprNames, FunctionBody.exprBoundNames] using hmem
  | add hL hR ihL ihR | sub hL hR ihL ihR | mul hL hR ihL ihR
  | div hL hR ihL ihR | mod hL hR ihL ihR | eq hL hR ihL ihR
  | lt hL hR ihL ihR | gt hL hR ihL ihR | ge hL hR ihL ihR | le hL hR ihL ihR
  | bitAnd hL hR ihL ihR | bitOr hL hR ihL ihR | bitXor hL hR ihL ihR
  | logicalAnd hL hR ihL ihR | logicalOr hL hR ihL ihR
  | shl hL hR ihL ihR | shr hL hR ihL ihR | min hL hR ihL ihR | max hL hR ihL ihR
  | ceilDiv hL hR ihL ihR | wMulDown hL hR ihL ihR | wDivUp hL hR ihL ihR
  | keccak256 hL hR ihL ihR
  | slt hL hR ihL ihR | sgt hL hR ihL ihR | sdiv hL hR ihL ihR
  | smod hL hR ihL ihR | sar hL hR ihL ihR | byte hL hR ihL ihR | signextend hL hR ihL ihR =>
      intro name hmem
      simp [collectExprNames, FunctionBody.exprBoundNames] at hmem ⊢
      rcases hmem with hmem | hmem
      · exact Or.inl (ihL _ hmem)
      · exact Or.inr (ihR _ hmem)
  | logicalNot h ih | bitNot h ih | tload h ih | calldataload h ih | mload h ih
  | extcodesize h ih | returndataOptionalBoolAt h ih =>
      intro name hmem; simp [collectExprNames] at hmem
      simpa [FunctionBody.exprBoundNames] using ih _ hmem
  | ite hC hT hE ihC ihT ihE =>
      intro name hmem; simp only [collectExprNames] at hmem; simp only [FunctionBody.exprBoundNames]
      rcases List.mem_append.mp hmem with hmem12 | hmem
      · rcases List.mem_append.mp hmem12 with h | h
        · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl (ihC _ h))))
        · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr (ihT _ h))))
      · exact List.mem_append.mpr (Or.inr (ihE _ hmem))
  | mulDivDown hA hB hC ihA ihB ihC | mulDivUp hA hB hC ihA ihB ihC =>
      intro name hmem; simp only [collectExprNames] at hmem; simp only [FunctionBody.exprBoundNames]
      rcases List.mem_append.mp hmem with hmem12 | hmem
      · rcases List.mem_append.mp hmem12 with h | h
        · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl (ihA _ h))))
        · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr (ihB _ h))))
      · exact List.mem_append.mpr (Or.inr (ihC _ hmem))
  | builtinExp hB hE ihB ihE =>
      intro name hmem
      simp only [FunctionBody.exprBoundNames, FunctionBody.exprListBoundNames, List.append_nil]
      exact List.mem_append.mpr
        ((collectExprNames_builtinExp_split hmem).imp (ihB name) (ihE name))

private theorem mem_foldl_stmtNextScope_of_mem_scope
    {scope : List String}
    {stmts : List Stmt}
    {name : String}
    (hmem : name ∈ scope) :
    name ∈ List.foldl stmtNextScope scope stmts := by
  induction stmts generalizing scope with
  | nil => simpa
  | cons stmt rest ih =>
      simp only [List.foldl]
      exact ih (by simp [stmtNextScope]; right; exact hmem)

theorem stmtListBindNames_subset_foldl_stmtNextScope
    {scope : List String}
    {stmts : List Stmt}
    {name : String}
    (hmem : name ∈ collectStmtListBindNames stmts) :
    name ∈ List.foldl stmtNextScope scope stmts := by
  induction stmts generalizing scope with
  | nil => simp [collectStmtListBindNames] at hmem
  | cons stmt rest ih =>
      simp [collectStmtListBindNames] at hmem
      simp only [List.foldl]
      rcases hmem with hstmt | hrest
      · exact mem_foldl_stmtNextScope_of_mem_scope (by
          simp [stmtNextScope]; exact Or.inl hstmt)
      · exact ih hrest

/-- One statement of `List.foldl stmtNextScope`: the head's bindings are absorbed into the
statement-list bind names. -/
private theorem mem_scopeNames_cons_of_mem_stmtNextScope {fieldNames scope : List String}
    {stmt : Stmt} {rest : List Stmt} {name : String}
    (hmem : name ∈ stmtNextScope scope stmt ++ collectStmtListBindNames rest ++
      collectStmtListAssignedNames rest ++ fieldNames) :
    name ∈ scope ++ collectStmtListBindNames (stmt :: rest) ++
      collectStmtListAssignedNames (stmt :: rest) ++ fieldNames := by
  simp only [stmtNextScope, collectStmtListBindNames, collectStmtListAssignedNames,
    List.mem_append] at hmem ⊢
  tauto

/-- Every name in `List.foldl stmtNextScope scope stmts` comes from `scope` or is bound by
`stmts`; this holds for any statement list. -/
private theorem mem_scopeNames_of_mem_foldl_stmtNextScope {fieldNames : List String}
    {stmts : List Stmt} :
    ∀ {scope : List String} {name : String}, name ∈ List.foldl stmtNextScope scope stmts →
      name ∈ scope ++ collectStmtListBindNames stmts ++
        collectStmtListAssignedNames stmts ++ fieldNames := by
  induction stmts with
  | nil =>
      intro scope name hmem
      simp only [List.foldl_nil] at hmem
      simp [collectStmtListBindNames, collectStmtListAssignedNames, hmem]
  | cons stmt rest ih =>
      intro scope name hmem
      exact mem_scopeNames_cons_of_mem_stmtNextScope (ih hmem)

/-- Names in the scope reached after a disciplined statement prefix come from the initial
scope, the prefix's bound or assigned names, or the storage field names. -/
theorem stmtListScopeDiscipline_scope_names
    {fieldNames : List String}
    {scope : List String}
    {stmts : List Stmt}
    (_hdisc : StmtListScopeDiscipline fieldNames scope stmts) :
    ∀ name, name ∈ List.foldl stmtNextScope scope stmts →
      name ∈
        (scope ++ collectStmtListBindNames stmts ++
          collectStmtListAssignedNames stmts ++ fieldNames) :=
  fun _ hmem => mem_scopeNames_of_mem_foldl_stmtNextScope hmem

end Compiler.Proofs.IRGeneration

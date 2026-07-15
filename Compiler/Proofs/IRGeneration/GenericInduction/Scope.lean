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
          (List.foldl (fun acc s => collectStmtNames s ++ acc) scope «prefix»)
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
      | requireError _ _ _ | revertError _ _ | panicCode _ | returnValues _ | returnArray _
      | returnBytes _ | returnStorageWords _ | returnCodeData _ | calldatacopy _ _ _
      | returndataCopy _ _ _ | revertReturndata
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

private theorem validateScopedExprIdentifiers_pair_ok_left
    {context : String}
    {params : List Param}
    {paramScope dynamicParams immutableNames localScope : List String}
    {constructorArgCount : Option Nat}
    {lhs rhs : Expr}
    (hvalidate :
      (do
        validateScopedExprIdentifiers
          context params paramScope dynamicParams immutableNames localScope constructorArgCount lhs
        validateScopedExprIdentifiers
          context params paramScope dynamicParams immutableNames localScope constructorArgCount rhs) =
        Except.ok ()) :
    validateScopedExprIdentifiers
      context params paramScope dynamicParams immutableNames localScope constructorArgCount lhs =
        Except.ok () := by
  cases hlhs :
      validateScopedExprIdentifiers
        context params paramScope dynamicParams immutableNames localScope constructorArgCount lhs with
  | error err =>
      simp [hlhs] at hvalidate
      cases hvalidate
  | ok val =>
      cases val
      simpa using hlhs

private theorem validateScopedExprIdentifiers_pair_ok_right
    {context : String}
    {params : List Param}
    {paramScope dynamicParams immutableNames localScope : List String}
    {constructorArgCount : Option Nat}
    {lhs rhs : Expr}
    (hvalidate :
      (do
        validateScopedExprIdentifiers
          context params paramScope dynamicParams immutableNames localScope constructorArgCount lhs
        validateScopedExprIdentifiers
          context params paramScope dynamicParams immutableNames localScope constructorArgCount rhs) =
        Except.ok ()) :
    validateScopedExprIdentifiers
      context params paramScope dynamicParams immutableNames localScope constructorArgCount rhs =
        Except.ok () := by
  cases hlhs :
      validateScopedExprIdentifiers
        context params paramScope dynamicParams immutableNames localScope constructorArgCount lhs with
  | error err =>
      simp [hlhs] at hvalidate
      cases hvalidate
  | ok val =>
      cases val
      simpa [hlhs] using hvalidate

private theorem exprBoundNamesInScope_of_validateScopedExprIdentifiers_core
    {context : String}
    {params : List Param}
    {paramScope dynamicParams immutableNames localScope scope : List String}
    {constructorArgCount : Option Nat}
    {expr : Expr}
    (hcore : FunctionBody.ExprCompileCore expr)
    (hvalidate :
      validateScopedExprIdentifiers
        context params paramScope dynamicParams immutableNames localScope constructorArgCount expr =
          Except.ok ())
    (hparamsInScope : ∀ name, name ∈ paramScope → name ∈ scope)
    (hlocalsInScope : ∀ name, name ∈ localScope → name ∈ scope) :
    FunctionBody.exprBoundNamesInScope expr scope := by
  induction hcore with
  | literal =>
      intro name hmem
      simp [FunctionBody.exprBoundNames] at hmem
  | param name0 =>
      intro name hmem
      have hparam : name0 ∈ paramScope := by
        by_cases hname : name0 ∈ paramScope
        · exact hname
        · simp [validateScopedExprIdentifiers, hname] at hvalidate
      simp [FunctionBody.exprBoundNames] at hmem
      subst name
      exact hparamsInScope name0 hparam
  | localVar name0 =>
      intro name hmem
      have hlocal : name0 ∈ localScope := by
        by_cases hname : name0 ∈ localScope
        · exact hname
        · simp [validateScopedExprIdentifiers, hname] at hvalidate
      simp [FunctionBody.exprBoundNames] at hmem
      subst name
      exact hlocalsInScope name0 hlocal
  | caller | contractAddress | txOrigin | msgValue | blockTimestamp | blockNumber | chainid | blobbasefee
  | calldatasize =>
      intro name hmem
      simp [FunctionBody.exprBoundNames] at hmem
  | add hL hR ihL ihR
  | sub hL hR ihL ihR
  | mul hL hR ihL ihR
  | div hL hR ihL ihR
  | mod hL hR ihL ihR
  | eq hL hR ihL ihR
  | lt hL hR ihL ihR
  | gt hL hR ihL ihR
  | ge hL hR ihL ihR
  | le hL hR ihL ihR
  | bitAnd hL hR ihL ihR
  | bitOr hL hR ihL ihR
  | bitXor hL hR ihL ihR
  | slt hL hR ihL ihR | sgt hL hR ihL ihR | sdiv hL hR ihL ihR
  | smod hL hR ihL ihR | sar hL hR ihL ihR | byte hL hR ihL ihR | signextend hL hR ihL ihR =>
      rename_i lhs rhs
      have hpair :
          (do
            validateScopedExprIdentifiers
              context params paramScope dynamicParams immutableNames localScope constructorArgCount lhs
            validateScopedExprIdentifiers
              context params paramScope dynamicParams immutableNames localScope constructorArgCount rhs) =
            Except.ok () := by
        simpa [validateScopedExprIdentifiers] using hvalidate
      intro name hmem
      simp [FunctionBody.exprBoundNames] at hmem
      rcases hmem with hmem | hmem
      · exact ihL (validateScopedExprIdentifiers_pair_ok_left hpair) name hmem
      · exact ihR (validateScopedExprIdentifiers_pair_ok_right hpair) name hmem
  | logicalNot h ih
  | bitNot h ih
  | tload h ih
  | calldataload h ih
  | mload h ih =>
      intro name hmem
      simpa [FunctionBody.exprBoundNames] using
        ih
          (by simpa [validateScopedExprIdentifiers] using hvalidate)
          name
          (by simpa [FunctionBody.exprBoundNames] using hmem)
  | shl hS hV ihS ihV
  | shr hS hV ihS ihV =>
      rename_i shift value
      have hpair :
          (do
            validateScopedExprIdentifiers
              context params paramScope dynamicParams immutableNames localScope constructorArgCount shift
            validateScopedExprIdentifiers
              context params paramScope dynamicParams immutableNames localScope constructorArgCount value) =
            Except.ok () := by
        simpa [validateScopedExprIdentifiers] using hvalidate
      intro name hmem
      simp [FunctionBody.exprBoundNames] at hmem
      rcases hmem with hmem | hmem
      · exact ihS (validateScopedExprIdentifiers_pair_ok_left hpair) name hmem
      · exact ihV (validateScopedExprIdentifiers_pair_ok_right hpair) name hmem
  | min hL hR ihL ihR
  | max hL hR ihL ihR =>
      rename_i lhs rhs
      have hpair :
          (do
            validateScopedExprIdentifiers
              context params paramScope dynamicParams immutableNames localScope constructorArgCount lhs
            validateScopedExprIdentifiers
              context params paramScope dynamicParams immutableNames localScope constructorArgCount rhs) =
            Except.ok () := by
        simp only [validateScopedExprIdentifiers] at hvalidate
        revert hvalidate
        cases validateArithDuplicatedOperandPurity context _ with
        | ok _ => simp [Bind.bind, Except.bind]
        | error e => simp [Bind.bind, Except.bind]
      intro name hmem
      simp [FunctionBody.exprBoundNames] at hmem
      rcases hmem with hmem | hmem
      · exact ihL (validateScopedExprIdentifiers_pair_ok_left hpair) name hmem
      · exact ihR (validateScopedExprIdentifiers_pair_ok_right hpair) name hmem
  | ceilDiv hL hR ihL ihR
  | wDivUp hL hR ihL ihR =>
      rename_i lhs rhs
      have hpair :
          (do
            validateScopedExprIdentifiers
              context params paramScope dynamicParams immutableNames localScope constructorArgCount lhs
            validateScopedExprIdentifiers
              context params paramScope dynamicParams immutableNames localScope constructorArgCount rhs) =
            Except.ok () := by
        simp only [validateScopedExprIdentifiers] at hvalidate
        revert hvalidate
        cases validateArithDuplicatedOperandPurity context _ with
        | ok _ => simp [Bind.bind, Except.bind]
        | error e => simp [Bind.bind, Except.bind]
      intro name hmem
      simp [FunctionBody.exprBoundNames] at hmem
      rcases hmem with hmem | hmem
      · exact ihL (validateScopedExprIdentifiers_pair_ok_left hpair) name hmem
      · exact ihR (validateScopedExprIdentifiers_pair_ok_right hpair) name hmem
  | wMulDown hL hR ihL ihR =>
      rename_i lhs rhs
      have hpair :
          (do
            validateScopedExprIdentifiers
              context params paramScope dynamicParams immutableNames localScope constructorArgCount lhs
            validateScopedExprIdentifiers
              context params paramScope dynamicParams immutableNames localScope constructorArgCount rhs) =
            Except.ok () := by
        simpa [validateScopedExprIdentifiers] using hvalidate
      intro name hmem
      simp [FunctionBody.exprBoundNames] at hmem
      rcases hmem with hmem | hmem
      · exact ihL (validateScopedExprIdentifiers_pair_ok_left hpair) name hmem
      · exact ihR (validateScopedExprIdentifiers_pair_ok_right hpair) name hmem
  | mulDivDown hA hB hC ihA ihB ihC =>
      rename_i a b c
      have htriple :
          (do
            validateScopedExprIdentifiers
              context params paramScope dynamicParams immutableNames localScope constructorArgCount a
            validateScopedExprIdentifiers
              context params paramScope dynamicParams immutableNames localScope constructorArgCount b
            validateScopedExprIdentifiers
              context params paramScope dynamicParams immutableNames localScope constructorArgCount c) =
            Except.ok () := by
        simpa [validateScopedExprIdentifiers] using hvalidate
      have hA_ok :
          validateScopedExprIdentifiers
            context params paramScope dynamicParams immutableNames localScope constructorArgCount a =
            Except.ok () := by
        revert htriple
        cases ha :
            validateScopedExprIdentifiers
              context params paramScope dynamicParams immutableNames localScope constructorArgCount a with
        | error e => simp [ha, Bind.bind, Except.bind]
        | ok v => intro; rfl
      have hB_ok :
          validateScopedExprIdentifiers
            context params paramScope dynamicParams immutableNames localScope constructorArgCount b =
            Except.ok () := by
        revert htriple
        cases ha :
            validateScopedExprIdentifiers
              context params paramScope dynamicParams immutableNames localScope constructorArgCount a with
        | error e => simp [ha, Bind.bind, Except.bind]
        | ok v =>
          cases hb :
              validateScopedExprIdentifiers
                context params paramScope dynamicParams immutableNames localScope constructorArgCount b with
          | error e => simp [ha, hb, Bind.bind, Except.bind]
          | ok v => intro; rfl
      have hC_ok :
          validateScopedExprIdentifiers
            context params paramScope dynamicParams immutableNames localScope constructorArgCount c =
            Except.ok () := by
        revert htriple
        cases ha :
            validateScopedExprIdentifiers
              context params paramScope dynamicParams immutableNames localScope constructorArgCount a with
        | error e => simp [ha, Bind.bind, Except.bind]
        | ok v =>
          cases hb :
              validateScopedExprIdentifiers
                context params paramScope dynamicParams immutableNames localScope constructorArgCount b with
          | error e => simp [ha, hb, Bind.bind, Except.bind]
          | ok v =>
            simp [ha, hb, Bind.bind, Except.bind]
      intro name hmem
      simp only [FunctionBody.exprBoundNames] at hmem
      rcases List.mem_append.mp hmem with hmem12 | hmem
      · rcases List.mem_append.mp hmem12 with h | h
        · exact ihA hA_ok name h
        · exact ihB hB_ok name h
      · exact ihC hC_ok name hmem
  | mulDivUp hA hB hC ihA ihB ihC =>
      rename_i a b c
      have htriple :
          (do
            validateScopedExprIdentifiers
              context params paramScope dynamicParams immutableNames localScope constructorArgCount a
            validateScopedExprIdentifiers
              context params paramScope dynamicParams immutableNames localScope constructorArgCount b
            validateScopedExprIdentifiers
              context params paramScope dynamicParams immutableNames localScope constructorArgCount c) =
            Except.ok () := by
        simp only [validateScopedExprIdentifiers] at hvalidate
        revert hvalidate
        cases validateArithDuplicatedOperandPurity context _ with
        | ok _ => simp [Bind.bind, Except.bind]
        | error e => simp [Bind.bind, Except.bind]
      have hA_ok :
          validateScopedExprIdentifiers
            context params paramScope dynamicParams immutableNames localScope constructorArgCount a =
            Except.ok () := by
        revert htriple
        cases ha :
            validateScopedExprIdentifiers
              context params paramScope dynamicParams immutableNames localScope constructorArgCount a with
        | error e => simp [ha, Bind.bind, Except.bind]
        | ok v => intro; rfl
      have hB_ok :
          validateScopedExprIdentifiers
            context params paramScope dynamicParams immutableNames localScope constructorArgCount b =
            Except.ok () := by
        revert htriple
        cases ha :
            validateScopedExprIdentifiers
              context params paramScope dynamicParams immutableNames localScope constructorArgCount a with
        | error e => simp [ha, Bind.bind, Except.bind]
        | ok v =>
          cases hb :
              validateScopedExprIdentifiers
                context params paramScope dynamicParams immutableNames localScope constructorArgCount b with
          | error e => simp [ha, hb, Bind.bind, Except.bind]
          | ok v => intro; rfl
      have hC_ok :
          validateScopedExprIdentifiers
            context params paramScope dynamicParams immutableNames localScope constructorArgCount c =
            Except.ok () := by
        revert htriple
        cases ha :
            validateScopedExprIdentifiers
              context params paramScope dynamicParams immutableNames localScope constructorArgCount a with
        | error e => simp [ha, Bind.bind, Except.bind]
        | ok v =>
          cases hb :
              validateScopedExprIdentifiers
                context params paramScope dynamicParams immutableNames localScope constructorArgCount b with
          | error e => simp [ha, hb, Bind.bind, Except.bind]
          | ok v =>
            simp [ha, hb, Bind.bind, Except.bind]
      intro name hmem
      simp only [FunctionBody.exprBoundNames] at hmem
      rcases List.mem_append.mp hmem with hmem12 | hmem
      · rcases List.mem_append.mp hmem12 with h | h
        · exact ihA hA_ok name h
        · exact ihB hB_ok name h
      · exact ihC hC_ok name hmem
  | ite hC hT hE ihC ihT ihE =>
      rename_i cond thenVal elseVal
      have hC_ok :
          validateScopedExprIdentifiers
            context params paramScope dynamicParams immutableNames localScope constructorArgCount cond =
            Except.ok () := by
        simp only [validateScopedExprIdentifiers] at hvalidate
        revert hvalidate
        cases exprContainsCallLike cond || exprContainsCallLike thenVal ||
          exprContainsCallLike elseVal with
        | true => simp [Bind.bind, Except.bind]
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, Pure.pure, Except.pure,
            Bind.bind, Except.bind]
          intro h
          cases hc :
              validateScopedExprIdentifiers
                context params paramScope dynamicParams immutableNames localScope constructorArgCount cond with
          | error e => simp [hc] at h
          | ok v => rfl
      have hT_ok :
          validateScopedExprIdentifiers
            context params paramScope dynamicParams immutableNames localScope constructorArgCount thenVal =
            Except.ok () := by
        simp only [validateScopedExprIdentifiers] at hvalidate
        revert hvalidate
        cases exprContainsCallLike cond || exprContainsCallLike thenVal ||
          exprContainsCallLike elseVal with
        | true => simp [Bind.bind, Except.bind]
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, Pure.pure, Except.pure,
            Bind.bind, Except.bind]
          intro h
          cases hc :
              validateScopedExprIdentifiers
                context params paramScope dynamicParams immutableNames localScope constructorArgCount cond with
          | error e => simp [hc] at h
          | ok v =>
            cases ht :
                validateScopedExprIdentifiers
                  context params paramScope dynamicParams immutableNames localScope constructorArgCount thenVal with
            | error e => simp [hc, ht] at h
            | ok v => rfl
      have hE_ok :
          validateScopedExprIdentifiers
            context params paramScope dynamicParams immutableNames localScope constructorArgCount elseVal =
            Except.ok () := by
        simp only [validateScopedExprIdentifiers] at hvalidate
        revert hvalidate
        cases exprContainsCallLike cond || exprContainsCallLike thenVal ||
          exprContainsCallLike elseVal with
        | true => simp [Bind.bind, Except.bind]
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, Pure.pure, Except.pure,
            Bind.bind, Except.bind]
          intro h
          cases hc :
              validateScopedExprIdentifiers
                context params paramScope dynamicParams immutableNames localScope constructorArgCount cond with
          | error e => simp [hc] at h
          | ok v =>
            cases ht :
                validateScopedExprIdentifiers
                  context params paramScope dynamicParams immutableNames localScope constructorArgCount thenVal with
            | error e => simp [hc, ht] at h
            | ok v => simpa [hc, ht] using h
      intro name hmem
      simp only [FunctionBody.exprBoundNames] at hmem
      rcases List.mem_append.mp hmem with hmem12 | hmem
      · rcases List.mem_append.mp hmem12 with hmem | hmem
        · exact ihC hC_ok name hmem
        · exact ihT hT_ok name hmem
      · exact ihE hE_ok name hmem
  | logicalAnd hL hR ihL ihR
  | logicalOr hL hR ihL ihR =>
      rename_i lhs rhs
      have hpair :
          (do
            validateScopedExprIdentifiers
              context params paramScope dynamicParams immutableNames localScope constructorArgCount lhs
            validateScopedExprIdentifiers
              context params paramScope dynamicParams immutableNames localScope constructorArgCount rhs) =
            Except.ok () := by
        by_cases hcall : exprContainsCallLike lhs = true ∨ exprContainsCallLike rhs = true
        · simp [validateScopedExprIdentifiers, validateLogicalOperandPurity, hcall] at hvalidate
          cases hvalidate
        · simpa [validateScopedExprIdentifiers, validateLogicalOperandPurity, hcall] using hvalidate
      intro name hmem
      simp [FunctionBody.exprBoundNames] at hmem
      rcases hmem with hmem | hmem
      · exact ihL (validateScopedExprIdentifiers_pair_ok_left hpair) name hmem
      · exact ihR (validateScopedExprIdentifiers_pair_ok_right hpair) name hmem

private theorem stmtListScopeDiscipline_of_validateScopedStmtListIdentifiers
    {fieldNames : List String}
    {context : String}
    {params : List Param}
    {paramScope dynamicParams immutableNames localScope scope : List String}
    {constructorArgCount : Option Nat}
    {stmts : List Stmt}
    {finalScope : List String}
    (hcore : StmtListScopeCore fieldNames stmts)
    (hvalidate :
      validateScopedStmtListIdentifiers
        context params paramScope dynamicParams immutableNames localScope constructorArgCount stmts =
          Except.ok finalScope)
    (hparamsInScope : ∀ name, name ∈ paramScope → name ∈ scope)
    (hlocalsInScope : ∀ name, name ∈ localScope → name ∈ scope) :
    StmtListScopeDiscipline fieldNames scope stmts := by
  induction hcore generalizing localScope scope finalScope with
  | nil =>
      simp only [validateScopedStmtListIdentifiers, pure, Except.pure] at hvalidate
      cases hvalidate
      exact StmtListScopeDiscipline.nil
  | letVar hvalueCore hrest ih =>
      rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
        ⟨nextLocalScope, hstmt, hrestValidate⟩
      have hstmt' := hstmt
      unfold validateScopedStmtIdentifiers at hstmt'
      revert hstmt'
      rcases hExprVal : validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount _ with _ | _
      · intro h; simp [hExprVal, bind, Except.bind] at h
      · simp only [hExprVal, bind, Except.bind, pure, Except.pure]
        intro h
        split at h <;> try (simp at h)
        split at h <;> try (simp at h)
        cases h
        exact StmtListScopeDiscipline.letVar
          hvalueCore
          (exprBoundNamesInScope_of_validateScopedExprIdentifiers_core
            hvalueCore hExprVal hparamsInScope hlocalsInScope)
          (ih hrestValidate
            (by
              intro other hmem
              exact mem_stmtNextScope_of_mem_scope (hparamsInScope other hmem))
            (by
              intro other hmem
              simp at hmem
              rcases hmem with rfl | hmem
              · exact List.mem_append.mpr <| Or.inl <| by simp [stmtNextScope, collectStmtNames]
              · exact mem_stmtNextScope_of_mem_scope (hlocalsInScope other hmem)))
  | assignVar hvalueCore hrest ih =>
      rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
        ⟨nextLocalScope, hstmt, hrestValidate⟩
      have hstmt' := hstmt
      unfold validateScopedStmtIdentifiers at hstmt'
      -- assignVar: if !localScope.contains name then throw ...; validateExpr ...; pure localScope
      revert hstmt'
      split
      · intro h; simp [bind, Except.bind] at h
      · intro hstmt'
        simp only [bind, Except.bind, pure, Except.pure] at hstmt'
        rcases hExprVal : validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount _ with _ | _
        · rw [hExprVal] at hstmt'; exact absurd hstmt' (by simp)
        · rw [hExprVal] at hstmt'; simp at hstmt'; cases hstmt'
          exact StmtListScopeDiscipline.assignVar
            hvalueCore
            (exprBoundNamesInScope_of_validateScopedExprIdentifiers_core
              hvalueCore hExprVal hparamsInScope hlocalsInScope)
            (ih hrestValidate
              (by
                intro other hmem
                exact mem_stmtNextScope_of_mem_scope (hparamsInScope other hmem))
              (by
                intro other hmem
                exact mem_stmtNextScope_of_mem_scope (hlocalsInScope other hmem)))
  | require hcondCore hrest ih =>
      rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
        ⟨nextLocalScope, hstmt, hrestValidate⟩
      have hstmt' := hstmt
      unfold validateScopedStmtIdentifiers at hstmt'
      revert hstmt'
      rcases hExprVal : validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount _ with _ | _
      · intro h; simp [bind, Except.bind] at h
      · simp only [bind, Except.bind, pure, Except.pure]
        intro h; cases h
        exact StmtListScopeDiscipline.require
          hcondCore
          (exprBoundNamesInScope_of_validateScopedExprIdentifiers_core
            hcondCore hExprVal hparamsInScope hlocalsInScope)
          (ih hrestValidate
            (by
              intro other hmem
              exact mem_stmtNextScope_of_mem_scope (hparamsInScope other hmem))
            (by
              intro other hmem
              exact mem_stmtNextScope_of_mem_scope (hlocalsInScope other hmem)))
  | return_ hvalueCore hrest ih =>
      rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
        ⟨nextLocalScope, hstmt, hrestValidate⟩
      have hstmt' := hstmt
      unfold validateScopedStmtIdentifiers at hstmt'
      revert hstmt'
      rcases hExprVal : validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount _ with _ | _
      · intro h; simp [bind, Except.bind] at h
      · simp only [bind, Except.bind, pure, Except.pure]
        intro h; cases h
        exact StmtListScopeDiscipline.return_
          hvalueCore
          (exprBoundNamesInScope_of_validateScopedExprIdentifiers_core
            hvalueCore hExprVal hparamsInScope hlocalsInScope)
          (ih hrestValidate
            (by
              intro other hmem
              exact mem_stmtNextScope_of_mem_scope (hparamsInScope other hmem))
            (by
              intro other hmem
              exact mem_stmtNextScope_of_mem_scope (hlocalsInScope other hmem)))
  | stop hrest ih =>
      rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
        ⟨nextLocalScope, hstmt, hrestValidate⟩
      have hstmt' := hstmt
      unfold validateScopedStmtIdentifiers at hstmt'
      simp only [pure, Except.pure] at hstmt'
      cases hstmt'
      refine StmtListScopeDiscipline.stop ?_
      exact ih hrestValidate hparamsInScope hlocalsInScope
  | setStorage hfield hvalueCore hrest ih =>
      rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
        ⟨nextLocalScope, hstmt, hrestValidate⟩
      have hstmt' := hstmt
      unfold validateScopedStmtIdentifiers at hstmt'
      revert hstmt'
      rcases hExprVal : validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount _ with _ | _
      · intro h; simp [bind, Except.bind] at h
      · simp only [bind, Except.bind, pure, Except.pure]
        intro h; cases h
        exact StmtListScopeDiscipline.setStorage
          hfield
          hvalueCore
          (exprBoundNamesInScope_of_validateScopedExprIdentifiers_core
            hvalueCore hExprVal hparamsInScope hlocalsInScope)
          (ih hrestValidate
            (by
              intro other hmem
              exact mem_stmtNextScope_of_mem_scope (hparamsInScope other hmem))
            (by
              intro other hmem
              exact mem_stmtNextScope_of_mem_scope (hlocalsInScope other hmem)))
  | setStorageAddr hfield hvalueCore hrest ih =>
      rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
        ⟨nextLocalScope, hstmt, hrestValidate⟩
      have hstmt' := hstmt
      unfold validateScopedStmtIdentifiers at hstmt'
      revert hstmt'
      rcases hExprVal : validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount _ with _ | _
      · intro h; simp [bind, Except.bind] at h
      · simp only [bind, Except.bind, pure, Except.pure]
        intro h; cases h
        exact StmtListScopeDiscipline.setStorageAddr
          hfield
          hvalueCore
          (exprBoundNamesInScope_of_validateScopedExprIdentifiers_core
            hvalueCore hExprVal hparamsInScope hlocalsInScope)
          (ih hrestValidate
            (by
              intro other hmem
              exact mem_stmtNextScope_of_mem_scope (hparamsInScope other hmem))
            (by
              intro other hmem
              exact mem_stmtNextScope_of_mem_scope (hlocalsInScope other hmem)))
  | setImmutable hvalueCore hrest ih =>
      rename_i immName immValue immRest
      rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
        ⟨nextLocalScope, hstmt, hrestValidate⟩
      have hstmt' := hstmt
      unfold validateScopedStmtIdentifiers at hstmt'
      revert hstmt'
      rcases hExprVal :
          validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames
            localScope constructorArgCount _ with _ | _
      · intro h
        cases constructorArgCount with
        | none =>
            simp [hExprVal, bind, Except.bind] at h
        | some _ =>
            by_cases himm : immutableNames = [] ∨ immName ∈ immutableNames
            · simp [hExprVal, himm, bind, Except.bind] at h
              cases h
            · simp [hExprVal, himm, bind, Except.bind] at h
              cases h
      · intro h
        cases constructorArgCount with
        | none =>
            simp [hExprVal, bind, Except.bind] at h
        | some _ =>
            by_cases himm : immutableNames = [] ∨ immName ∈ immutableNames
            · simp [hExprVal, himm, bind, Except.bind] at h
              cases h
              exact StmtListScopeDiscipline.setImmutable
                hvalueCore
                (exprBoundNamesInScope_of_validateScopedExprIdentifiers_core
                  hvalueCore hExprVal hparamsInScope hlocalsInScope)
                (ih hrestValidate
                  (by
                    intro other hmem
                    exact mem_stmtNextScope_of_mem_scope (hparamsInScope other hmem))
                  (by
                    intro other hmem
                    exact mem_stmtNextScope_of_mem_scope (hlocalsInScope other hmem)))
            · simp [hExprVal, himm, bind, Except.bind] at h
              cases h
  | setStorageWord hfield hvalueCore hrest ih =>
      rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
        ⟨nextLocalScope, hstmt, hrestValidate⟩
      have hstmt' := hstmt
      unfold validateScopedStmtIdentifiers at hstmt'
      revert hstmt'
      rcases hExprVal : validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount _ with _ | _
      · intro h; simp [bind, Except.bind] at h
      · simp only [bind, Except.bind, pure, Except.pure]
        intro h; cases h
        exact StmtListScopeDiscipline.setStorageWord
          hfield
          hvalueCore
          (exprBoundNamesInScope_of_validateScopedExprIdentifiers_core
            hvalueCore hExprVal hparamsInScope hlocalsInScope)
          (ih hrestValidate
            (by
              intro other hmem
              exact mem_stmtNextScope_of_mem_scope (hparamsInScope other hmem))
            (by
              intro other hmem
              exact mem_stmtNextScope_of_mem_scope (hlocalsInScope other hmem)))
  | mstore hcoreOffset hcoreValue hrest ih =>
      rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
        ⟨nextLocalScope, hstmt, hrestValidate⟩
      have hstmt' := hstmt
      unfold validateScopedStmtIdentifiers at hstmt'
      revert hstmt'
      rcases hOffsetVal : validateScopedExprIdentifiers context params paramScope dynamicParams
          immutableNames localScope constructorArgCount _ with _ | _
      · intro h; simp [bind, Except.bind] at h
      · simp only [hOffsetVal, bind, Except.bind]
        rcases hValueVal : validateScopedExprIdentifiers context params paramScope dynamicParams
          immutableNames localScope constructorArgCount _ with _ | _
        · intro h; simp [hValueVal, bind, Except.bind] at h
        · simp only [hValueVal, bind, Except.bind, pure, Except.pure]
          intro h; cases h
          exact StmtListScopeDiscipline.mstore
            hcoreOffset
            (exprBoundNamesInScope_of_validateScopedExprIdentifiers_core
              hcoreOffset hOffsetVal hparamsInScope hlocalsInScope)
            hcoreValue
            (exprBoundNamesInScope_of_validateScopedExprIdentifiers_core
              hcoreValue hValueVal hparamsInScope hlocalsInScope)
            (ih hrestValidate
              (by intro other hmem
                  exact mem_stmtNextScope_of_mem_scope (hparamsInScope other hmem))
              (by intro other hmem
                  exact mem_stmtNextScope_of_mem_scope (hlocalsInScope other hmem)))
  | tstore hcoreOffset hcoreValue hrest ih =>
      rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
        ⟨nextLocalScope, hstmt, hrestValidate⟩
      have hstmt' := hstmt
      unfold validateScopedStmtIdentifiers at hstmt'
      revert hstmt'
      rcases hOffsetVal : validateScopedExprIdentifiers context params paramScope dynamicParams
          immutableNames localScope constructorArgCount _ with _ | _
      · intro h; simp [bind, Except.bind] at h
      · simp only [hOffsetVal, bind, Except.bind]
        rcases hValueVal : validateScopedExprIdentifiers context params paramScope dynamicParams
          immutableNames localScope constructorArgCount _ with _ | _
        · intro h; simp [hValueVal, bind, Except.bind] at h
        · simp only [hValueVal, bind, Except.bind, pure, Except.pure]
          intro h; cases h
          exact StmtListScopeDiscipline.tstore
            hcoreOffset
            (exprBoundNamesInScope_of_validateScopedExprIdentifiers_core
              hcoreOffset hOffsetVal hparamsInScope hlocalsInScope)
            hcoreValue
            (exprBoundNamesInScope_of_validateScopedExprIdentifiers_core
              hcoreValue hValueVal hparamsInScope hlocalsInScope)
            (ih hrestValidate
              (by intro other hmem
                  exact mem_stmtNextScope_of_mem_scope (hparamsInScope other hmem))
              (by intro other hmem
                  exact mem_stmtNextScope_of_mem_scope (hlocalsInScope other hmem)))
  | ite hcondCore hthenCore helseCore hrest ihThen ihElse ihRest =>
      rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
        ⟨nextLocalScope, hstmt, hrestValidate⟩
      have hstmt' := hstmt
      unfold validateScopedStmtIdentifiers at hstmt'
      revert hstmt'
      rcases hCondVal : validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount _ with _ | _
      · intro h; simp [bind, Except.bind] at h
      · simp only [bind, Except.bind, pure, Except.pure]
        rcases hThenVal : validateScopedStmtListIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount _ with _ | _
        · intro h; simp [hThenVal, bind, Except.bind] at h
        · simp only [hThenVal, bind, Except.bind]
          rcases hElseVal : validateScopedStmtListIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount _ with _ | _
          · intro h; simp [hElseVal, bind, Except.bind] at h
          · simp only [hElseVal, bind, Except.bind, pure, Except.pure]
            intro h; cases h
            exact StmtListScopeDiscipline.ite
              hcondCore
              (exprBoundNamesInScope_of_validateScopedExprIdentifiers_core
                hcondCore hCondVal hparamsInScope hlocalsInScope)
              (ihThen hThenVal hparamsInScope hlocalsInScope)
              (ihElse hElseVal hparamsInScope hlocalsInScope)
              (ihRest hrestValidate
                (by
                  intro other hmem
                  exact mem_stmtNextScope_of_mem_scope (hparamsInScope other hmem))
                (by
                  intro other hmem
                  exact mem_stmtNextScope_of_mem_scope (hlocalsInScope other hmem)))
  | forEachLiteralZero hbodyCore hrestCore ihBody ihRest =>
      rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
        ⟨nextLocalScope, hstmt, hrestValidate⟩
      have hstmt' := hstmt
      unfold validateScopedStmtIdentifiers at hstmt'
      revert hstmt'
      simp only [bind, Except.bind, pure, Except.pure]
      intro hstmt'
      rcases hCountVal :
          validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope
            constructorArgCount (Expr.literal 0) with _ | _
      · rw [hCountVal] at hstmt'; simp at hstmt'
      · rw [hCountVal] at hstmt'
        rcases hBodyVal :
            validateScopedStmtListIdentifiers context params paramScope dynamicParams
              immutableNames (_ :: localScope) constructorArgCount _ with _ | _
        · rw [hBodyVal] at hstmt'; simp at hstmt'
        · rw [hBodyVal] at hstmt'; simp at hstmt'; cases hstmt'
          exact StmtListScopeDiscipline.forEachLiteralZero
            (ihBody hBodyVal
              (by
                intro other hmem
                simp [hparamsInScope other hmem])
              (by
                intro other hmem
                simp at hmem
                rcases hmem with h | h
                · simp [h]
                · simp [hlocalsInScope other h]))
            (ihRest hrestValidate
              (by
                intro other hmem
                exact mem_stmtNextScope_of_mem_scope (hparamsInScope other hmem))
              (by
                intro other hmem
                exact mem_stmtNextScope_of_mem_scope (hlocalsInScope other hmem)))
  | forEachLiteralEmpty hrestCore ihRest =>
      rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
        ⟨nextLocalScope, hstmt, hrestValidate⟩
      have hstmt' := hstmt
      unfold validateScopedStmtIdentifiers at hstmt'
      revert hstmt'
      simp only [bind, Except.bind, pure, Except.pure]
      intro hstmt'
      rcases hCountVal :
          validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope
            constructorArgCount (Expr.literal _) with _ | _
      · rw [hCountVal] at hstmt'; simp at hstmt'
      · rw [hCountVal] at hstmt'
        rcases hBodyVal :
            validateScopedStmtListIdentifiers context params paramScope dynamicParams
              immutableNames (_ :: localScope) constructorArgCount [] with _ | _
        · rw [hBodyVal] at hstmt'; simp at hstmt'
        · rw [hBodyVal] at hstmt'; simp at hstmt'; cases hstmt'
          exact StmtListScopeDiscipline.forEachLiteralEmpty
            (ihRest hrestValidate
              (by
                intro other hmem
                exact mem_stmtNextScope_of_mem_scope (hparamsInScope other hmem))
              (by
                intro other hmem
                exact mem_stmtNextScope_of_mem_scope (hlocalsInScope other hmem)))
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

private theorem scopeNamesPresent_foldl_stmtNextScope_of_validateScopedStmtListIdentifiers
    {fieldNames : List String}
    {context : String}
    {params : List Param}
    {paramScope dynamicParams immutableNames localScope scope : List String}
    {constructorArgCount : Option Nat}
    {stmts : List Stmt}
    {finalScope : List String}
    (hcore : StmtListScopeCore fieldNames stmts)
    (hvalidate :
      validateScopedStmtListIdentifiers
        context params paramScope dynamicParams immutableNames localScope constructorArgCount stmts =
          Except.ok finalScope)
    (hparamsInScope : ∀ name, name ∈ paramScope → name ∈ scope)
    (hlocalsInScope : ∀ name, name ∈ localScope → name ∈ scope) :
    ∀ name, name ∈ finalScope → name ∈ List.foldl stmtNextScope scope stmts := by
  induction hcore generalizing localScope scope finalScope with
  | nil =>
      simp only [validateScopedStmtListIdentifiers, pure, Except.pure] at hvalidate
      cases hvalidate
      intro name hmem
      exact hlocalsInScope name hmem
  | letVar hvalueCore hrest ih =>
      rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
        ⟨nextLocalScope, hstmt, hrestValidate⟩
      have hstmt' := hstmt
      unfold validateScopedStmtIdentifiers at hstmt'
      revert hstmt'
      rcases hExprVal : validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount _ with _ | _
      · intro h; simp [bind, Except.bind] at h
      · simp only [hExprVal, bind, Except.bind, pure, Except.pure]
        intro h
        split at h <;> try (simp at h)
        split at h <;> try (simp at h)
        cases h
        intro other hmem
        exact ih hrestValidate
          (by
            intro name hname
            exact mem_stmtNextScope_of_mem_scope (hparamsInScope name hname))
          (by
            intro name hname
            simp at hname
            rcases hname with rfl | hname
            · simp [stmtNextScope, collectStmtNames]
            · exact mem_stmtNextScope_of_mem_scope (hlocalsInScope name hname))
          other hmem
  | assignVar hvalueCore hrest ih =>
      rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
        ⟨nextLocalScope, hstmt, hrestValidate⟩
      have hstmt' := hstmt
      unfold validateScopedStmtIdentifiers at hstmt'
      revert hstmt'
      split
      · intro h; simp [bind, Except.bind] at h
      · intro hstmt'
        simp only [bind, Except.bind, pure, Except.pure] at hstmt'
        rcases hExprVal : validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount _ with _ | _
        · rw [hExprVal] at hstmt'; exact absurd hstmt' (by simp)
        · rw [hExprVal] at hstmt'; simp at hstmt'; cases hstmt'
          intro other hmem
          exact ih hrestValidate
            (by
              intro name hname
              exact mem_stmtNextScope_of_mem_scope (stmt := _) (hparamsInScope name hname))
            (by
              intro name hname
              exact mem_stmtNextScope_of_mem_scope (stmt := _) (hlocalsInScope name hname))
            other hmem
  | require hcondCore hrest ih =>
      rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
        ⟨nextLocalScope, hstmt, hrestValidate⟩
      have hstmt' := hstmt
      unfold validateScopedStmtIdentifiers at hstmt'
      revert hstmt'
      rcases hExprVal : validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount _ with _ | _
      · intro h; simp [bind, Except.bind] at h
      · simp only [bind, Except.bind, pure, Except.pure]
        intro h; cases h
        intro other hmem
        exact ih hrestValidate
          (by
            intro name hname
            exact mem_stmtNextScope_of_mem_scope (hparamsInScope name hname))
          (by
            intro name hname
            exact mem_stmtNextScope_of_mem_scope (hlocalsInScope name hname))
          other hmem
  | return_ hvalueCore hrest ih =>
      rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
        ⟨nextLocalScope, hstmt, hrestValidate⟩
      have hstmt' := hstmt
      unfold validateScopedStmtIdentifiers at hstmt'
      revert hstmt'
      rcases hExprVal : validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount _ with _ | _
      · intro h; simp [bind, Except.bind] at h
      · simp only [bind, Except.bind, pure, Except.pure]
        intro h; cases h
        intro other hmem
        exact ih hrestValidate
          (by
            intro name hname
            exact mem_stmtNextScope_of_mem_scope (hparamsInScope name hname))
          (by
            intro name hname
            exact mem_stmtNextScope_of_mem_scope (hlocalsInScope name hname))
          other hmem
  | stop hrest ih =>
      rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
        ⟨nextLocalScope, hstmt, hrestValidate⟩
      have hstmt' := hstmt
      unfold validateScopedStmtIdentifiers at hstmt'
      simp only [pure, Except.pure] at hstmt'
      cases hstmt'
      intro other hmem
      simp only [List.foldl, stmtNextScope, collectStmtNames] at hmem ⊢
      exact ih hrestValidate hparamsInScope hlocalsInScope other hmem
  | setStorage hfield hvalueCore hrest ih =>
      rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
        ⟨nextLocalScope, hstmt, hrestValidate⟩
      have hstmt' := hstmt
      unfold validateScopedStmtIdentifiers at hstmt'
      revert hstmt'
      rcases hExprVal : validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount _ with _ | _
      · intro h; simp [bind, Except.bind] at h
      · simp only [bind, Except.bind, pure, Except.pure]
        intro h; cases h
        intro other hmem
        exact ih hrestValidate
          (by
            intro name hname
            exact mem_stmtNextScope_of_mem_scope (hparamsInScope name hname))
          (by
            intro name hname
            exact mem_stmtNextScope_of_mem_scope (hlocalsInScope name hname))
          other hmem
  | setStorageAddr hfield hvalueCore hrest ih =>
      rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
        ⟨nextLocalScope, hstmt, hrestValidate⟩
      have hstmt' := hstmt
      unfold validateScopedStmtIdentifiers at hstmt'
      revert hstmt'
      rcases hExprVal : validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount _ with _ | _
      · intro h; simp [bind, Except.bind] at h
      · simp only [bind, Except.bind, pure, Except.pure]
        intro h; cases h
        intro other hmem
        exact ih hrestValidate
          (by
            intro name hname
            exact mem_stmtNextScope_of_mem_scope (hparamsInScope name hname))
          (by
            intro name hname
            exact mem_stmtNextScope_of_mem_scope (hlocalsInScope name hname))
          other hmem
  | setImmutable hvalueCore hrest ih =>
      rename_i immName immValue immRest
      rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
        ⟨nextLocalScope, hstmt, hrestValidate⟩
      have hstmt' := hstmt
      unfold validateScopedStmtIdentifiers at hstmt'
      revert hstmt'
      rcases hExprVal :
          validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames
            localScope constructorArgCount _ with _ | _
      · intro h
        cases constructorArgCount with
        | none =>
            simp [hExprVal, bind, Except.bind] at h
        | some _ =>
            by_cases himm : immutableNames = [] ∨ immName ∈ immutableNames
            · simp [hExprVal, himm, bind, Except.bind] at h
              cases h
            · simp [hExprVal, himm, bind, Except.bind] at h
              cases h
      · intro h
        cases constructorArgCount with
        | none =>
            simp [hExprVal, bind, Except.bind] at h
        | some _ =>
            by_cases himm : immutableNames = [] ∨ immName ∈ immutableNames
            · simp [hExprVal, himm, bind, Except.bind] at h
              cases h
              intro other hmem
              exact ih hrestValidate
                (by
                  intro name hname
                  exact mem_stmtNextScope_of_mem_scope (hparamsInScope name hname))
                (by
                  intro name hname
                  exact mem_stmtNextScope_of_mem_scope (hlocalsInScope name hname))
                other hmem
            · simp [hExprVal, himm, bind, Except.bind] at h
              cases h
  | setStorageWord hfield hvalueCore hrest ih =>
      rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
        ⟨nextLocalScope, hstmt, hrestValidate⟩
      have hstmt' := hstmt
      unfold validateScopedStmtIdentifiers at hstmt'
      revert hstmt'
      rcases hExprVal : validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount _ with _ | _
      · intro h; simp [bind, Except.bind] at h
      · simp only [bind, Except.bind, pure, Except.pure]
        intro h; cases h
        intro other hmem
        exact ih hrestValidate
          (by
            intro name hname
            exact mem_stmtNextScope_of_mem_scope (hparamsInScope name hname))
          (by
            intro name hname
            exact mem_stmtNextScope_of_mem_scope (hlocalsInScope name hname))
          other hmem
  | mstore hcoreOffset hcoreValue hrest ih =>
      rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
        ⟨nextLocalScope, hstmt, hrestValidate⟩
      have hstmt' := hstmt
      unfold validateScopedStmtIdentifiers at hstmt'
      revert hstmt'
      rcases hOffsetVal : validateScopedExprIdentifiers context params paramScope dynamicParams
          immutableNames localScope constructorArgCount _ with _ | _
      · intro h; simp [bind, Except.bind] at h
      · simp only [hOffsetVal, bind, Except.bind]
        rcases hValueVal : validateScopedExprIdentifiers context params paramScope dynamicParams
          immutableNames localScope constructorArgCount _ with _ | _
        · intro h; simp [hValueVal, bind, Except.bind] at h
        · simp only [hValueVal, bind, Except.bind, pure, Except.pure]
          intro h; cases h
          intro other hmem
          exact ih hrestValidate
            (by intro name hname
                exact mem_stmtNextScope_of_mem_scope (hparamsInScope name hname))
            (by intro name hname
                exact mem_stmtNextScope_of_mem_scope (hlocalsInScope name hname))
            other hmem
  | tstore hcoreOffset hcoreValue hrest ih =>
      rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
        ⟨nextLocalScope, hstmt, hrestValidate⟩
      have hstmt' := hstmt
      unfold validateScopedStmtIdentifiers at hstmt'
      revert hstmt'
      rcases hOffsetVal : validateScopedExprIdentifiers context params paramScope dynamicParams
          immutableNames localScope constructorArgCount _ with _ | _
      · intro h; simp [bind, Except.bind] at h
      · simp only [hOffsetVal, bind, Except.bind]
        rcases hValueVal : validateScopedExprIdentifiers context params paramScope dynamicParams
          immutableNames localScope constructorArgCount _ with _ | _
        · intro h; simp [hValueVal, bind, Except.bind] at h
        · simp only [hValueVal, bind, Except.bind, pure, Except.pure]
          intro h; cases h
          intro other hmem
          exact ih hrestValidate
            (by intro name hname
                exact mem_stmtNextScope_of_mem_scope (hparamsInScope name hname))
            (by intro name hname
                exact mem_stmtNextScope_of_mem_scope (hlocalsInScope name hname))
            other hmem
  | ite hcondCore hthenCore helseCore hrest ihThen ihElse ihRest =>
      rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
        ⟨nextLocalScope, hstmt, hrestValidate⟩
      have hstmt' := hstmt
      unfold validateScopedStmtIdentifiers at hstmt'
      revert hstmt'
      rcases hCondVal : validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount _ with _ | _
      · intro h; simp [bind, Except.bind] at h
      · simp only [bind, Except.bind, pure, Except.pure]
        rcases hThenVal : validateScopedStmtListIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount _ with _ | _
        · intro h; simp [hThenVal, bind, Except.bind] at h
        · simp only [hThenVal, bind, Except.bind]
          rcases hElseVal : validateScopedStmtListIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount _ with _ | _
          · intro h; simp [hElseVal, bind, Except.bind] at h
          · simp only [hElseVal, bind, Except.bind, pure, Except.pure]
            intro h; cases h
            intro other hmem
            exact ihRest hrestValidate
              (by
                intro name hname
                exact mem_stmtNextScope_of_mem_scope (hparamsInScope name hname))
              (by
                intro name hname
                exact mem_stmtNextScope_of_mem_scope (hlocalsInScope name hname))
              other hmem
  | forEachLiteralZero hbodyCore hrestCore ihBody ihRest =>
      rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
        ⟨nextLocalScope, hstmt, hrestValidate⟩
      have hstmt' := hstmt
      unfold validateScopedStmtIdentifiers at hstmt'
      revert hstmt'
      simp only [bind, Except.bind, pure, Except.pure]
      intro hstmt'
      rcases hCountVal :
          validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope
            constructorArgCount (Expr.literal 0) with _ | _
      · rw [hCountVal] at hstmt'; simp at hstmt'
      · rw [hCountVal] at hstmt'
        rcases hBodyVal :
            validateScopedStmtListIdentifiers context params paramScope dynamicParams
              immutableNames (_ :: localScope) constructorArgCount _ with _ | _
        · rw [hBodyVal] at hstmt'; simp at hstmt'
        · rw [hBodyVal] at hstmt'; simp at hstmt'; cases hstmt'
          intro other hmem
          exact ihRest hrestValidate
            (by
              intro name hname
              exact mem_stmtNextScope_of_mem_scope (hparamsInScope name hname))
              (by
                intro name hname
                exact mem_stmtNextScope_of_mem_scope (hlocalsInScope name hname))
              other hmem
  | forEachLiteralEmpty hrestCore ihRest =>
      rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
        ⟨nextLocalScope, hstmt, hrestValidate⟩
      have hstmt' := hstmt
      unfold validateScopedStmtIdentifiers at hstmt'
      revert hstmt'
      simp only [bind, Except.bind, pure, Except.pure]
      intro hstmt'
      rcases hCountVal :
          validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope
            constructorArgCount (Expr.literal _) with _ | _
      · rw [hCountVal] at hstmt'; simp at hstmt'
      · rw [hCountVal] at hstmt'
        rcases hBodyVal :
            validateScopedStmtListIdentifiers context params paramScope dynamicParams
              immutableNames (_ :: localScope) constructorArgCount [] with _ | _
        · rw [hBodyVal] at hstmt'; simp at hstmt'
        · rw [hBodyVal] at hstmt'; simp at hstmt'; cases hstmt'
          intro other hmem
          exact ihRest hrestValidate
            (by
              intro name hname
              exact mem_stmtNextScope_of_mem_scope (stmt := _) (hparamsInScope name hname))
            (by
              intro name hname
              exact mem_stmtNextScope_of_mem_scope (stmt := _) (hlocalsInScope name hname))
            other hmem

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
        name hname

theorem collectExprNames_mem_exprBoundNames_of_core
    {expr : Expr}
    (hcore : FunctionBody.ExprCompileCore expr) :
    ∀ name, name ∈ collectExprNames expr → name ∈ FunctionBody.exprBoundNames expr := by
  induction hcore with
  | literal _ | caller | contractAddress | txOrigin | msgValue | blockTimestamp | blockNumber | chainid
  | blobbasefee | calldatasize =>
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
  | slt hL hR ihL ihR | sgt hL hR ihL ihR | sdiv hL hR ihL ihR
  | smod hL hR ihL ihR | sar hL hR ihL ihR | byte hL hR ihL ihR | signextend hL hR ihL ihR =>
      intro name hmem
      simp [collectExprNames, FunctionBody.exprBoundNames] at hmem ⊢
      rcases hmem with hmem | hmem
      · exact Or.inl (ihL _ hmem)
      · exact Or.inr (ihR _ hmem)
  | logicalNot h ih | bitNot h ih | tload h ih | calldataload h ih | mload h ih =>
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
  | nil => simp [collectStmtListNames] at hmem
  | cons stmt rest ih =>
      simp [collectStmtListBindNames] at hmem
      simp only [List.foldl]
      rcases hmem with hstmt | hrest
      · exact mem_foldl_stmtNextScope_of_mem_scope (by
          simp [stmtNextScope]; exact hstmt)
      · exact ih hrest

theorem stmtListScopeDiscipline_scope_names
    {fieldNames : List String}
    {scope : List String}
    {stmts : List Stmt}
    (hdisc : StmtListScopeDiscipline fieldNames scope stmts) :
    ∀ name, name ∈ List.foldl stmtNextScope scope stmts →
      name ∈
        (scope ++ collectStmtListBindNames stmts ++
          collectStmtListAssignedNames stmts ++ fieldNames) := by
  induction hdisc with
  | nil =>
      intro name hmem
      simp only [List.foldl] at hmem
      simp [collectStmtListBindNames, collectStmtListAssignedNames]
      exact Or.inl hmem
  | letVar hcore hinScope _ ih =>
      intro other hmem
      simp only [List.foldl] at hmem
      have htail := ih other hmem
      simp [stmtNextScope, collectStmtBindNames, collectStmtListBindNames,
        collectStmtListAssignedNames, collectStmtAssignedNames] at htail ⊢
      rcases htail with hname | hvalue | hscope | hbind | hassign | hfield
      · right; left; exact hname
      · left; exact hinScope _ (collectExprNames_mem_exprBoundNames_of_core hcore _ hvalue)
      · left; exact hscope
      · right; right; left; exact hbind
      · right; right; right; left; exact hassign
      · right; right; right; right; exact hfield
  | assignVar hcore hinScope _ ih =>
      intro other hmem
      simp only [List.foldl] at hmem
      have htail := ih other hmem
      simp [stmtNextScope, collectStmtBindNames, collectStmtListBindNames,
        collectStmtListAssignedNames, collectStmtAssignedNames] at htail ⊢
      rcases htail with hname | hvalue | hscope | hbind | hassign | hfield
      · right; right; left; exact hname
      · left; exact hinScope _ (collectExprNames_mem_exprBoundNames_of_core hcore _ hvalue)
      · left; exact hscope
      · right; left; exact hbind
      · right; right; right; left; exact hassign
      · right; right; right; right; exact hfield
  | require hcore hinScope _ ih =>
      intro other hmem
      simp only [List.foldl] at hmem
      have htail := ih other hmem
      simp [stmtNextScope, collectStmtBindNames, collectStmtListBindNames,
        collectStmtListAssignedNames, collectStmtAssignedNames] at htail ⊢
      rcases htail with hcond | hscope | hbind | hassign | hfield
      · left; exact hinScope _ (collectExprNames_mem_exprBoundNames_of_core hcore _ hcond)
      · left; exact hscope
      · right; left; exact hbind
      · right; right; left; exact hassign
      · right; right; right; exact hfield
  | return_ hcore hinScope _ ih =>
      intro other hmem
      simp only [List.foldl] at hmem
      have htail := ih other hmem
      simp [stmtNextScope, collectStmtBindNames, collectStmtListBindNames,
        collectStmtListAssignedNames, collectStmtAssignedNames] at htail ⊢
      rcases htail with hvalue | hscope | hbind | hassign | hfield
      · left; exact hinScope _ (collectExprNames_mem_exprBoundNames_of_core hcore _ hvalue)
      · left; exact hscope
      · right; left; exact hbind
      · right; right; left; exact hassign
      · right; right; right; exact hfield
  | stop _ ih =>
      intro other hmem
      simp only [List.foldl, stmtNextScope, collectStmtBindNames, List.nil_append] at hmem
      have htail := ih other hmem
      simp [collectStmtListBindNames, collectStmtBindNames,
        collectStmtListAssignedNames, collectStmtAssignedNames] at htail ⊢
      exact htail
  | setStorage _hfield hcore hinScope _ ih =>
      intro other hmem
      simp only [List.foldl] at hmem
      have htail := ih other hmem
      simp [stmtNextScope, collectStmtBindNames, collectStmtListBindNames,
        collectStmtListAssignedNames, collectStmtAssignedNames] at htail ⊢
      rcases htail with hvalue | hscope | hbind | hassign | hfld
      · left; exact hinScope _ (collectExprNames_mem_exprBoundNames_of_core hcore _ hvalue)
      · left; exact hscope
      · right; left; exact hbind
      · right; right; left; exact hassign
      · right; right; right; exact hfld
  | setStorageAddr _hfield hcore hinScope _ ih =>
      intro other hmem
      simp only [List.foldl] at hmem
      have htail := ih other hmem
      simp [stmtNextScope, collectStmtBindNames, collectStmtListBindNames,
        collectStmtListAssignedNames, collectStmtAssignedNames] at htail ⊢
      rcases htail with hvalue | hscope | hbind | hassign | hfld
      · left; exact hinScope _ (collectExprNames_mem_exprBoundNames_of_core hcore _ hvalue)
      · left; exact hscope
      · right; left; exact hbind
      · right; right; left; exact hassign
      · right; right; right; exact hfld
  | setImmutable hcore hinScope _ ih =>
      intro other hmem
      simp only [List.foldl] at hmem
      have htail := ih other hmem
      simp [stmtNextScope, collectStmtBindNames, collectStmtListBindNames,
        collectStmtListAssignedNames, collectStmtAssignedNames] at htail ⊢
      rcases htail with hvalue | hscope | hbind | hassign | hfld
      · left; exact hinScope _ (collectExprNames_mem_exprBoundNames_of_core hcore _ hvalue)
      · left; exact hscope
      · right; left; exact hbind
      · right; right; left; exact hassign
      · right; right; right; exact hfld
  | setStorageWord _hfield hcore hinScope _ ih =>
      intro other hmem
      simp only [List.foldl] at hmem
      have htail := ih other hmem
      simp [stmtNextScope, collectStmtBindNames, collectStmtListBindNames,
        collectStmtListAssignedNames, collectStmtAssignedNames] at htail ⊢
      rcases htail with hvalue | hscope | hbind | hassign | hfld
      · left; exact hinScope _ (collectExprNames_mem_exprBoundNames_of_core hcore _ hvalue)
      · left; exact hscope
      · right; left; exact hbind
      · right; right; left; exact hassign
      · right; right; right; exact hfld
  | mstore hcoreOffset hinScopeOffset hcoreValue hinScopeValue _ ih =>
      intro other hmem
      simp only [List.foldl] at hmem
      have htail := ih other hmem
      simp [stmtNextScope, collectStmtBindNames, collectStmtListBindNames,
        collectStmtListAssignedNames, collectStmtAssignedNames] at htail ⊢
      rcases htail with hoffset | hvalue | hscope | hbind | hassign | hfld
      · left; exact hinScopeOffset _ (collectExprNames_mem_exprBoundNames_of_core hcoreOffset _ hoffset)
      · left; exact hinScopeValue _ (collectExprNames_mem_exprBoundNames_of_core hcoreValue _ hvalue)
      · left; exact hscope
      · right; left; exact hbind
      · right; right; left; exact hassign
      · right; right; right; exact hfld
  | tstore hcoreOffset hinScopeOffset hcoreValue hinScopeValue _ ih =>
      intro other hmem
      simp only [List.foldl] at hmem
      have htail := ih other hmem
      simp [stmtNextScope, collectStmtBindNames, collectStmtListBindNames,
        collectStmtListAssignedNames, collectStmtAssignedNames] at htail ⊢
      rcases htail with hoffset | hvalue | hscope | hbind | hassign | hfld
      · left; exact hinScopeOffset _ (collectExprNames_mem_exprBoundNames_of_core hcoreOffset _ hoffset)
      · left; exact hinScopeValue _ (collectExprNames_mem_exprBoundNames_of_core hcoreValue _ hvalue)
      · left; exact hscope
      · right; left; exact hbind
      · right; right; left; exact hassign
      · right; right; right; exact hfld
  | @ite scope cond thenBranch elseBranch rest hcore hinScope _ _ _ ihThen ihElse ihRest =>
      intro other hmem
      simp only [List.foldl] at hmem
      have htail := ihRest other hmem
      simp only [List.mem_append, stmtNextScope, collectStmtBindNames,
        collectStmtListBindNames, collectStmtBindNames,
        collectStmtListAssignedNames, collectStmtAssignedNames] at htail ⊢
      rcases htail with ((((( hcond | hthenNames ) | helseNames ) | hscope ) | hbind ) | hassign ) | hfield
      · left; left; left
        exact hinScope _ (collectExprNames_mem_exprBoundNames_of_core hcore _ hcond)
      · have hmemFoldl := stmtListBindNames_subset_foldl_stmtNextScope (scope := scope) hthenNames
        have hthenResult := ihThen other hmemFoldl
        simp only [List.mem_append,
          collectStmtListBindNames, collectStmtBindNames,
          collectStmtListAssignedNames, collectStmtAssignedNames] at hthenResult
        rcases hthenResult with (( hscope | hbind ) | hassign ) | hfield
        · left; left; left; exact hscope
        · left; left; right; left; left; exact hbind
        · left; right; left; left; exact hassign
        · right; exact hfield
      · have hmemFoldl := stmtListBindNames_subset_foldl_stmtNextScope (scope := scope) helseNames
        have helseResult := ihElse other hmemFoldl
        simp only [List.mem_append,
          collectStmtListBindNames, collectStmtBindNames,
          collectStmtListAssignedNames, collectStmtAssignedNames] at helseResult
        rcases helseResult with (( hscope | hbind ) | hassign ) | hfield
        · left; left; left; exact hscope
        · left; left; right; left; right; exact hbind
        · left; right; left; right; exact hassign
        · right; exact hfield
      · left; left; left; exact hscope
      · left; left; right; right; exact hbind
      · left; right; right; exact hassign
      · right; exact hfield
  | @forEachLiteralZero scope varName body rest _ _ ihBody ihRest =>
      intro other hmem
      simp only [List.foldl] at hmem
      have htail := ihRest other hmem
      simp [stmtNextScope, collectStmtBindNames, collectExprNames,
        collectStmtListBindNames, collectStmtBindNames,
        collectStmtListAssignedNames, collectStmtAssignedNames] at htail
      rcases htail with hvar | hbodyName | hscope | hbindRest | hassignRest | hfield
      · simp [collectStmtListBindNames, collectStmtBindNames,
          collectStmtListAssignedNames, collectStmtAssignedNames, hvar]
      ·
        have hmemFoldl := stmtListBindNames_subset_foldl_stmtNextScope
          (scope := varName :: scope) hbodyName
        have hbodyResult := ihBody other hmemFoldl
        simp [collectStmtListBindNames, collectStmtBindNames,
          collectStmtListAssignedNames, collectStmtAssignedNames] at hbodyResult ⊢
        tauto
      · simp [collectStmtListBindNames, collectStmtBindNames,
          collectStmtListAssignedNames, collectStmtAssignedNames, hscope]
      · simp [collectStmtListBindNames, collectStmtBindNames,
          collectStmtListAssignedNames, collectStmtAssignedNames, hbindRest]
      · simp [collectStmtListBindNames, collectStmtBindNames,
          collectStmtListAssignedNames, collectStmtAssignedNames, hassignRest]
      · simp [collectStmtListBindNames, collectStmtBindNames,
          collectStmtListAssignedNames, collectStmtAssignedNames, hfield]
  | @forEachLiteralEmpty scope varName n rest _ ihRest =>
      intro other hmem
      simp only [List.foldl] at hmem
      have htail := ihRest other hmem
      simp [stmtNextScope, collectStmtBindNames, collectExprNames,
        collectStmtListBindNames,
        collectStmtListAssignedNames, collectStmtAssignedNames] at htail ⊢
      tauto


end Compiler.Proofs.IRGeneration

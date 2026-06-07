import Compiler.Proofs.IRGeneration.GenericInduction.ResultRelation

set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.CompilationModel
open Compiler.Yul

private theorem legacyCompatibleExternalStmtList_append
    {before after : List YulStmt}
    (hbefore : LegacyCompatibleExternalStmtList before)
    (hafter : LegacyCompatibleExternalStmtList after) :
    LegacyCompatibleExternalStmtList (before ++ after) := by
  induction hbefore generalizing after with
  | nil =>
      simpa using hafter
  | comment msg rest hrest ih =>
      simpa using LegacyCompatibleExternalStmtList.comment msg (rest ++ after) (ih hafter)
  | let_ name value rest hrest ih =>
      simpa using LegacyCompatibleExternalStmtList.let_ name value (rest ++ after) (ih hafter)
  | assign name value rest hrest ih =>
      simpa using LegacyCompatibleExternalStmtList.assign name value (rest ++ after) (ih hafter)
  | expr value rest hrest ih =>
      simpa using LegacyCompatibleExternalStmtList.expr value (rest ++ after) (ih hafter)
  | if_ cond body rest hbody hrest ihBody ihRest =>
      simpa using LegacyCompatibleExternalStmtList.if_ cond body (rest ++ after) hbody (ihRest hafter)
  | block body rest hbody hrest ihBody ihRest =>
      simpa using LegacyCompatibleExternalStmtList.block body (rest ++ after) hbody (ihRest hafter)
  | for_ init cond post body rest hinit hpost hbody hrest ihInit ihPost ihBody ihRest =>
      simpa using
        LegacyCompatibleExternalStmtList.for_ init cond post body (rest ++ after)
          hinit hpost hbody (ihRest hafter)
  | funcDef name params rets body rest hbody hrest ihBody ihRest =>
      simpa using
        LegacyCompatibleExternalStmtList.funcDef name params rets body (rest ++ after) hbody (ihRest hafter)

private theorem legacyCompatibleExternalStmtList_of_exprStmtExprs
    (exprs : List YulExpr) :
    LegacyCompatibleExternalStmtList (exprs.map YulStmt.expr) := by
  induction exprs with
  | nil =>
      exact LegacyCompatibleExternalStmtList.nil
  | cons expr rest ih =>
      simpa using LegacyCompatibleExternalStmtList.expr expr (rest.map YulStmt.expr) ih

private theorem legacyCompatibleExternalStmtList_revertWithMessage
    (message : String) :
    LegacyCompatibleExternalStmtList (CompilationModel.revertWithMessage message) := by
  unfold CompilationModel.revertWithMessage
  let headerExprs :=
    [ YulExpr.call "mstore" [YulExpr.lit 0, YulExpr.hex errorStringSelectorWord]
    , YulExpr.call "mstore" [YulExpr.lit 4, YulExpr.lit 32]
    , YulExpr.call "mstore"
        [YulExpr.lit 36, YulExpr.lit (CompilationModel.bytesFromString message).length]
    ]
  let dataExprs :=
    (((CompilationModel.chunkBytes32 (CompilationModel.bytesFromString message)).zipIdx).map
      (fun (chunk, idx) =>
        let offset := 68 + idx * 32
        let word := CompilationModel.wordFromBytes chunk
        YulExpr.call "mstore" [YulExpr.lit offset, YulExpr.hex word]))
  let revertStmt :=
    YulStmt.expr
      (YulExpr.call "revert"
        [ YulExpr.lit 0
        , YulExpr.lit
            (68 + (((CompilationModel.bytesFromString message).length + 31) / 32) * 32)
        ])
  simpa [headerExprs, dataExprs, revertStmt, List.append_assoc] using
    legacyCompatibleExternalStmtList_append
      (before := headerExprs.map YulStmt.expr)
      (after := dataExprs.map YulStmt.expr ++ [revertStmt])
      (legacyCompatibleExternalStmtList_of_exprStmtExprs headerExprs)
      (legacyCompatibleExternalStmtList_append
        (before := dataExprs.map YulStmt.expr)
      (after := [revertStmt])
      (legacyCompatibleExternalStmtList_of_exprStmtExprs dataExprs)
      (LegacyCompatibleExternalStmtList.expr
        (YulExpr.call "revert"
          [ YulExpr.lit 0
            , YulExpr.lit
            (68 + (((CompilationModel.bytesFromString message).length + 31) / 32) * 32)
            ])
          []
          LegacyCompatibleExternalStmtList.nil))

private theorem field_mem_of_findFieldWithResolvedSlot_some
    {fields : List Field}
    {fieldName : String}
    {f : Field}
    {slot : Nat}
    (hfind : findFieldWithResolvedSlot fields fieldName = some (f, slot)) :
    f ∈ fields :=
  field_mem_of_findFieldWithResolvedSlot_eq_some hfind

private theorem legacyCompatibleExternalStmtList_of_compileSetStorage_ok_of_noPackedFields_resolved
    {fields : List Field}
    {fieldName : String}
    {value : Expr}
    {bodyIR : List YulStmt}
    {f : Field}
    {slot : Nat}
    {requireAddressField : Bool}
    (hnoPacked : ∀ field ∈ fields, field.packedBits = none)
    (hfind : findFieldWithResolvedSlot fields fieldName = some (f, slot))
    (hcompile :
      CompilationModel.compileSetStorage fields .calldata fieldName value requireAddressField =
        Except.ok bodyIR) :
    LegacyCompatibleExternalStmtList bodyIR := by
  have hmem := field_mem_of_findFieldWithResolvedSlot_some hfind
  have hunpacked := hnoPacked f hmem
  unfold CompilationModel.compileSetStorage at hcompile
  simp only [hfind] at hcompile
  by_cases hmap : isMapping fields fieldName
  · simp [hmap] at hcompile
  · simp only [hmap, ite_false] at hcompile
    cases requireAddressField with
    | false =>
        simp only [ite_false, Bind.bind, Except.bind, pure, Except.pure] at hcompile
        rcases hve : CompilationModel.compileExpr fields .calldata value with err | valueExpr
        · simp [hve, Bind.bind, Except.bind] at hcompile
        · simp only [hve, Except.ok.injEq] at hcompile
          cases hty : f.ty with
          | adt name maxFields =>
              simp [hty] at hcompile
          | uint256 | address | dynamicArray | mappingTyped | mappingStruct | mappingStruct2 =>
              cases hslots : f.aliasSlots with
              | nil =>
                  simp [hslots, hunpacked, hty] at hcompile; subst hcompile
                  exact .expr _ [] .nil
              | cons s rest =>
                  simp [hslots, hunpacked, hty] at hcompile; subst hcompile
                  refine .block _ [] (.let_ _ _ _ ?_) .nil
                  simp only [← List.map_cons, ← List.map_map, ← Function.comp_def]
                  exact legacyCompatibleExternalStmtList_of_exprStmtExprs _
    | true =>
        simp only [ite_true, Bind.bind, Except.bind, pure, Except.pure] at hcompile
        cases hty : f.ty <;> simp [hty, Bind.bind, Except.bind, pure, Except.pure] at hcompile
        rcases hve : CompilationModel.compileExpr fields .calldata value with err | valueExpr
        · simp [hve, Bind.bind, Except.bind] at hcompile
        · simp only [hve, Except.ok.injEq] at hcompile
          cases hslots : f.aliasSlots with
          | nil =>
              simp [hslots, hunpacked] at hcompile; subst hcompile
              exact .expr _ [] .nil
          | cons s rest =>
              simp [hslots, hunpacked] at hcompile; subst hcompile
              refine .block _ [] (.let_ _ _ _ ?_) .nil
              simp only [← List.map_cons, ← List.map_map, ← Function.comp_def]
              exact legacyCompatibleExternalStmtList_of_exprStmtExprs _

private theorem legacyCompatibleExternalStmtList_of_compileSetStorage_ok_of_noPackedFields_aux
    {fields : List Field}
    {fieldName : String}
    {value : Expr}
    {bodyIR : List YulStmt}
    {requireAddressField : Bool}
    (hnoPacked : ∀ field ∈ fields, field.packedBits = none)
    (hcompile :
      CompilationModel.compileSetStorage fields .calldata fieldName value requireAddressField =
        Except.ok bodyIR) :
    LegacyCompatibleExternalStmtList bodyIR := by
  unfold CompilationModel.compileSetStorage at hcompile
  by_cases hmap : isMapping fields fieldName
  · simp [hmap] at hcompile
  · simp only [hmap, ite_false] at hcompile
    rcases hfind : findFieldWithResolvedSlot fields fieldName with _ | ⟨f, slot⟩
    · simp [hfind] at hcompile
    · simp only [hfind] at hcompile
      exact legacyCompatibleExternalStmtList_of_compileSetStorage_ok_of_noPackedFields_resolved
        hnoPacked hfind (by rwa [CompilationModel.compileSetStorage, if_neg hmap, hfind])

/-- The current helper-free compiled theorem target already accepts the scalar
storage write emitted by `compileSetStorage` when packed-field writes are
excluded. -/
theorem legacyCompatibleExternalStmtList_of_compileSetStorage_ok_of_noPackedFields
    {fields : List Field}
    {fieldName : String}
    {value : Expr}
    {bodyIR : List YulStmt}
    (hnoPacked : ∀ field ∈ fields, field.packedBits = none)
    (hcompile :
      CompilationModel.compileSetStorage fields .calldata fieldName value =
        Except.ok bodyIR) :
    LegacyCompatibleExternalStmtList bodyIR := by
  exact legacyCompatibleExternalStmtList_of_compileSetStorage_ok_of_noPackedFields_aux
    hnoPacked hcompile

private theorem legacyCompatibleExternalStmtList_of_compileStmt_ok_letVar
    {fields : List Field}
    {events : List EventDef}
    {errors : List ErrorDef}
    {inScopeNames : List String}
    {name : String}
    {value : Expr}
    {bodyIR : List YulStmt}
    (hcompile :
      CompilationModel.compileStmt
        fields events errors .calldata [] false inScopeNames [] (.letVar name value) =
          Except.ok bodyIR) :
    LegacyCompatibleExternalStmtList bodyIR := by
  unfold CompilationModel.compileStmt at hcompile
  rcases hvalue : CompilationModel.compileExpr fields .calldata value with _ | valueIR
  · simp [hvalue] at hcompile
  · simp [hvalue] at hcompile
    cases hcompile
    exact LegacyCompatibleExternalStmtList.let_ name valueIR [] LegacyCompatibleExternalStmtList.nil

private theorem legacyCompatibleExternalStmtList_of_compileStmt_ok_assignVar
    {fields : List Field}
    {events : List EventDef}
    {errors : List ErrorDef}
    {inScopeNames : List String}
    {name : String}
    {value : Expr}
    {bodyIR : List YulStmt}
    (hcompile :
      CompilationModel.compileStmt
        fields events errors .calldata [] false inScopeNames [] (.assignVar name value) =
          Except.ok bodyIR) :
    LegacyCompatibleExternalStmtList bodyIR := by
  unfold CompilationModel.compileStmt at hcompile
  rcases hvalue : CompilationModel.compileExpr fields .calldata value with _ | valueIR
  · simp [hvalue] at hcompile
  · simp [hvalue] at hcompile
    cases hcompile
    exact LegacyCompatibleExternalStmtList.assign name valueIR [] LegacyCompatibleExternalStmtList.nil

private theorem legacyCompatibleExternalStmtList_of_compileStmt_ok_require
    {fields : List Field}
    {events : List EventDef}
    {errors : List ErrorDef}
    {inScopeNames : List String}
    {cond : Expr}
    {message : String}
    {bodyIR : List YulStmt}
    (hcompile :
      CompilationModel.compileStmt
        fields events errors .calldata [] false inScopeNames [] (.require cond message) =
          Except.ok bodyIR) :
    LegacyCompatibleExternalStmtList bodyIR := by
  unfold CompilationModel.compileStmt at hcompile
  rcases hfail : CompilationModel.compileRequireFailCond fields .calldata cond with _ | failCond
  · simp [hfail] at hcompile
  · simp [hfail] at hcompile
    cases hcompile
    exact LegacyCompatibleExternalStmtList.if_
      failCond
      (CompilationModel.revertWithMessage message)
      []
      (legacyCompatibleExternalStmtList_revertWithMessage message)
      LegacyCompatibleExternalStmtList.nil

private theorem legacyCompatibleExternalStmtList_of_compileStmt_ok_return
    {fields : List Field}
    {events : List EventDef}
    {errors : List ErrorDef}
    {inScopeNames : List String}
    {value : Expr}
    {bodyIR : List YulStmt}
    (hcompile :
      CompilationModel.compileStmt
        fields events errors .calldata [] false inScopeNames [] (.return value) =
          Except.ok bodyIR) :
    LegacyCompatibleExternalStmtList bodyIR := by
  unfold CompilationModel.compileStmt at hcompile
  rcases hvalue : CompilationModel.compileExpr fields .calldata value with _ | valueIR
  · simp [hvalue] at hcompile
  · simp [hvalue] at hcompile
    cases hcompile
    exact LegacyCompatibleExternalStmtList.expr
      (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
      [YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32])]
      (LegacyCompatibleExternalStmtList.expr
        (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32])
        []
        LegacyCompatibleExternalStmtList.nil)

private theorem legacyCompatibleExternalStmtList_of_compileStmt_ok_stop
    {fields : List Field}
    {events : List EventDef}
    {errors : List ErrorDef}
    {inScopeNames : List String}
    {bodyIR : List YulStmt}
    (hcompile :
      CompilationModel.compileStmt
        fields events errors .calldata [] false inScopeNames [] .stop =
          Except.ok bodyIR) :
    LegacyCompatibleExternalStmtList bodyIR := by
  unfold CompilationModel.compileStmt at hcompile
  injection hcompile with hbody
  subst hbody
  exact LegacyCompatibleExternalStmtList.expr
    (YulExpr.call "stop" [])
    []
    LegacyCompatibleExternalStmtList.nil

private theorem legacyCompatibleExternalStmtList_of_compileStmt_ok_mstore
    {fields : List Field}
    {events : List EventDef}
    {errors : List ErrorDef}
    {inScopeNames : List String}
    {offset value : Expr}
    {bodyIR : List YulStmt}
    (hcompile :
      CompilationModel.compileStmt
        fields events errors .calldata [] false inScopeNames [] (.mstore offset value) =
          Except.ok bodyIR) :
    LegacyCompatibleExternalStmtList bodyIR := by
  unfold CompilationModel.compileStmt at hcompile
  rcases hoffset : CompilationModel.compileExpr fields .calldata offset with _ | offsetIR
  · simp [hoffset] at hcompile
    cases hcompile
  · rcases hvalue : CompilationModel.compileExpr fields .calldata value with _ | valueIR
    · simp [hoffset, hvalue] at hcompile
      cases hcompile
    · simp [hoffset, hvalue] at hcompile
      cases hcompile
      exact LegacyCompatibleExternalStmtList.expr
        (YulExpr.call "mstore" [offsetIR, valueIR])
        []
        LegacyCompatibleExternalStmtList.nil

private theorem legacyCompatibleExternalStmtList_of_compileStmt_ok_tstore
    {fields : List Field}
    {events : List EventDef}
    {errors : List ErrorDef}
    {inScopeNames : List String}
    {offset value : Expr}
    {bodyIR : List YulStmt}
    (hcompile :
      CompilationModel.compileStmt
        fields events errors .calldata [] false inScopeNames [] (.tstore offset value) =
          Except.ok bodyIR) :
    LegacyCompatibleExternalStmtList bodyIR := by
  unfold CompilationModel.compileStmt at hcompile
  rcases hoffset : CompilationModel.compileExpr fields .calldata offset with _ | offsetIR
  · simp [hoffset] at hcompile
    cases hcompile
  · rcases hvalue : CompilationModel.compileExpr fields .calldata value with _ | valueIR
    · simp [hoffset, hvalue] at hcompile
      cases hcompile
    · simp [hoffset, hvalue] at hcompile
      cases hcompile
      exact LegacyCompatibleExternalStmtList.expr
        (YulExpr.call "tstore" [offsetIR, valueIR])
        []
        LegacyCompatibleExternalStmtList.nil

private def setStorageWordAliasBody
    (slot wordOffset : Nat)
    (valueIR : YulExpr)
    (aliases : List Nat) : List YulStmt :=
  YulStmt.let_ "__compat_value" valueIR ::
    YulStmt.expr
      (YulExpr.call "sstore"
        [if wordOffset = 0 then YulExpr.lit slot
         else YulExpr.call "add" [YulExpr.lit slot, YulExpr.lit wordOffset],
         YulExpr.ident "__compat_value"]) ::
    aliases.map (fun writeSlot =>
      YulStmt.expr
        (YulExpr.call "sstore"
          [if wordOffset = 0 then YulExpr.lit writeSlot
           else YulExpr.call "add" [YulExpr.lit writeSlot, YulExpr.lit wordOffset],
           YulExpr.ident "__compat_value"]))

private theorem legacyCompatibleExternalStmtList_setStorageWord_aliasBlock
    (slot wordOffset : Nat)
    (valueIR : YulExpr)
    (aliases : List Nat) :
    LegacyCompatibleExternalStmtList
      [YulStmt.block (setStorageWordAliasBody slot wordOffset valueIR aliases)] := by
  unfold setStorageWordAliasBody
  refine LegacyCompatibleExternalStmtList.block _ [] ?_ LegacyCompatibleExternalStmtList.nil
  apply LegacyCompatibleExternalStmtList.let_
  simpa using legacyCompatibleExternalStmtList_of_exprStmtExprs
    (YulExpr.call "sstore"
      [if wordOffset = 0 then YulExpr.lit slot
       else YulExpr.call "add" [YulExpr.lit slot, YulExpr.lit wordOffset],
       YulExpr.ident "__compat_value"] ::
     aliases.map (fun writeSlot =>
      YulExpr.call "sstore"
        [if wordOffset = 0 then YulExpr.lit writeSlot
         else YulExpr.call "add" [YulExpr.lit writeSlot, YulExpr.lit wordOffset],
         YulExpr.ident "__compat_value"]))

private theorem legacyCompatibleExternalStmtList_of_compileStmt_ok_setStorageWord
    {fields : List Field} {events : List EventDef} {errors : List ErrorDef}
    {inScopeNames : List String} {field : String} {wordOffset : Nat}
    {value : Expr} {bodyIR : List YulStmt}
    (hcompile : CompilationModel.compileStmt fields events errors .calldata [] false
        inScopeNames [] (.setStorageWord field wordOffset value) =
          Except.ok bodyIR) :
    LegacyCompatibleExternalStmtList bodyIR := by
  unfold CompilationModel.compileStmt at hcompile
  rcases hfind : findFieldWithResolvedSlot fields field with _ | ⟨f, slot⟩
  · simp [hfind] at hcompile
  · rcases hvalue : CompilationModel.compileExpr fields .calldata value with _ | valueIR
    · simp [hfind, hvalue] at hcompile
      cases hcompile
    · simp [hfind, hvalue] at hcompile
      generalize halias : f.aliasSlots = aliases at hcompile ⊢
      cases aliases
      ·
          have hbody :
              bodyIR =
                [YulStmt.expr
                  (YulExpr.call "sstore"
                    [if wordOffset = 0 then YulExpr.lit slot
                     else YulExpr.call "add" [YulExpr.lit slot, YulExpr.lit wordOffset],
                     valueIR])] := by
            simpa using hcompile.symm
          subst bodyIR
          exact LegacyCompatibleExternalStmtList.expr
            (YulExpr.call "sstore"
              [if wordOffset = 0 then YulExpr.lit slot
               else YulExpr.call "add" [YulExpr.lit slot, YulExpr.lit wordOffset],
               valueIR])
            []
            LegacyCompatibleExternalStmtList.nil
      ·
        rename_i aliasSlot restAliases
        have hbody : bodyIR =
            [YulStmt.block
              (setStorageWordAliasBody slot wordOffset valueIR
                (aliasSlot :: restAliases))] := by
          simpa [setStorageWordAliasBody] using hcompile.symm
        subst bodyIR
        exact legacyCompatibleExternalStmtList_setStorageWord_aliasBlock
          slot wordOffset valueIR (aliasSlot :: restAliases)

mutual
/-- On the current supported contract surface, successful single-statement
compilation stays inside the legacy helper-free external Yul subset. This is
the compiled-side compatibility fact needed to reuse already-proved helper-free
cases inside the exact helper-aware compiled seam. -/
theorem legacyCompatibleExternalStmtList_of_compileStmt_ok_on_supportedContractSurface
    {fields : List Field}
    {events : List EventDef}
    {errors : List ErrorDef}
    {inScopeNames : List String}
    {stmt : Stmt}
    {bodyIR : List YulStmt}
    (hnoPacked : ∀ field ∈ fields, field.packedBits = none)
    (hsurface : stmtTouchesUnsupportedContractSurface stmt = false)
    (hcompile :
      CompilationModel.compileStmt
        fields events errors .calldata [] false inScopeNames [] stmt = Except.ok bodyIR) :
    LegacyCompatibleExternalStmtList bodyIR := by
  cases stmt with
  | letVar name value =>
      simp [stmtTouchesUnsupportedContractSurface] at hsurface
      exact legacyCompatibleExternalStmtList_of_compileStmt_ok_letVar hcompile
  | assignVar name value =>
      simp [stmtTouchesUnsupportedContractSurface] at hsurface
      exact legacyCompatibleExternalStmtList_of_compileStmt_ok_assignVar hcompile
  | setStorage fieldName value =>
      simp [stmtTouchesUnsupportedContractSurface] at hsurface
      unfold CompilationModel.compileStmt at hcompile
      exact legacyCompatibleExternalStmtList_of_compileSetStorage_ok_of_noPackedFields hnoPacked hcompile
  | setStorageAddr fieldName value =>
      simp [stmtTouchesUnsupportedContractSurface] at hsurface
      unfold CompilationModel.compileStmt at hcompile
      exact legacyCompatibleExternalStmtList_of_compileSetStorage_ok_of_noPackedFields_aux
        (requireAddressField := true)
        hnoPacked
        hcompile
  | setStorageWord field wordOffset value =>
      simp [stmtTouchesUnsupportedContractSurface] at hsurface
      exact legacyCompatibleExternalStmtList_of_compileStmt_ok_setStorageWord hcompile
  | require cond message =>
      simp [stmtTouchesUnsupportedContractSurface] at hsurface
      exact legacyCompatibleExternalStmtList_of_compileStmt_ok_require hcompile
  | «return» value =>
      simp [stmtTouchesUnsupportedContractSurface] at hsurface
      exact legacyCompatibleExternalStmtList_of_compileStmt_ok_return hcompile
  | stop =>
      simp [stmtTouchesUnsupportedContractSurface] at hsurface
      exact legacyCompatibleExternalStmtList_of_compileStmt_ok_stop hcompile
  | mstore offset value =>
      simp [stmtTouchesUnsupportedContractSurface] at hsurface
      exact legacyCompatibleExternalStmtList_of_compileStmt_ok_mstore hcompile
  | tstore offset value =>
      simp [stmtTouchesUnsupportedContractSurface] at hsurface
      exact legacyCompatibleExternalStmtList_of_compileStmt_ok_tstore hcompile
  | ite cond thenBranch elseBranch =>
      simp only [stmtTouchesUnsupportedContractSurface, Bool.or_eq_false_iff] at hsurface
      simp only [CompilationModel.compileStmt, bind, Except.bind] at hcompile
      cases hcond : CompilationModel.compileExpr fields .calldata cond with
      | error e => simp [hcond] at hcompile
      | ok condIR =>
          simp only [hcond] at hcompile
          cases hthen : CompilationModel.compileStmtList fields events errors .calldata [] false inScopeNames [] thenBranch with
          | error e => simp [hthen] at hcompile
          | ok thenIR =>
              simp only [hthen] at hcompile
              cases helse : CompilationModel.compileStmtList fields events errors .calldata [] false inScopeNames [] elseBranch with
              | error e => simp [helse] at hcompile
              | ok elseIR =>
                  simp only [helse] at hcompile
                  have hthenLegacy := legacyCompatibleExternalStmtList_of_compileStmtList_ok_on_supportedContractSurface
                    hnoPacked hsurface.1.2 hthen
                  have helseLegacy := legacyCompatibleExternalStmtList_of_compileStmtList_ok_on_supportedContractSurface
                    hnoPacked hsurface.2 helse
                  by_cases hempty : elseBranch.isEmpty
                  · simp [hempty] at hcompile
                    cases hcompile
                    exact .if_ condIR thenIR [] hthenLegacy .nil
                  · simp [hempty] at hcompile
                    cases hcompile
                    exact .block _ []
                      (.let_ _ condIR _
                        (.if_ _ thenIR _
                          hthenLegacy
                          (.if_ _ elseIR [] helseLegacy .nil)))
                      .nil
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
                      Bool.or_eq_false_iff] at hsurface
                    exact Bool.or_eq_false_iff.mpr hsurface
              simp only [CompilationModel.compileStmt, bind, Except.bind] at hcompile
              cases hbody :
                  CompilationModel.compileStmtList fields events errors .calldata [] false
                    (CompilationModel.forEachBodyScope inScopeNames varName (Expr.literal 0) body) [] body with
              | error e => simp [CompilationModel.compileExpr, pure, Except.pure, hbody] at hcompile
              | ok loopBodyIR =>
                  simp [CompilationModel.compileExpr, hbody] at hcompile
                  cases hcompile
                  let forUsedNames :=
                    varName :: (inScopeNames ++ collectExprNames (Expr.literal 0) ++ collectStmtListNames body)
                  let idxName := pickFreshName "__forEach_idx" forUsedNames
                  let countName := pickFreshName "__forEach_count" (idxName :: forUsedNames)
                  let initStmts := [
                    YulStmt.let_ idxName (YulExpr.lit 0),
                    YulStmt.let_ countName (YulExpr.lit 0),
                    YulStmt.let_ varName (YulExpr.lit 0)
                  ]
                  let condExpr := YulExpr.call "lt" [YulExpr.ident idxName, YulExpr.ident countName]
                  let postStmts := [YulStmt.assign idxName (YulExpr.call "add" [YulExpr.ident idxName, YulExpr.lit 1])]
                  let bodyWithBind := YulStmt.assign varName (YulExpr.ident idxName) :: loopBodyIR
                  simpa [forUsedNames, idxName, countName, initStmts, condExpr, postStmts,
                    bodyWithBind] using
                    (LegacyCompatibleExternalStmtList.for_ initStmts condExpr postStmts bodyWithBind []
                    (LegacyCompatibleExternalStmtList.let_ idxName (YulExpr.lit 0) _
                      (LegacyCompatibleExternalStmtList.let_ countName (YulExpr.lit 0) _
                        (LegacyCompatibleExternalStmtList.let_ varName (YulExpr.lit 0) _
                          LegacyCompatibleExternalStmtList.nil)))
                    (LegacyCompatibleExternalStmtList.assign idxName
                      (YulExpr.call "add" [YulExpr.ident idxName, YulExpr.lit 1]) _
                      LegacyCompatibleExternalStmtList.nil)
                    (LegacyCompatibleExternalStmtList.assign varName (YulExpr.ident idxName) loopBodyIR <|
                      legacyCompatibleExternalStmtList_of_compileStmtList_ok_on_supportedContractSurface
                        hnoPacked hbodySurface hbody)
                    LegacyCompatibleExternalStmtList.nil)
          | succ n =>
              cases body with
              | nil =>
                  simp only [CompilationModel.compileStmt, bind, Except.bind] at hcompile
                  simp [CompilationModel.compileExpr, CompilationModel.compileStmtList] at hcompile
                  cases hcompile
                  let forUsedNames :=
                    varName :: (inScopeNames ++
                      collectExprNames (Expr.literal (n + 1)) ++ collectStmtListNames [])
                  let idxName := pickFreshName "__forEach_idx" forUsedNames
                  let countName := pickFreshName "__forEach_count" (idxName :: forUsedNames)
                  let initStmts := [
                    YulStmt.let_ idxName (YulExpr.lit 0),
                    YulStmt.let_ countName
                      (YulExpr.lit ((n + 1) % CompilationModel.uint256Modulus)),
                    YulStmt.let_ varName (YulExpr.lit 0)
                  ]
                  let condExpr := YulExpr.call "lt" [YulExpr.ident idxName, YulExpr.ident countName]
                  let postStmts := [YulStmt.assign idxName
                    (YulExpr.call "add" [YulExpr.ident idxName, YulExpr.lit 1])]
                  let bodyWithBind := [YulStmt.assign varName (YulExpr.ident idxName)]
                  simpa [forUsedNames, idxName, countName, initStmts, condExpr,
                    postStmts, bodyWithBind] using
                    (LegacyCompatibleExternalStmtList.for_ initStmts condExpr postStmts bodyWithBind []
                      (LegacyCompatibleExternalStmtList.let_ idxName (YulExpr.lit 0) _
                        (LegacyCompatibleExternalStmtList.let_ countName
                          (YulExpr.lit ((n + 1) % CompilationModel.uint256Modulus)) _
                          (LegacyCompatibleExternalStmtList.let_ varName (YulExpr.lit 0) _
                            LegacyCompatibleExternalStmtList.nil)))
                      (LegacyCompatibleExternalStmtList.assign idxName
                        (YulExpr.call "add" [YulExpr.ident idxName, YulExpr.lit 1]) _
                        LegacyCompatibleExternalStmtList.nil)
                      (LegacyCompatibleExternalStmtList.assign varName (YulExpr.ident idxName) []
                        LegacyCompatibleExternalStmtList.nil)
                      LegacyCompatibleExternalStmtList.nil)
              | cons _ _ =>
                  simp [stmtTouchesUnsupportedContractSurface] at hsurface
      | _ =>
          simp [stmtTouchesUnsupportedContractSurface] at hsurface
  | _ =>
      simp [stmtTouchesUnsupportedContractSurface] at hsurface
termination_by sizeOf stmt

/-- On the current supported contract surface, successful statement-list
compilation stays inside the legacy helper-free external Yul subset. -/
theorem legacyCompatibleExternalStmtList_of_compileStmtList_ok_on_supportedContractSurface
    {fields : List Field}
    {events : List EventDef}
    {errors : List ErrorDef}
    {inScopeNames : List String}
    {stmts : List Stmt}
    {bodyIR : List YulStmt}
    (hnoPacked : ∀ field ∈ fields, field.packedBits = none)
    (hsurface : stmtListTouchesUnsupportedContractSurface stmts = false)
    (hcompile :
      CompilationModel.compileStmtList
        fields events errors .calldata [] false inScopeNames [] stmts = Except.ok bodyIR) :
    LegacyCompatibleExternalStmtList bodyIR := by
  match stmts with
  | [] =>
      simp [CompilationModel.compileStmtList] at hcompile
      cases hcompile
      exact .nil
  | stmt :: rest =>
      have hsplit := Bool.or_eq_false_iff.mp hsurface
      have hstmtSurface : stmtTouchesUnsupportedContractSurface stmt = false := by
        simpa [stmtListTouchesUnsupportedContractSurface] using hsplit.1
      have hrestSurface : stmtListTouchesUnsupportedContractSurface rest = false := by
        simpa [stmtListTouchesUnsupportedContractSurface] using hsplit.2
      rcases FunctionBody.compileStmtList_cons_ok_inv hcompile with
        ⟨headIR, tailIR, hhead, htail, rfl⟩
      exact legacyCompatibleExternalStmtList_append
        (legacyCompatibleExternalStmtList_of_compileStmt_ok_on_supportedContractSurface
          hnoPacked hstmtSurface hhead)
        (legacyCompatibleExternalStmtList_of_compileStmtList_ok_on_supportedContractSurface
          hnoPacked hrestSurface htail)
termination_by sizeOf stmts
end

/-- Derive the compiled-side legacy-compatibility witness needed by the exact
helper-aware induction seam from the existing supported contract-surface scan. -/
theorem stmtListCompiledLegacyCompatible_of_supportedContractSurface
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hnoPacked : ∀ field ∈ fields, field.packedBits = none)
    (hsurface : stmtListTouchesUnsupportedContractSurface stmts = false) :
    StmtListCompiledLegacyCompatible fields scope stmts := by
  induction stmts generalizing scope with
  | nil =>
      exact .nil
  | cons stmt rest ih =>
      have hsplit := Bool.or_eq_false_iff.mp hsurface
      have hstmtSurface : stmtTouchesUnsupportedContractSurface stmt = false := by
        simpa [stmtListTouchesUnsupportedContractSurface] using hsplit.1
      have hrestSurface : stmtListTouchesUnsupportedContractSurface rest = false := by
        simpa [stmtListTouchesUnsupportedContractSurface] using hsplit.2
      refine .cons ?_ (ih hrestSurface)
      intro compiledIR hcompile
      exact legacyCompatibleExternalStmtList_of_compileStmt_ok_on_supportedContractSurface
        hnoPacked hstmtSurface hcompile

/-- Any list-level compiled witness for full legacy compatibility also suffices
for the weaker exact-seam witness that only constrains helper-free heads. -/
theorem stmtListHelperFreeCompiledLegacyCompatible_of_compiledLegacyCompatible
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hlegacy : StmtListCompiledLegacyCompatible fields scope stmts) :
    StmtListHelperFreeCompiledLegacyCompatible fields scope stmts := by
  induction hlegacy with
  | nil =>
      exact .nil
  | @cons scope stmt rest hhead htail ih =>
      refine .cons ?_ ih
      intro _ compiledIR hcompile
      exact hhead compiledIR hcompile

/-- The current supported contract surface already implies the weaker exact-seam
compiled disjointness witness whenever the runtime contract has no internal
helper table. This lets the active exact helper-aware wrapper target the
generalized calls-disjoint bridge directly instead of routing through the older
helper-free legacy-compatibility witness. -/
theorem stmtListHelperFreeCompiledCallsDisjoint_of_supportedContractSurface
    {runtimeContract : IRContract}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hnoPacked : ∀ field ∈ fields, field.packedBits = none)
    (hsurface : stmtListTouchesUnsupportedContractSurface stmts = false)
    (hinternal : runtimeContract.internalFunctions = []) :
    StmtListHelperFreeCompiledCallsDisjoint runtimeContract fields scope stmts := by
  induction stmts generalizing scope with
  | nil =>
      exact .nil
  | cons stmt rest ih =>
      have hsplit := Bool.or_eq_false_iff.mp hsurface
      have hstmtSurface : stmtTouchesUnsupportedContractSurface stmt = false := by
        simpa [stmtListTouchesUnsupportedContractSurface] using hsplit.1
      have hrestSurface : stmtListTouchesUnsupportedContractSurface rest = false := by
        simpa [stmtListTouchesUnsupportedContractSurface] using hsplit.2
      refine .cons ?_ (ih hrestSurface)
      intro _ compiledIR hcompile
      exact YulStmtListCallsDisjointFromInternalTable_of_internalFunctions_nil
        runtimeContract
        hinternal
        compiledIR
        (legacyCompatibleExternalStmtList_of_compileStmt_ok_on_supportedContractSurface
          hnoPacked
          hstmtSurface
          hcompile)

private theorem legacyCompatibleExternalStmtList_of_exprMap
    (exprs : List YulExpr) :
    LegacyCompatibleExternalStmtList (exprs.map YulStmt.expr) := by
  induction exprs with
  | nil =>
      exact .nil
  | cons expr rest ih =>
      simpa using LegacyCompatibleExternalStmtList.expr expr (rest.map YulStmt.expr) ih

private theorem legacyCompatibleExternalStmtList_of_letBindings
    (bindings : List (String × YulExpr))
    (rest : List YulStmt)
    (hrest : LegacyCompatibleExternalStmtList rest) :
    LegacyCompatibleExternalStmtList
      (bindings.map (fun binding => YulStmt.let_ binding.1 binding.2) ++ rest) := by
  revert hrest
  induction bindings with
  | nil =>
      intro hrest
      simpa using hrest
  | cons binding restBindings ih =>
      intro hrest
      simpa using LegacyCompatibleExternalStmtList.let_ binding.1 binding.2
        ((restBindings.map (fun inner => YulStmt.let_ inner.1 inner.2)) ++ rest)
        (ih hrest)

private theorem legacyCompatibleExternalStmtList_of_mappingWriteCompatBlock
    (slot slot' : Nat)
    (rest' : List Nat)
    (keyExpr valueExpr : YulExpr)
    (wordOffset : Nat) :
    LegacyCompatibleExternalStmtList
      [YulStmt.block (
        ([("__compat_key", keyExpr), ("__compat_value", valueExpr)].map
            (fun binding => YulStmt.let_ binding.1 binding.2)) ++
          (slot :: slot' :: rest').map (fun writeSlot =>
            YulStmt.expr
              (YulExpr.call "sstore"
                [let mappingBase :=
                    YulExpr.call "mappingSlot"
                      [YulExpr.lit writeSlot, YulExpr.ident "__compat_key"]
                 if wordOffset == 0 then mappingBase
                 else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset],
                 YulExpr.ident "__compat_value"])))] := by
  let compatExprs :=
    (slot :: slot' :: rest').map (fun writeSlot =>
      YulExpr.call "sstore"
        [let mappingBase :=
            YulExpr.call "mappingSlot"
              [YulExpr.lit writeSlot, YulExpr.ident "__compat_key"]
         if wordOffset == 0 then mappingBase
         else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset],
         YulExpr.ident "__compat_value"])
  have hcompatExprs :
      LegacyCompatibleExternalStmtList (compatExprs.map YulStmt.expr) :=
    legacyCompatibleExternalStmtList_of_exprStmtExprs compatExprs
  refine LegacyCompatibleExternalStmtList.block _ [] ?_ .nil
  simpa [compatExprs] using
    (legacyCompatibleExternalStmtList_of_letBindings
      [("__compat_key", keyExpr), ("__compat_value", valueExpr)]
      (compatExprs.map YulStmt.expr)
      hcompatExprs)

private theorem legacyCompatibleExternalStmtList_of_mapping2CompatBlock
    (slot slot' : Nat)
    (rest' : List Nat)
    (key1Expr key2Expr valueExpr : YulExpr) :
    LegacyCompatibleExternalStmtList
      [YulStmt.block (
        ([ ("__compat_key1", key1Expr)
         , ("__compat_key2", key2Expr)
         , ("__compat_value", valueExpr)
         ].map (fun binding => YulStmt.let_ binding.1 binding.2)) ++
          (slot :: slot' :: rest').map (fun writeSlot =>
            let innerSlot :=
              YulExpr.call "mappingSlot" [YulExpr.lit writeSlot, YulExpr.ident "__compat_key1"]
            YulStmt.expr (YulExpr.call "sstore"
              [YulExpr.call "mappingSlot" [innerSlot, YulExpr.ident "__compat_key2"],
               YulExpr.ident "__compat_value"])))] := by
  let compatExprs :=
    (slot :: slot' :: rest').map (fun writeSlot =>
      let innerSlot :=
        YulExpr.call "mappingSlot" [YulExpr.lit writeSlot, YulExpr.ident "__compat_key1"]
      YulExpr.call "sstore"
        [YulExpr.call "mappingSlot" [innerSlot, YulExpr.ident "__compat_key2"],
         YulExpr.ident "__compat_value"])
  have hcompatExprs :
      LegacyCompatibleExternalStmtList (compatExprs.map YulStmt.expr) :=
    legacyCompatibleExternalStmtList_of_exprStmtExprs compatExprs
  refine LegacyCompatibleExternalStmtList.block _ [] ?_ .nil
  simpa [compatExprs] using
    (legacyCompatibleExternalStmtList_of_letBindings
      [("__compat_key1", key1Expr), ("__compat_key2", key2Expr), ("__compat_value", valueExpr)]
      (compatExprs.map YulStmt.expr)
      hcompatExprs)

private theorem legacyCompatibleExternalStmtList_of_compileMappingSlotWrite_ok
    {fields : List Field}
    {field : String}
    {keyExpr valueExpr : YulExpr}
    {label : String}
    {wordOffset : Nat}
    {bodyIR : List YulStmt}
    (hcompile :
      CompilationModel.compileMappingSlotWrite fields field keyExpr valueExpr label wordOffset =
        Except.ok bodyIR) :
    LegacyCompatibleExternalStmtList bodyIR := by
  unfold CompilationModel.compileMappingSlotWrite at hcompile
  by_cases hmapping : isMapping fields field
  · simp [hmapping] at hcompile
    cases hslots : findFieldWriteSlots fields field with
    | none =>
        simp [hslots] at hcompile
    | some slots =>
        simp [hslots] at hcompile
        cases slots with
        | nil =>
            simp at hcompile
        | cons slot rest =>
            cases rest with
            | nil =>
                injection hcompile with hbody
                subst hbody
                exact LegacyCompatibleExternalStmtList.expr _ [] .nil
            | cons slot' rest' =>
                injection hcompile with hbody
                subst hbody
                simpa using
                  legacyCompatibleExternalStmtList_of_mappingWriteCompatBlock
                    slot slot' rest' keyExpr valueExpr wordOffset
  · simp [hmapping] at hcompile

private theorem legacyCompatibleExternalStmtList_of_mapping2WordCompatBlock
    (slot slot' : Nat)
    (rest' : List Nat)
    (key1Expr key2Expr valueExpr : YulExpr)
    (wordOffset : Nat) :
    LegacyCompatibleExternalStmtList
      [YulStmt.block (
        ([ ("__compat_key1", key1Expr)
         , ("__compat_key2", key2Expr)
         , ("__compat_value", valueExpr)
         ].map (fun binding => YulStmt.let_ binding.1 binding.2)) ++
          (slot :: slot' :: rest').map (fun writeSlot =>
            let innerSlot :=
              YulExpr.call "mappingSlot" [YulExpr.lit writeSlot, YulExpr.ident "__compat_key1"]
            let outerSlot :=
              YulExpr.call "mappingSlot" [innerSlot, YulExpr.ident "__compat_key2"]
            let finalSlot :=
              if wordOffset == 0 then outerSlot
              else YulExpr.call "add" [outerSlot, YulExpr.lit wordOffset]
            YulStmt.expr (YulExpr.call "sstore"
              [finalSlot, YulExpr.ident "__compat_value"])))] := by
  let compatExprs :=
    (slot :: slot' :: rest').map (fun writeSlot =>
      let innerSlot :=
        YulExpr.call "mappingSlot" [YulExpr.lit writeSlot, YulExpr.ident "__compat_key1"]
      let outerSlot :=
        YulExpr.call "mappingSlot" [innerSlot, YulExpr.ident "__compat_key2"]
      let finalSlot :=
        if wordOffset == 0 then outerSlot
        else YulExpr.call "add" [outerSlot, YulExpr.lit wordOffset]
      YulExpr.call "sstore"
        [finalSlot, YulExpr.ident "__compat_value"])
  have hcompatExprs :
      LegacyCompatibleExternalStmtList (compatExprs.map YulStmt.expr) :=
    legacyCompatibleExternalStmtList_of_exprStmtExprs compatExprs
  refine LegacyCompatibleExternalStmtList.block _ [] ?_ .nil
  simpa [compatExprs] using
    (legacyCompatibleExternalStmtList_of_letBindings
      [("__compat_key1", key1Expr), ("__compat_key2", key2Expr), ("__compat_value", valueExpr)]
      (compatExprs.map YulStmt.expr)
      hcompatExprs)

private theorem legacyCompatibleExternalStmtList_of_compileSetMapping2Word_ok
    {fields : List Field}
    {dynamicSource : DynamicDataSource}
    {field : String}
    {key1 key2 : Expr}
    {wordOffset : Nat}
    {value : Expr}
    {bodyIR : List YulStmt}
    (hcompile :
      CompilationModel.compileSetMapping2Word fields dynamicSource field key1 key2 wordOffset value =
        Except.ok bodyIR) :
    LegacyCompatibleExternalStmtList bodyIR := by
  unfold CompilationModel.compileSetMapping2Word at hcompile
  by_cases hmapping : isMapping2 fields field
  · simp [hmapping] at hcompile
    cases hslots : findFieldWriteSlots fields field with
    | none =>
        simp [hslots] at hcompile
    | some slots =>
        simp [hslots, bind, Except.bind] at hcompile
        rcases hkey1 : CompilationModel.compileExpr fields dynamicSource key1 with _ | key1Expr
        · simp [hkey1] at hcompile
        · simp [hkey1] at hcompile
          rcases hkey2 : CompilationModel.compileExpr fields dynamicSource key2 with _ | key2Expr
          · simp [hkey2] at hcompile
          · simp [hkey2] at hcompile
            rcases hvalue : CompilationModel.compileExpr fields dynamicSource value with _ | valueExpr
            · simp [hvalue] at hcompile
            · simp [hvalue] at hcompile
              cases slots with
              | nil =>
                  simp at hcompile
              | cons slot rest =>
                  cases rest with
                  | nil =>
                      injection hcompile with hbody
                      subst hbody
                      exact LegacyCompatibleExternalStmtList.expr _ [] .nil
                  | cons slot' rest' =>
                      injection hcompile with hbody
                      subst hbody
                      simpa using
                        legacyCompatibleExternalStmtList_of_mapping2WordCompatBlock
                          slot slot' rest' key1Expr key2Expr valueExpr wordOffset
  · simp [hmapping] at hcompile

private theorem legacyCompatibleExternalStmtList_of_mapLetStmts
    {α : Type} (xs : List α) (f : α → String) (g : α → YulExpr) :
    LegacyCompatibleExternalStmtList (xs.map (fun x => YulStmt.let_ (f x) (g x))) := by
  induction xs with
  | nil => exact .nil
  | cons x rest ih => exact .let_ (f x) (g x) _ ih

private theorem legacyCompatibleExternalStmtList_of_mapExprStmts
    {α : Type} (xs : List α) (f : α → YulExpr) :
    LegacyCompatibleExternalStmtList (xs.map (fun x => YulStmt.expr (f x))) := by
  induction xs with
  | nil => exact .nil
  | cons x rest ih => exact .expr (f x) _ ih

private theorem legacyCompatibleExternalStmtList_of_mapBlockStmts
    {α : Type} (xs : List α) (f : α → List YulStmt)
    (hf : ∀ x, LegacyCompatibleExternalStmtList (f x)) :
    LegacyCompatibleExternalStmtList (xs.map (fun x => YulStmt.block (f x))) := by
  induction xs with
  | nil => exact .nil
  | cons x rest ih => exact .block _ _ (hf x) ih

private theorem legacyCompatibleExternalStmtList_of_compileSetMappingChain_ok
    {fields : List Field}
    {dynamicSource : DynamicDataSource}
    {field : String}
    {keys : List Expr}
    {value : Expr}
    {bodyIR : List YulStmt}
    (hcompile :
      CompilationModel.compileSetMappingChain fields dynamicSource field keys value =
        Except.ok bodyIR) :
    LegacyCompatibleExternalStmtList bodyIR := by
  unfold CompilationModel.compileSetMappingChain at hcompile
  by_cases hmapping : isMapping fields field
  · simp [hmapping] at hcompile
    cases hslots : findFieldWriteSlots fields field with
    | none =>
        simp [hslots] at hcompile
    | some slots =>
        simp [hslots, bind, Except.bind] at hcompile
        rcases hkeys : CompilationModel.compileExprList fields dynamicSource keys with _ | keyExprs
        · simp [hkeys] at hcompile
        · simp [hkeys] at hcompile
          rcases hvalue : CompilationModel.compileExpr fields dynamicSource value with _ | valueExpr
          · simp [hvalue] at hcompile
          · simp [hvalue] at hcompile
            cases slots with
            | nil =>
                simp at hcompile
            | cons slot rest =>
                cases rest with
                | nil =>
                    injection hcompile with hbody
                    subst hbody
                    exact LegacyCompatibleExternalStmtList.expr _ [] .nil
                | cons slot' rest' =>
                    injection hcompile with hbody
                    subst hbody
                    refine LegacyCompatibleExternalStmtList.block _ [] ?_ .nil
                    apply LegacyCompatibleExternalStmtList.let_ "__compat_value" valueExpr
                    apply legacyCompatibleExternalStmtList_append
                    · exact legacyCompatibleExternalStmtList_of_mapLetStmts
                        keyExprs.zipIdx
                        (fun p => s!"__compat_key{p.2}")
                        (fun p => p.1)
                    · exact legacyCompatibleExternalStmtList_of_mapExprStmts _ _
  · simp [hmapping] at hcompile

private theorem legacyCompatibleExternalStmtList_of_compileMappingPackedSlotWrite_ok
    {fields : List Field}
    {field : String}
    {keyExpr valueExpr : YulExpr}
    {wordOffset : Nat}
    {packed : PackedBits}
    {label : String}
    {bodyIR : List YulStmt}
    (hcompile :
      CompilationModel.compileMappingPackedSlotWrite fields field keyExpr valueExpr wordOffset packed label =
        Except.ok bodyIR) :
    LegacyCompatibleExternalStmtList bodyIR := by
  unfold CompilationModel.compileMappingPackedSlotWrite at hcompile
  by_cases hmapping : isMapping fields field
  · by_cases hvalid : packedBitsValid packed
    · simp [hmapping, hvalid] at hcompile
      cases hslots : findFieldWriteSlots fields field with
      | none =>
          simp [hslots] at hcompile
      | some slots =>
          simp [hslots] at hcompile
          cases slots with
          | nil =>
              simp at hcompile
          | cons slot rest =>
              cases rest with
              | nil =>
                  injection hcompile with hbody
                  subst hbody
                  exact .block _ []
                    (.let_ _ _ _ (.let_ _ _ _ (.let_ _ _ _ (.let_ _ _ _ (.expr _ [] .nil))))) .nil
              | cons slot' rest' =>
                  injection hcompile with hbody
                  subst hbody
                  refine .block _ [] ?_ .nil
                  apply LegacyCompatibleExternalStmtList.let_ _ _ _
                  apply LegacyCompatibleExternalStmtList.let_ _ _ _
                  apply LegacyCompatibleExternalStmtList.let_ _ _ _
                  induction (slot :: slot' :: rest') with
                  | nil => exact .nil
                  | cons s rs ih =>
                      exact .block _ _ (.let_ _ _ _ (.let_ _ _ _ (.expr _ [] .nil))) ih
    · simp [hmapping, hvalid] at hcompile
  · simp [hmapping] at hcompile

private theorem legacyCompatibleExternalStmtList_of_compileSetStructMember_ok
    {fields : List Field}
    {dynamicSource : DynamicDataSource}
    {field : String}
    {key : Expr}
    {memberName : String}
    {value : Expr}
    {bodyIR : List YulStmt}
    (hcompile :
      CompilationModel.compileSetStructMember fields dynamicSource field key memberName value =
        Except.ok bodyIR) :
    LegacyCompatibleExternalStmtList bodyIR := by
  unfold CompilationModel.compileSetStructMember at hcompile
  simp only [bind, Except.bind, pure, Except.pure] at hcompile
  by_cases hm2 : isMapping2 fields field
  · simp [hm2] at hcompile
  · simp [hm2] at hcompile
    cases hstruct : findStructMembers fields field with
    | none => simp [hstruct] at hcompile
    | some members =>
        simp [hstruct] at hcompile
        cases hmem : findStructMember members memberName with
        | none => simp [hmem] at hcompile
        | some member =>
            simp [hmem] at hcompile
            cases hpacked : member.packed with
            | none =>
                simp [hpacked, bind, Except.bind] at hcompile
                rcases hkey : CompilationModel.compileExpr fields dynamicSource key with _ | keyExpr
                · simp [hkey] at hcompile
                · rcases hvalue : CompilationModel.compileExpr fields dynamicSource value with _ | valueExpr
                  · simp [hkey, hvalue] at hcompile
                  · simp [hkey, hvalue] at hcompile
                    exact legacyCompatibleExternalStmtList_of_compileMappingSlotWrite_ok hcompile
            | some packed =>
                simp [hpacked, bind, Except.bind] at hcompile
                rcases hkey : CompilationModel.compileExpr fields dynamicSource key with _ | keyExpr
                · simp [hkey] at hcompile
                · rcases hvalue : CompilationModel.compileExpr fields dynamicSource value with _ | valueExpr
                  · simp [hkey, hvalue] at hcompile
                  · simp [hkey, hvalue] at hcompile
                    exact legacyCompatibleExternalStmtList_of_compileMappingPackedSlotWrite_ok hcompile

private theorem legacyCompatibleExternalStmtList_of_compileSetStructMember2_ok
    {fields : List Field}
    {dynamicSource : DynamicDataSource}
    {field : String}
    {key1 key2 : Expr}
    {memberName : String}
    {value : Expr}
    {bodyIR : List YulStmt}
    (hcompile :
      CompilationModel.compileSetStructMember2 fields dynamicSource field key1 key2 memberName value =
        Except.ok bodyIR) :
    LegacyCompatibleExternalStmtList bodyIR := by
  unfold CompilationModel.compileSetStructMember2 at hcompile
  simp only [bind, Except.bind, pure, Except.pure] at hcompile
  by_cases hm2 : isMapping2 fields field
  · simp [hm2] at hcompile
    cases hstruct : findStructMembers fields field with
    | none => simp [hstruct] at hcompile
    | some members =>
        simp [hstruct] at hcompile
        cases hmem : findStructMember members memberName with
        | none => simp [hmem] at hcompile
        | some member =>
            simp [hmem] at hcompile
            cases hslots : findFieldWriteSlots fields field with
            | none => simp [hslots] at hcompile
            | some slots =>
                simp [hslots, bind, Except.bind] at hcompile
                rcases hkey1 : CompilationModel.compileExpr fields dynamicSource key1 with _ | key1Expr
                · simp [hkey1] at hcompile
                · simp [hkey1] at hcompile
                  rcases hkey2 : CompilationModel.compileExpr fields dynamicSource key2 with _ | key2Expr
                  · simp [hkey2] at hcompile
                  · simp [hkey2] at hcompile
                    rcases hvalue : CompilationModel.compileExpr fields dynamicSource value with _ | valueExpr
                    · simp [hvalue] at hcompile
                    · simp [hvalue] at hcompile
                      cases hpacked : member.packed with
                      | none =>
                          simp [hpacked] at hcompile
                          cases slots with
                          | nil => simp at hcompile
                          | cons slot rest =>
                              cases rest with
                              | nil =>
                                  -- Single slot, unpacked: [expr (sstore [...])]
                                  simp [pure, Except.pure] at hcompile
                                  subst hcompile
                                  exact .expr _ [] .nil
                              | cons slot' rest' =>
                                  -- Multi slot, unpacked: [block (lets ++ expr_stmts)]
                                  injection hcompile with hbody
                                  subst hbody
                                  apply LegacyCompatibleExternalStmtList.block _ []
                                  · apply LegacyCompatibleExternalStmtList.let_ _ _ _
                                    apply LegacyCompatibleExternalStmtList.let_ _ _ _
                                    apply LegacyCompatibleExternalStmtList.let_ _ _ _
                                    exact legacyCompatibleExternalStmtList_of_mapExprStmts _ _
                                  · exact .nil
                      | some packed =>
                          simp [hpacked] at hcompile
                          cases slots with
                          | nil => simp at hcompile
                          | cons slot rest =>
                              cases rest with
                              | nil =>
                                  -- Single slot, packed: [block [let_, let_, let_, let_, expr]]
                                  simp [pure, Except.pure] at hcompile
                                  subst hcompile
                                  exact .block _ []
                                    (.let_ _ _ _ (.let_ _ _ _ (.let_ _ _ _ (.let_ _ _ _ (.expr _ [] .nil))))) .nil
                              | cons slot' rest' =>
                                  -- Multi slot, packed
                                  simp only [pure, Except.pure] at hcompile
                                  injection hcompile with hbody
                                  subst hbody
                                  unfold CompilationModel.compileCompatPackedStorageWrites
                                  simp only [List.append_eq, List.cons_append, List.nil_append]
                                  refine .block _ [] ?_ .nil
                                  apply LegacyCompatibleExternalStmtList.let_ _ _ _
                                  apply LegacyCompatibleExternalStmtList.let_ _ _ _
                                  refine .block _ _ ?_ .nil
                                  apply LegacyCompatibleExternalStmtList.let_ _ _ _
                                  apply LegacyCompatibleExternalStmtList.let_ _ _ _
                                  simp only [List.map_map]
                                  exact legacyCompatibleExternalStmtList_of_mapBlockStmts _ _
                                    (fun _ => .let_ _ _ _ (.let_ _ _ _ (.expr _ [] .nil)))
  · simp [hm2] at hcompile

private theorem legacyCompatibleExternalStmtList_of_compileSetMapping2_ok
    {fields : List Field}
    {dynamicSource : DynamicDataSource}
    {field : String}
    {key1 key2 value : Expr}
    {bodyIR : List YulStmt}
    (hcompile :
      CompilationModel.compileSetMapping2 fields dynamicSource field key1 key2 value =
        Except.ok bodyIR) :
    LegacyCompatibleExternalStmtList bodyIR := by
  unfold CompilationModel.compileSetMapping2 at hcompile
  by_cases hmapping : isMapping2 fields field
  · simp [hmapping] at hcompile
    cases hslots : findFieldWriteSlots fields field with
    | none =>
        simp [hslots] at hcompile
    | some slots =>
        simp [hslots] at hcompile
        rcases hkey1 : CompilationModel.compileExpr fields dynamicSource key1 with _ | key1Expr
        · simp [hkey1] at hcompile
          cases hcompile
        · rcases hkey2 : CompilationModel.compileExpr fields dynamicSource key2 with _ | key2Expr
          · simp [hkey1, hkey2] at hcompile
            cases hcompile
          · rcases hvalue : CompilationModel.compileExpr fields dynamicSource value with _ | valueExpr
            · simp [hkey1, hkey2, hvalue] at hcompile
              cases hcompile
            · simp [hkey1, hkey2, hvalue] at hcompile
              cases slots with
              | nil =>
                simp at hcompile
                cases hcompile
              | cons slot rest =>
                  cases rest with
                  | nil =>
                      injection hcompile with hbody
                      subst hbody
                      exact LegacyCompatibleExternalStmtList.expr _ [] .nil
                  | cons slot' rest' =>
                      injection hcompile with hbody
                      subst hbody
                      simpa using
                        legacyCompatibleExternalStmtList_of_mapping2CompatBlock
                          slot slot' rest' key1Expr key2Expr valueExpr
  · simp [hmapping] at hcompile

private theorem stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites_cons_inv
    {stmt : Stmt}
    {rest : List Stmt}
    (hsurface :
      stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites (stmt :: rest) = false) :
    stmtTouchesUnsupportedContractSurfaceExceptMappingWrites stmt = false ∧
      stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites rest = false := by
  simpa [stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites] using
    (Bool.or_eq_false_iff.mp hsurface)

/-- On the Tier 2 alternate contract surface, successful single-statement
compilation still stays inside the legacy helper-free external Yul subset. This
extends the exact helper-aware compiled seam to the already-proved singleton
mapping-write fragment instead of forcing it back onto the stricter default
surface. -/
theorem legacyCompatibleExternalStmtList_of_compileStmt_ok_on_supportedContractSurface_exceptMappingWrites
    {fields : List Field}
    {events : List EventDef}
    {errors : List ErrorDef}
    {inScopeNames : List String}
    {stmt : Stmt}
    {bodyIR : List YulStmt}
    (hnoPacked : ∀ field ∈ fields, field.packedBits = none)
    (hsurface : stmtTouchesUnsupportedContractSurfaceExceptMappingWrites stmt = false)
    (hcompile :
      CompilationModel.compileStmt
        fields events errors .calldata [] false inScopeNames [] stmt = Except.ok bodyIR) :
    LegacyCompatibleExternalStmtList bodyIR := by
  cases stmt with
  | setMapping field key value =>
      unfold CompilationModel.compileStmt at hcompile
      simp only [bind, Except.bind] at hcompile
      rcases hkey : CompilationModel.compileExpr fields .calldata key with _ | keyExpr <;>
        simp [hkey] at hcompile
      rcases hvalue : CompilationModel.compileExpr fields .calldata value with _ | valueExpr <;>
        simp [hvalue] at hcompile
      exact legacyCompatibleExternalStmtList_of_compileMappingSlotWrite_ok hcompile
  | setMappingUint field key value =>
      unfold CompilationModel.compileStmt at hcompile
      simp only [bind, Except.bind] at hcompile
      rcases hkey : CompilationModel.compileExpr fields .calldata key with _ | keyExpr <;>
        simp [hkey] at hcompile
      rcases hvalue : CompilationModel.compileExpr fields .calldata value with _ | valueExpr <;>
        simp [hvalue] at hcompile
      exact legacyCompatibleExternalStmtList_of_compileMappingSlotWrite_ok hcompile
  | setMapping2 field key1 key2 value =>
      unfold CompilationModel.compileStmt at hcompile
      exact legacyCompatibleExternalStmtList_of_compileSetMapping2_ok hcompile
  | setMappingWord field key wordOffset value =>
      unfold CompilationModel.compileStmt at hcompile
      simp only [bind, Except.bind] at hcompile
      rcases hkey : CompilationModel.compileExpr fields .calldata key with _ | keyExpr <;>
        simp [hkey] at hcompile
      rcases hvalue : CompilationModel.compileExpr fields .calldata value with _ | valueExpr <;>
        simp [hvalue] at hcompile
      exact legacyCompatibleExternalStmtList_of_compileMappingSlotWrite_ok hcompile
  | setMapping2Word field key1 key2 wordOffset value =>
      unfold CompilationModel.compileStmt at hcompile
      exact legacyCompatibleExternalStmtList_of_compileSetMapping2Word_ok hcompile
  | setMappingPackedWord field key wordOffset packed value =>
      unfold CompilationModel.compileStmt at hcompile
      simp only [bind, Except.bind] at hcompile
      rcases hkey : CompilationModel.compileExpr fields .calldata key with _ | keyExpr <;>
        simp [hkey] at hcompile
      rcases hvalue : CompilationModel.compileExpr fields .calldata value with _ | valueExpr <;>
        simp [hvalue] at hcompile
      exact legacyCompatibleExternalStmtList_of_compileMappingPackedSlotWrite_ok hcompile
  | setMappingChain field keys value =>
      unfold CompilationModel.compileStmt at hcompile
      exact legacyCompatibleExternalStmtList_of_compileSetMappingChain_ok hcompile
  | setStructMember field key memberName value =>
      unfold CompilationModel.compileStmt at hcompile
      exact legacyCompatibleExternalStmtList_of_compileSetStructMember_ok hcompile
  | setStructMember2 field key1 key2 memberName value =>
      unfold CompilationModel.compileStmt at hcompile
      exact legacyCompatibleExternalStmtList_of_compileSetStructMember2_ok hcompile
  | letVar _ _ | assignVar _ _ | setStorage _ _ | setStorageAddr _ _ | setStorageWord _ _ _
  | storageArrayPush _ _ | storageArrayPop _ | setStorageArrayElement _ _ _
  | require _ | requireError _ _ | revertError _ _
  | «return» _ | returnValues _ | returnArray _ | returnBytes _
  | returnStorageWords _ | returnCodeData _ | mstore _ _ | tstore _ _ | calldatacopy _ _ _
  | returndataCopy _ _ _ | revertReturndata | stop
  | ite _ _ _ | forEach _ _ _ | emit _ _
  | internalCall _ _ | internalCallAssign _ _ _ | rawLog _ _ _
  | externalCallBind _ _ _ | tryExternalCallBind _ _ _ _ | ecm _ _
  | unsafeBlock _ _ | unsafeYul _ | matchAdt _ _ _ =>
      exact legacyCompatibleExternalStmtList_of_compileStmt_ok_on_supportedContractSurface
        hnoPacked
        (by simpa [stmtTouchesUnsupportedContractSurfaceExceptMappingWrites] using hsurface)
        hcompile

/-- Tier 2 list-level legacy-compatibility witness for the alternate singleton
mapping-write surface. -/
theorem stmtListCompiledLegacyCompatible_of_supportedContractSurface_exceptMappingWrites
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hnoPacked : ∀ field ∈ fields, field.packedBits = none)
    (hsurface : stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites stmts = false) :
    StmtListCompiledLegacyCompatible fields scope stmts := by
  induction stmts generalizing scope with
  | nil =>
      exact .nil
  | cons stmt rest ih =>
      have hsplit := stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites_cons_inv hsurface
      have hstmtSurface := hsplit.1
      have hrestSurface := hsplit.2
      refine .cons ?_ (ih hrestSurface)
      intro compiledIR hcompile
      exact
        legacyCompatibleExternalStmtList_of_compileStmt_ok_on_supportedContractSurface_exceptMappingWrites
          hnoPacked hstmtSurface hcompile

/-- List-level legacy-compatibility witness for the alternate singleton
mapping-write surface. This is the direct `compileStmtList` analogue of the
single-statement theorem above. -/
theorem legacyCompatibleExternalStmtList_of_compileStmtList_ok_on_supportedContractSurface_exceptMappingWrites
    {fields : List Field}
    {events : List EventDef}
    {errors : List ErrorDef}
    {inScopeNames : List String}
    {stmts : List Stmt}
    {bodyIR : List YulStmt}
    (hnoPacked : ∀ field ∈ fields, field.packedBits = none)
    (hsurface : stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites stmts = false)
    (hcompile :
      CompilationModel.compileStmtList
        fields events errors .calldata [] false inScopeNames [] stmts = Except.ok bodyIR) :
    LegacyCompatibleExternalStmtList bodyIR := by
  match stmts with
  | [] =>
      simp [CompilationModel.compileStmtList] at hcompile
      cases hcompile
      exact .nil
  | stmt :: rest =>
      have hsplit := stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites_cons_inv hsurface
      have hstmtSurface := hsplit.1
      have hrestSurface := hsplit.2
      rcases FunctionBody.compileStmtList_cons_ok_inv hcompile with
        ⟨headIR, tailIR, hhead, htail, rfl⟩
      exact legacyCompatibleExternalStmtList_append
        (legacyCompatibleExternalStmtList_of_compileStmt_ok_on_supportedContractSurface_exceptMappingWrites
          hnoPacked hstmtSurface hhead)
        (legacyCompatibleExternalStmtList_of_compileStmtList_ok_on_supportedContractSurface_exceptMappingWrites
          hnoPacked hrestSurface htail)
termination_by sizeOf stmts

theorem stmtListHelperFreeCompiledLegacyCompatible_of_supportedContractSurface_exceptMappingWrites
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hnoPacked : ∀ field ∈ fields, field.packedBits = none)
    (hsurface : stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites stmts = false) :
    StmtListHelperFreeCompiledLegacyCompatible fields scope stmts :=
  stmtListHelperFreeCompiledLegacyCompatible_of_compiledLegacyCompatible
    (stmtListCompiledLegacyCompatible_of_supportedContractSurface_exceptMappingWrites
      (fields := fields)
      (scope := scope)
      (stmts := stmts)
      hnoPacked
      hsurface)

/-- Tier 2 exact-seam compiled disjointness witness for the alternate singleton
mapping-write surface when the runtime contract has no internal helper table. -/
theorem stmtListHelperFreeCompiledCallsDisjoint_of_supportedContractSurface_exceptMappingWrites
    {runtimeContract : IRContract}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hnoPacked : ∀ field ∈ fields, field.packedBits = none)
    (hsurface : stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites stmts = false)
    (hinternal : runtimeContract.internalFunctions = []) :
    StmtListHelperFreeCompiledCallsDisjoint runtimeContract fields scope stmts := by
  induction stmts generalizing scope with
  | nil =>
      exact .nil
  | cons stmt rest ih =>
      have hsplit := stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites_cons_inv hsurface
      have hstmtSurface := hsplit.1
      have hrestSurface := hsplit.2
      refine .cons ?_ (ih hrestSurface)
      intro _ compiledIR hcompile
      exact
        YulStmtListCallsDisjointFromInternalTable_of_internalFunctions_nil
          runtimeContract
          hinternal
          compiledIR
          (legacyCompatibleExternalStmtList_of_compileStmt_ok_on_supportedContractSurface_exceptMappingWrites
            hnoPacked
            hstmtSurface
            hcompile)

end Compiler.Proofs.IRGeneration

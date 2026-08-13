import Lean
import Verity.Macro.Syntax
import Verity.Macro.Executable
import Verity.Macro.Translate
import Verity.Macro.Bridge
import Verity.Core.Intrinsics
import Verity.Core.Uint256

namespace Verity.Macro

open Lean
open Lean.Elab
open Lean.Elab.Command

set_option hygiene false

partial def parseIntrinsicTemplateExpr (stx : TSyntax `verityIntrinsicTemplateExpr) :
    CommandElabM Compiler.Yul.YulExpr := do
  match stx with
  | `(verityIntrinsicTemplateExpr| $func:ident ( $[$args:verityIntrinsicTemplateExpr],* )) => do
      pure <| Compiler.Yul.YulExpr.call (toString func.getId)
        (← args.toList.mapM parseIntrinsicTemplateExpr)
  | `(verityIntrinsicTemplateExpr| $name:ident) =>
      pure <| Compiler.Yul.YulExpr.ident (toString name.getId)
  | `(verityIntrinsicTemplateExpr| $n:num) =>
      pure <| Compiler.Yul.YulExpr.lit n.getNat
  | `(verityIntrinsicTemplateExpr| $s:str) =>
      pure <| Compiler.Yul.YulExpr.str s.getString
  | _ =>
      throwErrorAt stx "unsupported intrinsic template expression"

def parseIntrinsicTemplateStmt (stx : TSyntax `verityIntrinsicTemplateStmt) :
    CommandElabM Compiler.Yul.YulStmt := do
  match stx with
  | `(verityIntrinsicTemplateStmt| let $name:ident := $value:verityIntrinsicTemplateExpr) =>
      pure <| Compiler.Yul.YulStmt.let_ (toString name.getId) (← parseIntrinsicTemplateExpr value)
  | `(verityIntrinsicTemplateStmt| $name:ident := $value:verityIntrinsicTemplateExpr) =>
      pure <| Compiler.Yul.YulStmt.assign (toString name.getId) (← parseIntrinsicTemplateExpr value)
  | `(verityIntrinsicTemplateStmt| yulcall $func:ident ( $[$args:verityIntrinsicTemplateExpr],* )) =>
      pure <| Compiler.Yul.YulStmt.exprStmt
        (Compiler.Yul.YulExpr.call (toString func.getId)
          (← args.toList.mapM parseIntrinsicTemplateExpr))
  | `(verityIntrinsicTemplateStmt| comment $text:str) =>
      pure <| Compiler.Yul.YulStmt.comment text.getString
  | `(verityIntrinsicTemplateStmt| leave) =>
      pure Compiler.Yul.YulStmt.leave
  | _ =>
      throwErrorAt stx "unsupported intrinsic template statement"

private def cleanTypeSyntaxString (ty : Term) : String :=
  String.ofList <| (toString ty).toList.filter (fun c => c != '`')

private def isUint256TypeSyntax (ty : Term) : Bool :=
  let rendered := cleanTypeSyntaxString ty
  rendered == "Uint256" ||
    rendered == "Verity.Uint256" ||
    rendered == "Verity.Core.Uint256" ||
    rendered.endsWith ".Uint256"

private def parseIntrinsicProofStatus (status : Ident) : CommandElabM String := do
  let rendered := toString status.getId
  match rendered with
  | "proved" | "assumed" | "unchecked" => pure rendered
  | _ =>
      throwErrorAt status
        "unsupported proof status for verity_intrinsic obligation; expected proved, assumed, or unchecked"

private def elabVerityContractOrMixin (stx : Syntax) : CommandElabM Unit := do
  let parsed ← parseContractSyntax stx
  let contractName := parsed.contractName
  let structDecls := parsed.structDecls
  let adtDecls := parsed.adtDecls
  let fields := parsed.fields
  let roleDecls := parsed.roleDecls
  let storageStructAccessors := parsed.storageStructAccessors
  let errorDecls := parsed.errorDecls
  let eventDecls := parsed.eventDecls
  let constDecls := parsed.constDecls
  let immutableDecls := parsed.immutableDecls
  let externalDecls := parsed.externalDecls
  let ctor := parsed.ctor
  let modifiers := parsed.modifiers
  let functions := parsed.functions
  let storageNamespace := parsed.storageNamespace
  let isMixin := parsed.isMixin
  let resolvedIncludes := parsed.resolvedIncludes

  validateGeneratedDefNamesPublic fields constDecls immutableDecls functions
  validateConstantDeclsPublic constDecls
  validateImmutableDeclsPublic fields constDecls immutableDecls ctor
  validateExternalDeclsPublic externalDecls
  let mut mixinModifiers : Array ModifierDecl := #[]
  let mut mixinFields : Array StorageFieldDecl := #[]
  let mut mixinErrorDecls : Array ErrorDecl := #[]
  let mut mixinEventDecls : Array EventDecl := #[]
  let mut mixinConstDecls : Array ConstantDecl := #[]
  let mut mixinImmutableDecls : Array ImmutableDecl := #[]
  let mut mixinExternalDecls : Array ExternalDecl := #[]
  let mut mixinFunctions : Array FunctionDecl := #[]
  let mut mixinRoleDecls : Array RoleDecl := #[]
  let mut mixinParsed : Array (Name × ParsedContractSyntax) := #[]
  for mixinName in resolvedIncludes do
    match (← lookupContractSyntaxPublic mixinName) with
    | some mixin =>
        mixinModifiers := mixinModifiers ++ mixin.modifiers
        mixinFields := mixinFields ++ mixin.fields
        mixinErrorDecls := mixinErrorDecls ++ mixin.errorDecls
        mixinEventDecls := mixinEventDecls ++ mixin.eventDecls
        mixinConstDecls := mixinConstDecls ++ mixin.constDecls
        mixinImmutableDecls := mixinImmutableDecls ++ mixin.immutableDecls
        mixinExternalDecls := mixinExternalDecls ++ mixin.externalDecls
        mixinFunctions := mixinFunctions ++ mixin.functions
        mixinRoleDecls := mixinRoleDecls ++ mixin.roleDecls
        mixinParsed := mixinParsed.push (mixinName, mixin)
    | none => pure ()
  let translationFields := mixinFields ++ fields
  let translationErrorDecls := mixinErrorDecls ++ errorDecls
  let translationEventDecls := mixinEventDecls ++ eventDecls
  let translationConstDecls := mixinConstDecls ++ constDecls
  let translationImmutableDecls := mixinImmutableDecls ++ immutableDecls
  let translationExternalDecls := mixinExternalDecls ++ externalDecls
  let translationFunctions := mixinFunctions ++ functions
  let translationRoleDecls := mixinRoleDecls ++ roleDecls
  validateFunctionDeclsPublic translationFields translationErrorDecls translationEventDecls
    translationConstDecls translationImmutableDecls translationExternalDecls ctor
    (mixinModifiers ++ modifiers) translationFunctions

  let declarationNs ← getCurrNamespace
  elabCommand (← `(namespace $contractName))
  try
    for constant in constDecls do
      elabCommand (← mkConstantDefCommandPublic constant)

    for structDecl in structDecls do
      elabCommand (← mkStructDefCommandPublic structDecl)
      elabCommand (← mkStructEventArgInstanceCommandPublic structDecl)

    let aliasCmds ← mkIncludeAliasCommandsPublic resolvedIncludes
    for cmd in aliasCmds do
      elabCommand cmd

    for field in fields do
      if field.emitDef then
        elabCommand (← mkStorageDefCommandPublic field)

    for accessor in storageStructAccessors do
      for cmd in (← mkStorageStructAccessorCommandsPublic accessor) do
        elabCommand cmd

    for imm in immutableDecls.zipIdx do
      elabCommand (← mkStorageDefCommandPublic (immutableStorageFieldDecl fields imm.1 imm.2))

    for cmd in (← mkExecutableStructMappingCommandsPublic fields) do
      elabCommand cmd

    -- Emit storageNamespace : Nat for the contract (#1730, Axis 4 Step 4a).
    -- Use the resolved namespace from parseContractSyntax to respect custom keys.
    elabCommand (← mkStorageNamespaceCommand (toString contractName.getId) storageNamespace)

    if isMixin then
      for modDecl in modifiers do
        elabCommand (← mkModifierDefCommandPublic modDecl)
      match ctor with
      | some ctorDecl =>
          elabCommand (← mkConstructorDefCommandPublic ctorDecl)
      | none => pure ()

    if !resolvedIncludes.isEmpty then
      match ctor with
      | some ctorDecl =>
          elabCommand (← mkHostConstructorDefCommandPublic resolvedIncludes ctorDecl)
      | none => pure ()

    -- Translation (not storage-def emission) must see mixin fields/decls so
    -- inlined mixin-modifier CompilationModel bodies can resolve slots,
    -- custom errors, constants, and helpers.
    for fn in functions do
      let fnCmds ← mkFunctionCommandsPublic translationFields translationRoleDecls
        translationErrorDecls translationConstDecls translationImmutableDecls
        translationExternalDecls translationFunctions fn resolvedIncludes
        (boundImmutableDecls := immutableDecls)
      for cmd in fnCmds do
        elabCommand cmd
      elabCommand (← mkBridgeCommand fn.ident)

    let specName : Ident :=
      if resolvedIncludes.isEmpty then mkIdent (Name.mkSimple "spec")
      else mkIdent (Name.mkSimple "host_spec")
    let mut modelCtor := ctor
    if !resolvedIncludes.isEmpty then
      match ctor with
      | some ctorDecl =>
          modelCtor := some (← expandMixinConstructorForModelPublic
            translationFields translationConstDecls translationImmutableDecls
            translationExternalDecls ctorDecl mixinParsed)
      | none => pure ()
    let constructorImmutableDecls :=
      includedMixinImmutablesForHostPublic ctor mixinParsed ++ immutableDecls
    elabCommand (← mkSpecCommandPublic (toString contractName.getId) fields roleDecls errorDecls eventDecls constDecls immutableDecls externalDecls modelCtor modifiers functions adtDecls storageNamespace specName translationFields translationErrorDecls translationConstDecls translationImmutableDecls translationExternalDecls translationFunctions constructorImmutableDecls)
    if !resolvedIncludes.isEmpty then
      elabCommand (← mkMergedSpecCommandPublic (toString contractName.getId) resolvedIncludes)

    let findIdxSimpCmds ← mkFindIdxFieldSimpCommandsPublic contractName fields
    for cmd in findIdxSimpCmds do
      elabCommand cmd

    let findIdxParamSimpCmds ← mkFindIdxParamSimpCommandsPublic contractName ctor functions
    for cmd in findIdxParamSimpCmds do
      elabCommand cmd

    -- Emit per-function semantic preservation theorem skeletons after spec generation.
    for fn in functions do
      elabCommand (← mkSemanticBridgeCommand contractName fields fn)

    -- Emit per-function _is_view theorems for view functions (#1729, Axis 3 Step 1a).
    for fn in functions do
      if fn.isView then
        elabCommand (← mkViewTheoremCommand fn)
        if fn.params.isEmpty && fn.requiresRole.isNone && fn.nonReentrantLock.isNone then
          elabCommand (← mkViewFrameTheoremCommand fn)

    -- Emit per-function _is_pure theorems for pure functions.
    for fn in functions do
      if fn.isPure then
        elabCommand (← mkPureTheoremCommand fn)

    registerContractSyntax (declarationNs ++ contractName.getId) parsed

    -- Emit per-function _no_calls theorems for no_external_calls functions (#1729, Axis 3 Step 1c).
    for fn in functions do
      if fn.noExternalCalls then
        elabCommand (← mkNoCallsTheoremCommand fn)

    -- Emit per-function _modifies theorem and _frame definition for
    -- functions with modifies(...) annotation (#1729, Axis 3 Step 1b).
    -- Mixin / include functions keep the frame definition; the automatic
    -- `_frame_holds` simp proof cannot close over mixin `require` guards.
    let generateExecutionFrame := !isMixin && resolvedIncludes.isEmpty
    for fn in functions do
      if !fn.modifies.isEmpty then
        elabCommand (← mkModifiesTheoremCommand fn)
        let frameCmds ← mkFrameDefCommand translationFields fn generateExecutionFrame
        for cmd in frameCmds do
          elabCommand cmd

    -- Emit per-function _effects conjunction theorem when multiple effect
    -- annotations are active on the same function (#1729, Axis 3 Step 1d).
    for fn in functions do
      if effectAnnotationCount fn ≥ 2 then
        elabCommand (← mkEffectsTheoremCommand fn)

    -- Emit per-function _cei_compliant theorem for functions that use default
    -- CEI enforcement (rung 1) — i.e. not opted out via any escalation rung.
    -- (#1728, Axis 2 Step 2a)
    for fn in functions do
      if !fn.allowPostInteractionWrites && fn.nonReentrantLock.isNone && !fn.ceiSafe then
        elabCommand (← mkCEICompliantTheoremCommand fn)

    -- Emit per-function _nonreentrant theorem for functions with nonreentrant(field).
    -- (#1728, Axis 2 Step 2b — known-safe guard rung)
    for fn in functions do
      match fn.nonReentrantLock with
      | some lockIdent =>
          elabCommand (← mkNonReentrantTheoremCommand fn (toString lockIdent.getId))
      | none => pure ()

    -- Emit per-function _cei_safe theorem for functions with cei_safe annotation.
    -- (#1728, Axis 2 Step 2b — Lean proof rung)
    for fn in functions do
      if fn.ceiSafe then
        elabCommand (← mkCEISafeTheoremCommand fn)

    -- Emit per-function _requires_role theorem for functions with requires(field).
    -- (#1728, Axis 2 Step 2c — access control)
    for role in roleDecls do
      elabCommand (← mkRoleDeclTheoremCommand role)

    for fn in functions do
      match fn.requiresRole with
      | some roleIdent =>
          elabCommand (← mkRequiresRoleTheoremCommand fn (toString roleIdent.getId))
          match roleDecls.find? (fun role => role.name == toString roleIdent.getId) with
          | some role => elabCommand (← mkAccessControlTheoremCommand fn role)
          | none => pure ()
      | none => pure ()

    elabCommand (← `(end $contractName))
  catch err =>
    elabCommand (← `(end $contractName))
    throw err

@[command_elab verityContractCmd]
def elabVerityContract : CommandElab := fun stx =>
  elabVerityContractOrMixin stx

@[command_elab verityMixinCmd]
def elabVerityMixin : CommandElab := fun stx =>
  elabVerityContractOrMixin stx

@[command_elab verityIntrinsicCmd]
def elabVerityIntrinsic : CommandElab := fun stx => do
  match stx with
  -- Accept one or more comma-separated typed parameters (#1977). The Yul
  -- `verbatim` lowering's input arity must match the parameter count.
  | `(verity_intrinsic $name:ident ( $[ $paramNames:ident : $paramTypes:term ],* ) : $retTy:term
        where $pureKw:ident; yul := $yul:verityIntrinsicYul; min_fork := $fork:ident;
        semantics := $semantics:term; obligation [ $[$obligations:verityIntrinsicObligation],* ]) => do
      unless toString pureKw.getId == "pure" do
        throwErrorAt pureKw "verity_intrinsic currently supports only pure intrinsics"
      if paramNames.size == 0 then
        throwErrorAt stx "verity_intrinsic requires at least one parameter"
      for pair in paramNames.zip paramTypes do
        unless isUint256TypeSyntax pair.2 do
          throwErrorAt pair.2
            s!"verity_intrinsic parameter '{toString pair.1.getId}' must have type Uint256; got {cleanTypeSyntaxString pair.2}"
      unless isUint256TypeSyntax retTy do
        throwErrorAt retTy s!"verity_intrinsic return type must be Uint256; got {cleanTypeSyntaxString retTy}"
      let parsedObligations ← obligations.mapM fun obligation => do
        match obligation with
        | `(verityIntrinsicObligation| $obligationName:ident := $status:ident $message:str) => do
            let statusString ← parseIntrinsicProofStatus status
            pure (toString obligationName.getId, statusString, message.getString)
        | _ =>
            throwErrorAt obligation "expected obligation entry `<name> := assumed \"reason\"`"
      let yulLowering ←
        match yul with
        | `(verityIntrinsicYul| verbatim $inArity:num $outArity:num (hex $opcode:str)) =>
            if inArity.getNat != paramNames.size then
              throwErrorAt yul s!"verity_intrinsic `verbatim` input arity {inArity.getNat} does not match the {paramNames.size} declared parameter(s)"
            pure <| Verity.Core.Intrinsics.YulLowering.verbatim
              inArity.getNat outArity.getNat opcode.getString
        | `(verityIntrinsicYul| builtin $builtin:str) =>
            -- Cross-check builtin input arity against the declared parameter
            -- count when the builtin has a known fixed arity. Builtins not
            -- listed in `yulBuiltinArity?` (e.g. custom precompile wrappers)
            -- still go through without enforcement so consumers can register
            -- novel names.
            let builtinName := builtin.getString
            match Verity.Core.Intrinsics.yulBuiltinArity? builtinName with
            | some (inArity, _outArity) =>
                if inArity != paramNames.size then
                  throwErrorAt yul s!"verity_intrinsic `builtin \"{builtinName}\"` expects {inArity} input(s) but {paramNames.size} parameter(s) were declared"
            | none => pure ()
            pure <| Verity.Core.Intrinsics.YulLowering.builtin builtinName
        | `(verityIntrinsicYul| [template ( $[$templateParams:ident],* ) -> $output:ident := [ $[$body:verityIntrinsicTemplateStmt],* ]]) =>
            if templateParams.size != paramNames.size then
              throwErrorAt yul s!"verity_intrinsic `template` input arity {templateParams.size} does not match the {paramNames.size} declared parameter(s)"
            for pair in templateParams.zip paramNames do
              let templateParam := toString pair.1.getId
              let declaredParam := toString pair.2.getId
              unless templateParam == declaredParam do
                throwErrorAt pair.1 s!"verity_intrinsic `template` parameter '{templateParam}' does not match declared parameter '{declaredParam}'"
            let bodyStmts ← body.toList.mapM parseIntrinsicTemplateStmt
            pure <| Verity.Core.Intrinsics.YulLowering.template
              (templateParams.toList.map (fun p => toString p.getId))
              (toString output.getId)
              bodyStmts
              parsedObligations.toList
        | _ =>
            throwErrorAt yul "expected `verbatim <inputs> <outputs> (hex \"...\")`, `builtin \"...\"`, or `[template (<params>) -> <output> := [<statements>]]`"
      match yulLowering.outputArity? with
      | some 1 => pure ()
      | some outArity =>
          throwErrorAt yul s!"verity_intrinsic lowering must produce exactly 1 output word, got {outArity}"
      | none => pure ()
      let minFork ←
        match Verity.Core.Intrinsics.HardFork.parse? (toString fork.getId) with
        | some parsed => pure parsed
        | none => throwErrorAt fork
            s!"unknown intrinsic min_fork '{toString fork.getId}' (expected cancun, prague, osaka, or fusaka alias)"
      let nameStr := toString name.getId
      let paramNameStrs : List String := paramNames.toList.map (fun id => toString id.getId)
      let paramTypeStrs : List String := paramTypes.toList.map toString
      let decl : Verity.Core.Intrinsics.IntrinsicDecl := {
        name := nameStr,
        paramNames := paramNameStrs,
        paramTypes := paramTypeStrs,
        returnType := toString retTy,
        isPure := true,
        yul := yulLowering,
        minFork := minFork,
        obligations := parsedObligations.toList,
        sourceHint := some "elabVerityIntrinsic"
      }
      liftIO <| Verity.Macro.registerIntrinsic decl
      -- Emit `def name : T1 -> T2 -> ... -> Tn -> retTy := semantics`.
      -- Curried right-associative arrow chain matches Lean's standard
      -- function shape; the `semantics` term must therefore be a
      -- curried function value (e.g. `fun x y z => ...` for three params).
      let arrowType ← paramTypes.foldrM
        (fun ty acc => `($ty -> $acc))
        retTy
      let wrapperCmd ← `(command| def $name:ident : $arrowType := $semantics)
      elabCommand wrapperCmd
      let obligationSummaryName : Ident :=
        ⟨mkIdent (name.getId.appendAfter "_intrinsic_obligations")⟩
      let obligationSummary := String.intercalate "\n" <|
        parsedObligations.toList.map (fun (n, status, msg) => s!"{n}: {status} {msg}")
      let obligationCmd ← `(command| def $obligationSummaryName:ident : String := $(strTermPublic obligationSummary))
      elabCommand obligationCmd
  | _ =>
      throwErrorAt stx
        "unsupported verity_intrinsic declaration; expected one or more parameters, yul, min_fork, semantics, and obligation clauses"

end Verity.Macro

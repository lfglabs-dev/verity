import Lean
import Compiler.Modules.ERC20
import Compiler.Modules.Calls
import Compiler.Modules.Oracle
import Compiler.Modules.Precompiles
import Compiler.Selectors
import Compiler.CompilationModel.InternalNaming
import Compiler.Keccak.Sponge
import Verity.Macro.Translate.Parsing
import Verity.Macro.Translate.Expr
import Verity.Macro.Executable
import Verity.Macro.ExternalCalls
import Verity.Macro.Functions
import Verity.Macro.Interfaces
import Verity.Macro.Internal
import Verity.Macro.Storage
import Verity.Macro.Types
import Verity.Macro.Syntax

namespace Verity.Macro

open Lean
open Lean.Elab
open Lean.Elab.Command

set_option hygiene false

register_option verity.storageNamespace.default : Bool := {
  defValue := false
  descr := "Apply the default contract-name storage namespace to verity_contract declarations that omit storage_namespace"
}

private def translateCustomErrorArgExprs
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (errorDecls : Array ErrorDecl)
    (errorName : String)
    (args : Array Term) : CommandElabM (Array Term) := do
  let some errorDecl := errorDecls.find? (fun decl => decl.name == errorName)
    | throwError s!"unknown custom error '{errorName}'"
  if args.size != errorDecl.params.size then
    throwError s!"custom error '{errorName}' expects {errorDecl.params.size} args, got {args.size}"
  args.zip errorDecl.params |>.mapM fun (arg, expectedTy) => do
    let raw ← translatePureExprWithTypes fields constDecls immutableDecls params locals arg
    normalizeTranslatedExprForType expectedTy arg raw

mutual
private partial def validateDoSeqExprTypes
    (ownerName : String)
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (externalDecls : Array ExternalDecl)
    (errorDecls : Array ErrorDecl)
    (functions : Array FunctionDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (doSeq : DoSeq) : CommandElabM Unit := do
  match doSeq with
  | `(doSeq| $[$elems:doElem]*) =>
      let _ ← validateDoElemsExprTypes ownerName fields constDecls immutableDecls externalDecls errorDecls functions params locals elems
      pure ()
  | _ => throwErrorAt doSeq "unsupported branch body; expected do-sequence"

private partial def validateDoElemsExprTypes
    (ownerName : String)
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (externalDecls : Array ExternalDecl)
    (errorDecls : Array ErrorDecl)
    (functions : Array FunctionDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (elems : Array (TSyntax `doElem)) : CommandElabM (Array TypedLocal) := do
  let mut branchLocals := locals
  for elem in elems do
    branchLocals ← validateDoElemExprTypes ownerName fields constDecls immutableDecls externalDecls errorDecls functions params branchLocals elem
  pure branchLocals

private partial def validateDoElemExprTypes
    (ownerName : String)
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (externalDecls : Array ExternalDecl)
    (errorDecls : Array ErrorDecl)
    (functions : Array FunctionDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (elem : TSyntax `doElem) : CommandElabM (Array TypedLocal) := do
  let tupleCase? ← do
    let stx := elem.raw
    if stx.getKind == `Lean.Parser.Term.doLet then
      let decl := stx[3]
      let patDecl := decl[0]
      match tupleBinderNames? patDecl[0] with
      | some names =>
          let rhs : Term := ⟨patDecl[4]⟩
          match ← resolveQualifiedFunctionApp? fields constDecls immutableDecls externalDecls params locals rhs with
          | some (qualifiedName, _) =>
              let typedNames ← unsafe qualifiedTupleBindTypedLocals patDecl qualifiedName names
              pure (some (locals ++ typedNames))
          | none =>
              match (← tryExternalCallBindStmt? fields constDecls immutableDecls externalDecls params locals rhs names) with
              | some (_, typedNames) => pure (some (locals ++ typedNames))
              | none =>
                  match (← inferTupleSourceTypes? fields constDecls immutableDecls externalDecls functions params locals rhs) with
                  | some valueTys =>
                      if names.size != valueTys.size then
                        throwErrorAt patDecl s!"tuple destructuring binds {names.size} names, but the source provides {valueTys.size} values"
                      for (name?, ty) in names.zip valueTys do
                        if let some name := name? then
                          requireSupportedLocalBindingType patDecl s!"local binding '{name}'" ty
                      let typedNames := (names.zip valueTys).filterMap fun (name?, ty) =>
                        name?.map (fun name => mkTypedLocal name ty)
                      pure (some (locals ++ typedNames))
                  | none => pure none
      | none => pure none
    else if stx.getKind == `Lean.Parser.Term.doLetArrow then
      let patDecl := stx[3]
      match tupleBinderNames? patDecl[0] with
      | some names =>
          let rhs : Term := ⟨patDecl[3][0]⟩
          match ← resolveQualifiedFunctionApp? fields constDecls immutableDecls externalDecls params locals rhs with
          | some (qualifiedName, _) =>
              let typedNames ← unsafe qualifiedTupleBindTypedLocals patDecl qualifiedName names
              pure (some (locals ++ typedNames))
          | none =>
              match (← tryExternalCallBindStmt? fields constDecls immutableDecls externalDecls params locals rhs names) with
              | some (_, typedNames) => pure (some (locals ++ typedNames))
              | none =>
                  match (← inferTupleSourceTypes? fields constDecls immutableDecls externalDecls functions params locals rhs) with
                  | some valueTys =>
                      if names.size != valueTys.size then
                        throwErrorAt patDecl s!"tuple destructuring binds {names.size} names, but the source provides {valueTys.size} values"
                      for (name?, ty) in names.zip valueTys do
                        if let some name := name? then
                          requireSupportedLocalBindingType patDecl s!"local binding '{name}'" ty
                      let typedNames := (names.zip valueTys).filterMap fun (name?, ty) =>
                        name?.map (fun name => mkTypedLocal name ty)
                      pure (some (locals ++ typedNames))
                  | none => pure none
      | none => pure none
    else
      pure none
  match tupleCase? with
  | some typedLocals => pure typedLocals
  | none => match elem with
      | `(doElem| let _ := ($rhs:term : $_ty:term)) =>
          validateDoElemExprTypes ownerName fields constDecls immutableDecls externalDecls
            errorDecls functions params locals (← `(doElem| let _ := $rhs:term))
      | `(doElem| let _ := $rhs:term) =>
          let discardName := freshSyntheticLocalName "discard" params locals #[]
          let discardIdent := mkIdent (Name.mkSimple discardName)
          validateDoElemExprTypes ownerName fields constDecls immutableDecls externalDecls
            errorDecls functions params locals (← `(doElem| let $discardIdent:ident := $rhs:term))
      | `(doElem| let _ ← $rhs:term) =>
          let discardName := freshSyntheticLocalName "__discard" params locals #[]
          let discardIdent := mkIdent (Name.mkSimple discardName)
          validateDoElemExprTypes ownerName fields constDecls immutableDecls externalDecls
            errorDecls functions params locals (← `(doElem| let $discardIdent:ident ← $rhs:term))
      | `(doElem| let mut $name:ident := $rhs:term) =>
          let ty ← inferPureExprType fields constDecls immutableDecls externalDecls params locals rhs
          requireSupportedLocalBindingType name s!"local binding '{toString name.getId}'" ty
          let interfaceName? ← interfaceNameOfTerm? params locals rhs
          pure <| locals.push (mkTypedLocal (toString name.getId) ty interfaceName?)
      | `(doElem| let $name:ident := $rhs:term) =>
          match arrayElementAliasSource? params rhs with
          | some (paramName, index, elemTy) =>
              requireWordLikeType index "arrayElement alias index"
                (← inferPureExprType fields constDecls immutableDecls externalDecls params locals index)
              pure <| locals.push
                { name := toString name.getId
                  ty := elemTy
                  source := .arrayElement paramName index elemTy }
          | none =>
              let ty ← inferPureExprType fields constDecls immutableDecls externalDecls params locals rhs
              requireSupportedLocalBindingType name s!"local binding '{toString name.getId}'" ty
              let interfaceName? ← interfaceNameOfTerm? params locals rhs
              pure <| locals.push (mkTypedLocal (toString name.getId) ty interfaceName?)
      | `(doElem| let $name:ident ← $rhs:term) =>
          match stripParens rhs with
          | `(term| allocArray $len:term) =>
              requireWordLikeType len "allocArray length"
                (← inferPureExprType fields constDecls immutableDecls externalDecls params locals len)
              pure <| locals.push
                { name := toString name.getId
                  ty := .array .uint256
                  source := .memoryArray }
          | _ =>
              match ← localInternalArrayReturnBind? fields constDecls immutableDecls externalDecls functions params locals rhs with
              | some (_, _, elemTy) =>
                  pure <| locals.push
                    { name := toString name.getId
                      ty := .array elemTy
                      source := .memoryArray }
              | none =>
                  -- requireSomeUintError is the only bind source that takes
                  -- a custom-error name; validate the error name against the
                  -- contract's `errors` block before falling through to the
                  -- generic bind-source typer.
                  match stripParens rhs with
                  | `(term| requireSomeUintError $_optExpr:term $errorName:ident($args,*)) =>
                      let argTypes ← args.getElems.mapM
                        (inferPureExprType fields constDecls immutableDecls externalDecls params locals)
                      validateCustomErrorCall ownerName (toString errorName.getId)
                        params errorDecls args.getElems argTypes
                  | _ => pure ()
                  match ← resolveTypedInterfaceCall? fields constDecls immutableDecls externalDecls params locals rhs with
                  | some (_, _, _, some retTy, _) =>
                      requireSupportedLocalBindingType name s!"local binding '{toString name.getId}'" retTy
                      pure <| locals.push (mkTypedLocal (toString name.getId) retTy)
                  | some (_, _, _, none, _) =>
                      -- void interface method: cannot bind its (empty) result
                      throwErrorAt rhs s!"interface call '{toString name.getId}' binds a void method; call it as a statement, not `let ... ←`"
                  | none =>
                      match ← callResultBindStmt? fields constDecls immutableDecls externalDecls params locals rhs (toString name.getId) with
                      | some (_, resultLocal) =>
                          pure <| locals.push resultLocal
                      | none =>
                          let ty ← inferBindSourceType fields constDecls immutableDecls externalDecls functions params locals rhs
                          requireSupportedLocalBindingType name s!"local binding '{toString name.getId}'" ty
                          pure <| locals.push (mkTypedLocal (toString name.getId) ty)
      | `(doElem| $name:ident := $rhs:term) =>
          let _ ← inferPureExprType fields constDecls immutableDecls externalDecls params locals rhs
          pure locals
      | `(doElem| return $value:term) =>
          let _ ←
            match (← inferTupleSourceTypes? fields constDecls immutableDecls externalDecls functions params locals value) with
            | some _ => pure .unit
            | none => inferPureExprType fields constDecls immutableDecls externalDecls params locals value
          pure locals
      | `(doElem| pure ()) =>
          pure locals
      | `(doElem| if $cond:term then $thenBranch:doSeq else $elseBranch:doSeq) =>
          requireBoolType cond "if condition" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals cond)
          validateDoSeqExprTypes ownerName fields constDecls immutableDecls externalDecls errorDecls functions params locals thenBranch
          validateDoSeqExprTypes ownerName fields constDecls immutableDecls externalDecls errorDecls functions params locals elseBranch
          pure locals
      | `(doElem| forEach $name:term $count:term $body:term) =>
          requireWordLikeType count "forEach count" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals count)
          match stripParens body with
          | `(term| do $[$inner:doElem]*) =>
              let _ ← validateDoElemsExprTypes
                ownerName fields constDecls immutableDecls externalDecls errorDecls functions params
                (locals.push (mkTypedLocal (← expectStringOrIdent name) .uint256))
                inner
              pure locals
          | _ => throwErrorAt body "forEach body must be a do block"
      | `(doElem| forEachSetBit $name:term $bitmap:term $body:term) =>
          requireWordLikeType bitmap "forEachSetBit bitmap" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals bitmap)
          match stripParens body with
          | `(term| do $[$inner:doElem]*) =>
              let _ ← validateDoElemsExprTypes
                ownerName fields constDecls immutableDecls externalDecls errorDecls functions params
                (locals.push (mkTypedLocal (← expectStringOrIdent name) .uint256))
                inner
              pure locals
          | _ => throwErrorAt body "forEachSetBit body must be a do block"
      | `(doElem| requireError $cond:term $errorName:ident($args,*)) =>
          requireBoolType cond "requireError condition" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals cond)
          let argTypes ← args.getElems.mapM
            (inferPureExprType fields constDecls immutableDecls externalDecls params locals)
          validateCustomErrorCall ownerName (toString errorName.getId)
            params errorDecls args.getElems argTypes
          pure locals
      | `(doElem| revert $errorName:ident($args,*)) =>
          let argTypes ← args.getElems.mapM
            (inferPureExprType fields constDecls immutableDecls externalDecls params locals)
          validateCustomErrorCall ownerName (toString errorName.getId)
            params errorDecls args.getElems argTypes
          pure locals
      | `(doElem| revertError $errorName:ident($args,*)) =>
          let argTypes ← args.getElems.mapM
            (inferPureExprType fields constDecls immutableDecls externalDecls params locals)
          validateCustomErrorCall ownerName (toString errorName.getId)
            params errorDecls args.getElems argTypes
          pure locals
      | `(doElem| panic($code:term)) =>
          requireWordLikeType code "panic code"
            (← inferPureExprType fields constDecls immutableDecls externalDecls params locals code)
          pure locals
      | `(doElem| tryCatch $attempt:term $handler:term) => do
          requireWordLikeType attempt "tryCatch attempt"
            (← inferPureExprType fields constDecls immutableDecls externalDecls params locals attempt)
          let (payloadName?, catchElems) ← parseTryCatchHandler handler
          validateTryCatchHandlerDoesNotUsePayload handler payloadName? catchElems
          let _ ← validateDoElemsExprTypes ownerName fields constDecls immutableDecls externalDecls errorDecls functions params locals catchElems
          pure locals
      | `(doElem| unsafe $_reason:str do $body:doSeq) =>
          validateDoSeqExprTypes ownerName fields constDecls immutableDecls externalDecls errorDecls functions params locals body
          pure locals
      | `(doElem| ecmBind $names:term $module:term $args:term) =>
          let resultVars ← expectStringList names
          ensureFreshLocalNames (typedLocalNames locals) (resultVars.map some) names
          validateEcmExprListLiteral fields constDecls immutableDecls externalDecls params locals
            args "ECM argument"
          validateResultEcmModuleTerm module resultVars
          pure <| locals ++ resultVars.map (fun name => mkTypedLocal name .uint256)
      | `(doElem| emit $_eventName:term $values:term) =>
          match stripParens values with
          | `(term| [ $[$args],* ]) =>
              let mut branchLocals := locals
              for arg in args do
                match ← localInternalArrayReturnBind? fields constDecls immutableDecls externalDecls functions params branchLocals arg with
                | some (_, _, elemTy) =>
                    let tempName := freshSyntheticLocalName "emit_array" params branchLocals #[]
                    branchLocals := branchLocals.push
                      { name := tempName
                        ty := .array elemTy
                        source := .memoryArray }
                | none =>
                    let _ ← inferEmitArgExprType fields constDecls immutableDecls externalDecls params branchLocals arg
                    pure ()
              pure locals
          | _ => throwErrorAt values "expected list literal [..]"
      | `(doElem| $stmt:term) =>
          validateEffectStmtExprTypes fields constDecls immutableDecls externalDecls functions params locals stmt
          pure locals
      | _ => throwErrorAt elem "unsupported do element"

private partial def validateEffectStmtExprTypes
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (externalDecls : Array ExternalDecl)
    (functions : Array FunctionDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (stx : Term) : CommandElabM Unit := do
  let stx := stripParens stx
  match stx with
  | `(term| safeTransfer $token:term $to:term $amount:term) =>
      for arg in [token, to, amount] do
        requireWordLikeType arg "ERC-20 helper" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals arg)
  | `(term| safeTransferFrom $token:term $fromAddr:term $to:term $amount:term) =>
      for arg in [token, fromAddr, to, amount] do
        requireWordLikeType arg "ERC-20 helper" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals arg)
  | `(term| safeApprove $token:term $spender:term $amount:term) =>
      for arg in [token, spender, amount] do
        requireWordLikeType arg "ERC-20 helper" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals arg)
  | `(term| legacyStringSafeTransfer $token:term $to:term $amount:term) =>
      for arg in [token, to, amount] do
        requireWordLikeType arg "ERC-20 helper" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals arg)
  | `(term| legacyStringSafeTransferFrom $token:term $fromAddr:term $to:term $amount:term) =>
      for arg in [token, fromAddr, to, amount] do
        requireWordLikeType arg "ERC-20 helper" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals arg)
  | `(term| setStorage $field:ident $value:term) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.adtInfo?, f.ty with
      | some _, _ => pure ()
      | none, .scalar (.adt _ _) => pure ()
      | _, _ =>
          let _ ← inferPureExprType fields constDecls immutableDecls externalDecls params locals value
          pure ()
  | `(term| setStorageAddr $_field:ident $value:term)
    | `(term| require $value:term $_msg) =>
      let _ ← inferPureExprType fields constDecls immutableDecls externalDecls params locals value
      pure ()
  | `(term| setPackedStorage $_field:ident $_wordOffset:num $value:term) =>
      let _ ← inferPureExprType fields constDecls immutableDecls externalDecls params locals value
      pure ()
  | `(term| pushStorageArray $_field:ident $value:term) => do
      let _ ← inferPureExprType fields constDecls immutableDecls externalDecls params locals value
      pure ()
  | `(term| popStorageArray $_field:ident) =>
      pure ()
  | `(term| setStorageArrayElement $_field:ident $index:term $value:term) => do
      let _ ← inferPureExprType fields constDecls immutableDecls externalDecls params locals index
      let _ ← inferPureExprType fields constDecls immutableDecls externalDecls params locals value
      pure ()
  | `(term| setMapping $_field:ident $key:term $value:term) | `(term| setMappingAddr $_field:ident $key:term $value:term)
    | `(term| setMappingUint $_field:ident $key:term $value:term) | `(term| setMappingUintAddr $_field:ident $key:term $value:term)
    | `(term| setMappingWord $_field:ident $key:term $_wordOffset:num $value:term)
    | `(term| setStructMember $_field:term $key:term $_member:term $value:term) => do
      let _ ← inferPureExprType fields constDecls immutableDecls externalDecls params locals key
      let _ ← inferPureExprType fields constDecls immutableDecls externalDecls params locals value
  | `(term| setMapping2 $_field:ident $key1:term $key2:term $value:term)
    | `(term| setStructMember2 $_field:term $key1:term $key2:term $_member:term $value:term) => do
      let _ ← inferPureExprType fields constDecls immutableDecls externalDecls params locals key1
      let _ ← inferPureExprType fields constDecls immutableDecls externalDecls params locals key2
      let _ ← inferPureExprType fields constDecls immutableDecls externalDecls params locals value
  | `(term| setMappingN $_field:ident $keys:term $value:term) => do
      for key in (← expectMappingKeyTerms keys) do
        let _ ← inferPureExprType fields constDecls immutableDecls externalDecls params locals key
      let _ ← inferPureExprType fields constDecls immutableDecls externalDecls params locals value
  | `(term| setMemoryArrayElement $name:term $index:term $value:term) => do
      let (_, elemTy) ← requireSupportedMemoryArrayLocal name "setMemoryArrayElement" locals
      unless isSingleWordStaticValueType elemTy do
        throwErrorAt name s!"setMemoryArrayElement currently supports only Array<wordLike> memory locals, got Array {renderValueType elemTy}"
      requireWordLikeType index "memory array index"
        (← inferPureExprType fields constDecls immutableDecls externalDecls params locals index)
      requireDeclaredValueType value "setMemoryArrayElement value" elemTy
        (← inferPureExprType fields constDecls immutableDecls externalDecls params locals value)
      pure ()
  | `(term| mstore $offset:term $value:term) | `(term| memoryStore($offset, $value))
    | `(term| tstore $offset:term $value:term) => do
      requireWordLikeType offset "memory-store offset"
        (← inferPureExprType fields constDecls immutableDecls externalDecls params locals offset)
      requireWordLikeType value "memory-store value"
        (← inferPureExprType fields constDecls immutableDecls externalDecls params locals value)
  | `(term| calldatacopy $destOffset:term $sourceOffset:term $size:term)
    | `(term| returndataCopy $destOffset:term $sourceOffset:term $size:term)
    | `(term| returnDataCopy($destOffset, $sourceOffset, $size)) => do
      requireWordLikeType destOffset "returndata-copy destination offset"
        (← inferPureExprType fields constDecls immutableDecls externalDecls params locals destOffset)
      requireWordLikeType sourceOffset "returndata-copy source offset"
        (← inferPureExprType fields constDecls immutableDecls externalDecls params locals sourceOffset)
      requireWordLikeType size "returndata-copy size"
        (← inferPureExprType fields constDecls immutableDecls externalDecls params locals size)
  | `(term| rawLog $topics:term $dataOffset:term $dataSize:term) => do
      match stripParens topics with
      | `(term| [ $[$xs],* ]) =>
          for x in xs do
            let _ ← inferPureExprType fields constDecls immutableDecls externalDecls params locals x
      | _ => throwErrorAt topics "expected list literal [..]"
      let _ ← inferPureExprType fields constDecls immutableDecls externalDecls params locals dataOffset
      let _ ← inferPureExprType fields constDecls immutableDecls externalDecls params locals dataSize
  | `(term| returnValues $values:term) => do
      match stripParens values with
      | `(term| [ $[$xs],* ]) =>
          for x in xs do
            let _ ← inferPureExprType fields constDecls immutableDecls externalDecls params locals x
      | _ => throwErrorAt values "expected list literal [..]"
      pure ()
  | `(term| emit $_eventName:term $values:term) => do
      match stripParens values with
      | `(term| [ $[$xs],* ]) =>
          for x in xs do
            let _ ← inferEmitArgExprType fields constDecls immutableDecls externalDecls params locals x
      | _ => throwErrorAt values "expected list literal [..]"
      pure ()
  | `(term| ecmDo $_module:term $args:term) => do
      validateEcmExprListLiteral fields constDecls immutableDecls externalDecls params locals
        args "ECM argument"
      pure ()
  | `(term| returnArray $name:term) => do
      match localMemoryArray? locals name with
      | some (_, elemTy) =>
          unless isSingleWordStaticValueType elemTy do
            throwErrorAt name s!"returnArray currently supports only Array<wordLike> memory locals, got Array {renderValueType elemTy}"
      | none =>
          let ty ← requireDirectParamRef name "returnArray" params
          requireSupportedReturnArrayType name "returnArray" ty
  | `(term| returnBytes $name:term) => do
      let ty ← requireDirectParamRef name "returnBytes" params
      requireSupportedReturnBytesType name "returnBytes" ty
  | `(term| returnStorageWords $name:term) => do
      let ty ← requireDirectParamRef name "returnStorageWords" params
      requireSupportedReturnStorageWordsType name "returnStorageWords" ty
  | `(term| returnCodeData $pointer:term) => do
      requireDeclaredValueType pointer "returnCodeData pointer" .address
        (← inferPureExprType fields constDecls immutableDecls externalDecls params locals pointer)
  | `(term| externalCallBind $_names:term $_fnName:term $args:term)
    | `(term| tryExternalCallBind $_successVar:term $_names:term $_fnName:term $args:term) =>
      match stripParens args with
      | `(term| [ $[$xs],* ]) =>
          for x in xs do
            let _ ← inferPureExprType fields constDecls immutableDecls externalDecls params locals x
      | _ => throwErrorAt args "expected list literal [..]"
  | `(term| callExternal $name:ident ($[$args:term],*)) => do
      let extName := toString name.getId
      let ext ← match externalDecls.find? (fun ext => ext.name == extName) with
        | some ext => pure ext
        | none => throwErrorAt name s!"unknown linked external '{extName}'"
      unless ext.returnTys.isEmpty do
        throwErrorAt stx s!"callExternal '{extName}' returns values; bind it with `let ... ← ...`"
      validateLinkedExternalCallArgs fields constDecls immutableDecls externalDecls params locals
        extName ext.params args
      let _ ← translateLinkedExternalCallArgs fields constDecls immutableDecls params locals args
  | `(term| revertReturndata) =>
      pure ()
  | _ =>
      -- a typed interface call in statement position is only valid when the
      -- method is void; `resolveTypedInterfaceCall?` already validates arg
      -- count, arg types, and the supported typed-interface ABI fragment.
      match ← resolveTypedInterfaceCall? fields constDecls immutableDecls externalDecls params locals stx with
      | some (_, _, _, none, _) => do
          pure ()
      | some (_, _, _, some retTy, _) =>
          throwErrorAt stx
            s!"interface call returns {renderValueType retTy}; bind it with `let ... ← ...`"
      | none =>
      match ← resolveLocalFunctionApp? fields constDecls immutableDecls externalDecls functions params locals stx with
      | some (fn, argTerms) =>
          ensureCallableAsInternalHelper stx fn
          if fn.returnTy != .unit then
            throwErrorAt stx
              s!"helper call '{fn.name}' returns {renderValueType fn.returnTy}; use `let ... ← {fn.name} ...` or tuple destructuring"
          for arg in argTerms do
            let _ ← inferPureExprType fields constDecls immutableDecls externalDecls params locals arg
          pure ()
      | none =>
          let _ ← inferPureExprType fields constDecls immutableDecls externalDecls params locals stx
          pure ()
end

private def validateFunctionBodyExprTypes
    (fields : Array StorageFieldDecl)
    (errorDecls : Array ErrorDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (externalDecls : Array ExternalDecl)
    (functions : Array FunctionDecl)
    (fn : FunctionDecl) : CommandElabM Unit := do
  match fn.body with
  | `(term| do $[$elems:doElem]*) =>
      let _ ← validateDoElemsExprTypes fn.name fields constDecls immutableDecls externalDecls errorDecls functions fn.params #[] elems
      pure ()
  | _ => throwErrorAt fn.body "function body must be a do block"

private def validateConstantExprTypes
    (constDecls : Array ConstantDecl) : CommandElabM Unit := do
  for constant in constDecls do
    let inferredTy ← inferPureExprType #[] constDecls #[] #[] #[] #[] constant.body
    requireDeclaredValueType constant.body s!"constant '{constant.name}'" constant.ty inferredTy

private def validateConstructorBodyExprTypes
    (fields : Array StorageFieldDecl)
    (errorDecls : Array ErrorDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (externalDecls : Array ExternalDecl)
    (functions : Array FunctionDecl)
    (ctor : ConstructorDecl) : CommandElabM Unit := do
  match ctor.body with
  | `(term| do $[$elems:doElem]*) =>
      let _ ← validateDoElemsExprTypes "constructor" fields constDecls immutableDecls externalDecls errorDecls functions ctor.params #[] elems
      pure ()
  | _ => throwErrorAt ctor.body "constructor body must be a do block"

private def translateERC20BindStmt?
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (functions : Array FunctionDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (varName : String)
    (rhs : Term) : CommandElabM (Option Term) := do
  let rhs := stripParens rhs
  match rhs with
  | `(term| balanceOf $token:term $owner:term) =>
      match lookupFunctionByNameAndArity functions "balanceOf" 2 with
      | some localFn =>
          throwErrorAt rhs
            s!"ERC-20 helper form '{localFn.name}' conflicts with contract function '{localFn.name}'; rename the function or avoid the direct helper syntax here"
      | none =>
          let tokenExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals token
          let ownerExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals owner
          pure <| some (← `(Compiler.CompilationModel.Stmt.ecm
            (Compiler.Modules.ERC20.balanceOfModule $(strTerm varName))
            [$tokenExpr, $ownerExpr]))
  | `(term| allowance $token:term $owner:term $spender:term) =>
      match lookupFunctionByNameAndArity functions "allowance" 3 with
      | some localFn =>
          throwErrorAt rhs
            s!"ERC-20 helper form '{localFn.name}' conflicts with contract function '{localFn.name}'; rename the function or avoid the direct helper syntax here"
      | none =>
          let tokenExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals token
          let ownerExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals owner
          let spenderExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals spender
          pure <| some (← `(Compiler.CompilationModel.Stmt.ecm
            (Compiler.Modules.ERC20.allowanceModule $(strTerm varName))
            [$tokenExpr, $ownerExpr, $spenderExpr]))
  | `(term| totalSupply $token:term) =>
      match lookupFunctionByNameAndArity functions "totalSupply" 1 with
      | some localFn =>
          throwErrorAt rhs
            s!"ERC-20 helper form '{localFn.name}' conflicts with contract function '{localFn.name}'; rename the function or avoid the direct helper syntax here"
      | none =>
          let tokenExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals token
          pure <| some (← `(Compiler.CompilationModel.Stmt.ecm
            (Compiler.Modules.ERC20.totalSupplyModule $(strTerm varName))
            [$tokenExpr]))
  | _ => pure none

private def adtConstructorApp? (stx : Term) : Option (Ident × Array Term) :=
  let stx := stripParens stx
  match stx with
  | `(term| $ctor:ident) => some (ctor, #[])
  | `(term| $ctor:ident $args:term*) => some (ctor, args)
  | _ => none

private def adtConstructorSyntax? (stx : Term) : Option (String × Array Term) :=
  let stx := stripParens stx
  match stx with
  | `(term| $variant:str) => some (variant.getString, #[])
  | `(term| ($variant:str, [ $[$args:term],* ])) => some (variant.getString, args)
  | `(term| adt $variant:str) => some (variant.getString, #[])
  | `(term| adt $variant:str [ $[$args:term],* ]) => some (variant.getString, args)
  | _ =>
      match adtConstructorApp? stx with
      | some (variant, args) =>
          if toString variant.getId == "adt" then
            match args with
            | #[arg] =>
                match stripParens arg with
                | `(term| $variant:str) => some (variant.getString, #[])
                | _ => none
            | #[arg, argList] =>
                match stripParens arg, stripParens argList with
                | `(term| $variant:str), `(term| [ $[$payloadArgs:term],* ]) =>
                    some (variant.getString, payloadArgs)
                | _, _ => none
            | _ => none
          else
            some (toString variant.getId, args)
      | none => none

private def translateAdtConstructForStorage
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (adtName : String)
    (value : Term) : CommandElabM Term := do
  match adtConstructorSyntax? value with
  | some (variantName, args) =>
      let argExprs ← args.mapM (translatePureExprWithTypes fields constDecls immutableDecls params locals)
      `(Compiler.CompilationModel.Expr.adtConstruct
          $(strTerm adtName)
          $(strTerm variantName)
          [ $[$argExprs],* ])
  | none =>
      throwErrorAt value
        s!"ADT storage assignment for '{adtName}' must use a variant constructor so payload slots are preserved"

private def storageFieldAdtName? (field : StorageFieldDecl) : Option String :=
  match field.adtInfo? with
  | some (adtName, _) => some adtName
  | none =>
      match field.ty with
      | .scalar (.adt adtName _) => some adtName
      | _ => none

private def translateEffectStmt
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (externalDecls : Array ExternalDecl)
    (functions : Array FunctionDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (stx : Term) : CommandElabM Term := do
  let stx := stripParens stx
  match stx with
  | `(term| safeTransfer $token:term $to:term $amount:term) =>
      match lookupFunctionByNameAndArity functions "safeTransfer" 3 with
      | some localFn =>
          throwErrorAt stx
            s!"ERC-20 helper form '{localFn.name}' conflicts with contract function '{localFn.name}'; rename the function or avoid the direct helper syntax here"
      | _ =>
          let tokenExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals token
          let toExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals to
          let amountExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals amount
          `(Compiler.CompilationModel.Stmt.ecm
              Compiler.Modules.ERC20.safeTransferModule
              [$tokenExpr, $toExpr, $amountExpr])
  | `(term| safeTransferFrom $token:term $fromAddr:term $to:term $amount:term) =>
      match lookupFunctionByNameAndArity functions "safeTransferFrom" 4 with
      | some localFn =>
          throwErrorAt stx
            s!"ERC-20 helper form '{localFn.name}' conflicts with contract function '{localFn.name}'; rename the function or avoid the direct helper syntax here"
      | _ =>
          let tokenExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals token
          let fromExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals fromAddr
          let toExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals to
          let amountExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals amount
          `(Compiler.CompilationModel.Stmt.ecm
              Compiler.Modules.ERC20.safeTransferFromModule
              [$tokenExpr, $fromExpr, $toExpr, $amountExpr])
   | `(term| safeApprove $token:term $spender:term $amount:term) =>
       match lookupFunctionByNameAndArity functions "safeApprove" 3 with
       | some localFn =>
           throwErrorAt stx
             s!"ERC-20 helper form '{localFn.name}' conflicts with contract function '{localFn.name}'; rename the function or avoid the direct helper syntax here"
       | _ =>
           let tokenExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals token
           let spenderExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals spender
           let amountExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals amount
           `(Compiler.CompilationModel.Stmt.ecm
               Compiler.Modules.ERC20.safeApproveModule
               [$tokenExpr, $spenderExpr, $amountExpr])
   | `(term| legacyStringSafeTransfer $token:term $to:term $amount:term) =>
       match lookupFunctionByNameAndArity functions "legacyStringSafeTransfer" 3 with
       | some localFn =>
           throwErrorAt stx
             s!"ERC-20 helper form '{localFn.name}' conflicts with contract function '{localFn.name}'; rename the function or avoid the direct helper syntax here"
       | _ =>
           let tokenExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals token
           let toExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals to
           let amountExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals amount
           `(Compiler.CompilationModel.Stmt.ecm
               Compiler.Modules.ERC20.legacyStringSafeTransferModule
               [$tokenExpr, $toExpr, $amountExpr])
   | `(term| legacyStringSafeTransferFrom $token:term $fromAddr:term $to:term $amount:term) =>
       match lookupFunctionByNameAndArity functions "legacyStringSafeTransferFrom" 4 with
       | some localFn =>
           throwErrorAt stx
             s!"ERC-20 helper form '{localFn.name}' conflicts with contract function '{localFn.name}'; rename the function or avoid the direct helper syntax here"
       | _ =>
           let tokenExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals token
           let fromExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals fromAddr
           let toExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals to
           let amountExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals amount
           `(Compiler.CompilationModel.Stmt.ecm
               Compiler.Modules.ERC20.legacyStringSafeTransferFromModule
               [$tokenExpr, $fromExpr, $toExpr, $amountExpr])
   | `(term| ecmDo $module:term $args:term) =>
      validateEffectOnlyEcmModuleTerm module
      let argExprs ← expectExprList fields constDecls immutableDecls params locals args
      `(Compiler.CompilationModel.Stmt.ecm
          $module
          [ $[$argExprs],* ])
  | `(term| setStorage $field:ident $value:term) =>
      let f ← lookupStorageField fields (toString field.getId)
      match storageFieldAdtName? f with
      | some adtName =>
          `(Compiler.CompilationModel.Stmt.setStorage
              $(strTerm f.name)
              $(← translateAdtConstructForStorage fields constDecls immutableDecls params locals adtName value))
      | none =>
          match f.ty with
          | .scalar .uint256 | .scalar .int256 | .scalar (.newtype _ .uint256) =>
              `(Compiler.CompilationModel.Stmt.setStorage $(strTerm f.name) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals value))
          | .scalar (.adt adtName _) =>
              `(Compiler.CompilationModel.Stmt.setStorage
                  $(strTerm f.name)
                  $(← translateAdtConstructForStorage fields constDecls immutableDecls params locals adtName value))
          | .scalar .address | .scalar (.newtype _ .address) =>
              throwErrorAt stx s!"field '{f.name}' is Address-valued; use setStorageAddr"
          | .dynamicArray _ =>
              throwErrorAt stx s!"field '{f.name}' is a storage dynamic array; use pushStorageArray/popStorageArray/setStorageArrayElement"
          | _ =>
              throwErrorAt stx s!"field '{f.name}' is not Uint256; use setStorageAddr"
  | `(term| setStorageAddr $field:ident $value) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .scalar .address | .scalar (.newtype _ .address) =>
          `(Compiler.CompilationModel.Stmt.setStorageAddr $(strTerm f.name) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals value))
      | .scalar .uint256 | .scalar (.newtype _ .uint256) =>
          throwErrorAt stx s!"field '{f.name}' is Uint256-valued; use setStorage"
      | .dynamicArray _ =>
          throwErrorAt stx s!"field '{f.name}' is a storage dynamic array; use pushStorageArray/popStorageArray/setStorageArrayElement"
      | _ =>
          throwErrorAt stx s!"field '{f.name}' is not Address; use setStorage"
  | `(term| setPackedStorage $field:ident $wordOffset:num $value:term) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .scalar _ =>
          `(Compiler.CompilationModel.Stmt.setStorageWord
              $(strTerm f.name)
              $(natTerm (← natFromSyntax wordOffset))
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals value))
      | .dynamicArray _ =>
          throwErrorAt stx s!"field '{f.name}' is a storage dynamic array; setPackedStorage requires a scalar root slot"
      | .mappingAddressToUint256 | .mappingUintToUint256 | .mapping2AddressToAddressToUint256
      | .mappingChain _ | .mappingStruct _ _ | .mappingStruct2 _ _ _ =>
          throwErrorAt stx s!"field '{f.name}' is a mapping; setPackedStorage requires a scalar root slot"
  | `(term| setMapping $field:ident $key:term $value:term) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .mappingAddressToUint256 =>
          `(Compiler.CompilationModel.Stmt.setMapping
              $(strTerm f.name)
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals key)
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals value))
      | .mappingUintToUint256 =>
          `(Compiler.CompilationModel.Stmt.setMappingUint
              $(strTerm f.name)
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals key)
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals value))
      | .mapping2AddressToAddressToUint256 =>
          throwErrorAt stx s!"field '{f.name}' is a double mapping; use setMapping2"
      | .mappingChain _ =>
          throwErrorAt stx s!"field '{f.name}' uses {storageTypeMappingDepth? f.ty |>.getD 0} mapping keys; use setMappingN"
      | .dynamicArray _ =>
          throwErrorAt stx s!"field '{f.name}' is a storage dynamic array; use pushStorageArray/popStorageArray/setStorageArrayElement"
      | .mappingStruct _ _ | .mappingStruct2 _ _ _ =>
          throwErrorAt stx s!"field '{f.name}' is a struct-valued mapping; use setStructMember/setStructMember2"
      | .scalar _ => throwErrorAt stx s!"field '{f.name}' is not a mapping"
  | `(term| setMappingAddr $field:ident $key:term $value:term) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .mappingAddressToUint256 =>
          `(Compiler.CompilationModel.Stmt.setMapping
              $(strTerm f.name)
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals key)
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals value))
      | .mappingUintToUint256 =>
          throwErrorAt stx s!"field '{f.name}' is Uint256-keyed; use setMappingUintAddr"
      | .mapping2AddressToAddressToUint256 =>
          throwErrorAt stx s!"field '{f.name}' is a double mapping; use setMapping2"
      | .mappingChain _ =>
          throwErrorAt stx s!"field '{f.name}' uses {storageTypeMappingDepth? f.ty |>.getD 0} mapping keys; use setMappingN"
      | .dynamicArray _ =>
          throwErrorAt stx s!"field '{f.name}' is a storage dynamic array; use pushStorageArray/popStorageArray/setStorageArrayElement"
      | .mappingStruct _ _ | .mappingStruct2 _ _ _ =>
          throwErrorAt stx s!"field '{f.name}' is a struct-valued mapping; use setStructMember/setStructMember2"
      | .scalar _ => throwErrorAt stx s!"field '{f.name}' is not a mapping"
  | `(term| setMappingUint $field:ident $key:term $value:term) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .mappingUintToUint256 =>
          `(Compiler.CompilationModel.Stmt.setMappingUint
              $(strTerm f.name)
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals key)
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals value))
      | .mappingAddressToUint256 =>
          throwErrorAt stx s!"field '{f.name}' is Address-keyed; use setMapping"
      | .mapping2AddressToAddressToUint256 =>
          throwErrorAt stx s!"field '{f.name}' is a double mapping; use setMapping2"
      | .mappingChain _ =>
          throwErrorAt stx s!"field '{f.name}' uses {storageTypeMappingDepth? f.ty |>.getD 0} mapping keys; use setMappingN"
      | .dynamicArray _ =>
          throwErrorAt stx s!"field '{f.name}' is a storage dynamic array; use pushStorageArray/popStorageArray/setStorageArrayElement"
      | .mappingStruct _ _ | .mappingStruct2 _ _ _ =>
          throwErrorAt stx s!"field '{f.name}' is a struct-valued mapping; use setStructMember/setStructMember2"
      | .scalar _ => throwErrorAt stx s!"field '{f.name}' is not a mapping"
  | `(term| setMappingUintAddr $field:ident $key:term $value:term) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .mappingUintToUint256 =>
          `(Compiler.CompilationModel.Stmt.setMappingUint
              $(strTerm f.name)
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals key)
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals value))
      | .mappingAddressToUint256 =>
          throwErrorAt stx s!"field '{f.name}' is Address-keyed; use setMappingAddr"
      | .mapping2AddressToAddressToUint256 =>
          throwErrorAt stx s!"field '{f.name}' is a double mapping; use setMapping2"
      | .mappingChain _ =>
          throwErrorAt stx s!"field '{f.name}' uses {storageTypeMappingDepth? f.ty |>.getD 0} mapping keys; use setMappingN"
      | .dynamicArray _ =>
          throwErrorAt stx s!"field '{f.name}' is a storage dynamic array; use pushStorageArray/popStorageArray/setStorageArrayElement"
      | .mappingStruct _ _ | .mappingStruct2 _ _ _ =>
          throwErrorAt stx s!"field '{f.name}' is a struct-valued mapping; use setStructMember/setStructMember2"
      | .scalar _ => throwErrorAt stx s!"field '{f.name}' is not a mapping"
  | `(term| setMappingWord $field:ident $key:term $wordOffset:num $value:term) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .mappingAddressToUint256 | .mappingUintToUint256 =>
          `(Compiler.CompilationModel.Stmt.setMappingWord
              $(strTerm f.name)
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals key)
              $wordOffset
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals value))
      | .mapping2AddressToAddressToUint256 =>
          throwErrorAt stx s!"field '{f.name}' is a double mapping; use setMapping2Word"
      | .mappingStruct _ _ =>
          throwErrorAt stx s!"field '{f.name}' is a struct-valued mapping; use setStructMember"
      | .mappingStruct2 _ _ _ =>
          throwErrorAt stx s!"field '{f.name}' is a nested struct mapping; use setStructMember2"
      | .dynamicArray _ =>
          throwErrorAt stx s!"field '{f.name}' is a storage dynamic array; use pushStorageArray/popStorageArray/setStorageArrayElement"
      | .scalar _ => throwErrorAt stx s!"field '{f.name}' is not a mapping"
      | .mappingChain _ =>
          throwErrorAt stx s!"field '{f.name}' uses {storageTypeMappingDepth? f.ty |>.getD 0} mapping keys; use setMappingN"
  | `(term| setMapping2 $field:ident $key1:term $key2:term $value:term) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .mapping2AddressToAddressToUint256 =>
          `(Compiler.CompilationModel.Stmt.setMapping2
              $(strTerm f.name)
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals key1)
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals key2)
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals value))
      | .mappingStruct2 _ _ _ =>
          throwErrorAt stx s!"field '{f.name}' is a nested struct mapping; use setStructMember2"
      | .mappingStruct _ _ =>
          throwErrorAt stx s!"field '{f.name}' is a struct-valued mapping; use setStructMember"
      | _ => throwErrorAt stx s!"field '{f.name}' is not a double mapping"
  | `(term| setMappingN $field:ident $keys:term $value:term) => do
      let f ← lookupStorageField fields (toString field.getId)
      let keyTerms ← expectMappingKeyTerms keys
      match storageTypeMappingKeyTypes? f.ty with
      | some keyTypes =>
          if keyTerms.size != keyTypes.length then
            throwErrorAt stx s!"field '{f.name}' expects {keyTypes.length} mapping keys, but setMappingN received {keyTerms.size}"
          let keyExprs ← keyTerms.mapM (translatePureExprWithTypes fields constDecls immutableDecls params locals)
          `(Compiler.CompilationModel.Stmt.setMappingChain
              $(strTerm f.name)
              [ $[$keyExprs],* ]
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals value))
      | none =>
          match f.ty with
          | .mappingStruct _ _ | .mappingStruct2 _ _ _ =>
              throwErrorAt stx s!"field '{f.name}' is a struct-valued mapping; use setStructMember/setStructMember2"
          | _ => throwErrorAt stx s!"field '{f.name}' is not a mapping"
  | `(term| pushStorageArray $field:ident $value:term) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .dynamicArray _ =>
          `(Compiler.CompilationModel.Stmt.storageArrayPush
              $(strTerm f.name)
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals value))
      | _ => throwErrorAt stx s!"field '{f.name}' is not a storage dynamic array"
  | `(term| popStorageArray $field:ident) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .dynamicArray _ =>
          `(Compiler.CompilationModel.Stmt.storageArrayPop $(strTerm f.name))
      | _ => throwErrorAt stx s!"field '{f.name}' is not a storage dynamic array"
  | `(term| setStorageArrayElement $field:ident $index:term $value:term) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .dynamicArray _ =>
          `(Compiler.CompilationModel.Stmt.setStorageArrayElement
              $(strTerm f.name)
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals index)
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals value))
      | _ => throwErrorAt stx s!"field '{f.name}' is not a storage dynamic array"
  | `(term| require $cond $msg) =>
      `(Compiler.CompilationModel.Stmt.require
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals cond)
          $(strTerm (← expectStringLiteral msg)))
  | `(term| setMemoryArrayElement $name:term $index:term $value:term) => do
      let (arrayName, elemTy) ← requireSupportedMemoryArrayLocal name "setMemoryArrayElement" locals
      unless isSingleWordStaticValueType elemTy do
        throwErrorAt name s!"setMemoryArrayElement currently supports only Array<wordLike> memory locals, got Array {renderValueType elemTy}"
      let indexExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals index
      let valueExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals value
      let dataOffsetExpr : Term ←
        `(Compiler.CompilationModel.Expr.localVar $(strTerm (memoryArrayDataOffsetName arrayName)))
      let elementOffsetExpr : Term ←
        `(Compiler.CompilationModel.Expr.add
            $dataOffsetExpr
            (Compiler.CompilationModel.Expr.mul $indexExpr (Compiler.CompilationModel.Expr.literal 32)))
      `(Compiler.CompilationModel.Stmt.unsafeBlock
          "write memory-backed uint256 array element"
          [Compiler.CompilationModel.Stmt.mstore $elementOffsetExpr $valueExpr])
  | `(term| mstore $offset:term $value:term) | `(term| memoryStore($offset, $value)) =>
      `(Compiler.CompilationModel.Stmt.mstore
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals offset)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals value))
  | `(term| tstore $offset:term $value:term) =>
      `(Compiler.CompilationModel.Stmt.tstore
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals offset)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals value))
  | `(term| calldatacopy $destOffset:term $sourceOffset:term $size:term) =>
      `(Compiler.CompilationModel.Stmt.calldatacopy
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals destOffset)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals sourceOffset)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals size))
  | `(term| returndataCopy $destOffset:term $sourceOffset:term $size:term)
    | `(term| returnDataCopy($destOffset, $sourceOffset, $size)) =>
      `(Compiler.CompilationModel.Stmt.returndataCopy
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals destOffset)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals sourceOffset)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals size))
  | `(term| revertReturndata) =>
      `(Compiler.CompilationModel.Stmt.revertReturndata)
  | `(term| returnValues $values:term) =>
      let valueExprs ← expectExprList fields constDecls immutableDecls params locals values
      `(Compiler.CompilationModel.Stmt.returnValues [ $[$valueExprs],* ])
  | `(term| returnArray $name:term) =>
      `(Compiler.CompilationModel.Stmt.returnArray $(strTerm (← expectStringOrIdent name)))
  | `(term| returnBytes $name:term) =>
      `(Compiler.CompilationModel.Stmt.returnBytes $(strTerm (← expectStringOrIdent name)))
  | `(term| returnStorageWords $name:term) =>
      `(Compiler.CompilationModel.Stmt.returnStorageWords $(strTerm (← expectStringOrIdent name)))
  | `(term| returnCodeData $pointer:term) =>
      `(Compiler.CompilationModel.Stmt.returnCodeData
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals pointer))
  | `(term| emit $eventName:term $args:term) =>
      let evName := ← expectStringOrIdent eventName
      let argExprs ← expectEmitExprList fields constDecls immutableDecls params locals args
      `(Compiler.CompilationModel.Stmt.emit $(strTerm evName) [ $[$argExprs],* ])
  | `(term| rawLog $topics:term $dataOffset:term $dataSize:term) =>
      let topicExprs ← expectExprList fields constDecls immutableDecls params locals topics
      `(Compiler.CompilationModel.Stmt.rawLog
          [ $[$topicExprs],* ]
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals dataOffset)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals dataSize))
  | `(term| externalCallBind $names:term $fnName:term $args:term) =>
      let resultNames := ← expectStringList names
      let resultNameTerms := resultNames.map strTerm
      let targetFn := ← expectStringOrIdent fnName
      let argExprs ←
        match stripParens args with
        | `(term| [ $[$xs],* ]) =>
            translateLinkedExternalCallArgs fields constDecls immutableDecls params locals xs
        | _ => throwErrorAt args "expected list literal [..]"
      `(Compiler.CompilationModel.Stmt.externalCallBind
          [ $[$resultNameTerms],* ]
          $(strTerm targetFn)
          [ $[$argExprs],* ])
  | `(term| callExternal $name:ident ($[$args:term],*)) =>
      let extName := toString name.getId
      let ext ← match externalDecls.find? (fun ext => ext.name == extName) with
        | some ext => pure ext
        | none => throwErrorAt name s!"unknown linked external '{extName}'"
      unless ext.returnTys.isEmpty do
        throwErrorAt stx s!"callExternal '{extName}' returns values; bind it with `let ... ← ...`"
      validateLinkedExternalCallArgs fields constDecls immutableDecls externalDecls params locals
        extName ext.params args
      let argExprs ← translateLinkedExternalCallArgs fields constDecls immutableDecls params locals args (some ext.params)
      `(Compiler.CompilationModel.Stmt.externalCallBind [] $(strTerm extName) [ $[$argExprs],* ])
  | `(term| setStructMember $field:term $key:term $member:term $value:term) =>
      let fieldName := ← expectStringOrIdent field
      let memberName := ← expectStringOrIdent member
      let _ ← lookupStructMemberDecl fields fieldName memberName false
      `(Compiler.CompilationModel.Stmt.setStructMember
          $(strTerm fieldName)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals key)
          $(strTerm memberName)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals value))
  | `(term| setStructMember2 $field:term $key1:term $key2:term $member:term $value:term) =>
      let fieldName := ← expectStringOrIdent field
      let memberName := ← expectStringOrIdent member
      let _ ← lookupStructMemberDecl fields fieldName memberName true
      `(Compiler.CompilationModel.Stmt.setStructMember2
          $(strTerm fieldName)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals key1)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals key2)
          $(strTerm memberName)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals value))
  | _ =>
      -- void typed interface call in statement position lowers to the
      -- no-return ECM (selector + args call, failure-returndata bubbled, but
      -- no returndatasize check and no return decode).
      match ← resolveTypedInterfaceCall? fields constDecls immutableDecls externalDecls params locals stx with
      | some (ext, target, argTerms, none, selector) =>
          let targetExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals target
          let argExprs ← argTerms.mapM
            (translatePureExprWithTypes fields constDecls immutableDecls params locals)
          let isStaticTerm ← if ext.isView then `(true) else `(false)
          `(Compiler.CompilationModel.Stmt.ecm
              (Compiler.Modules.Calls.noReturnModule
                $(natTerm selector)
                $(natTerm argExprs.size)
                $isStaticTerm)
              [ $targetExpr, $[$argExprs],* ])
      | some (_, _, _, some retTy, _) =>
          throwErrorAt stx
            s!"interface call returns {renderValueType retTy}; bind it with `let ... ← ...`"
      | none =>
      match ← resolveLocalFunctionApp? fields constDecls immutableDecls externalDecls functions params locals stx with
      | some (fn, argTerms) =>
          ensureCallableAsInternalHelper stx fn
          if fn.returnTy != .unit then
            throwErrorAt stx
              s!"helper call '{fn.name}' returns {renderValueType fn.returnTy}; use `let ... ← {fn.name} ...` or tuple destructuring"
          let argExprs ← translateInternalHelperCallArgs
            fields constDecls immutableDecls params locals fn argTerms
          `(Compiler.CompilationModel.Stmt.internalCall
              $(strTerm (internalHelperSpecNameFor fn))
              [ $[$argExprs],* ])
      | none =>
          throwErrorAt stx "unsupported statement in do block"

mutual
private partial def translateDoElems
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (externalDecls : Array ExternalDecl)
    (errorDecls : Array ErrorDecl)
    (functions : Array FunctionDecl)
    (returnTy : ValueType)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (mutableLocals : Array String)
    (elems : Array (TSyntax `doElem)) : CommandElabM (Array Term × Array TypedLocal × Array String) := do
  let mut branchLocals := locals
  let mut branchMutableLocals := mutableLocals
  let mut stmts : Array Term := #[]
  for elem in elems do
    let (newStmts, newLocals, newMutableLocals) ←
      translateDoElem fields constDecls immutableDecls externalDecls errorDecls functions returnTy params branchLocals branchMutableLocals elem
    stmts := stmts ++ newStmts
    branchLocals := newLocals
    branchMutableLocals := newMutableLocals
  pure (stmts, branchLocals, branchMutableLocals)

private partial def translateDoSeqToStmtTerms
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (externalDecls : Array ExternalDecl)
    (errorDecls : Array ErrorDecl)
    (functions : Array FunctionDecl)
    (returnTy : ValueType)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (mutableLocals : Array String)
    (doSeq : DoSeq) : CommandElabM (Array Term) := do
  match doSeq with
  | `(doSeq| $[$elems:doElem]*) =>
      pure (← (translateDoElems fields constDecls immutableDecls externalDecls errorDecls functions returnTy params locals mutableLocals elems)).1
  | _ => throwErrorAt doSeq "unsupported branch body; expected do-sequence"

private partial def translateDoElem
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (externalDecls : Array ExternalDecl)
    (errorDecls : Array ErrorDecl)
    (functions : Array FunctionDecl)
    (returnTy : ValueType)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (mutableLocals : Array String)
    (elem : TSyntax `doElem) : CommandElabM (Array Term × Array TypedLocal × Array String) := do
  let localNames := typedLocalNames locals
  let tupleCase? ← do
    let stx := elem.raw
    if stx.getKind == `Lean.Parser.Term.doLet then
      let decl := stx[3]
      let patDecl := decl[0]
      match tupleBinderNames? patDecl[0] with
      | some names =>
          ensureFreshLocalNames localNames names stx
          let rhs : Term := ⟨patDecl[4]⟩
          let rhs := stripParens rhs
          match rhs with
          | `(term| $id:ident) =>
              match (← tupleParamElemExprs? params (toString id.getId)) with
              | some valueExprs =>
                  if names.size != valueExprs.size then
                    throwErrorAt patDecl s!"tuple destructuring binds {names.size} names, but the source provides {valueExprs.size} values"
                  let boundPairs := (names.zip valueExprs).filterMap fun (name?, valueExpr) =>
                    name?.map (fun name => (name, valueExpr))
                  let stmts ← boundPairs.mapM fun (name, valueExpr) =>
                    `(Compiler.CompilationModel.Stmt.letVar $(strTerm name) $valueExpr)
                  let valueTys ← inferTupleSourceTypes? fields constDecls immutableDecls externalDecls functions params locals rhs
                  match valueTys with
                  | some tys =>
                      let typedPairs := (names.zip tys).filterMap fun (name?, ty) => name?.map (fun name => mkTypedLocal name ty)
                      pure (some (stmts, locals ++ typedPairs, mutableLocals))
                  | none => throwErrorAt rhs "unable to infer tuple local types"
              | none =>
                  match (← tupleInternalCallAssignStmt? fields constDecls immutableDecls externalDecls functions params locals rhs names) with
                  | some stmt =>
                      let valueTys ← inferTupleSourceTypes? fields constDecls immutableDecls externalDecls functions params locals rhs
                      match valueTys with
                      | some tys =>
                          let typedPairs := (names.zip tys).filterMap fun (name?, ty) => name?.map (fun name => mkTypedLocal name ty)
                          pure (some (#[(stmt)], locals ++ typedPairs, mutableLocals))
                      | none =>
                          match ← resolveQualifiedFunctionApp? fields constDecls immutableDecls externalDecls params locals rhs with
                          | some (qualifiedName, _) =>
                              let typedPairs ← unsafe qualifiedTupleBindTypedLocals patDecl qualifiedName names
                              pure (some (#[(stmt)], locals ++ typedPairs, mutableLocals))
                          | none => throwErrorAt rhs "unable to infer tuple local types"
                  | none =>
                      match (← tryExternalCallBindStmt? fields constDecls immutableDecls externalDecls params locals rhs names) with
                      | some (stmt, typedPairs) =>
                          pure (some (#[(stmt)], locals ++ typedPairs, mutableLocals))
                      | none => throwErrorAt rhs "tuple destructuring currently requires a tuple literal, tuple-typed parameter, structMembers/structMembers2 source, internal helper call, or tryExternalCall"
          | _ =>
              match (← arrayElementTupleDestructureStmts? fields constDecls immutableDecls params locals mutableLocals rhs names) with
              | some (stmts, syntheticLocal) =>
                  let valueTys ← inferTupleSourceTypes? fields constDecls immutableDecls externalDecls functions params locals rhs
                  match valueTys with
                  | some tys =>
                      let typedPairs := (names.zip tys).filterMap fun (name?, ty) => name?.map (fun name => mkTypedLocal name ty)
                      pure (some (stmts, locals.push syntheticLocal ++ typedPairs, mutableLocals))
                  | none => throwErrorAt rhs "unable to infer tuple local types"
              | none =>
                  match (← tupleLiteralOrStructValueExprs? fields constDecls immutableDecls params locals rhs) with
                  | some valueExprs =>
                      if names.size != valueExprs.size then
                        throwErrorAt patDecl s!"tuple destructuring binds {names.size} names, but the source provides {valueExprs.size} values"
                      let boundPairs := (names.zip valueExprs).filterMap fun (name?, valueExpr) =>
                        name?.map (fun name => (name, valueExpr))
                      let stmts ← boundPairs.mapM fun (name, valueExpr) =>
                        `(Compiler.CompilationModel.Stmt.letVar $(strTerm name) $valueExpr)
                      let valueTys ← inferTupleSourceTypes? fields constDecls immutableDecls externalDecls functions params locals rhs
                      match valueTys with
                      | some tys =>
                          let typedPairs := (names.zip tys).filterMap fun (name?, ty) => name?.map (fun name => mkTypedLocal name ty)
                          pure (some (stmts, locals ++ typedPairs, mutableLocals))
                      | none => throwErrorAt rhs "unable to infer tuple local types"
                  | none =>
                      match (← tupleInternalCallAssignStmt? fields constDecls immutableDecls externalDecls functions params locals rhs names) with
                      | some stmt =>
                          let valueTys ← inferTupleSourceTypes? fields constDecls immutableDecls externalDecls functions params locals rhs
                          match valueTys with
                          | some tys =>
                              let typedPairs := (names.zip tys).filterMap fun (name?, ty) => name?.map (fun name => mkTypedLocal name ty)
                              pure (some (#[(stmt)], locals ++ typedPairs, mutableLocals))
                          | none =>
                              match ← resolveQualifiedFunctionApp? fields constDecls immutableDecls externalDecls params locals rhs with
                              | some (qualifiedName, _) =>
                                  let typedPairs ← unsafe qualifiedTupleBindTypedLocals patDecl qualifiedName names
                                  pure (some (#[(stmt)], locals ++ typedPairs, mutableLocals))
                              | none => throwErrorAt rhs "unable to infer tuple local types"
                      | none =>
                          match (← tryExternalCallBindStmt? fields constDecls immutableDecls externalDecls params locals rhs names) with
                          | some (stmt, typedPairs) =>
                              pure (some (#[(stmt)], locals ++ typedPairs, mutableLocals))
                          | none =>
                              let valueExprs ← tupleValueExprs fields constDecls immutableDecls params locals rhs
                              if names.size != valueExprs.size then
                                throwErrorAt patDecl s!"tuple destructuring binds {names.size} names, but the source provides {valueExprs.size} values"
                              let boundPairs := (names.zip valueExprs).filterMap fun (name?, valueExpr) =>
                                name?.map (fun name => (name, valueExpr))
                              let stmts ← boundPairs.mapM fun (name, valueExpr) =>
                                `(Compiler.CompilationModel.Stmt.letVar $(strTerm name) $valueExpr)
                              let valueTys ← inferTupleSourceTypes? fields constDecls immutableDecls externalDecls functions params locals rhs
                              match valueTys with
                              | some tys =>
                                  let typedPairs := (names.zip tys).filterMap fun (name?, ty) => name?.map (fun name => mkTypedLocal name ty)
                                  pure (some (stmts, locals ++ typedPairs, mutableLocals))
                              | none => throwErrorAt rhs "unable to infer tuple local types"
      | none => pure none
    else if stx.getKind == `Lean.Parser.Term.doLetArrow then
      let patDecl := stx[3]
      match tupleBinderNames? patDecl[0] with
      | some names =>
          ensureFreshLocalNames localNames names stx
          let rhs : Term := ⟨patDecl[3][0]⟩
          match (← tupleInternalCallAssignStmt? fields constDecls immutableDecls externalDecls functions params locals rhs names) with
          | some stmt =>
              let valueTys ← inferTupleSourceTypes? fields constDecls immutableDecls externalDecls functions params locals rhs
              match valueTys with
              | some tys =>
                  let typedPairs := (names.zip tys).filterMap fun (name?, ty) => name?.map (fun name => mkTypedLocal name ty)
                  pure (some (#[(stmt)], locals ++ typedPairs, mutableLocals))
              | none =>
                  match ← resolveQualifiedFunctionApp? fields constDecls immutableDecls externalDecls params locals rhs with
                  | some (qualifiedName, _) =>
                      let typedPairs ← unsafe qualifiedTupleBindTypedLocals patDecl qualifiedName names
                      pure (some (#[(stmt)], locals ++ typedPairs, mutableLocals))
                  | none => throwErrorAt rhs "unable to infer tuple local types"
          | none =>
              match (← tryExternalCallBindStmt? fields constDecls immutableDecls externalDecls params locals rhs names) with
              | some (stmt, typedPairs) =>
                  pure (some (#[(stmt)], locals ++ typedPairs, mutableLocals))
              | none => throwErrorAt rhs "tuple bind sources must be internal helper calls or tryExternalCall"
      | none => pure none
    else
      pure none
  match tupleCase? with
  | some result => pure result
  | none => match elem with
      | `(doElem| let _ := ($rhs:term : $_ty:term)) =>
          translateDoElem fields constDecls immutableDecls externalDecls errorDecls functions returnTy params locals mutableLocals
            (← `(doElem| let _ := $rhs:term))
      | `(doElem| let _ := $rhs:term) =>
          let discardName := freshSyntheticLocalName "discard" params locals mutableLocals
          let discardIdent := mkIdent (Name.mkSimple discardName)
          translateDoElem fields constDecls immutableDecls externalDecls errorDecls functions returnTy params locals mutableLocals
            (← `(doElem| let $discardIdent:ident := $rhs:term))
      | `(doElem| let _ ← $rhs:term) =>
          let discardName := freshSyntheticLocalName "__discard" params locals mutableLocals
          let discardIdent := mkIdent (Name.mkSimple discardName)
          translateDoElem fields constDecls immutableDecls externalDecls errorDecls functions returnTy params locals mutableLocals
            (← `(doElem| let $discardIdent:ident ← $rhs:term))
      | `(doElem| let mut $name:ident := $rhs:term) =>
          let varName := toString name.getId
          if localNames.contains varName then
            throwErrorAt name s!"duplicate local variable '{varName}'"
          let rhsExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals rhs
          let ty ← inferPureExprType fields constDecls immutableDecls externalDecls params locals rhs
          let interfaceName? ← interfaceNameOfTerm? params locals rhs
          pure
            (#[(← `(Compiler.CompilationModel.Stmt.letVar $(strTerm varName) $rhsExpr))],
              locals.push (mkTypedLocal varName ty interfaceName?),
              mutableLocals.push varName)
      | `(doElem| let $name:ident := $rhs:term) =>
          let varName := toString name.getId
          if localNames.contains varName then
            throwErrorAt name s!"duplicate local variable '{varName}'"
          match arrayElementAliasSource? params rhs with
          | some (paramName, index, elemTy) =>
              requireWordLikeType index "arrayElement alias index"
                (← inferPureExprType fields constDecls immutableDecls externalDecls params locals index)
              pure
                (#[],
                  locals.push
                    { name := varName
                      ty := elemTy
                      source := .arrayElement paramName index elemTy },
                  mutableLocals)
          | none =>
              let rhsExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals rhs
              let ty ← inferPureExprType fields constDecls immutableDecls externalDecls params locals rhs
              let interfaceName? ← interfaceNameOfTerm? params locals rhs
              pure
                (#[(← `(Compiler.CompilationModel.Stmt.letVar $(strTerm varName) $rhsExpr))],
                  locals.push (mkTypedLocal varName ty interfaceName?),
                  mutableLocals)
      | `(doElem| let $name:ident ← $rhs:term) =>
          let varName := toString name.getId
          if localNames.contains varName then
            throwErrorAt name s!"duplicate local variable '{varName}'"
          match stripParens rhs with
          | `(term| callExternal $externalName:ident ($[$args:term],*)) =>
              let extName := toString externalName.getId
              let ext ← match externalDecls.find? (fun ext => ext.name == extName) with
                | some ext => pure ext
                | none => throwErrorAt externalName s!"unknown linked external '{extName}'"
              match ext.returnTys.toList with
              | [retTy] =>
                  validateLinkedExternalCallArgs fields constDecls immutableDecls externalDecls params locals
                    extName ext.params args
                  let argExprs ← translateLinkedExternalCallArgs fields constDecls immutableDecls params locals args (some ext.params)
                  let flatNames ← flattenExternalResultNames varName retTy
                  if flatNames.length != 1 then
                    throwErrorAt rhs s!"callExternal '{extName}' return type expands to {flatNames.length} values and cannot be bound to one source variable"
                  let resultTerms := flatNames.toArray.map strTerm
                  pure
                    (#[(← `(Compiler.CompilationModel.Stmt.externalCallBind
                        [ $[$resultTerms],* ] $(strTerm extName) [ $[$argExprs],* ]))],
                      locals.push { name := varName, ty := retTy, source := LocalSource.value },
                      mutableLocals)
              | [] => throwErrorAt rhs s!"callExternal '{extName}' returns Unit; invoke it as a statement"
              | _ => throwErrorAt rhs s!"callExternal '{extName}' returns multiple values; use externalCallBind with explicit result names"
          | `(term| callResult $_extName:term $_args:term) =>
              match (← callResultBindStmt? fields constDecls immutableDecls externalDecls params locals rhs varName) with
              | some (stmt, resultLocal) => pure (#[stmt], locals.push resultLocal, mutableLocals)
              | none => throwErrorAt rhs "invalid callResult bind"
          | `(term| ecmCall $moduleFactory:term $args:term) =>
              let argExprs ← expectEcmExprList fields constDecls immutableDecls params locals args
              let moduleTerm ← `(term| (($moduleFactory) $(strTerm varName)))
              validateSingleResultEcmModuleTerm moduleTerm varName
              pure
                (#[(← `(Compiler.CompilationModel.Stmt.ecm
                        $moduleTerm
                        [ $[$argExprs],* ]))],
                  locals.push (mkTypedLocal varName .uint256),
                  mutableLocals)
          | `(term| ecrecover $hash:term $v:term $r:term $s:term) =>
              let hashExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals hash
              let vExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals v
              let rExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals r
              let sExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals s
              pure
                (#[(← `(Compiler.CompilationModel.Stmt.ecm
                        (Compiler.Modules.Precompiles.ecrecoverModule $(strTerm varName))
                        [$hashExpr, $vExpr, $rExpr, $sExpr]))],
                  locals.push (mkTypedLocal varName .address),
                  mutableLocals)
          | `(term| tryExternalCall $extName:term $args:term) =>
              -- Zero-return tryExternalCall: `let success ← tryExternalCall "fn" [args]`
              -- produces Stmt.tryExternalCallBind successVar [] externalName args
              let targetFn := ← expectStringOrIdent extName
              let argExprs ← expectExprList fields constDecls immutableDecls params locals args
              pure
                (#[(← `(Compiler.CompilationModel.Stmt.tryExternalCallBind
                        $(strTerm varName)
                        []
                        $(strTerm targetFn)
                        [ $[$argExprs],* ]))],
                  locals.push (mkTypedLocal varName .bool),
                  mutableLocals)
          | `(term| allocArray $len:term) =>
              requireWordLikeType len "allocArray length"
                (← inferPureExprType fields constDecls immutableDecls externalDecls params locals len)
              let lenExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals len
              let lengthName := memoryArrayLengthName varName
              let dataOffsetName := memoryArrayDataOffsetName varName
              let lengthLocal : Term ← `(Compiler.CompilationModel.Expr.localVar $(strTerm lengthName))
              let dataOffsetLocal : Term ← `(Compiler.CompilationModel.Expr.localVar $(strTerm dataOffsetName))
              let dataOffsetExpr : Term ←
                `(Compiler.CompilationModel.Expr.add
                    (Compiler.CompilationModel.Expr.mload (Compiler.CompilationModel.Expr.literal 64))
                    (Compiler.CompilationModel.Expr.literal 32))
              let arrayHeadExpr : Term ←
                `(Compiler.CompilationModel.Expr.sub $dataOffsetLocal (Compiler.CompilationModel.Expr.literal 32))
              let freePtrExpr : Term ←
                `(Compiler.CompilationModel.Expr.add
                    $dataOffsetLocal
                    (Compiler.CompilationModel.Expr.mul $lengthLocal (Compiler.CompilationModel.Expr.literal 32)))
              pure
                (#[
                    (← `(Compiler.CompilationModel.Stmt.letVar $(strTerm lengthName) $lenExpr)),
                    (← `(Compiler.CompilationModel.Stmt.letVar $(strTerm dataOffsetName) $dataOffsetExpr)),
                    (← `(Compiler.CompilationModel.Stmt.unsafeBlock
                          "allocate memory-backed uint256 array"
                          [Compiler.CompilationModel.Stmt.mstore $arrayHeadExpr $lengthLocal,
                           Compiler.CompilationModel.Stmt.mstore
                            (Compiler.CompilationModel.Expr.literal 64)
                            $freePtrExpr]))
                  ],
                  locals.push
                    { name := varName
                      ty := .array .uint256
                      source := .memoryArray },
                  mutableLocals)
          | _ =>
              match ← localInternalArrayReturnBind? fields constDecls immutableDecls externalDecls functions params locals rhs with
              | some (fn, argTerms, elemTy) =>
                  let argExprs ← translateInternalHelperCallArgs
                    fields constDecls immutableDecls params locals fn argTerms
                  let resultNameTerms := #[
                    strTerm (memoryArrayDataOffsetName varName),
                    strTerm (memoryArrayLengthName varName)
                  ]
                  pure
                    (#[(← `(Compiler.CompilationModel.Stmt.internalCallAssign
                            [ $[$resultNameTerms],* ]
                            $(strTerm (internalHelperSpecNameFor fn))
                            [ $[$argExprs],* ]))],
                      locals.push
                        { name := varName
                          ty := .array elemTy
                          source := .memoryArray },
                      mutableLocals)
              | none =>
                  let safeBind? ← translateSafeRequireBind fields constDecls immutableDecls params locals varName rhs
                  match safeBind? with
                  | some safeStmts =>
                      let safeTy ← inferBindSourceType
                        fields constDecls immutableDecls externalDecls functions params locals rhs
                      pure (safeStmts, locals.push (mkTypedLocal varName safeTy), mutableLocals)
                  | none =>
                      match (← translateERC20BindStmt? fields constDecls immutableDecls functions params locals varName rhs) with
                      | some stmt =>
                          pure (#[(stmt)], locals.push (mkTypedLocal varName .uint256), mutableLocals)
                      | none =>
                          match ← resolveTypedInterfaceCall? fields constDecls immutableDecls externalDecls params locals rhs with
                          | some (ext, target, argTerms, some retTy, selector) =>
                              let targetExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals target
                              let argExprs ← argTerms.mapM
                                (translatePureExprWithTypes fields constDecls immutableDecls params locals)
                              let stmt ←
                                if ext.isView then
                                  match staticAbiWordCount? retTy with
                                  | some 1 =>
                                      `(Compiler.CompilationModel.Stmt.ecm
                                          (Compiler.Modules.Oracle.typedReadWordSummaryModule
                                            $(strTerm varName)
                                            $(strTerm ext.name)
                                            $(natTerm selector)
                                            $(natTerm argExprs.size))
                                          [ $targetExpr, $[$argExprs],* ])
                                  | some n =>
                                      throwErrorAt rhs
                                        s!"typed interface view call '{ext.name}' can use the oracle summary only for one static ABI word; return has {n} static ABI words ({renderValueType retTy}). ABI-frame typed-interface view returns are not implemented yet (#1982)."
                                  | none =>
                                      throwErrorAt rhs
                                        s!"typed interface view call '{ext.name}' can use the oracle summary only for one static ABI word; return has no static ABI word layout ({renderValueType retTy}). ABI-frame typed-interface view returns are not implemented yet (#1982)."
                                else
                                  `(Compiler.CompilationModel.Stmt.ecm
                                      (Compiler.Modules.Calls.withReturnModule
                                        $(strTerm varName)
                                        $(natTerm selector)
                                        $(natTerm argExprs.size)
                                        false)
                                      [ $targetExpr, $[$argExprs],* ])
                              let normalization? ←
                                match retTy with
                                | .uintN bits => do
                                    let normalization ← `(Compiler.CompilationModel.Stmt.assignVar $(strTerm varName)
                                      (Compiler.CompilationModel.Expr.bitAnd
                                        (Compiler.CompilationModel.Expr.localVar $(strTerm varName))
                                        (Compiler.CompilationModel.Expr.literal $(natTerm (2 ^ bits - 1)))))
                                    pure (some normalization)
                                | .intN bits => do
                                    let normalization ← `(Compiler.CompilationModel.Stmt.assignVar $(strTerm varName)
                                      (Compiler.CompilationModel.Expr.signextend
                                        (Compiler.CompilationModel.Expr.literal $(natTerm (bits / 8 - 1)))
                                        (Compiler.CompilationModel.Expr.localVar $(strTerm varName))))
                                    pure (some normalization)
                                | .bytesN bytes => do
                                    let normalization ← `(Compiler.CompilationModel.Stmt.assignVar $(strTerm varName)
                                      (Compiler.CompilationModel.Expr.bitAnd
                                        (Compiler.CompilationModel.Expr.localVar $(strTerm varName))
                                        (Compiler.CompilationModel.Expr.literal
                                          $(natTerm ((2 ^ (8 * bytes) - 1) * 2 ^ (8 * (32 - bytes)))))))
                                    pure (some normalization)
                                | _ => pure none
                              let stmts := match normalization? with | some normalization => #[stmt, normalization] | none => #[stmt]
                              pure
                                (stmts,
                                  locals.push (mkTypedLocal varName retTy),
                                  mutableLocals)
                          | some (_, _, _, none, _) =>
                              -- void interface method bound with `let ... ←`: not allowed
                              throwErrorAt rhs s!"interface call '{varName}' binds a void method; call it as a statement, not `let ... ←`"
                          | none =>
                              let rhsExpr ← translateBindSource fields constDecls immutableDecls externalDecls functions params locals rhs
                              let ty ← inferBindSourceType fields constDecls immutableDecls externalDecls functions params locals rhs
                              pure
                                (#[(← `(Compiler.CompilationModel.Stmt.letVar $(strTerm varName) $rhsExpr))],
                                  locals.push (mkTypedLocal varName ty),
                                  mutableLocals)
      | `(doElem| $name:ident := $rhs:term) =>
          let varName := toString name.getId
          if !localNames.contains varName then
            throwErrorAt name s!"cannot assign unknown variable '{varName}'"
          if !mutableLocals.contains varName then
            throwErrorAt name s!"cannot assign immutable variable '{varName}'; declare it with 'let mut'"
          let some localInfo := locals.find? (fun entry => entry.name == varName)
            | throwErrorAt name s!"cannot resolve type of mutable variable '{varName}'"
          let rawRhsExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals rhs
          let rhsExpr ← normalizeTranslatedExprForType localInfo.ty rhs rawRhsExpr
          pure
            (#[(← `(Compiler.CompilationModel.Stmt.assignVar $(strTerm varName) $rhsExpr))],
              locals,
              mutableLocals)
      | `(doElem| return $value:term) =>
          match (← arrayElementTupleReturnStmts? fields constDecls immutableDecls params locals mutableLocals value) with
          | some (stmts, syntheticLocal) =>
              pure (stmts, locals.push syntheticLocal, mutableLocals)
          | none =>
              match (← tupleReturnValueExprs? fields constDecls immutableDecls params locals value) with
              | some valueExprs =>
                  pure (#[(← `(Compiler.CompilationModel.Stmt.returnValues [ $[$valueExprs],* ]))], locals, mutableLocals)
              | none =>
                  let valueExpr ←
                    match returnTy with
                    | .bytesN bytes =>
                        match stripParens value with
                        | `(term| $n:num) =>
                            let literal ← natFromSyntax n
                            let normalized := (literal % 2 ^ (8 * bytes)) * 2 ^ (8 * (32 - bytes))
                            `(Compiler.CompilationModel.Expr.literal $(natTerm normalized))
                        | _ =>
                            translatePureExprWithTypes fields constDecls immutableDecls params locals value
                    | _ =>
                        translatePureExprWithTypes fields constDecls immutableDecls params locals value
                  pure (#[(← `(Compiler.CompilationModel.Stmt.return $valueExpr))], locals, mutableLocals)
      | `(doElem| pure ()) =>
          pure (#[], locals, mutableLocals)
      | `(doElem| if $cond:term then $thenBranch:doSeq else $elseBranch:doSeq) =>
          let condExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals cond
          let thenStmts ← translateDoSeqToStmtTerms fields constDecls immutableDecls externalDecls errorDecls functions returnTy params locals mutableLocals thenBranch
          let elseStmts ← translateDoSeqToStmtTerms fields constDecls immutableDecls externalDecls errorDecls functions returnTy params locals mutableLocals elseBranch
          pure
            (#[(← `(Compiler.CompilationModel.Stmt.ite
              $condExpr
              [ $[$thenStmts],* ]
              [ $[$elseStmts],* ]))],
              locals,
              mutableLocals)
      | `(doElem| tryCatch $attempt:term $handler:term) => do
          let trySuccessName :=
            freshSyntheticLocalName "verity_try_success" params locals mutableLocals
          let (payloadName?, catchElems) ← parseTryCatchHandler handler
          validateTryCatchHandlerDoesNotUsePayload handler payloadName? catchElems
          let attemptExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals attempt
          let catchTranslation ←
            translateDoElems fields constDecls immutableDecls externalDecls errorDecls functions returnTy params locals mutableLocals catchElems
          let catchStmts := catchTranslation.1
          pure
            (#[
              (← `(Compiler.CompilationModel.Stmt.letVar $(strTerm trySuccessName) $attemptExpr)),
              (← `(Compiler.CompilationModel.Stmt.ite
                    (Compiler.CompilationModel.Expr.eq
                      (Compiler.CompilationModel.Expr.localVar $(strTerm trySuccessName))
                      (Compiler.CompilationModel.Expr.literal 0))
                    [ $[$catchStmts],* ]
                    []))
            ],
            locals,
            mutableLocals)
      | `(doElem| forEach $name:term $count:term $body:term) =>
          let loopVar := ← expectStringOrIdent name
          let countExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals count
          let bodyStmts ←
            match stripParens body with
            | `(term| do $[$inner:doElem]*) =>
                pure (← (translateDoElems fields constDecls immutableDecls externalDecls errorDecls functions returnTy params (locals.push (mkTypedLocal loopVar .uint256)) mutableLocals inner)).1
            | _ => throwErrorAt body "forEach body must be a do block"
          pure
            (#[(← `(Compiler.CompilationModel.Stmt.forEach
                $(strTerm loopVar)
                $countExpr
                [ $[$bodyStmts],* ]))],
              locals,
              mutableLocals)
      | `(doElem| forEachSetBit $name:term $bitmap:term $body:term) =>
          let loopVar := ← expectStringOrIdent name
          let bitmapExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals bitmap
          let bodyStmts ←
            match stripParens body with
            | `(term| do $[$inner:doElem]*) =>
                pure (← (translateDoElems fields constDecls immutableDecls externalDecls errorDecls functions returnTy params (locals.push (mkTypedLocal loopVar .uint256)) mutableLocals inner)).1
            | _ => throwErrorAt body "forEachSetBit body must be a do block"
          pure
            (#[(← `(Compiler.CompilationModel.Stmt.forEachSetBit
                $(strTerm loopVar)
                $bitmapExpr
                [ $[$bodyStmts],* ]))],
              locals,
              mutableLocals)
      | `(doElem| requireError $cond:term $errorName:ident($args,*)) =>
          let argExprs ← translateCustomErrorArgExprs fields constDecls immutableDecls params locals
            errorDecls (toString errorName.getId) args.getElems
          pure
            (#[(← `(Compiler.CompilationModel.Stmt.requireError
                    $(← translatePureExprWithTypes fields constDecls immutableDecls params locals cond)
                    $(strTerm (toString errorName.getId))
                    [ $[$argExprs],* ]))],
              locals,
              mutableLocals)
      | `(doElem| revert $errorName:ident($args,*)) =>
          let argExprs ← translateCustomErrorArgExprs fields constDecls immutableDecls params locals
            errorDecls (toString errorName.getId) args.getElems
          pure
            (#[(← `(Compiler.CompilationModel.Stmt.revertError
                    $(strTerm (toString errorName.getId))
                    [ $[$argExprs],* ]))],
              locals,
              mutableLocals)
      | `(doElem| revertError $errorName:ident($args,*)) =>
          let argExprs ← translateCustomErrorArgExprs fields constDecls immutableDecls params locals
            errorDecls (toString errorName.getId) args.getElems
          pure
            (#[(← `(Compiler.CompilationModel.Stmt.revertError
                    $(strTerm (toString errorName.getId))
                    [ $[$argExprs],* ]))],
              locals,
              mutableLocals)
      | `(doElem| panic($code:term)) =>
          pure
            (#[(← `(Compiler.CompilationModel.Stmt.panicCode
                    $(← translatePureExprWithTypes fields constDecls immutableDecls params locals code)))],
              locals,
              mutableLocals)
      | `(doElem| unsafe $reason:str do $body:doSeq) =>
          let bodyStmts ← translateDoSeqToStmtTerms fields constDecls immutableDecls externalDecls errorDecls functions returnTy params locals mutableLocals body
          let reasonStr := reason.getString
          pure
            (#[(← `(Compiler.CompilationModel.Stmt.unsafeBlock
                    $(Lean.Quote.quote reasonStr)
                    [ $[$bodyStmts],* ]))],
              locals,
              mutableLocals)
      | `(doElem| ecmBind $names:term $module:term $args:term) =>
          let resultVars ← expectStringList names
          ensureFreshLocalNames localNames (resultVars.map some) names
          validateResultEcmModuleTerm module resultVars
          let argExprs ← expectEcmExprList fields constDecls immutableDecls params locals args
          let typedLocals := resultVars.map (fun name => mkTypedLocal name .uint256)
          pure
            (#[(← `(Compiler.CompilationModel.Stmt.ecm
                    $module
                    [ $[$argExprs],* ]))],
              locals ++ typedLocals,
              mutableLocals)
      | `(doElem| emit $eventName:term $values:term) =>
          let evName := ← expectStringOrIdent eventName
          match stripParens values with
          | `(term| [ $[$args],* ]) =>
              let mut stmts : Array Term := #[]
              let mut branchLocals := locals
              let mut emitArgs : Array Term := #[]
              for arg in args do
                match ← localInternalArrayReturnBind? fields constDecls immutableDecls externalDecls functions params branchLocals arg with
                | some (fn, argTerms, elemTy) =>
                    let tempName := freshSyntheticLocalName "emit_array" params branchLocals mutableLocals
                    let argExprs ← translateInternalHelperCallArgs
                      fields constDecls immutableDecls params branchLocals fn argTerms
                    let resultNameTerms := #[
                      strTerm (memoryArrayDataOffsetName tempName),
                      strTerm (memoryArrayLengthName tempName)
                    ]
                    stmts := stmts.push (← `(Compiler.CompilationModel.Stmt.internalCallAssign
                      [ $[$resultNameTerms],* ]
                      $(strTerm (internalHelperSpecNameFor fn))
                      [ $[$argExprs],* ]))
                    branchLocals := branchLocals.push
                      { name := tempName
                        ty := .array elemTy
                        source := .memoryArray }
                    let tempTerm : Term := ⟨(mkIdent (Name.mkSimple tempName)).raw⟩
                    emitArgs := emitArgs.push (← translateEmitArgExpr fields constDecls immutableDecls params branchLocals tempTerm)
                | none =>
                    emitArgs := emitArgs.push (← translateEmitArgExpr fields constDecls immutableDecls params branchLocals arg)
              stmts := stmts.push (← `(Compiler.CompilationModel.Stmt.emit $(strTerm evName) [ $[$emitArgs],* ]))
              pure (stmts, locals, mutableLocals)
          | _ => throwErrorAt values "expected list literal [..]"
      | `(doElem| $stmt:term) =>
          pure (#[(← translateEffectStmt fields constDecls immutableDecls externalDecls functions params locals stmt)], locals, mutableLocals)
      | _ => throwErrorAt elem "unsupported do element"
end

private def translateBodyToStmtTerms
    (fields : Array StorageFieldDecl)
    (roleDecls : Array RoleDecl)
    (errorDecls : Array ErrorDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (externalDecls : Array ExternalDecl)
    (functions : Array FunctionDecl)
    (fn : FunctionDecl) : CommandElabM (Array Term) := do
  match fn.body with
  | `(term| do $[$elems:doElem]*) =>
      let guardPrelude ← initGuardPreludeStmtTerms fields fn
      let rolePrelude ← roleGuardPreludeStmtTerms fields roleDecls fn
      let modifierPrelude ← fn.modifiers.mapM fun modIdent =>
        `(Compiler.CompilationModel.Stmt.internalCall $(strTerm (modifierInternalName (toString modIdent.getId))) [])
      let stmts := guardPrelude ++ rolePrelude ++ modifierPrelude ++ (← translateDoElems fields constDecls immutableDecls externalDecls errorDecls functions fn.returnTy fn.params #[] #[] elems).1
      let mut stmts := stmts
      if fn.returnTy == .unit then
        stmts := stmts.push (← `(Compiler.CompilationModel.Stmt.stop))
      pure stmts
  | _ => throwErrorAt fn.body "function body must be a do block"

private def translateConstructorBodyToStmtTerms
    (fields : Array StorageFieldDecl)
    (errorDecls : Array ErrorDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (externalDecls : Array ExternalDecl)
    (functions : Array FunctionDecl)
    (ctor : ConstructorDecl) : CommandElabM (Array Term) := do
  match ctor.body with
  | `(term| do $[$elems:doElem]*) =>
      pure (← (translateDoElems fields constDecls immutableDecls externalDecls errorDecls functions .unit ctor.params #[] #[] elems)).1
  | _ => throwErrorAt ctor.body "constructor body must be a do block"

private def immutableInitStmtTerms
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (ctorParams : Array ParamDecl) : CommandElabM (Array Term) := do
  let mut out := #[]
  for imm in immutableDecls do
    let mkStore (valueExpr : Term) : CommandElabM Term := do
      match imm.ty with
      | .uint256 | .int256 | .uint8 | .uint16 | .bytes32 | .bool =>
          `(Compiler.CompilationModel.Stmt.setImmutable $(strTerm imm.name) $valueExpr)
      | .uintN bits =>
          `(Compiler.CompilationModel.Stmt.setImmutable $(strTerm imm.name)
              (Compiler.CompilationModel.Expr.bitAnd $valueExpr
                (Compiler.CompilationModel.Expr.literal $(natTerm (2 ^ bits - 1)))))
      | .intN bits =>
          `(Compiler.CompilationModel.Stmt.setImmutable $(strTerm imm.name)
              (Compiler.CompilationModel.Expr.signextend
                (Compiler.CompilationModel.Expr.literal $(natTerm (bits / 8 - 1))) $valueExpr))
      | .bytesN bytes =>
          let mask := (2 ^ (8 * bytes) - 1) * 2 ^ (8 * (32 - bytes))
          `(Compiler.CompilationModel.Stmt.setImmutable $(strTerm imm.name)
              (Compiler.CompilationModel.Expr.bitAnd $valueExpr
                (Compiler.CompilationModel.Expr.literal $(natTerm mask))))
      | .address =>
          `(Compiler.CompilationModel.Stmt.setImmutable $(strTerm imm.name) $valueExpr)
      | _ =>
          throwErrorAt imm.ident s!"immutable '{imm.name}' uses unsupported type"
    let checkedInit? ←
      translateSafeRequireBind fields constDecls #[] ctorParams #[]
        "__immutable_init_value" imm.body
    match checkedInit? with
    | some stmts =>
        match stmts.back? with
        | some stmt =>
            match stmt with
            | `(Compiler.CompilationModel.Stmt.letVar $_ $valueExpr) =>
                out := out ++ stmts.pop.push (← mkStore valueExpr)
            | _ =>
                throwErrorAt imm.ident
                  s!"immutable '{imm.name}' checked initializer lowered to an unexpected statement shape"
        | none =>
            throwErrorAt imm.ident
              s!"immutable '{imm.name}' checked initializer lowered to an unexpected statement shape"
    | none =>
        let valueExpr ← translatePureExpr fields constDecls #[] ctorParams #[] imm.body
        out := out.push (← mkStore valueExpr)
  pure out

def mkSuffixedIdent (base : Ident) (suffix : String) : CommandElabM Ident :=
  let rec appendSuffix : Name → Name
    | .anonymous => .str .anonymous suffix
    | .str p s => .str p (s ++ suffix)
    | .num p n => .str p (toString n ++ suffix)
  pure <| mkIdent <| appendSuffix base.getId

private def mkContractFnType (params : Array ParamDecl) (retTy : ValueType) : CommandElabM Term := do
  let mut ty ← `(Verity.Contract $(← contractValueTypeTerm retTy))
  for param in params.reverse do
    ty ← `(($(← contractValueTypeTerm param.ty)) → $ty)
  pure ty

private def mkTupleProjectionTerm (base : Term) (elemTys : List ValueType) (idx : Nat) : CommandElabM Term := do
  let rec go (tupleTerm : Term) (remaining : List ValueType) (targetIdx : Nat) : CommandElabM Term := do
    match remaining with
    | [] => throwError "tuple projection index out of bounds"
    | [_] =>
        if targetIdx == 0 then
          pure tupleTerm
        else
          throwError "tuple projection index out of bounds"
    | _ :: rest =>
        if targetIdx == 0 then
          `(Prod.fst $tupleTerm)
        else
          go (← `(Prod.snd $tupleTerm)) rest (targetIdx - 1)
  go base elemTys idx

private def injectTupleParamAliases (params : Array ParamDecl) (body : Term) : CommandElabM Term := do
  let mut wrappedBody := body
  for param in params.reverse do
    match param.ty with
    | .tuple elemTys =>
        let baseTerm : Term := mkIdent param.ident.getId
        for (_elemTy, idx) in (elemTys.toArray.zipIdx).reverse do
          let aliasName := mkIdent <| Name.str .anonymous s!"{param.name}_{idx}"
          let projection ← mkTupleProjectionTerm baseTerm elemTys idx
          wrappedBody ← `(term| let $aliasName := $projection; $wrappedBody)
    | _ => pure ()
  pure wrappedBody

private def typedInterfaceCallReturnType?
    (externalDecls : Array ExternalDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (stx : Term) : CommandElabM (Option ValueType) := do
  let some (target, methodName, _argTerms) := typedDotCallSyntax? stx
    | pure none
  let targetName ←
    match stripParens target with
    | `(term| $targetIdent:ident) => pure (toString targetIdent.getId)
    | _ => pure ""
  let some interfaceName := lookupInterfaceName? params locals targetName
    | pure none
  let externalName := interfaceExternalName interfaceName methodName
  let some ext := externalDecls.find? (fun ext => ext.name == externalName)
    | pure none
  match ext.returnTys.toList with
  | [retTy] => pure (some retTy)
  | _ => pure none

/-- True when `stx` is a typed interface call whose method is void (no returns
    clause). Used to drop statement-position void calls from the executable
    wrapper, where they have nothing to bind. -/
private def isVoidTypedInterfaceCall?
    (externalDecls : Array ExternalDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (stx : Term) : CommandElabM Bool := do
  let some (target, methodName, _argTerms) := typedDotCallSyntax? stx
    | pure false
  let targetName ←
    match stripParens target with
    | `(term| $targetIdent:ident) => pure (toString targetIdent.getId)
    | _ => pure ""
  let some interfaceName := lookupInterfaceName? params locals targetName
    | pure false
  let externalName := interfaceExternalName interfaceName methodName
  let some ext := externalDecls.find? (fun ext => ext.name == externalName)
    | pure false
  pure ext.returnTys.isEmpty

mutual
private partial def rewriteForEachExecutableDoSeq
    (externalDecls : Array ExternalDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (doSeq : DoSeq) : CommandElabM DoSeq := do
  match doSeq with
  | `(doSeq| $[$elems:doElem]*) =>
      let (elems, _) ← rewriteForEachExecutableDoElems externalDecls params locals elems
      `(doSeq| $[$elems:doElem]*)
  | _ => throwErrorAt doSeq "unsupported branch body; expected do-sequence"

private partial def rewriteForEachExecutableDoElems
    (externalDecls : Array ExternalDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (elems : Array (TSyntax `doElem)) : CommandElabM (Array (TSyntax `doElem) × Array TypedLocal) := do
  let mut rewritten : Array (TSyntax `doElem) := #[]
  let mut currentLocals := locals
  for elem in elems do
    let (newElems, newLocals) ← rewriteForEachExecutableDoElem externalDecls params currentLocals elem
    rewritten := rewritten ++ newElems
    currentLocals := newLocals
  pure (rewritten, currentLocals)

private partial def rewriteForEachExecutableDoElem
    (externalDecls : Array ExternalDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (elem : TSyntax `doElem) : CommandElabM (Array (TSyntax `doElem) × Array TypedLocal) := do
  match elem with
  | `(doElem| let _ := $rhs:term) =>
      let discardName := freshSyntheticLocalName "__discard" params locals #[]
      let discardIdent := mkIdent (Name.mkSimple discardName)
      rewriteForEachExecutableDoElem externalDecls params locals
        (← `(doElem| let $discardIdent:ident := $rhs:term))
  | `(doElem| let _ ← $rhs:term) =>
      let discardName := freshSyntheticLocalName "__discard" params locals #[]
      let discardIdent := mkIdent (Name.mkSimple discardName)
      rewriteForEachExecutableDoElem externalDecls params locals
        (← `(doElem| let $discardIdent:ident ← $rhs:term))
  | `(doElem| let $name:ident := $rhs:term) =>
      let varName := toString name.getId
      let interfaceName? ← interfaceNameOfTerm? params locals rhs
      let locals :=
        match interfaceName? with
        | some iface => locals.push (mkTypedLocal varName .address (some iface))
        | none => locals
      pure (#[elem], locals)
  | `(doElem| let $name:ident ← $rhs:term) =>
      match ← typedInterfaceCallReturnType? externalDecls params locals rhs with
      | some retTy =>
          let retTyTerm ← contractValueTypeTerm retTy
          pure (#[← `(doElem| let $name:ident := (panic! "typed interface calls are compiler-only in executable wrappers" : $retTyTerm))],
            locals.push (mkTypedLocal (toString name.getId) retTy))
      | none => pure (#[elem], locals)
  | `(doElem| let $pat:term ← $rhs:term) =>
      match tupleBinderNames? pat with
      | some _ =>
          match stripParens rhs with
          | `(term| tryExternalCall $name:term $_args:term) =>
              let extName := ← expectStringOrIdent name
              match externalDecls.find? (fun ext => ext.name == extName) with
              | some ext =>
                  match ext.returnTys.toList with
                  | [retTy] =>
                      let retTyTerm ← contractValueTypeTerm retTy
                      pure (#[← `(doElem| let $pat:term ← ($rhs : _root_.Verity.Contract (Bool × $retTyTerm)))], locals)
                  | _ => pure (#[elem], locals)
              | none => pure (#[elem], locals)
          | _ => pure (#[elem], locals)
      | none => pure (#[elem], locals)
  | `(doElem| forEach $name:term $_count:term $body:term) =>
      let loopIdent := mkIdent (Name.mkSimple (← expectStringOrIdent name))
      match stripParens body with
      | `(term| do $[$inner:doElem]*) =>
          let (inner, _) ← rewriteForEachExecutableDoElems externalDecls params locals inner
          pure (#[← `(doElem| let $loopIdent : Uint256 := 0)] ++ inner, locals)
      | _ => throwErrorAt body "forEach body must be a do block"
  | `(doElem| forEachSetBit $name:term $_bitmap:term $body:term) =>
      let loopIdent := mkIdent (Name.mkSimple (← expectStringOrIdent name))
      match stripParens body with
      | `(term| do $[$inner:doElem]*) =>
          let (inner, _) ← rewriteForEachExecutableDoElems externalDecls params locals inner
          pure (#[← `(doElem| let $loopIdent : Uint256 := 0)] ++ inner, locals)
      | _ => throwErrorAt body "forEachSetBit body must be a do block"
  | `(doElem| if $cond:term then $thenBranch:doSeq else $elseBranch:doSeq) =>
      let thenBranch ← rewriteForEachExecutableDoSeq externalDecls params locals thenBranch
      let elseBranch ← rewriteForEachExecutableDoSeq externalDecls params locals elseBranch
      pure (#[← `(doElem| if $cond then $thenBranch else $elseBranch)], locals)
  | `(doElem| tryCatch $attempt:term $handler:term) =>
      let tryCatchFn := Lean.mkIdentFrom attempt `_root_.Contracts.tryCatchWord
      match stripParens handler with
      | `(term| fun $name:ident => do $[$catchElems:doElem]*) =>
          let (catchElems, _) ← rewriteForEachExecutableDoElems externalDecls params locals catchElems
          pure (#[← `(doElem| $tryCatchFn:ident $attempt (fun $name => do $[$catchElems:doElem]*))], locals)
      | `(term| do $[$catchElems:doElem]*) =>
          let (catchElems, _) ← rewriteForEachExecutableDoElems externalDecls params locals catchElems
          pure (#[← `(doElem| $tryCatchFn:ident $attempt (fun _ => do $[$catchElems:doElem]*))], locals)
      | _ =>
          throwErrorAt handler
            "tryCatch handler must be `fun _ => do ...` or a direct `do ...` block"
  | `(doElem| unsafe $_reason:str do $body:doSeq) =>
      let body ← rewriteForEachExecutableDoSeq externalDecls params locals body
      pure (#[← `(doElem| do $body)], locals)
  | `(doElem| $stmt:term) =>
      -- a void typed interface call in statement position is compiler-only;
      -- drop it from the executable wrapper (it returns nothing to bind).
      if (← isVoidTypedInterfaceCall? externalDecls params locals stmt) then
        pure (#[← `(doElem| pure ())], locals)
      else
        pure (#[elem], locals)
  | other =>
      pure (#[other], locals)
end

private def rewriteForEachExecutableBody (externalDecls : Array ExternalDecl) (params : Array ParamDecl) (body : Term) : CommandElabM Term := do
  match body with
  | `(term| do $[$elems:doElem]*) =>
      let (elems, _) ← rewriteForEachExecutableDoElems externalDecls params #[] elems
      `(do $[$elems:doElem]*)
  | _ => pure body

private def mkContractFnValue (params : Array ParamDecl) (body : Term) : CommandElabM Term := do
  let mut value ← injectTupleParamAliases params body
  for param in params.reverse do
    let pid := param.ident
    value ← `(fun ($pid : $(← contractValueTypeTerm param.ty)) => $value)
  pure value

private def mkModelParamsTerm (params : Array ParamDecl) : CommandElabM Term := do
  let xs ← params.mapM fun p => do
    `(Compiler.CompilationModel.Param.mk $(strTerm p.name) $(← modelParamTypeTerm p.ty))
  `([ $[$xs],* ])

private def storageSlotInnerTypeTerm (ty : StorageType) : CommandElabM Term := do
  let rec mkStorageMappingTy (keys : List MappingKeyType) : CommandElabM Term := do
    match keys with
    | [] => `(Uint256)
    | keyTy :: rest =>
        `(($(← storageKeyTypeContractTerm keyTy) → $(← mkStorageMappingTy rest)))
  match ty with
    | .scalar .uint256 => `(Uint256)
    | .scalar .int256 => `(Uint256)
    | .scalar .uint8 => throwError "storage field cannot be Uint8; use Uint256 encoding"
    | .scalar .uint16 => throwError "storage field cannot be Uint16; use Uint256 encoding"
    | .scalar (.uintN _) => throwError "narrow integer storage is tracked separately in #2060"
    | .scalar (.intN _) => throwError "narrow integer storage is tracked separately in #2060"
    | .scalar (.bytesN _) => throwError "fixed-bytes storage is tracked separately in #2060"
    | .scalar .address => `(Address)
    | .scalar .bytes32 => throwError "storage field cannot be Bytes32; use Uint256 encoding"
    | .scalar .bool => throwError "storage field cannot be Bool; use Uint256 (0/1) encoding"
    | .scalar .string => throwError "storage field cannot be String; use Uint256 encoding"
    | .scalar .bytes => throwError "storage field cannot be Bytes; use Uint256 encoding"
    | .scalar (.array _) => throwError "storage field cannot be Array; use mapping encodings"
    | .scalar (.fixedArray _ _) => throwError "storage field cannot be FixedArray; use mapping encodings"
    | .scalar (.tuple _) => throwError "storage field cannot be Tuple; use mapping encodings"
    | .scalar (.struct _ _) => throwError "storage field cannot be named struct; use mapping encodings"
    | .scalar .unit => throwError "storage field cannot be Unit"
    | .scalar (.newtype _ baseType) =>
        -- Newtypes erased to base type for storage (#1727 Step 3b)
        match baseType with
        | .uint256 => `(Uint256)
        | .address => `(Address)
        | _ => throwError "storage field with newtype base type not supported; use Uint256 or Address"
    | .scalar (.adt _ _) => `(Uint256)  -- ADTs stored as tag value in storage (#1727 Step 5b)
    | .dynamicArray .uint256 => `(List Uint256)
    | .dynamicArray .address => `(List Address)
    | .dynamicArray .bool => `(List Bool)
    | .dynamicArray .uint8 => throwError "storage dynamic arrays currently support only Uint256 elements on the macro path"
    | .dynamicArray .bytes32 => `(List Uint256)
    | .mappingAddressToUint256 => `(Address → Uint256)
    | .mapping2AddressToAddressToUint256 => `(Address → Address → Uint256)
    | .mappingUintToUint256 => `(Uint256 → Uint256)
    | .mappingChain keyTypes => mkStorageMappingTy keyTypes
    | .mappingStruct keyType _ => `(($(← storageKeyTypeContractTerm keyType) → Uint256))
    | .mappingStruct2 outerKey innerKey _ =>
        `(($(← storageKeyTypeContractTerm outerKey) → $(← storageKeyTypeContractTerm innerKey) → Uint256))

private def mkStorageDefCommand (field : StorageFieldDecl) : CommandElabM Cmd := do
  let storageTy ← storageSlotInnerTypeTerm field.ty
  let fid := field.ident
  `(command| def $fid : Verity.StorageSlot $storageTy := ⟨$(natTerm field.slotNum)⟩)

private def storageAccessorTypeName (parts : List String) : Ident :=
  mkIdent (Name.mkSimple (String.intercalate "_" parts ++ "_StorageSlots"))

private partial def storageAccessorTreeName : StorageAccessorTree → String
  | .leaf name .. => name
  | .node name _ => name

private partial def storageAccessorTypeCommands
    (path : List String) : StorageAccessorTree → CommandElabM (Array Cmd)
  | .leaf .. => pure #[]
  | .node _ children => do
      let mut cmds : Array Cmd := #[]
      for child in children do
        cmds := cmds ++ (← storageAccessorTypeCommands (path ++ [storageAccessorTreeName child]) child)
      let typeId := storageAccessorTypeName path
      let mut fieldIds : Array Ident := #[]
      let mut fieldTypes : Array Term := #[]
      for child in children do
        fieldIds := fieldIds.push (mkIdent (Name.mkSimple (storageAccessorTreeName child)))
        match child with
        | .leaf _ ty _ =>
            fieldTypes := fieldTypes.push (← `(Verity.StorageSlot $(← storageSlotInnerTypeTerm ty)))
        | .node name _ =>
            fieldTypes := fieldTypes.push (storageAccessorTypeName (path ++ [name]))
      cmds := cmds.push (← `(command| structure $typeId where
          $[$fieldIds:ident : $fieldTypes:term]*))
      pure cmds

private partial def storageAccessorValueTerm : StorageAccessorTree → CommandElabM Term
  | .leaf _ ty slotNum => do
      `((⟨$(natTerm slotNum)⟩ : Verity.StorageSlot $(← storageSlotInnerTypeTerm ty)))
  | .node _ children => do
      let fieldIds := children.map (fun child => mkIdent (Name.mkSimple (storageAccessorTreeName child)))
      let values ← children.mapM storageAccessorValueTerm
      `({ $[$fieldIds:ident := $values:term],* })

def mkStorageStructAccessorCommandsPublic
    (accessor : StorageStructAccessorDecl) : CommandElabM (Array Cmd) := do
  let typeCmds ← storageAccessorTypeCommands [accessor.name] accessor.tree
  let rootType := storageAccessorTypeName [accessor.name]
  let rootValue ← storageAccessorValueTerm accessor.tree
  let rootCmd ← `(command| def $(accessor.ident) : $rootType := $rootValue)
  pure (typeCmds.push rootCmd)

private def packedOptionTerm (packed : Option (Nat × Nat)) : CommandElabM Term := do
  match packed with
  | none => `(none)
  | some (offset, width) => `(some ($(natTerm offset), $(natTerm width)))

private def mkStructMemberReadBranches
    (fields : Array StorageFieldDecl)
    (nested : Bool)
    (fallbackTerm : Term) : CommandElabM Term := do
  let mut acc := fallbackTerm
  for field in fields.reverse do
    match nested, field.ty with
    | false, .mappingStruct _ members =>
        for member in members.reverse do
          let packedTerm ← packedOptionTerm member.packed
          acc ← `(if field == $(strTerm field.name) && member == $(strTerm member.name) then
              _root_.Contracts.structMemberAt $(natTerm field.slotNum) $(natTerm member.wordOffset)
                $packedTerm key
            else
              $acc)
    | true, .mappingStruct2 _ _ members =>
        for member in members.reverse do
          let packedTerm ← packedOptionTerm member.packed
          acc ← `(if field == $(strTerm field.name) && member == $(strTerm member.name) then
              _root_.Contracts.structMember2At $(natTerm field.slotNum) $(natTerm member.wordOffset)
                $packedTerm key1 key2
            else
              $acc)
    | _, _ => pure ()
  pure acc

private def mkStructMemberWriteBranches
    (fields : Array StorageFieldDecl)
    (nested : Bool)
    (fallbackTerm : Term) : CommandElabM Term := do
  let mut acc := fallbackTerm
  for field in fields.reverse do
    match nested, field.ty with
    | false, .mappingStruct _ members =>
        for member in members.reverse do
          let packedTerm ← packedOptionTerm member.packed
          acc ← `(if field == $(strTerm field.name) && member == $(strTerm member.name) then
              _root_.Contracts.setStructMemberAt $(natTerm field.slotNum) $(natTerm member.wordOffset)
                $packedTerm key value
            else
              $acc)
    | true, .mappingStruct2 _ _ members =>
        for member in members.reverse do
          let packedTerm ← packedOptionTerm member.packed
          acc ← `(if field == $(strTerm field.name) && member == $(strTerm member.name) then
              _root_.Contracts.setStructMember2At $(natTerm field.slotNum) $(natTerm member.wordOffset)
                $packedTerm key1 key2 value
            else
              $acc)
    | _, _ => pure ()
  pure acc

private def hasStructMapping (fields : Array StorageFieldDecl) : Bool :=
  fields.any fun field =>
    match field.ty with
    | .mappingStruct _ _ => true
    | _ => false

private def hasStructMapping2 (fields : Array StorageFieldDecl) : Bool :=
  fields.any fun field =>
    match field.ty with
    | .mappingStruct2 _ _ _ => true
    | _ => false

def mkExecutableStructMappingCommandsPublic (fields : Array StorageFieldDecl) :
    CommandElabM (Array Cmd) := do
  let mut cmds : Array Cmd := #[]
  if hasStructMapping fields then
    let readFallback : Term ← `(pure default)
    let writeFallback : Term ← `(pure ())
    let readBranches ← mkStructMemberReadBranches fields false readFallback
    let writeBranches ← mkStructMemberWriteBranches fields false writeFallback
    cmds := cmds.push (← `(command|
      def structMember {κ α : Type} [Inhabited α] [_root_.Contracts.StorageKey κ]
          [_root_.Contracts.StorageWord α] (field : String) (key : κ) (member : String) :
          Verity.Contract α :=
        $readBranches))
    cmds := cmds.push (← `(command|
      def setStructMember {κ α : Type} [_root_.Contracts.StorageKey κ]
          [_root_.Contracts.StorageWord α] (field : String) (key : κ) (member : String)
          (value : α) : Verity.Contract Unit :=
        $writeBranches))
  if hasStructMapping2 fields then
    let readFallback : Term ← `(pure default)
    let writeFallback : Term ← `(pure ())
    let readBranches ← mkStructMemberReadBranches fields true readFallback
    let writeBranches ← mkStructMemberWriteBranches fields true writeFallback
    cmds := cmds.push (← `(command|
      def structMember2 {κ₁ κ₂ α : Type} [Inhabited α] [_root_.Contracts.StorageKey κ₁]
          [_root_.Contracts.StorageKey κ₂] [_root_.Contracts.StorageWord α] (field : String)
          (key1 : κ₁) (key2 : κ₂) (member : String) : Verity.Contract α :=
        $readBranches))
    cmds := cmds.push (← `(command|
      def setStructMember2 {κ₁ κ₂ α : Type} [_root_.Contracts.StorageKey κ₁]
          [_root_.Contracts.StorageKey κ₂] [_root_.Contracts.StorageWord α] (field : String)
          (key1 : κ₁) (key2 : κ₂) (member : String) (value : α) : Verity.Contract Unit :=
        $writeBranches))
  pure cmds

private def mkModelFieldTerm (field : StorageFieldDecl) : CommandElabM Term := do
  let packedTerm ←
    match field.packedBits with
    | none => `(none)
    | some (offset, width) =>
        `(some { offset := $(natTerm offset), width := $(natTerm width) })
  let transientTerm ← if field.isTransient then `(true) else `(false)
  `(Compiler.CompilationModel.Field.mk
      $(strTerm field.name)
      $(← modelFieldTypeTerm field.ty)
      $transientTerm
      (some $(natTerm field.slotNum))
      $packedTerm
      [])

private def mkModelErrorTerm (err : ErrorDecl) : CommandElabM Term := do
  let paramTerms ← err.params.mapM modelParamTypeTerm
  `(Compiler.CompilationModel.ErrorDef.mk
      $(strTerm err.name)
      [ $[$paramTerms],* ])

private def mkModelEventParamTerm (param : EventParamDecl) : CommandElabM Term := do
  let tyTerm ← modelParamTypeTerm param.ty
  let kindTerm ←
    if param.isIndexed then
      `(Compiler.CompilationModel.EventParamKind.indexed)
    else
      `(Compiler.CompilationModel.EventParamKind.unindexed)
  `(Compiler.CompilationModel.EventParam.mk
      $(strTerm param.name)
      $tyTerm
      $kindTerm)

private def mkModelEventTerm (ev : EventDecl) : CommandElabM Term := do
  let paramTerms ← ev.params.mapM mkModelEventParamTerm
  `(Compiler.CompilationModel.EventDef.mk
      $(strTerm ev.name)
      [ $[$paramTerms],* ])

private def mkModelExternalTerm (ext : ExternalDecl) : CommandElabM Term := do
  let paramTerms ← ext.params.mapM modelParamTypeTerm
  let returnTerms ← ext.returnTys.mapM modelParamTypeTerm
  let returnTypeTerm ←
    match ext.returnTys.toList with
    | [] => `(none)
    | [retTy] => `(some $(← modelParamTypeTerm retTy))
    | _ => `(none)
  let linkModeTerm ←
    match ext.linkMode with
    | .external => `(Compiler.CompilationModel.ForeignLinkMode.external)
    | .objectLinked => `(Compiler.CompilationModel.ForeignLinkMode.objectLinked)
    | .inline => `(Compiler.CompilationModel.ForeignLinkMode.inline)
    | .compilerRuntime => `(Compiler.CompilationModel.ForeignLinkMode.compilerRuntime)
  `( ({
      name := $(strTerm ext.name)
      params := [ $[$paramTerms],* ]
      returnType := $returnTypeTerm
      «returns» := [ $[$returnTerms],* ]
      proofStatus := Compiler.ProofStatus.assumed
      axiomNames := []
      linkMode := $linkModeTerm
    } : Compiler.CompilationModel.ExternalFunction) )

private def mkModelLocalObligationTerm (obligation : LocalObligationDecl) : CommandElabM Term := do
  let proofStatusTerm ←
    match obligation.proofStatus with
    | .proved => `(Compiler.ProofStatus.proved)
    | .assumed => `(Compiler.ProofStatus.assumed)
    | .unchecked => `(Compiler.ProofStatus.unchecked)
  `(Compiler.CompilationModel.LocalObligation.mk
      $(strTerm obligation.name)
      $(strTerm obligation.obligation)
      $proofStatusTerm)

private def termSource (term : Term) : String :=
  (term.raw.reprint.getD (toString term.raw)).trimAscii.toString

private def isIdentChar (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || ('0' ≤ c && c ≤ '9')

private def sanitizeObligationPart (s : String) : String :=
  let chars := s.toList.map fun c => if isIdentChar c then c else '_'
  let collapsed := chars.foldl
    (fun acc c =>
      match acc.getLast? with
      | some '_' => if c == '_' then acc else acc ++ [c]
      | _ => acc ++ [c])
    []
  let trimmed := (collapsed.dropWhile (· == '_')).reverse.dropWhile (· == '_') |>.reverse
  let rendered := String.ofList trimmed
  if rendered.isEmpty then "expr" else rendered

private def checkedArithmeticApp? (term : Term) : Option (String × String × Term × Term) :=
  match stripParens term with
  | `(term| safeAdd $a:term $b:term) =>
      some ("add_no_overflow", "Verity.Proofs.Stdlib.Math.CheckedArithmetic.AddNoOverflow", a, b)
  | `(term| safeSub $a:term $b:term) =>
      some ("sub_no_underflow", "Verity.Proofs.Stdlib.Math.CheckedArithmetic.SubNoUnderflow", a, b)
  | `(term| safeMul $a:term $b:term) =>
      some ("mul_no_overflow", "Verity.Proofs.Stdlib.Math.CheckedArithmetic.MulNoOverflow", a, b)
  | `(term| addPanic $a:term $b:term) =>
      some ("add_no_overflow", "Verity.Proofs.Stdlib.Math.CheckedArithmetic.AddNoOverflow", a, b)
  | `(term| subPanic $a:term $b:term) =>
      some ("sub_no_underflow", "Verity.Proofs.Stdlib.Math.CheckedArithmetic.SubNoUnderflow", a, b)
  | `(term| mulPanic $a:term $b:term) =>
      some ("mul_no_overflow", "Verity.Proofs.Stdlib.Math.CheckedArithmetic.MulNoOverflow", a, b)
  | _ => none

private partial def collectCheckedArithmeticApps (stx : Syntax) : Array (String × String × Term × Term) :=
  let here :=
    match checkedArithmeticApp? ⟨stx⟩ with
    | some app => #[app]
    | none => #[]
  stx.getArgs.foldl
    (fun acc child => acc ++ collectCheckedArithmeticApps child)
    here

private def generatedArithmeticObligationsFromSyntax
    (owner : String)
    (bodies : Array Syntax) : Array LocalObligationDecl :=
  let apps := bodies.foldl
    (fun acc body => acc ++ collectCheckedArithmeticApps body)
    #[]
  let apps := apps.foldl
    (fun acc app =>
      let (kind, pred, lhs, rhs) := app
      let duplicate := acc.any fun prev =>
        let (prevKind, prevPred, prevLhs, prevRhs) := prev
        prevKind == kind && prevPred == pred &&
          termSource prevLhs == termSource lhs &&
          termSource prevRhs == termSource rhs
      if duplicate then acc else acc.push app)
    #[]
  apps.mapIdx fun idx (kind, pred, lhs, rhs) =>
    let name :=
      s!"checked_arithmetic_{sanitizeObligationPart owner}_{idx + 1}_{kind}"
    let obligation :=
      s!"Prove `{pred} ({termSource lhs}) ({termSource rhs})` for the checked arithmetic operation emitted at this entrypoint."
    { ident := mkIdent (Name.mkSimple name)
      name := name
      obligation := obligation
      proofStatus := .assumed }

private def generatedArithmeticObligations
    (owner : String)
    (body : Term) : Array LocalObligationDecl :=
  generatedArithmeticObligationsFromSyntax owner #[body.raw]

private def mergeGeneratedLocalObligations
    (declared generated : Array LocalObligationDecl) : Array LocalObligationDecl :=
  generated.foldl
    (fun acc obligation =>
      if acc.any (fun prev => prev.name == obligation.name) then acc else acc.push obligation)
    declared

private def functionLocalObligationsWithArithmetic (fn : FunctionDecl) : Array LocalObligationDecl :=
  mergeGeneratedLocalObligations fn.localObligations (generatedArithmeticObligations fn.name fn.body)

private def immutableInitArithmeticBodies (immutableDecls : Array ImmutableDecl) : Array Syntax :=
  immutableDecls.map (fun imm => imm.body.raw)

private def constructorLocalObligationsWithArithmetic
    (ctor : ConstructorDecl)
    (immutableDecls : Array ImmutableDecl) : Array LocalObligationDecl :=
  let bodies := immutableInitArithmeticBodies immutableDecls |>.push ctor.body.raw
  mergeGeneratedLocalObligations ctor.localObligations
    (generatedArithmeticObligationsFromSyntax "constructor" bodies)

private def synthesizedConstructorLocalObligationsWithArithmetic
    (immutableDecls : Array ImmutableDecl) : Array LocalObligationDecl :=
  generatedArithmeticObligationsFromSyntax "constructor"
    (immutableInitArithmeticBodies immutableDecls)

private def mkAdtVariantTerm (variant : AdtVariantDecl) (tag : Nat) : CommandElabM Term := do
  let fieldTerms ← variant.fields.mapM fun p => do
    let tyTerm ← modelParamTypeTerm p.ty
    `(Compiler.CompilationModel.Param.mk $(strTerm p.name) $tyTerm)
  `(Compiler.CompilationModel.AdtVariant.mk
      $(strTerm variant.name)
      $(natTerm tag)
      [ $[$fieldTerms],* ])

private def mkAdtTypeDefTerm (adtDecl : AdtDecl) : CommandElabM Term := do
  let mut variantTerms : Array Term := #[]
  for (variant, idx) in adtDecl.variants.zipIdx do
    variantTerms := variantTerms.push (← mkAdtVariantTerm variant idx)
  `(Compiler.CompilationModel.AdtTypeDef.mk
      $(strTerm adtDecl.name)
      [ $[$variantTerms],* ])

private partial def collectQualifiedFunctionAppsFromSyntax (interfaceParamNames : Array String) (stx : Syntax) : Array Name :=
  let fromChildren : Array Name :=
    match stx with
    | .node _ _ args =>
        args.foldl (fun acc child => acc ++ collectQualifiedFunctionAppsFromSyntax interfaceParamNames child) #[]
    | _ => #[]
  match stx with
  | .node _ `Lean.Parser.Term.app args =>
      match args.getD 0 Syntax.missing with
      | .ident _ _ raw _ =>
          let components := nameComponents raw
          if isQualifiedFunctionName raw && (nameComponents raw).head? != some "Verity" &&
              !interfaceParamNames.contains (components.headD "") &&
              !startsWithLowercaseAscii (components.headD "") &&
              !raw.toString.endsWith ".mk" then
            fromChildren.push raw
          else
            fromChildren
      | _ => fromChildren
  | _ => fromChildren

private def uniqueNames (names : Array Name) : Array Name :=
  names.foldl
    (fun acc name => if acc.any (· == name) then acc else acc.push name)
    #[]

private def collectQualifiedFunctionAppsFromFunction (fn : FunctionDecl) : Array Name :=
  collectQualifiedFunctionAppsFromSyntax
    (fn.params.filterMap fun p => p.interfaceName?.map (fun _ => p.name))
    fn.body.raw

private def collectQualifiedFunctionAppsFromConstructor (ctor : ConstructorDecl) : Array Name :=
  collectQualifiedFunctionAppsFromSyntax #[] ctor.body.raw

private def mkQualifiedInternalFunctionTerm
    (usedNames : List String)
    (name : Name) : CommandElabM Term := do
  let modelIdent : Ident := mkIdent (qualifiedFunctionModelName name)
  `(({ $modelIdent with
        name := $(strTerm (qualifiedInternalHelperNameFromUsed usedNames name))
        isInternal := true } : Compiler.CompilationModel.FunctionSpec))

private def mkSpecCommand
    (contractName : String)
    (fields : Array StorageFieldDecl)
    (roleDecls : Array RoleDecl)
    (errorDecls : Array ErrorDecl)
    (eventDecls : Array EventDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (externalDecls : Array ExternalDecl)
    (ctor : Option ConstructorDecl)
    (modifiers : Array ModifierDecl)
    (functions : Array FunctionDecl)
    (adtDecls : Array AdtDecl)
    (storageNamespace : Option Nat) : CommandElabM Cmd := do
  let immutableTerms ← immutableDecls.mapM fun imm => do
    let tyTerm ← modelParamTypeTerm imm.ty
    let initTerm ← translatePureExpr fields constDecls #[] (ctor.map (·.params) |>.getD #[]) #[] imm.body
    `(({ name := $(strTerm imm.name), ty := $tyTerm, init := $initTerm } :
        Compiler.CompilationModel.ImmutableSpec))
  let fieldTerms ← fields.mapM mkModelFieldTerm
  let roleTerms ← roleDecls.mapM fun role => do
    let kindTerm ← match role.kind with
      | .scalarAddress => `(Compiler.CompilationModel.RoleKind.scalarAddress)
      | .mappingAddressToUint256 => `(Compiler.CompilationModel.RoleKind.mappingAddressToUint256)
    `(({ name := $(strTerm role.name), field := $(strTerm role.fieldName), kind := $kindTerm } :
        Compiler.CompilationModel.RoleDecl))
  let errorTerms ← errorDecls.mapM mkModelErrorTerm
  let eventTerms ← eventDecls.mapM mkModelEventTerm
  let externalTerms ← externalDecls.mapM mkModelExternalTerm
  let constructorTerm ←
    match ctor, immutableDecls.isEmpty with
    | none, true => `(none)
    | some ctor, _ =>
        let ctorParams ← mkModelParamsTerm ctor.params
        let ctorPayable ← if ctor.isPayable then `(true) else `(false)
        let ctorLocalObligationTerms ←
          (constructorLocalObligationsWithArithmetic ctor immutableDecls).mapM mkModelLocalObligationTerm
        let immutableInitTerms ← immutableInitStmtTerms fields constDecls immutableDecls ctor.params
        let ctorBodyTerms ← translateConstructorBodyToStmtTerms fields errorDecls constDecls immutableDecls externalDecls functions ctor
        let ctorAllTerms := immutableInitTerms ++ ctorBodyTerms
        `(some {
          params := $ctorParams
          isPayable := $ctorPayable
          localObligations := [ $[$ctorLocalObligationTerms],* ]
          body := [ $[$ctorAllTerms],* ]
        })
    | none, false =>
        let immutableInitTerms ← immutableInitStmtTerms fields constDecls immutableDecls #[]
        let ctorLocalObligationTerms ←
          (synthesizedConstructorLocalObligationsWithArithmetic immutableDecls).mapM mkModelLocalObligationTerm
        `(some {
          params := []
          isPayable := false
          localObligations := [ $[$ctorLocalObligationTerms],* ]
          body := [ $[$immutableInitTerms],* ]
        })
  let publicFunctions := functions.filter (fun fn => !fn.isInternal)
  let functionModelIds ← publicFunctions.mapM fun fn => mkSuffixedIdent fn.ident "_model"
  let internalFunctionTerms ← functions.filterMapM fun fn => do
    if supportsInternalHelperSpec fn then
      let modelBodyName ← mkSuffixedIdent fn.ident "_modelBody"
      let modelParams ← mkModelParamsTerm fn.params
      let localObligationTerms ← (functionLocalObligationsWithArithmetic fn).mapM mkModelLocalObligationTerm
      let payableTerm ← if fn.isPayable then `(true) else `(false)
      let viewTerm ← if fn.isView then `(true) else `(false)
      let pureTerm ← if fn.isPure then `(true) else `(false)
      let noExternalCallsTerm ← if fn.noExternalCalls then `(true) else `(false)
      -- The internal helper shadow runs *inside* an already-guarded call
      -- chain (the transient-storage reentrancy guard is attached at the
      -- external dispatch boundary via `attachNonReentrantGuard`, #1893),
      -- so it must drop `nonReentrantLock` to avoid double-guarding /
      -- false "internal nonreentrant" rejection at the
      -- compilation-model boundary. We propagate the CEI exemption that
      -- the public spec would have got from `nonReentrantLock` onto the
      -- shadow as `allowPostInteractionWrites := true` instead, so the
      -- shared body — which may legitimately contain post-external-call
      -- state writes once the public path has a guard — still validates
      -- through the shadow.
      let shadowAllowPostInteractionWritesTerm ←
        if fn.nonReentrantLock.isSome || fn.allowPostInteractionWrites then
          `(true)
        else
          `(false)
      let ceiSafeTerm ← if fn.ceiSafe then `(true) else `(false)
      -- The internal helper shadow drops `nonReentrantLock` (the transient guard
      -- only runs at the external dispatch boundary), so the cross-function
      -- reentrancy gate would reject any external call it makes. The public entry
      -- is already protected — by its `nonreentrant` guard or its own
      -- `reentrancy_trusted` assertion — so propagate a `reentrancyTrusted` flag
      -- onto the shadow to record that its external calls run under that
      -- protection. When the public function carried neither, the public spec
      -- itself fails the gate first, so this never masks an unguarded entry.
      -- For a *lock-only* function (`nonReentrantLock` set, no
      -- `reentrancy_trusted`) the lock protection is local to the guarded entry
      -- and does NOT survive on the lock-free shadow, so the shadow is rendered
      -- unreachable: `ensureCallableAsInternalHelper` rejects any internal call
      -- to such a function at lowering. The `reentrancyTrusted` flag below is
      -- therefore only ever consumed for functions the author globally asserted
      -- `reentrancy_trusted`, where the lock-free internal path is sound.
      let shadowReentrancyTrustedTerm ←
        if fn.nonReentrantLock.isSome || fn.reentrancyTrusted then
          `(true)
        else
          `(false)
      let requiresRoleTerm ← match fn.requiresRole with
        | some roleIdent => `(some $(strTerm (toString roleIdent.getId)))
        | none => `(none)
      let internalModifiesTerms : Array Term := fn.modifies.map fun ident => strTerm (toString ident.getId)
      let returnTypeTerm ← modelReturnTypeTerm fn.returnTy
      let returnsTerm ← modelReturnsTerm fn.returnTy
      -- Internal helper shadow specs (for calls via `internalCall`) inherit most
      -- metadata from the public function. For `nonreentrant` functions the lock
      -- annotation is cleared on the shadow (the transient guard is only injected
      -- at the external dispatch boundary via `attachNonReentrantGuard` in
      -- Dispatch); CEI exemption is instead carried via `allowPostInteractionWrites`.
      -- This allows legitimate intra-contract / same-function calls through the
      -- shadow while the public entry remains protected against external reentrancy.
      -- (Addresses "Shadow guard blocks same-function calls" follow-up to #1893.)
      pure <| some (← `( ({
        name := $(strTerm (internalHelperSpecNameFor fn))
        params := $modelParams
        returnType := $returnTypeTerm
        «returns» := $returnsTerm
        isPayable := $payableTerm
        isView := $viewTerm
        isPure := $pureTerm
        noExternalCalls := $noExternalCallsTerm
        allowPostInteractionWrites := $shadowAllowPostInteractionWritesTerm
        nonReentrantLock := none
        ceiSafe := $ceiSafeTerm
        reentrancyTrusted := $shadowReentrancyTrustedTerm
        requiresRole := $requiresRoleTerm
        modifies := [ $[$internalModifiesTerms],* ]
        localObligations := [ $[$localObligationTerms],* ]
        body := $modelBodyName
        isInternal := true
      } : Compiler.CompilationModel.FunctionSpec) ))
    else
      pure none
  let modifierFunctionTerms ← modifiers.mapM fun modDecl => do
    let bodyTerms ←
      match modDecl.body with
      | `(term| do $[$elems:doElem]*) =>
          pure (← (translateDoElems fields constDecls immutableDecls externalDecls errorDecls functions .unit #[] #[] #[] elems)).1
      | _ => throwErrorAt modDecl.body "modifier body must be a do block"
    let bodyTerms := bodyTerms.push (← `(Compiler.CompilationModel.Stmt.stop))
    `( ({
        name := $(strTerm (modifierInternalName modDecl.name))
        params := []
        returnType := none
        «returns» := []
        isPayable := false
        isView := false
        isPure := false
        noExternalCalls := false
        allowPostInteractionWrites := false
        nonReentrantLock := none
        ceiSafe := false
        requiresRole := none
        modifies := []
        localObligations := []
        body := [ $[$bodyTerms],* ]
        isInternal := true
      } : Compiler.CompilationModel.FunctionSpec) )
  let qualifiedFunctionNames :=
    uniqueNames <|
      (functions.foldl (fun acc fn => acc ++ collectQualifiedFunctionAppsFromFunction fn) #[]) ++
      (match ctor with
      | some ctorDecl => collectQualifiedFunctionAppsFromConstructor ctorDecl
      | none => #[])
  let localInternalFunctionNames := (functions.map internalHelperSpecNameFor).toList
  let qualifiedInternalFunctionTerms ←
    qualifiedFunctionNames.mapM (mkQualifiedInternalFunctionTerm localInternalFunctionNames)
  let adtTypeTerms ← adtDecls.mapM mkAdtTypeDefTerm
  let functionModelTerms : Array Term := functionModelIds.map fun id => ⟨id.raw⟩
  let allFunctionTerms := functionModelTerms ++ internalFunctionTerms ++ modifierFunctionTerms ++ qualifiedInternalFunctionTerms
  let namespaceTerm ← match storageNamespace with
    | some ns => `(some $(natTerm ns))
    | none => `(none)
  `(command| def spec : Compiler.CompilationModel.CompilationModel := {
    name := $(strTerm contractName)
    fields := [ $[$fieldTerms],* ]
    «immutables» := [ $[$immutableTerms],* ]
    «roles» := [ $[$roleTerms],* ]
    «errors» := [ $[$errorTerms],* ]
    «events» := [ $[$eventTerms],* ]
    «constructor» := $constructorTerm
    functions := [ $[$allFunctionTerms],* ]
    «externals» := [ $[$externalTerms],* ]
    adtTypes := [ $[$adtTypeTerms],* ]
    storageNamespace := $namespaceTerm
  })

private def mkFindIdxFieldSimpCommands
    (contractIdent : Ident)
    (fields : Array StorageFieldDecl) : CommandElabM (Array Cmd) := do
  let contractName := toString contractIdent.getId
  let fieldTerms ← fields.mapM mkModelFieldTerm
  let fieldListTerm : Term ← `(([ $[$fieldTerms],* ] : List Compiler.CompilationModel.Field))
  let mut cmds : Array Cmd := #[]
  let mut idx := 0
  for field in fields do
    let baseName := s!"findIdx_{field.name}_{contractName}"
    let theoremName := mkIdent (Name.mkSimple baseName)
    let theoremNameDecide := mkIdent (Name.mkSimple (baseName ++ "_decide"))
    let idxTerm := natTerm idx
    let fieldNameTerm := strTerm field.name

    let eqCmd : Cmd ← `(command|
      @[simp] theorem $theoremName :
          List.findIdx? (fun x : Compiler.CompilationModel.Field => x.name == $fieldNameTerm)
            $fieldListTerm = some $idxTerm := by
        decide)
    cmds := cmds.push eqCmd

    let decideCmd : Cmd ← `(command|
      @[simp] theorem $theoremNameDecide :
          List.findIdx? (fun x : Compiler.CompilationModel.Field => decide (x.name = $fieldNameTerm))
            $fieldListTerm = some $idxTerm := by
        decide)
    cmds := cmds.push decideCmd
    idx := idx + 1
  pure cmds

private def mkFindIdxParamSimpCommandsForScope
    (contractName : String)
    (scopeName : String)
    (params : Array ParamDecl) : CommandElabM (Array Cmd) := do
  let paramNameTerms : Array Term := params.map (fun p => strTerm p.name)
  let paramListTerm : Term ← `(([ $[$paramNameTerms],* ] : List String))
  let mut cmds : Array Cmd := #[]
  let mut idx := 0
  for param in params do
    let baseName := s!"findIdx_param_{param.name}_{scopeName}_{contractName}"
    let theoremName := mkIdent (Name.mkSimple baseName)
    let theoremNameDecide := mkIdent (Name.mkSimple (baseName ++ "_decide"))
    let idxTerm := natTerm idx
    let paramNameTerm := strTerm param.name

    let eqCmd : Cmd ← `(command|
      @[simp] theorem $theoremName :
          List.findIdx? (fun x => x == $paramNameTerm)
            $paramListTerm = some $idxTerm := by
        decide)
    cmds := cmds.push eqCmd

    let decideCmd : Cmd ← `(command|
      @[simp] theorem $theoremNameDecide :
          List.findIdx? (fun x => decide (x = $paramNameTerm))
            $paramListTerm = some $idxTerm := by
        decide)
    cmds := cmds.push decideCmd
    idx := idx + 1
  pure cmds

private def mkFindIdxParamSimpCommands
    (contractIdent : Ident)
    (ctor : Option ConstructorDecl)
    (functions : Array FunctionDecl) : CommandElabM (Array Cmd) := do
  let contractName := toString contractIdent.getId
  let mut cmds : Array Cmd := #[]
  match ctor with
  | some ctorDecl =>
      let ctorCmds ← mkFindIdxParamSimpCommandsForScope contractName "constructor" ctorDecl.params
      cmds := cmds ++ ctorCmds
  | none => pure ()
  for fn in functions do
    let fnCmds ← mkFindIdxParamSimpCommandsForScope contractName (toString fn.ident.getId) fn.params
    cmds := cmds ++ fnCmds
  pure cmds

/-- Compute the storage namespace for a contract.
    `storageNamespace("Foo") = keccak256("Foo.storage.v0")` as a 256-bit Nat.
    The result can be used as a base offset so different contracts never collide
    in the shared 2^256 storage address space.
    (#1730, Axis 4 Step 4a) -/
def computeStorageNamespace (contractName : String) : Nat :=
  KeccakEngine.keccak256_str_nat s!"{contractName}.storage.v0"

/-- Compute a storage namespace from an explicit user-provided namespace key. -/
def computeStorageNamespaceKey (key : String) : Nat :=
  KeccakEngine.keccak256_str_nat key

private def natToBytes32BE (n : Nat) : ByteArray :=
  let bytes := (List.range 32).map fun idx =>
    UInt8.ofNat ((n / (256 ^ (31 - idx))) % 256)
  ⟨bytes.toArray⟩

/-- Compute an ERC-7201 namespace root:
    `keccak256(abi.encode(uint256(keccak256(key)) - 1)) & ~bytes32(uint256(0xff))`. -/
def computeERC7201StorageNamespaceKey (key : String) : Nat :=
  let keyHash := KeccakEngine.keccak256_str_nat key
  let encoded := natToBytes32BE (keyHash - 1)
  let slotHash := KeccakEngine.byteArrayToNatBE (KeccakEngine.keccak256 encoded)
  (slotHash / 256) * 256

private def defaultStorageNamespaceEnabled : CommandElabM Bool := do
  pure (verity.storageNamespace.default.get (← getOptions))

private def namespaceOffsetFromSpec
    (contractName : Ident) (spec : TSyntax `verityNamespaceSpec) : CommandElabM (Option Nat) := do
  match spec with
  | `(verityNamespaceSpec| storage_namespace erc7201 $customKey:str) =>
      match customKey.raw.isStrLit? with
      | some key => pure (some (computeERC7201StorageNamespaceKey key))
      | none => throwErrorAt customKey "expected storage namespace string literal"
  | `(verityNamespaceSpec| storage_namespace $customKey:str) =>
      match customKey.raw.isStrLit? with
      | some key => pure (some (computeStorageNamespaceKey key))
      | none => throwErrorAt customKey "expected storage namespace string literal"
  | `(verityNamespaceSpec| storage_namespace legacy) =>
      pure none
  | `(verityNamespaceSpec| storage_namespace) =>
      pure (some (computeStorageNamespace (toString contractName.getId)))
  | _ =>
      throwErrorAt spec "unsupported storage namespace syntax"

private def namespaceOffsetFromStorageItem?
    (contractName : Ident) (item : TSyntax `verityStorageItem) : CommandElabM (Option Nat) := do
  match item with
  | `(verityStorageItem| storage_namespace erc7201 $customKey:str) =>
      match customKey.raw.isStrLit? with
      | some key => pure (some (computeERC7201StorageNamespaceKey key))
      | none => throwErrorAt customKey "expected storage namespace string literal"
  | `(verityStorageItem| storage_namespace $customKey:str) =>
      match customKey.raw.isStrLit? with
      | some key => pure (some (computeStorageNamespaceKey key))
      | none => throwErrorAt customKey "expected storage namespace string literal"
  | `(verityStorageItem| storage_namespace) =>
      pure (some (computeStorageNamespace (toString contractName.getId)))
  | _ => pure none

private def storageFieldFromItem?
    (item : TSyntax `verityStorageItem) : CommandElabM (Option (TSyntax `verityStorageField)) := do
  match item with
  | `(verityStorageItem| $name:ident : $ty:term := slot $slotNum:num) =>
      pure (some (← `(verityStorageField| $name:ident : $ty:term := slot $slotNum:num)))
  | _ => pure none

private partial def offsetStorageAccessorTree (offset : Nat) : StorageAccessorTree → StorageAccessorTree
  | .leaf name ty slotNum => .leaf name ty (slotNum + offset)
  | .node name children => .node name (children.map (offsetStorageAccessorTree offset))

structure ParsedContractSyntax where
  contractName : Ident
  newtypeDecls : Array NewtypeDecl
  structDecls : Array StructDecl
  adtDecls : Array AdtDecl
  fields : Array StorageFieldDecl
  roleDecls : Array RoleDecl
  storageStructAccessors : Array StorageStructAccessorDecl
  errorDecls : Array ErrorDecl
  eventDecls : Array EventDecl
  constDecls : Array ConstantDecl
  immutableDecls : Array ImmutableDecl
  externalDecls : Array ExternalDecl
  ctor : Option ConstructorDecl
  modifiers : Array ModifierDecl
  functions : Array FunctionDecl
  storageNamespace : Option Nat

private def roleKindOfStorageField? (field : StorageFieldDecl) : Option RoleKind :=
  match field.ty with
  | .scalar .address | .scalar (.newtype _ .address) => some .scalarAddress
  | .mappingAddressToUint256 => some .mappingAddressToUint256
  | _ => none

private def parseRoleDecl
    (fields : Array StorageFieldDecl) (roleStx : TSyntax `verityRoleDecl)
    : CommandElabM RoleDecl := do
  match roleStx with
  | `(verityRoleDecl| $roleName:ident := $fieldName:ident) =>
      let backingName := toString fieldName.getId
      match fields.find? (fun field => field.name == backingName) with
      | none =>
          throwErrorAt fieldName s!"role '{toString roleName.getId}' references unknown storage field '{backingName}'; known fields: {(fields.map (·.name)).toList}"
      | some field =>
          match roleKindOfStorageField? field with
          | some kind =>
              pure {
                ident := roleName
                name := toString roleName.getId
                fieldIdent := fieldName
                fieldName := backingName
                kind := kind
              }
          | none =>
              throwErrorAt fieldName s!"role '{toString roleName.getId}' uses unsupported backing field '{backingName}'; roles require an Address scalar field or Address→Uint256 mapping"
  | _ => throwErrorAt roleStx "invalid role declaration"

def parseContractSyntax
    (stx : Syntax)
    : CommandElabM ParsedContractSyntax := do
  match stx with
  | `(command| verity_contract $contractName:ident where $[types $[$newtypeDecls:verityNewtype]*]? $[inductive $[$adtDecls:verityAdtDecl]*]? $[$nsSpec:verityNamespaceSpec]? storage $[$storageItems:verityStorageItem]* $[roles $[$roleDecls:verityRoleDecl]*]? $[$structDecls:verityStructDecl]* $[errors $[$errorDecls:verityError]*]? $[event_defs $[$eventDecls:verityEvent]*]? $[constants $[$constantDecls:verityConstant]*]? $[immutables $[$immutableDecls:verityImmutable]*]? $[interfaces $[$interfaceDecls:verityInterface]*]? $[linked_externals $[$externalDecls:verityExternal]*]? $[$ctor:verityConstructor]? $[$entrypoints:veritySpecialEntrypoint]* $[$modifierDecls:verityModifier]* $[$functions:verityFunction]*) =>
      -- Parse newtypes first — they are needed by all downstream type resolution
      let parsedNewtypes ←
        match newtypeDecls with
        | some decls => decls.mapM parseNewtype
        | none => pure #[]
      -- Validate: no duplicate type names
      let mut seenNames : Array String := #[]
      for nt in parsedNewtypes do
        if seenNames.contains nt.name then
          throwErrorAt nt.ident s!"duplicate type name '{nt.name}'"
        seenNames := seenNames.push nt.name
      -- Validate: type names don't shadow built-in types
      let builtinTypeNames := #["Uint256", "Int256", "Uint8", "Address", "Bytes32", "Bool", "String", "Bytes", "Unit", "Array", "Tuple"]
      for nt in parsedNewtypes do
        if builtinTypeNames.contains nt.name then
          throwErrorAt nt.ident s!"type name '{nt.name}' shadows a built-in type"
      let mut parsedStructs : Array StructDecl := #[]
      for structStx in structDecls do
        let parsedStruct ← parseStructDecl parsedNewtypes parsedStructs structStx
        if seenNames.contains parsedStruct.name then
          throwErrorAt parsedStruct.ident s!"duplicate type name '{parsedStruct.name}'"
        if builtinTypeNames.contains parsedStruct.name then
          throwErrorAt parsedStruct.ident s!"struct name '{parsedStruct.name}' shadows a built-in type"
        seenNames := seenNames.push parsedStruct.name
        parsedStructs := parsedStructs.push parsedStruct
      -- Parse ADT declarations (#1727, Axis 1 Step 5a)
      let parsedAdts ←
        match adtDecls with
        | some decls => decls.mapM (parseAdtDecl parsedNewtypes)
        | none => pure #[]
      -- Validate: no duplicate ADT names
      for adtDecl in parsedAdts do
        if seenNames.contains adtDecl.name then
          throwErrorAt adtDecl.ident s!"duplicate type name '{adtDecl.name}'"
        seenNames := seenNames.push adtDecl.name
      -- Validate: ADT names don't shadow built-in types
      for adtDecl in parsedAdts do
        if builtinTypeNames.contains adtDecl.name then
          throwErrorAt adtDecl.ident s!"ADT name '{adtDecl.name}' shadows a built-in type"
      -- Compute the initial namespace offset (#1730, #1896).
      -- Explicit `storage_namespace` syntax wins. Otherwise
      -- `set_option verity.storageNamespace.default true` applies the stable
      -- contract-name namespace to all following fields until overridden by an
      -- in-storage `storage_namespace` item. Contract-level
      -- `storage_namespace legacy` opts out of the automatic policy.
      --
      -- `namespaceFromContractSpec` records whether the seed namespace came
      -- from a contract-level `storage_namespace` directive (authoritative)
      -- or from the opt-in auto-default policy (overridable by the first
      -- in-storage `storage_namespace` item encountered). The distinction
      -- matters for `spec.storageNamespace` / layout & trust reports: an
      -- in-storage ERC-7201 root that comes before any field should be the
      -- reported root, not the auto-default contract-name root.
      let namespaceOpt : Option Nat ←
        match nsSpec with
        | some spec => namespaceOffsetFromSpec contractName spec
        | none =>
            if (← defaultStorageNamespaceEnabled) then
              pure (some (computeStorageNamespace (toString contractName.getId)))
            else
              pure none
      let namespaceFromContractSpec : Bool := nsSpec.isSome
      let parsedErrors ←
        match errorDecls with
        | some decls => decls.mapM (parseError parsedNewtypes parsedStructs parsedAdts)
        | none => pure #[]
      let parsedEvents ←
        match eventDecls with
        | some decls => decls.mapM (parseEvent parsedNewtypes parsedStructs parsedAdts)
        | none => pure #[]
      let parsedConstants ←
        match constantDecls with
        | some decls => decls.mapM (parseConstant parsedNewtypes)
        | none => pure #[]
      let parsedImmutables ←
        match immutableDecls with
        | some decls => decls.mapM (parseImmutable parsedNewtypes)
        | none => pure #[]
      let parsedInterfaces ←
        match interfaceDecls with
        | some decls => decls.mapM (parseInterface parsedNewtypes parsedStructs parsedAdts)
        | none => pure #[]
      let seenTypeLocalNames := seenNames.map localDeclName
      let mut seenInterfaceNames : Array String := #[]
      for iface in parsedInterfaces do
        let ifaceLocalName := localDeclName iface.name
        if seenTypeLocalNames.contains ifaceLocalName then
          throwErrorAt iface.ident s!"interface name '{ifaceLocalName}' conflicts with an existing type name"
        if builtinTypeNames.contains ifaceLocalName then
          throwErrorAt iface.ident s!"interface name '{ifaceLocalName}' shadows a built-in type"
        if seenInterfaceNames.contains ifaceLocalName then
          throwErrorAt iface.ident s!"duplicate interface name '{ifaceLocalName}'"
        seenInterfaceNames := seenInterfaceNames.push ifaceLocalName
      let interfaceNames := parsedInterfaces.map (·.name)
      let parsedExternals ←
        match externalDecls with
        | some decls => decls.mapM (parseExternal parsedNewtypes parsedStructs parsedAdts)
        | none => pure #[]
      let parsedExternals := interfaceExternals parsedInterfaces ++ parsedExternals
      -- Apply namespace offsets to parsed storage fields (#1730).  In-storage
      -- `storage_namespace` items switch the active namespace for subsequent
      -- fields, allowing multiple ERC-7201 roots in one contract model.
      let mut parsedFields : Array StorageFieldDecl := #[]
      let mut parsedStorageStructAccessors : Array StorageStructAccessorDecl := #[]
      let mut currentNamespaceOffset := namespaceOpt.getD 0
      let mut firstNamespaceOpt := namespaceOpt
      -- An auto-default seed is provisional: if the storage block opens with
      -- an explicit `storage_namespace` directive (before any field has been
      -- recorded), that directive describes where the first declared field
      -- actually lives, so we replace the auto-default seed for reporting.
      -- A contract-level `storage_namespace` is authoritative and never
      -- overwritten here.
      let mut firstNamespaceLocked : Bool := namespaceFromContractSpec
      for item in storageItems do
        match (← namespaceOffsetFromStorageItem? contractName item) with
        | some offset =>
            currentNamespaceOffset := offset
            if !firstNamespaceLocked then
              firstNamespaceOpt := some offset
              firstNamespaceLocked := true
        | none =>
            match (← parseTransientStorageItem parsedNewtypes parsedStructs parsedAdts item) with
            | some field =>
                parsedFields := parsedFields.push { field with slotNum := field.slotNum + currentNamespaceOffset }
                firstNamespaceLocked := true
            | none =>
                match (← parseStorageStructItem parsedNewtypes parsedStructs parsedAdts item) with
                | some (structFields, accessor) =>
                    parsedFields := parsedFields ++
                      (structFields.map fun field => { field with slotNum := field.slotNum + currentNamespaceOffset })
                    parsedStorageStructAccessors := parsedStorageStructAccessors.push
                      { accessor with tree := offsetStorageAccessorTree currentNamespaceOffset accessor.tree }
                    -- A field has now been recorded under the active namespace; later
                    -- in-storage `storage_namespace` items must not retroactively
                    -- relabel where the first field lives.
                    firstNamespaceLocked := true
                | none =>
                    match (← storageFieldFromItem? item) with
                    | some fieldStx =>
                        let field ← parseStorageField parsedNewtypes parsedStructs parsedAdts fieldStx
                        parsedFields := parsedFields.push { field with slotNum := field.slotNum + currentNamespaceOffset }
                        firstNamespaceLocked := true
                    | none =>
                        throwErrorAt item "unsupported storage item"
      let parsedRoles ←
        match roleDecls with
        | some decls => decls.mapM (parseRoleDecl parsedFields)
        | none => pure #[]
      let mut seenRoleNames : Array String := #[]
      for role in parsedRoles do
        if seenRoleNames.contains role.name then
          throwErrorAt role.ident s!"duplicate role declaration '{role.name}'"
        seenRoleNames := seenRoleNames.push role.name
      pure {
        contractName := contractName
        newtypeDecls := parsedNewtypes
        structDecls := parsedStructs
        adtDecls := parsedAdts
        fields := parsedFields
        roleDecls := parsedRoles
        storageStructAccessors := parsedStorageStructAccessors
        errorDecls := parsedErrors
        eventDecls := parsedEvents
        constDecls := parsedConstants
        immutableDecls := parsedImmutables
        externalDecls := parsedExternals
        ctor := (← ctor.mapM (parseConstructor parsedNewtypes parsedStructs parsedAdts))
        modifiers := (← modifierDecls.mapM parseModifier)
        functions :=
          assignOverloadInternalIdents
            (← monomorphizeHigherOrderHelpers
              ((← entrypoints.mapM parseSpecialEntrypoint) ++
                (← functions.mapM (parseFunction parsedNewtypes parsedStructs parsedAdts interfaceNames))))
        storageNamespace := firstNamespaceOpt
      }
  | _ => throwErrorAt stx "invalid verity_contract declaration"

private def mkConstantDefCommand (constant : ConstantDecl) : CommandElabM Cmd := do
  `(command| def $constant.ident : $(← contractValueTypeTerm constant.ty) := $constant.body)

def mkStorageDefCommandPublic (field : StorageFieldDecl) : CommandElabM Cmd :=
  mkStorageDefCommand field

def mkConstantDefCommandPublic (constant : ConstantDecl) : CommandElabM Cmd :=
  mkConstantDefCommand constant

def mkStructDefCommandPublic (decl : StructDecl) : CommandElabM Cmd := do
  let structId := decl.ident
  let fieldIds := decl.fields.map (·.ident)
  let fieldTys ← decl.fields.mapM (fun field => contractValueTypeTerm field.ty)
  `(command| structure $structId where
      $[$fieldIds:ident : $fieldTys:term]*
      deriving Repr, Inhabited)

def mkStructEventArgInstanceCommandPublic (decl : StructDecl) : CommandElabM Cmd := do
  let structId := decl.ident
  `(command| instance : CoeTC $structId _root_.Contracts.EventArg where
      coe _ := _root_.Contracts.EventArg.word (pure (0 : _root_.Verity.Uint256)))

/-- Generate a `def storageNamespace : Nat := <keccak-value>` command for
    the current contract.  Uses the resolved namespace value from
    `parseContractSyntax` to respect custom `storage_namespace "key"`.
    (#1730, Axis 4 Step 4a) -/
def mkStorageNamespaceCommand (contractName : String) (resolvedNamespace : Option Nat := none) : CommandElabM Cmd := do
  let _ := contractName
  let ns := resolvedNamespace.getD 0
  let id : Ident := mkIdent (Name.mkSimple "storageNamespace")
  `(command| def $id : Nat := $(natTerm ns))

def validateConstantDeclsPublic (constDecls : Array ConstantDecl) : CommandElabM Unit := do
  for constant in constDecls do
    validateConstantBody constDecls constant.body [constant.name]
  validateConstantExprTypes constDecls

def validateGeneratedDefNamesPublic
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (functions : Array FunctionDecl) : CommandElabM Unit := do
  let reservedGeneratedNames : Array String := #["spec", "storageNamespace"]
  let mut generatedHelperNames : Array String := reservedGeneratedNames
  if hasStructMapping fields then
    generatedHelperNames := generatedHelperNames.push "structMember"
    generatedHelperNames := generatedHelperNames.push "setStructMember"
  if hasStructMapping2 fields then
    generatedHelperNames := generatedHelperNames.push "structMember2"
    generatedHelperNames := generatedHelperNames.push "setStructMember2"

  let mut storageNames : Array String := #[]
  for field in fields do
    if generatedHelperNames.contains field.name then
      throwErrorAt field.ident
        s!"storage field '{field.name}' conflicts with reserved generated declaration '{field.name}'"
    if storageNames.contains field.name then
      throwErrorAt field.ident s!"duplicate storage field declaration '{field.name}'"
    storageNames := storageNames.push field.name

  let mut constantNames : Array String := #[]
  for constant in constDecls do
    if generatedHelperNames.contains constant.name then
      throwErrorAt constant.ident
        s!"constant '{constant.name}' conflicts with reserved generated declaration '{constant.name}'"
    if storageNames.contains constant.name then
      throwErrorAt constant.ident
        s!"constant '{constant.name}' conflicts with a storage field of the same name"
    if constantNames.contains constant.name then
      throwErrorAt constant.ident
        s!"duplicate constant declaration '{constant.name}'"
    constantNames := constantNames.push constant.name

  let mut immutableNames : Array String := #[]
  for imm in immutableDecls do
    if generatedHelperNames.contains imm.name then
      throwErrorAt imm.ident
        s!"immutable '{imm.name}' conflicts with reserved generated declaration '{imm.name}'"
    immutableNames := immutableNames.push imm.name

  let mut functionNames : Array String := #[]
  let mut functionSignatures : Array String := #[]
  let mut functionAbiSignatures : Array String := #[]
  for fn in functions do
    let generatedFnName := toString fn.ident.getId
    let signature := functionSignatureKey fn
    let abiSignature := functionAbiSignatureKey fn
    if generatedHelperNames.contains fn.name then
      throwErrorAt fn.ident
        s!"function '{fn.name}' conflicts with reserved generated declaration '{fn.name}'"
    if storageNames.contains fn.name then
      throwErrorAt fn.ident
        s!"function '{fn.name}' conflicts with a storage field of the same name"
    if constantNames.contains fn.name then
      throwErrorAt fn.ident
        s!"function '{fn.name}' conflicts with a contract constant of the same name"
    if immutableNames.contains fn.name then
      throwErrorAt fn.ident
        s!"function '{fn.name}' conflicts with an immutable of the same name"
    if storageNames.contains generatedFnName then
      throwErrorAt fn.ident
        s!"function '{fn.name}' generates internal declaration '{generatedFnName}' that conflicts with a storage field of the same name"
    if constantNames.contains generatedFnName then
      throwErrorAt fn.ident
        s!"function '{fn.name}' generates internal declaration '{generatedFnName}' that conflicts with a contract constant of the same name"
    if immutableNames.contains generatedFnName then
      throwErrorAt fn.ident
        s!"function '{fn.name}' generates internal declaration '{generatedFnName}' that conflicts with an immutable of the same name"
    if generatedHelperNames.contains generatedFnName then
      throwErrorAt fn.ident
        s!"function '{fn.name}' generates internal declaration '{generatedFnName}' that conflicts with reserved generated declaration '{generatedFnName}'"
    if functionSignatures.contains signature then
      throwErrorAt fn.ident
        s!"duplicate function declaration '{signature}'"
    if functionAbiSignatures.contains abiSignature then
      throwErrorAt fn.ident
        s!"duplicate function ABI signature '{abiSignature}' after ABI erasure"
    if functionNames.contains generatedFnName then
      throwErrorAt fn.ident
        s!"function '{fn.name}' generates duplicate internal declaration '{generatedFnName}'"
    functionNames := functionNames.push generatedFnName
    functionSignatures := functionSignatures.push signature
    functionAbiSignatures := functionAbiSignatures.push abiSignature

    let helperNames :=
      #[ s!"{generatedFnName}_modelBody"
       , s!"{generatedFnName}_model"
       , s!"{generatedFnName}_bridge"
       , s!"{generatedFnName}_semantic_preservation"
       , s!"{generatedFnName}_is_view"
       , s!"{generatedFnName}_no_calls"
       , s!"{generatedFnName}_modifies"
       , s!"{generatedFnName}_frame"
       , s!"{generatedFnName}_frame_rfl"
       , s!"{generatedFnName}_effects"
       , s!"{generatedFnName}_cei_compliant"
       , s!"{generatedFnName}_nonreentrant"
       , s!"{generatedFnName}_cei_safe"
       , s!"{generatedFnName}_requires_role"
       , s!"{generatedFnName}_access_control"
       ]
    for helperName in helperNames do
      if storageNames.contains helperName then
        throwErrorAt fn.ident
          s!"function '{fn.name}' generates helper '{helperName}' that conflicts with a storage field of the same name"
      if constantNames.contains helperName then
        throwErrorAt fn.ident
          s!"function '{fn.name}' generates helper '{helperName}' that conflicts with a contract constant of the same name"
      if immutableNames.contains helperName then
        throwErrorAt fn.ident
          s!"function '{fn.name}' generates helper '{helperName}' that conflicts with an immutable of the same name"
      if functionNames.contains helperName then
        throwErrorAt fn.ident
          s!"function '{fn.name}' generates helper '{helperName}' that conflicts with a function of the same name"
      if generatedHelperNames.contains helperName then
        throwErrorAt fn.ident
          s!"function '{fn.name}' generates duplicate helper declaration '{helperName}'"
      generatedHelperNames := generatedHelperNames.push helperName

def validateImmutableDeclsPublic
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (ctor : Option ConstructorDecl := none) : CommandElabM Unit := do
  let mut seenNames : Array String := #[]
  let ctorParams := ctor.map (·.params) |>.getD #[]
  for imm in immutableDecls do
    validateImmutableType imm
    let inferredTy ← inferPureExprType fields constDecls #[] #[] ctorParams #[] imm.body
    requireDeclaredValueType imm.body s!"immutable '{imm.name}'" imm.ty inferredTy
    if fields.any (fun field => field.name == imm.name) then
      throwErrorAt imm.ident
        s!"immutable '{imm.name}' conflicts with a storage field of the same name"
    if constDecls.any (fun constant => constant.name == imm.name) then
      throwErrorAt imm.ident
        s!"immutable '{imm.name}' conflicts with a contract constant of the same name"
    if seenNames.contains imm.name then
      throwErrorAt imm.ident
        s!"duplicate immutable declaration '{imm.name}'"
    seenNames := seenNames.push imm.name

def validateExternalDeclsPublic
    (externalDecls : Array ExternalDecl) : CommandElabM Unit := do
  let mut seenNames : Array String := #[]
  for ext in externalDecls do
    if seenNames.contains ext.name then
      throwErrorAt ext.ident
        s!"duplicate external declaration '{ext.name}'"
    if ext.interfaceName?.isSome then
      -- Typed-interface externals: #1982 progress — static composites
      -- (tuples/fixed-arrays of word-likes) now accepted on params and
      -- returns. True dynamic shapes still rejected at declaration time
      -- (error points at #1982).
      requireTypedInterfaceStaticParams ext.ident ext.name ext.params
      requireTypedInterfaceStaticReturns ext.ident ext.name ext.returnTys
    else
      -- Multi-return externals are allowed; the auto-revert expression form (externalCall)
      -- only supports single-return, but tryExternalCall supports any return count.
      -- (#1727, Axis 1 Step 5f)
      for paramTy in ext.params do
        validateExternalExecutableParamType ext.ident ext.name paramTy
      for returnTy in ext.returnTys do
        validateExternalExecutableType ext.ident ext.name returnTy "return"
    seenNames := seenNames.push ext.name

private def validateLocalObligationDecls
    (owner : String)
    (obligations : Array LocalObligationDecl) : CommandElabM Unit := do
  let mut seenNames : Array String := #[]
  for obligation in obligations do
    if obligation.obligation.isEmpty then
      throwErrorAt obligation.ident
        s!"{owner} local obligation '{obligation.name}' must not be empty"
    if seenNames.contains obligation.name then
      throwErrorAt obligation.ident
        s!"duplicate local obligation '{obligation.name}' on {owner}"
    seenNames := seenNames.push obligation.name

def validateFunctionDeclsPublic
    (fields : Array StorageFieldDecl)
    (errorDecls : Array ErrorDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (externalDecls : Array ExternalDecl)
    (ctor : Option ConstructorDecl)
    (modifiers : Array ModifierDecl)
    (functions : Array FunctionDecl) : CommandElabM Unit := do
  match ctor with
  | some ctor =>
      for param in ctor.params do
        rejectExecutableBoundaryAdt param.ident s!"constructor parameter '{param.name}'" param.ty
      validateLocalObligationDecls "constructor" ctor.localObligations
      validateConstructorBodyExprTypes fields errorDecls constDecls immutableDecls externalDecls functions ctor
  | none => pure ()
  let modifierNames := modifiers.map (·.name)
  for modDecl in modifiers do
    match modDecl.body with
    | `(term| do $[$elems:doElem]*) =>
        let _ ← validateDoElemsExprTypes modDecl.name fields constDecls immutableDecls externalDecls errorDecls functions #[] #[] elems
        pure ()
    | _ => throwErrorAt modDecl.body "modifier body must be a do block"
  for fn in functions do
    for param in fn.params do
      rejectExecutableBoundaryAdt param.ident s!"function '{fn.name}' parameter '{param.name}'" param.ty
    rejectExecutableBoundaryAdt fn.ident s!"function '{fn.name}' return type" fn.returnTy
    if fn.isInternal then
      ensureSupportsInternalHelperSpec fn.ident.raw fn
    validateLocalObligationDecls s!"function '{fn.name}'" fn.localObligations
    for modifierIdent in fn.modifiers do
      let modifierName := toString modifierIdent.getId
      if !modifierNames.contains modifierName then
        throwErrorAt modifierIdent s!"function '{fn.name}' references unknown modifier '{modifierName}'"
    -- Validate modifies field names exist in the storage section
    for modField in fn.modifies do
      let modName := toString modField.getId
      let allFieldNames := fields.map (·.name)
      if !allFieldNames.contains modName then
        throwErrorAt modField s!"function '{fn.name}': modifies references unknown storage field '{modName}'; known fields: {allFieldNames.toList}"
    -- view functions must not use modifies (they already imply no writes)
    if fn.isView && !fn.modifies.isEmpty then
      throwErrorAt fn.ident s!"function '{fn.name}' is marked view and modifies(...); view already guarantees no state writes"
    if fn.isPure && !fn.modifies.isEmpty then
      throwErrorAt fn.ident s!"function '{fn.name}' is marked pure and modifies(...); pure already guarantees no state writes"
    -- Validate nonreentrant lock field references a valid storage field of scalar uint256 type.
    -- The transient-storage guard prologue is only injected for *external*
    -- entrypoints (see `Compiler.CompilationModel.Dispatch.attachNonReentrantGuard`,
    -- #1893), so an `internal` function carrying `nonreentrant(lock)` would
    -- be CEI-exempted at the compilation-model boundary without ever
    -- materialising a runtime guard. Reject that combination at parse time
    -- to fail closed.
    match fn.nonReentrantLock with
    | some lockField =>
        if fn.isInternal then
          throwErrorAt lockField s!"function '{fn.name}': nonreentrant(<lock>) is only supported on external entrypoints; the synthesised transient-storage guard runs at the dispatch boundary, so internal helpers cannot rely on it. Move the guard to the public caller or drop the annotation."
        let lockName := toString lockField.getId
        let allFieldNames := fields.map (·.name)
        match fields.find? (fun field => field.name == lockName) with
        | none =>
          throwErrorAt lockField s!"function '{fn.name}': nonreentrant references unknown storage field '{lockName}'; known fields: {allFieldNames.toList}"
        | some field =>
            match field.ty with
            | .scalar .uint256 => pure ()
            | _ =>
                throwErrorAt lockField s!"function '{fn.name}': nonreentrant lock field '{lockName}' must be a scalar Uint256 storage field"
    | none => pure ()
    -- cei_safe and allow_post_interaction_writes are mutually exclusive with nonreentrant
    if fn.ceiSafe && fn.allowPostInteractionWrites then
      throwErrorAt fn.ident s!"function '{fn.name}': cei_safe and allow_post_interaction_writes are mutually exclusive"
    if fn.nonReentrantLock.isSome && fn.allowPostInteractionWrites then
      throwErrorAt fn.ident s!"function '{fn.name}': nonreentrant and allow_post_interaction_writes are mutually exclusive"
    if fn.nonReentrantLock.isSome && fn.ceiSafe then
      throwErrorAt fn.ident s!"function '{fn.name}': nonreentrant and cei_safe are mutually exclusive"
    validateFunctionBodyExprTypes fields errorDecls constDecls immutableDecls externalDecls functions fn

def mkFunctionCommandsPublic
    (fields : Array StorageFieldDecl)
    (roleDecls : Array RoleDecl)
    (errorDecls : Array ErrorDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (externalDecls : Array ExternalDecl)
    (functions : Array FunctionDecl)
    (fn : FunctionDecl) : CommandElabM (Array Cmd) := do
  let fnType ← mkContractFnType fn.params fn.returnTy
  let fnRoleGuardedBody ← mkRoleGuardedBody fields roleDecls fn
  let fnDecl := { fn with body := fnRoleGuardedBody }
  let fnGuardedBody ← mkInitGuardedBody fields fnDecl
  let fnBody ← mkImmutableBoundBody fields immutableDecls fn fnGuardedBody
  let fnExecutableBody ← rewriteForEachExecutableBody externalDecls fn.params fnBody
  let fnValue ← mkContractFnValue fn.params fnExecutableBody
  let modelBodyName ← mkSuffixedIdent fn.ident "_modelBody"
  let modelName ← mkSuffixedIdent fn.ident "_model"
  let stmtTerms ← translateBodyToStmtTerms fields roleDecls errorDecls constDecls immutableDecls externalDecls functions fn
  let modelParams ← mkModelParamsTerm fn.params
  let localObligationTerms ← (functionLocalObligationsWithArithmetic fn).mapM mkModelLocalObligationTerm
  let payableTerm ← if fn.isPayable then `(true) else `(false)
  let viewTerm ← if fn.isView then `(true) else `(false)
  let pureTerm ← if fn.isPure then `(true) else `(false)
  let noExternalCallsTerm ← if fn.noExternalCalls then `(true) else `(false)
  let allowPostInteractionWritesTerm ← if fn.allowPostInteractionWrites then `(true) else `(false)
  let nonReentrantLockTerm ← match fn.nonReentrantLock with
    | some lockIdent => `(some $(strTerm (toString lockIdent.getId)))
    | none => `(none)
  let ceiSafeTerm ← if fn.ceiSafe then `(true) else `(false)
  let reentrancyTrustedTerm ← if fn.reentrancyTrusted then `(true) else `(false)
  let requiresRoleTerm ← match fn.requiresRole with
    | some roleIdent => `(some $(strTerm (toString roleIdent.getId)))
    | none => `(none)
  let modifiesTerms : Array Term := fn.modifies.map fun ident => strTerm (toString ident.getId)
  let returnTypeTerm ← modelReturnTypeTerm fn.returnTy
  let returnsTerm ← modelReturnsTerm fn.returnTy

  let fnCmd : Cmd ← `(command| def $fn.ident : $fnType := $fnValue)
  let bodyCmd : Cmd ← `(command| def $modelBodyName : List Compiler.CompilationModel.Stmt := [ $[$stmtTerms],* ])
  let modelNameTerm :=
    if fn.isInternal then
      strTerm (internalHelperSpecNameFor fn)
    else
      strTerm fn.name
  let internalTerm ← if fn.isInternal then `(true) else `(false)
  let modelCmd : Cmd ← `(command| def $modelName : Compiler.CompilationModel.FunctionSpec := {
    name := $modelNameTerm
    params := $modelParams
    returnType := $returnTypeTerm
    «returns» := $returnsTerm
    isPayable := $payableTerm
    isView := $viewTerm
    isPure := $pureTerm
    noExternalCalls := $noExternalCallsTerm
    allowPostInteractionWrites := $allowPostInteractionWritesTerm
    nonReentrantLock := $nonReentrantLockTerm
    ceiSafe := $ceiSafeTerm
    reentrancyTrusted := $reentrancyTrustedTerm
    requiresRole := $requiresRoleTerm
    modifies := [ $[$modifiesTerms],* ]
    localObligations := [ $[$localObligationTerms],* ]
    body := $modelBodyName
    isInternal := $internalTerm
  })
  pure #[fnCmd, bodyCmd, modelCmd]

def mkSpecCommandPublic
    (contractName : String)
    (fields : Array StorageFieldDecl)
    (roleDecls : Array RoleDecl)
    (errorDecls : Array ErrorDecl)
    (eventDecls : Array EventDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (externalDecls : Array ExternalDecl)
    (ctor : Option ConstructorDecl)
    (modifiers : Array ModifierDecl)
    (functions : Array FunctionDecl)
    (adtDecls : Array AdtDecl)
    (storageNamespace : Option Nat) : CommandElabM Cmd :=
  mkSpecCommand contractName fields roleDecls errorDecls eventDecls constDecls immutableDecls externalDecls ctor modifiers functions adtDecls storageNamespace

def mkFindIdxFieldSimpCommandsPublic
    (contractIdent : Ident)
    (fields : Array StorageFieldDecl) : CommandElabM (Array Cmd) :=
  mkFindIdxFieldSimpCommands contractIdent fields

def mkFindIdxParamSimpCommandsPublic
    (contractIdent : Ident)
    (ctor : Option ConstructorDecl)
    (functions : Array FunctionDecl) : CommandElabM (Array Cmd) :=
  mkFindIdxParamSimpCommands contractIdent ctor functions

/-- Public wrapper for `contractValueTypeTerm`, used by the semantic bridge
    theorem generator in `Bridge.lean` (Issue #998). -/
def contractValueTypeTermPublic (ty : ValueType) : CommandElabM Term :=
  contractValueTypeTerm ty

/-- Public wrapper for `strTerm`, used by the semantic bridge
    theorem generator in `Bridge.lean` (Issue #998). -/
def strTermPublic (s : String) : Term := strTerm s

/-- Public wrapper for `natTerm`, used by the semantic bridge
    theorem generator in `Bridge.lean` (Issue #998). -/
def natTermPublic (n : Nat) : Term := natTerm n

end Verity.Macro

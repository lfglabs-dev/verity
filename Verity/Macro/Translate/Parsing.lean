import Lean
import Verity.Macro.ExternalCalls
import Verity.Macro.Storage
import Verity.Macro.Types
import Verity.Macro.Syntax

namespace Verity.Macro

open Lean
open Lean.Elab
open Lean.Elab.Command

set_option hygiene false

def parseStorageField (newtypes : Array NewtypeDecl) (structDecls : Array StructDecl := #[]) (adtDecls : Array AdtDecl := #[]) (stx : Syntax) : CommandElabM StorageFieldDecl := do
  match stx with
  | `(verityStorageField| $name:ident : $ty:term := slot $slotNum:num) =>
      let parsedTy ← storageTypeFromSyntax newtypes structDecls adtDecls ty
      let adtInfo? :=
        match parsedTy with
        | .scalar (.adt adtName maxFields) => some (adtName, maxFields)
        | _ => none
      pure {
        ident := name
        name := toString name.getId
        ty := parsedTy
        slotNum := ← natFromSyntax slotNum
        adtInfo? := adtInfo?
      }
  | _ => throwErrorAt stx "invalid storage field declaration"

private def narrowStorageWidth? : StorageType → Option Nat
  | .scalar .uint16 => some 16
  | .scalar (.uintN bits) => some bits
  | .scalar (.newtype _ base) => narrowStorageWidth? (.scalar base)
  | _ => none

/-- Assign Solidity-compatible least-significant-first offsets to consecutive
    narrow declarations sharing the same explicit base-slot anchor. -/
def applyAutomaticPackedLayout (fields : Array StorageFieldDecl) : Array StorageFieldDecl := Id.run do
  let mut out := #[]
  let mut anchor? : Option Nat := none
  let mut currentSlot := 0
  let mut offset := 0
  for field in fields do
    match narrowStorageWidth? field.ty with
    | some width =>
        let sameAnchor := anchor? == some field.slotNum &&
          out.back?.any (fun previous => previous.isTransient == field.isTransient)
        let nextOffset := if sameAnchor then offset else 0
        let (resolvedSlot, bitOffset) :=
          if nextOffset + width <= 256 then
            (if sameAnchor then currentSlot else field.slotNum, nextOffset)
          else (currentSlot + 1, 0)
        out := out.push { field with slotNum := resolvedSlot, packedBits := some (bitOffset, width) }
        anchor? := some field.slotNum
        currentSlot := resolvedSlot
        offset := bitOffset + width
    | none =>
        out := out.push field
        anchor? := none
        offset := 0
  return out

def parseTransientStorageItem (newtypes : Array NewtypeDecl) (structDecls : Array StructDecl := #[]) (adtDecls : Array AdtDecl := #[])
    (stx : TSyntax `verityStorageItem) : CommandElabM (Option StorageFieldDecl) := do
  match stx with
  | `(verityStorageItem| transient $name:ident : $ty:term := slot $slotNum:num) =>
      let parsedTy ← storageTypeFromSyntax newtypes structDecls adtDecls ty
      let adtInfo? :=
        match parsedTy with
        | .scalar (.adt adtName maxFields) => some (adtName, maxFields)
        | _ => none
      pure <| some {
        ident := name
        name := toString name.getId
        ty := parsedTy
        slotNum := ← natFromSyntax slotNum
        isTransient := true
        adtInfo? := adtInfo?
      }
  | _ => pure none

def pathFieldName (parts : List String) : String :=
  String.intercalate "." parts

def pathFieldModelName (parts : List String) : String :=
  String.intercalate "_" parts

def pathFieldIdent (root : Ident) (parts : List String) : Ident :=
  mkIdentFrom root (Name.mkSimple (pathFieldModelName parts))

partial def parseStorageStructMember
    (newtypes : Array NewtypeDecl)
    (structDecls : Array StructDecl := #[])
    (adtDecls : Array AdtDecl := #[])
    (rootIdent : Ident)
    (pathPrefix : List String)
    (baseSlot : Nat)
    (stx : TSyntax `verityStorageStructMember) :
    CommandElabM (Array StorageFieldDecl × StorageAccessorTree) := do
  let leafDecl (name : Ident) (ty : Term) (wordOffset : TSyntax `num)
      (packed : Option (TSyntax `num × TSyntax `num)) := do
    let localName := toString name.getId
    let parts := pathPrefix ++ [localName]
    let parsedTy ← storageTypeFromSyntax newtypes structDecls adtDecls ty
    let packedBits ←
      match packed with
      | none => pure none
      | some (offset, width) => pure (some (← natFromSyntax offset, ← natFromSyntax width))
    let slotNum := baseSlot + (← natFromSyntax wordOffset)
    let field : StorageFieldDecl := {
      ident := pathFieldIdent rootIdent parts
      name := pathFieldModelName parts
      ty := parsedTy
      slotNum := slotNum
      adtInfo? :=
        match parsedTy with
        | .scalar (.adt adtName maxFields) => some (adtName, maxFields)
        | _ => none
      packedBits := packedBits
      emitDef := false
      aliases := [pathFieldName parts]
    }
    pure (#[field], StorageAccessorTree.leaf localName parsedTy slotNum)
  match stx with
  | `(verityStorageStructMember| $name:ident : $ty:term @word $wordOffset:num) =>
      leafDecl name ty wordOffset none
  | `(verityStorageStructMember| $name:ident : $ty:term @word $wordOffset:num packed($offset:num,$width:num)) =>
      leafDecl name ty wordOffset (some (offset, width))
  | `(verityStorageStructMember| $name:ident : StorageStruct [ $[$members:verityStorageStructMember],* ] @word $wordOffset:num) =>
      let localName := toString name.getId
      let childBase := baseSlot + (← natFromSyntax wordOffset)
      let childPrefix := pathPrefix ++ [localName]
      let mut fields : Array StorageFieldDecl := #[]
      let mut children : Array StorageAccessorTree := #[]
      for member in members do
        let (memberFields, memberTree) ← parseStorageStructMember newtypes structDecls adtDecls rootIdent childPrefix childBase member
        fields := fields ++ memberFields
        children := children.push memberTree
      pure (fields, StorageAccessorTree.node localName children)
  | _ => throwErrorAt stx "invalid storage struct member declaration"

def parseStorageStructItem
    (newtypes : Array NewtypeDecl)
    (structDecls : Array StructDecl := #[])
    (adtDecls : Array AdtDecl := #[])
    (stx : TSyntax `verityStorageItem) :
    CommandElabM (Option (Array StorageFieldDecl × StorageStructAccessorDecl)) := do
  match stx with
  | `(verityStorageItem| $name:ident : StorageStruct [ $[$members:verityStorageStructMember],* ] := slot $slotNum:num) =>
      let rootName := toString name.getId
      let baseSlot ← natFromSyntax slotNum
      let mut fields : Array StorageFieldDecl := #[]
      let mut children : Array StorageAccessorTree := #[]
      for member in members do
        let (memberFields, memberTree) ← parseStorageStructMember newtypes structDecls adtDecls name [rootName] baseSlot member
        fields := fields ++ memberFields
        children := children.push memberTree
      pure (some (fields, {
        ident := name
        name := rootName
        tree := StorageAccessorTree.node rootName children
      }))
  | _ => pure none

def parseParam (newtypes : Array NewtypeDecl) (structDecls : Array StructDecl) (adtDecls : Array AdtDecl) (stx : Syntax) : CommandElabM ParamDecl := do
  match stx with
  | `(verityParam| $name:ident : $ty:term) =>
      pure {
        ident := name
        name := toString name.getId
        ty := ← valueTypeFromSyntax newtypes structDecls adtDecls ty
      }
  | _ => throwErrorAt stx "invalid parameter declaration"

def localDeclName (name : String) : String :=
  (name.splitOn ".").getLastD name

/-- Like `parseParam`, but additionally recognizes a higher-order
    function-pointer parameter type (e.g. `op : (Uint256) -> Uint256`) and
    records it as `ParamDecl.funcPtr?` instead of rejecting it (#1747).  Used
    only for regular `function` helpers; struct/ADT/event/constructor parameters
    still go through `parseParam`, which rejects function types at the boundary. -/
def parseFunctionParam (newtypes : Array NewtypeDecl) (structDecls : Array StructDecl) (adtDecls : Array AdtDecl) (stx : Syntax) : CommandElabM ParamDecl := do
  match stx with
  | `(verityParam| $name:ident : $ty:term) => do
      let (arrowArgs, arrowResult) ← collectArrowChainTypes (stripParens ty)
      if arrowArgs.isEmpty then
        pure {
          ident := name
          name := toString name.getId
          ty := ← valueTypeFromSyntax newtypes structDecls adtDecls ty
        }
      else
        -- Higher-order function-pointer parameter; validate the component types
        -- for diagnostics, then mark it for the monomorphization pre-pass.
        let paramTys ← arrowArgs.mapM (fun a =>
          valueTypeFromSyntax newtypes structDecls adtDecls (stripParens a))
        let returnTy ← valueTypeFromSyntax newtypes structDecls adtDecls arrowResult
        pure {
          ident := name
          name := toString name.getId
          ty := .unit
          funcPtr? := some { paramTys := paramTys.toArray, returnTy := returnTy }
        }
  | _ => throwErrorAt stx "invalid parameter declaration"

def parseFunctionParamWithInterfaces
    (newtypes : Array NewtypeDecl)
    (structDecls : Array StructDecl)
    (adtDecls : Array AdtDecl)
    (interfaceNames : Array String)
    (stx : Syntax) : CommandElabM ParamDecl := do
  match stx with
  | `(verityParam| $name:ident : $ty:term) =>
      match stripParens ty with
      | `(term| $interfaceIdent:ident) =>
          let interfaceName := toString interfaceIdent.getId
          if interfaceNames.contains interfaceName then
            let typeLocalNames :=
              (newtypes.map (fun decl => localDeclName decl.name)) ++
              (structDecls.map (fun decl => localDeclName decl.name)) ++
              (adtDecls.map (fun decl => localDeclName decl.name))
            if typeLocalNames.contains (localDeclName interfaceName) then
              throwErrorAt interfaceIdent
                s!"interface name '{localDeclName interfaceName}' conflicts with an existing type name"
            pure {
              ident := name
              name := toString name.getId
              ty := .address
              interfaceName? := some interfaceName
            }
          else
            parseFunctionParam newtypes structDecls adtDecls stx
      | _ => parseFunctionParam newtypes structDecls adtDecls stx
  | _ => throwErrorAt stx "invalid parameter declaration"

def parseNewtype (stx : Syntax) : CommandElabM NewtypeDecl := do
  match stx with
  | `(verityNewtype| $name:ident : $ty:term) =>
      let baseType ← valueTypeFromSyntax #[] #[] #[] ty
      -- Validate: newtypes must be based on scalar types (not arrays, tuples, or unit)
      match baseType with
      | .array _ => throwErrorAt ty "newtype base type must be a scalar type, not an array"
      | .tuple _ => throwErrorAt ty "newtype base type must be a scalar type, not a tuple"
      | .unit => throwErrorAt ty "newtype base type must be a scalar type, not Unit"
      | _ => pure ()
      pure {
        ident := name
        name := toString name.getId
        baseType := baseType
      }
  | _ => throwErrorAt stx "invalid type declaration"

def parseStructDecl (newtypes : Array NewtypeDecl) (structDecls : Array StructDecl) (stx : Syntax) : CommandElabM StructDecl := do
  match stx with
  | `(verityStructDecl| struct $name:ident where $[$fields:verityParam],*) =>
      let parsedFields ← fields.mapM (parseParam newtypes structDecls #[])
      if parsedFields.isEmpty then
        throwErrorAt name s!"struct '{toString name.getId}' must have at least one field"
      let mut seenFieldNames : Array String := #[]
      for field in parsedFields do
        if seenFieldNames.contains field.name then
          throwErrorAt field.ident s!"duplicate field '{field.name}' in struct '{toString name.getId}'"
        seenFieldNames := seenFieldNames.push field.name
      pure { ident := name, name := toString name.getId, fields := parsedFields }
  | _ => throwErrorAt stx "invalid struct declaration"

/-- Parse a single ADT variant: `| Name(field1 : Type1, field2 : Type2)` or `| Name`.
    (#1727, Axis 1 Step 5a) -/
def parseAdtVariant (newtypes : Array NewtypeDecl) (stx : Syntax) : CommandElabM AdtVariantDecl := do
  match stx with
  | `(verityAdtVariant| | $name:ident ($[$params:verityParam],*)) =>
      let parsedParams ← params.mapM (parseParam newtypes #[] #[])
      pure { ident := name, name := toString name.getId, fields := parsedParams }
  | `(verityAdtVariant| | $name:ident) =>
      pure { ident := name, name := toString name.getId, fields := #[] }
  | _ => throwErrorAt stx "invalid ADT variant declaration"

/-- Parse a full ADT declaration: `Name := | Variant1(...) | Variant2(...)`.
    (#1727, Axis 1 Step 5a) -/
def parseAdtDecl (newtypes : Array NewtypeDecl) (stx : Syntax) : CommandElabM AdtDecl := do
  match stx with
  | `(verityAdtDecl| $name:ident := $[$variants:verityAdtVariant]*) =>
      let parsedVariants ← variants.mapM (parseAdtVariant newtypes)
      if parsedVariants.isEmpty then
        throwErrorAt name s!"ADT '{toString name.getId}' must have at least one variant"
      if parsedVariants.size > 256 then
        throwErrorAt name
          s!"ADT '{toString name.getId}' has {parsedVariants.size} variants, but ADT tags are encoded as Uint8 and support at most 256 variants"
      -- Validate: no duplicate variant names within this ADT
      let mut seenVariantNames : Array String := #[]
      for v in parsedVariants do
        if seenVariantNames.contains v.name then
          throwErrorAt v.ident s!"duplicate variant name '{v.name}' in ADT '{toString name.getId}'"
        seenVariantNames := seenVariantNames.push v.name
      pure { ident := name, name := toString name.getId, variants := parsedVariants }
  | _ => throwErrorAt stx "invalid ADT declaration"

def parseError (newtypes : Array NewtypeDecl) (structDecls : Array StructDecl) (adtDecls : Array AdtDecl) (stx : Syntax) : CommandElabM ErrorDecl := do
  match stx with
  | `(verityError| error $name:ident ($[$params:term],*)) =>
      pure {
        ident := name
        name := toString name.getId
        params := ← params.mapM (valueTypeFromSyntax newtypes structDecls adtDecls)
      }
  | _ => throwErrorAt stx "invalid custom error declaration"

def parseEventParam
    (newtypes : Array NewtypeDecl)
    (structDecls : Array StructDecl)
    (adtDecls : Array AdtDecl)
    (stx : Syntax) : CommandElabM EventParamDecl := do
  match stx with
  | `(verityEventParam| $name:ident : $ty:term) =>
      pure {
        ident := name
        name := toString name.getId
        ty := ← valueTypeFromSyntax newtypes structDecls adtDecls ty
        isIndexed := false
      }
  | `(verityEventParam| @indexed $name:ident : $ty:term) =>
      pure {
        ident := name
        name := toString name.getId
        ty := ← valueTypeFromSyntax newtypes structDecls adtDecls ty
        isIndexed := true
      }
  | _ => throwErrorAt stx "invalid event parameter declaration"

def parseEvent
    (newtypes : Array NewtypeDecl)
    (structDecls : Array StructDecl)
    (adtDecls : Array AdtDecl)
    (stx : Syntax) : CommandElabM EventDecl := do
  match stx with
  | `(verityEvent| event $name:ident ($[$params:verityEventParam],*)) =>
      pure {
        ident := name
        name := toString name.getId
        params := ← params.mapM (parseEventParam newtypes structDecls adtDecls)
      }
  | _ => throwErrorAt stx "invalid event declaration"

def parseConstant (newtypes : Array NewtypeDecl) (stx : Syntax) : CommandElabM ConstantDecl := do
  match stx with
  | `(verityConstant| $name:ident : $ty:term := $body:term) =>
      pure {
        ident := name
        name := toString name.getId
        ty := ← valueTypeFromSyntax newtypes #[] #[] ty
        body := body
      }
  | _ => throwErrorAt stx "invalid constant declaration"

def parseImmutable (newtypes : Array NewtypeDecl) (stx : Syntax) : CommandElabM ImmutableDecl := do
  match stx with
  | `(verityImmutable| $name:ident : $ty:term := $body:term) =>
      pure {
        ident := name
        name := toString name.getId
        ty := ← valueTypeFromSyntax newtypes #[] #[] ty
        body := body
      }
  | _ => throwErrorAt stx "invalid immutable declaration"

def parseProofStatusIdent (stx : Syntax) : CommandElabM Compiler.ProofStatus := do
  match stx with
  | .ident _ raw _ _ =>
      match raw.toString with
      | "proved" => pure .proved
      | "assumed" => pure .assumed
      | "unchecked" => pure .unchecked
      | other =>
          throwErrorAt stx s!"unsupported proof status '{other}'; expected proved, assumed, or unchecked"
  | _ => throwErrorAt stx "expected proof status identifier"

def parseLocalObligation (stx : Syntax) : CommandElabM LocalObligationDecl := do
  match stx with
  | `(verityLocalObligation| $name:ident := $status:ident $obligation:str) =>
      pure {
        ident := name
        name := toString name.getId
        obligation := obligation.getString
        proofStatus := ← parseProofStatusIdent status
      }
  | _ => throwErrorAt stx "invalid local obligation declaration"

structure ParsedMutability where
  isPayable : Bool := false
  isView : Bool := false
  isPure : Bool := false
  isInternal : Bool := false
  noExternalCalls : Bool := false
  allowPostInteractionWrites : Bool := false
  nonReentrantLock : Option Ident := none
  ceiSafe : Bool := false
  reentrancyTrusted : Bool := false

def parseMutabilityModifiers
    (mods : Array (TSyntax `verityMutability))
    (stx : Syntax) : CommandElabM ParsedMutability := do
  let mut result : ParsedMutability := {}
  for mod in mods do
    match mod with
    | `(verityMutability| payable) =>
        if result.isPayable then
          throwErrorAt mod "duplicate 'payable' modifier"
        result := { result with isPayable := true }
    | `(verityMutability| view) =>
        if result.isView then
          throwErrorAt mod "duplicate 'view' modifier"
        result := { result with isView := true }
    | `(verityMutability| internal) =>
        if result.isInternal then
          throwErrorAt mod "duplicate 'internal' modifier"
        result := { result with isInternal := true }
    | `(verityMutability| no_external_calls) =>
        if result.noExternalCalls then
          throwErrorAt mod "duplicate 'no_external_calls' modifier"
        result := { result with noExternalCalls := true }
    | `(verityMutability| allow_post_interaction_writes) =>
        if result.allowPostInteractionWrites then
          throwErrorAt mod "duplicate 'allow_post_interaction_writes' modifier"
        result := { result with allowPostInteractionWrites := true }
    | `(verityMutability| nonreentrant($field:ident)) =>
        if result.nonReentrantLock.isSome then
          throwErrorAt mod "duplicate 'nonreentrant' modifier"
        result := { result with nonReentrantLock := some field }
    | `(verityMutability| cei_safe) =>
        if result.ceiSafe then
          throwErrorAt mod "duplicate 'cei_safe' modifier"
        result := { result with ceiSafe := true }
    | `(verityMutability| reentrancy_trusted) =>
        if result.reentrancyTrusted then
          throwErrorAt mod "duplicate 'reentrancy_trusted' modifier"
        result := { result with reentrancyTrusted := true }
    | _ => throwErrorAt stx "invalid function mutability modifier"
  pure result

def parseModifies (stx : TSyntax `verityModifies) : CommandElabM (Array Ident) := do
  match stx with
  | `(verityModifies| modifies($[$fields:ident],*)) =>
      let result := fields
      -- Check for duplicates
      let mut seen : Array String := #[]
      for f in result do
        let s := toString f.getId
        if seen.contains s then
          throwErrorAt f s!"duplicate field '{s}' in modifies annotation"
        seen := seen.push s
      pure result
  | _ => throwErrorAt stx "invalid modifies annotation"

def parseInitGuard (stx : TSyntax `verityInitGuard) : CommandElabM InitGuardDecl := do
  match stx with
  | `(verityInitGuard| initializer($field:ident)) =>
      pure (.initializer field (toString field.getId))
  | `(verityInitGuard| reinitializer($field:ident, $version:num)) => do
      let versionNat ← natFromSyntax version
      if versionNat == 0 then
        throwErrorAt version "reinitializer version must be greater than 0"
      pure (.reinitializer field (toString field.getId) versionNat)
  | _ => throwErrorAt stx "invalid initializer guard"

def parseLocalObligations
    (stx : TSyntax `verityLocalObligations) : CommandElabM (Array LocalObligationDecl) := do
  match stx with
  | `(verityLocalObligations| local_obligations [ $[$obligations:verityLocalObligation],* ]) =>
      obligations.mapM parseLocalObligation
  | _ => throwErrorAt stx "invalid local obligations declaration"

def hiddenEntrypointIdent (name : String) : Ident :=
  mkIdent (Name.mkSimple s!"__verity_{name}")

def modifierInternalName (name : String) : String :=
  s!"__modifier_{name}"

def parseSpecialEntrypoint (stx : Syntax) : CommandElabM FunctionDecl := do
  match stx with
  | `(veritySpecialEntrypoint| receive $[$localObligations?:verityLocalObligations]? := $body:term) => do
      let parsedLocalObligations ←
        match localObligations? with
        | some obligations => parseLocalObligations obligations
        | none => pure #[]
      pure {
        ident := hiddenEntrypointIdent "receive"
        name := "receive"
        params := #[]
        returnTy := .unit
        isPayable := true
        localObligations := parsedLocalObligations
        body := body
      }
  | `(veritySpecialEntrypoint| fallback $[$localObligations?:verityLocalObligations]? := $body:term) => do
      let parsedLocalObligations ←
        match localObligations? with
        | some obligations => parseLocalObligations obligations
        | none => pure #[]
      pure {
        ident := hiddenEntrypointIdent "fallback"
        name := "fallback"
        params := #[]
        returnTy := .unit
        localObligations := parsedLocalObligations
        body := body
      }
  | _ => throwErrorAt stx "invalid special entrypoint declaration"

def parseModifier (stx : Syntax) : CommandElabM ModifierDecl := do
  match stx with
  | `(verityModifier| modifier $name:ident := $body:term) =>
      pure { ident := name, name := toString name.getId, body := body }
  | _ => throwErrorAt stx "invalid modifier declaration"

def parseModifierUse (stx : TSyntax `verityModifierUse) : CommandElabM (Array Ident) := do
  match stx with
  | `(verityModifierUse| with $[$names:ident],*) => pure names
  | _ => throwErrorAt stx "invalid modifier use"

def parseFunction (newtypes : Array NewtypeDecl) (structDecls : Array StructDecl := #[]) (adtDecls : Array AdtDecl := #[]) (interfaceNames : Array String := #[]) (stx : Syntax) : CommandElabM FunctionDecl := do
  match stx with
  | `(verityFunction| function $[$modsBefore:verityMutability]* $[$pureMod?:pureMutabilityMarker]? $[$modsAfter:verityMutability]* $name:ident ($[$params:verityParam],*) $[$guard?:verityInitGuard]? $[$modifierUse?:verityModifierUse]? $[$requiresRoleClause?:verityRequiresRole]? $[$modifiesClause?:verityModifies]? $[$localObligations?:verityLocalObligations]? : $retTy:term := $body:term) => do
      let mut_ ← parseMutabilityModifiers (modsBefore ++ modsAfter) stx
      let mut_ := { mut_ with isPure := pureMod?.isSome }
      let parsedParams ← params.mapM (parseFunctionParamWithInterfaces newtypes structDecls adtDecls interfaceNames)
      let parsedReturnTy ← valueTypeFromSyntax newtypes structDecls adtDecls retTy
      let parsedGuard? ←
        match guard? with
        | some guard => pure (some (← parseInitGuard guard))
        | none => pure none
      let parsedRequiresRole ←
        match requiresRoleClause? with
        | some roleClause =>
            match roleClause with
            | `(verityRequiresRole| requires($roleField:ident)) => pure (some roleField)
            | _ => throwErrorAt roleClause "invalid requires annotation"
        | none => pure none
      let parsedModifies ←
        match modifiesClause? with
        | some modClause => parseModifies modClause
        | none => pure #[]
      let parsedModifiers ←
        match modifierUse? with
        | some modUse => parseModifierUse modUse
        | none => pure #[]
      let parsedLocalObligations ←
        match localObligations? with
        | some obligations => parseLocalObligations obligations
        | none => pure #[]
      pure {
        ident := name
        name := toString name.getId
        params := parsedParams
        returnTy := parsedReturnTy
        isPayable := mut_.isPayable
        isView := mut_.isView
        isPure := mut_.isPure
        isInternal := mut_.isInternal
        noExternalCalls := mut_.noExternalCalls
        allowPostInteractionWrites := mut_.allowPostInteractionWrites
        nonReentrantLock := mut_.nonReentrantLock
        ceiSafe := mut_.ceiSafe
        reentrancyTrusted := mut_.reentrancyTrusted
        requiresRole := parsedRequiresRole
        initGuard? := parsedGuard?
        modifies := parsedModifies
        localObligations := parsedLocalObligations
        modifiers := parsedModifiers
        body := body
      }
  | _ => throwErrorAt stx "invalid function declaration"

def parseConstructor (newtypes : Array NewtypeDecl) (structDecls : Array StructDecl := #[]) (adtDecls : Array AdtDecl := #[]) (stx : Syntax) : CommandElabM ConstructorDecl := do
  match stx with
  | `(verityConstructor| constructor ($[$params:verityParam],*) payable local_obligations [ $[$obligations:verityLocalObligation],* ] := $body:term) =>
      pure {
        params := ← params.mapM (parseParam newtypes structDecls adtDecls)
        isPayable := true
        localObligations := ← obligations.mapM parseLocalObligation
        body := body
      }
  | `(verityConstructor| constructor ($[$params:verityParam],*) payable := $body:term) =>
      pure {
        params := ← params.mapM (parseParam newtypes structDecls adtDecls)
        isPayable := true
        body := body
      }
  | `(verityConstructor| constructor ($[$params:verityParam],*) local_obligations [ $[$obligations:verityLocalObligation],* ] := $body:term) =>
      pure {
        params := ← params.mapM (parseParam newtypes structDecls adtDecls)
        localObligations := ← obligations.mapM parseLocalObligation
        body := body
      }
  | `(verityConstructor| constructor ($[$params:verityParam],*) := $body:term) =>
      pure {
        params := ← params.mapM (parseParam newtypes structDecls adtDecls)
        body := body
      }
  | _ => throwErrorAt stx "invalid constructor declaration"


end Verity.Macro

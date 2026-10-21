import Lean
import Compiler.SolidityImport.ExprHelpers

open Lean Meta Elab Command

namespace Compiler.CompilationModel.SolidityImport

/-!
# Solidity Import Storage & Struct Layout Helpers

Extracted storage-path qualification, struct layout decoding, dynamic storage array
slot arithmetic, and struct mapping slot helpers for the Solidity frontend importer,
accompanied by a 3-layer `StorageLayoutMetaSpec` specification bundle.
-/

def rawStorageFieldName : String := "_verity_raw_storage"

def topStructMemberFieldName (field member : String) : String :=
  let cleanMember := String.intercalate "__" (member.splitOn ".")
  s!"_verity_struct_{field}_{cleanMember}"

def splitSPathField (raw : String) : String × String :=
  match raw.splitOn "::" with
  | [f, p] => (f, p)
  | _ => (raw, "")

def qualifySPathMember (subPrefix member : String) : String :=
  if subPrefix == "" then member else s!"{subPrefix}.{member}"

def appendSPathSub (path : SPath) (subMember : String) : SPath :=
  let ext (raw : String) : String :=
    let (f, p) := splitSPathField raw
    let p' := qualifySPathMember p subMember
    s!"{f}::{p'}"
  match path with
  | .zero raw => .zero (ext raw)
  | .one raw k1 => .one (ext raw) k1
  | .two raw k1 k2 => .two (ext raw) k1 k2
  | other => other

def markField (name : String) : M Unit := do
  let env ← get
  unless env.referenced.contains name do
    modify fun e => { e with referenced := e.referenced.push name }

def markStructFixedArray (fieldName memberName : String) : M Unit := do
  let env ← get
  unless env.usedStructFixedArrays.contains (fieldName, memberName) do
    modify fun e => { e with usedStructFixedArrays := e.usedStructFixedArrays.push (fieldName, memberName) }

def markStructMapping (fieldName memberName : String) : M Unit := do
  let env ← get
  unless env.usedStructMappings.contains (fieldName, memberName) do
    modify fun e => { e with usedStructMappings := e.usedStructMappings.push (fieldName, memberName) }
  modify fun e => { e with usedRawStorage := true }

def markStructDynamicArray (fieldName memberName : String) : M Unit := do
  let env ← get
  unless env.usedStructDynamicArrays.contains (fieldName, memberName) do
    modify fun e => { e with usedStructDynamicArrays := e.usedStructDynamicArrays.push (fieldName, memberName) }
  modify fun e => { e with usedRawStorage := true }

def dynamicStorageArrayElement? (elemType : String) :
    Option (String × ParamType × SolidityAbi.ScalarKind) :=
  if elemType == "bytes4" then none else scalarArrayElement? (elemType ++ "[]")

def dynamicStorageArrayElemLayout (elemTy : String) : (Nat × Nat × Bool) :=
  if elemTy == "bool" then (8, 32, true)
  else if elemTy == "int256" || elemTy == "int" || elemTy == "bytes32" then (256, 1, false)
  else if elemTy == "address" || elemTy == "address payable" || elemTy.startsWith "contract " then (160, 1, false)
  else
    let bits := (bitsOf elemTy).getD 256
    let byteWidth := max 1 (bits / 8)
    (bits, max 1 (32 / byteWidth), false)

def resolveStructIdFromSolcType? (env : Env) (solcType : String) : Option Nat :=
  if solcType.startsWith "t_struct(" then
    let parts := solcType.splitOn ")"
    parts.getLast?.bind (fun s => (s.splitOn "_").head?.bind String.toNat?) |>.filter env.structs.contains
  else
    none

def normalizeSolcLayoutType (env : Env) (solcType : String) : String :=
  if solcType.startsWith "t_userDefinedValueType(" then
    let parts := solcType.splitOn ")"
    let byId? := parts.getLast?.bind String.toNat? |>.bind env.userValueTypeById.find?
    let innerName := ((solcType.drop 23).toString.splitOn ")").headD ""
    let byName? := env.userValueTypes.find? innerName
    match byId? <|> byName? with
    | some u => "t_" ++ u
    | none => solcType
  else
    solcType

def mappingKey (ty : String) : MetaM MappingKeyType :=
  match ty with
  | "t_bytes32" | "t_bytes4" => pure .bytes32
  | "t_address" | "t_address_payable" => pure .address
  | "t_uint256" | "t_int256" | "t_bool" => pure .uint256
  | _ =>
      if ty.startsWith "t_contract(" then pure .address
      else if ty.startsWith "t_enum(" then pure .uint256
      else if ty.startsWith "t_uint" || ty.startsWith "t_int" then do
        let numStr := if ty.startsWith "t_uint" then ty.drop 6 else ty.drop 5
        let some bits := numStr.toNat? | throwError "unsupported mapping key {ty}"
        unless bits > 0 && bits ≤ 256 && bits % 8 == 0 do
          throwError "unsupported mapping key {ty}"
        pure .uint256
      else throwError "unsupported mapping key {ty}"

def layoutType (types : Json) (id : String) : MetaM Json :=
  field types id

/-- Solidity names of the mapping keys of the state variable `name`
(`mapping(bytes32 id => ...)`), outermost first; `""` when unnamed. -/
def mappingKeyNames (env : Env) (name : String) : List String :=
  let decl := env.stateVars.toList.find? fun (_, j) => optStr j "name" == some name
  let rec go (fuel : Nat) (ty : Json) : List String :=
    match fuel with
    | 0 => []
    | fuel + 1 =>
      if optStr ty "nodeType" == some "Mapping" then
        (optStr ty "keyName" |>.getD "") :: (match field? ty "valueType" with
          | some v => go fuel v
          | none => [])
      else []
  match decl.bind (fun (_, j) => field? j "typeName") with
  | some ty => go 8 ty
  | none => []

partial def resolveRawStructInfo (structId : Nat) (at_ : Json) : M RawStructInfo := do
  let some sDecl := (← get).structs.find? structId
    | failAt at_ "unknown struct declaration"
  let sName ← mStr (← mField sDecl "name")
  let sMembers ← mArr (← mField sDecl "members")
  unless !sMembers.isEmpty do
    failAt sDecl s!"empty storage struct {sName} is unsupported"
  let mut currWord : Nat := 0
  let mut currByte : Nat := 0
  let mut scalars : Array RawStructMemberInfo := #[]
  let mut mappings : Array StructMappingInfo := #[]
  let mut dynamicArrays : Array StructDynamicArrayInfo := #[]
  let mut subStructs : Array RawStructSubStructInfo := #[]
  for mNode in sMembers do
    let mName ← mStr (← mField mNode "name")
    let mTy ← mType mNode
    let mTyNode ← mField mNode "typeName"
    if optStr mTyNode "nodeType" == some "Mapping" then
      let kNode ← mField mTyNode "keyType"
      let vNode ← mField mTyNode "valueType"
      let kTy ← mType kNode
      let vTy ← mType vNode
      let keyType ←
        if kTy == "address" || kTy == "address payable" || kTy.startsWith "contract " then
          pure MappingKeyType.address
        else if kTy == "uint256" || kTy == "uint" || (bitsOf kTy).isSome || (signedBitsOf kTy).isSome then
          pure MappingKeyType.uint256
        else if kTy == "bytes32" || kTy == "bytes4" then
          pure MappingKeyType.bytes32
        else
          failAt mNode s!"unsupported struct mapping key type {kTy}"
      let (valueWidth, booleanValue, valueStructId?) ←
        if vTy.startsWith "uint" then
          match bitsOf vTy with
          | some w => pure (w, false, none)
          | none => failAt mNode s!"unsupported struct mapping value type {vTy}"
        else if vTy == "int256" || vTy == "int" || vTy == "bytes32" then
          pure (256, false, none)
        else if vTy == "address" || vTy == "address payable" || vTy.startsWith "contract " then
          pure (160, false, none)
        else if vTy == "bool" then
          pure (8, true, none)
        else if vTy.startsWith "struct " && !vTy.contains "[" then do
          let valSid ← refInt vNode
          unless valSid >= 0 && (← get).structs.contains valSid.toNat do
            failAt mNode s!"unsupported struct mapping value type {vTy}"
          let _ ← resolveRawStructInfo valSid.toNat mNode
          pure (256, false, some valSid.toNat)
        else
          failAt mNode s!"unsupported struct mapping value type {vTy}"
      if currByte > 0 then
        currWord := currWord + 1
        currByte := 0
      let wordOffset := currWord
      currWord := currWord + 1
      mappings := mappings.push {
        member := mName
        solcType := mTy
        wordOffset
        keyType
        valueWidth
        booleanValue
        valueStructId := valueStructId?
      }
    else if optStr mTyNode "nodeType" == some "ArrayTypeName" && (field? mTyNode "length").isNone then
      let baseNode ← mField mTyNode "baseType"
      let baseTy ← mType baseNode
      let (elemTy, modelElemTy, abiKind, elemStructId?) ←
        if let some (eTy, mTy', aKind) := dynamicStorageArrayElement? baseTy then
          pure (eTy, mTy', aKind, none)
        else if baseTy.startsWith "struct " && !baseTy.contains "[" then do
          let elemSid ← refInt baseNode
          unless elemSid >= 0 && (← get).structs.contains elemSid.toNat do
            failAt mNode s!"unsupported storage struct dynamic array member {mName} : {mTy}"
          let elemInfo ← resolveRawStructInfo elemSid.toNat mNode
          unless elemInfo.mappings.isEmpty && elemInfo.dynamicArrays.isEmpty &&
              elemInfo.subStructs.isEmpty && !elemInfo.scalars.isEmpty && elemInfo.wordCount > 0 do
            failAt mNode s!"unsupported storage struct dynamic array member {mName} : {mTy}"
          pure (baseTy, ParamType.uint256, SolidityAbi.ScalarKind.bytes32, some elemSid.toNat)
        else
          failAt mNode s!"unsupported storage struct dynamic array member {mName} : {mTy}"
      if currByte > 0 then
        currWord := currWord + 1
        currByte := 0
      let wordOffset := currWord
      currWord := currWord + 1
      dynamicArrays := dynamicArrays.push {
        member := mName
        solcType := mTy
        wordOffset
        elemType := elemTy
        modelElemType := modelElemTy
        abiKind
        elemStructId := elemStructId?
      }
    else if mTy.startsWith "struct " && !mTy.contains "[" then
      let subSid ← refInt mTyNode
      unless subSid >= 0 && (← get).structs.contains subSid.toNat do
        failAt mNode s!"unresolved nested storage struct member {mName} : {mTy}"
      let subInfo ← resolveRawStructInfo subSid.toNat mNode
      if currByte > 0 then
        currWord := currWord + 1
        currByte := 0
      let wordOffset := currWord
      currWord := currWord + subInfo.wordCount
      subStructs := subStructs.push {
        member := mName
        structId := subSid.toNat
        wordOffset
      }
    else
      let (bitWidth, isBool) ←
        if mTy.startsWith "uint" then
          match bitsOf mTy with
          | some w => pure (w, false)
          | none => failAt mNode s!"unsupported storage struct member {mName} : {mTy}"
        else if mTy.startsWith "int" then
          match signedBitsOf mTy with
          | some w => pure (w, false)
          | none => failAt mNode s!"unsupported storage struct member {mName} : {mTy}"
        else if mTy == "bytes32" then
          pure (256, false)
        else if mTy == "address" || mTy == "address payable" || mTy.startsWith "contract " then
          pure (160, false)
        else if mTy == "bool" then
          pure (8, true)
        else
          failAt mNode s!"unsupported storage struct member {mName} : {mTy}"
      let byteWidth := bitWidth / 8
      if currByte + byteWidth > 32 then
        currWord := currWord + 1
        currByte := 0
      let wordOffset := currWord
      let byteOffset := currByte
      currByte := currByte + byteWidth
      if currByte == 32 then
        currWord := currWord + 1
        currByte := 0
      scalars := scalars.push {
        member := mName
        ty := mTy
        wordOffset
        byteOffset
        bitWidth
        isBool
      }
  let wordCount := if currByte > 0 then currWord + 1 else currWord
  return { structId, structName := sName, scalars, mappings, dynamicArrays, subStructs, wordCount }

partial def decodeStructLayoutMembers (name prefixStr : String) (baseWord : Nat) (types structTy : Json) :
    M (Array StructMember × Array String × Array String × Array String × Array StructFixedArrayInfo × Array StructMappingInfo × Array StructDynamicArrayInfo × Array (String × Nat)) := do
  let members ← mArr (← mField structTy "members")
  let mut members' : Array StructMember := #[]
  let mut names : Array String := #[]
  let mut skipped : Array String := #[]
  let mut booleanMembers : Array String := #[]
  let mut structFixedArrays : Array StructFixedArrayInfo := #[]
  let mut structMappings : Array StructMappingInfo := #[]
  let mut structDynamicArrays : Array StructDynamicArrayInfo := #[]
  let mut subStructs : Array (String × Nat) := #[]
  for m in members do
    let rawLabel ← mStr (← mField m "label")
    let qualLabel := if prefixStr == "" then rawLabel else s!"{prefixStr}.{rawLabel}"
    let rawSolcType ← mStr (← mField m "type")
    let solcType := normalizeSolcLayoutType (← get) rawSolcType
    let relWord ← mNat (← mField m "slot")
    let word := baseWord + relWord
    let byteOff ← mNat (← mField m "offset")
    if solcType.startsWith "t_struct(" then
      let some subTy := field? types rawSolcType
        | throwError "missing nested struct layout type {rawSolcType}"
      if byteOff == 0 && (← mStr (← mField subTy "encoding")) == "inplace" && (field? subTy "members").isSome then
        if let some sid := resolveStructIdFromSolcType? (← get) rawSolcType then
          subStructs := subStructs.push (qualLabel, sid)
          let (subMembers, subNames, subSkipped, subBools, subFixed, subMaps, subDyns, subSubs) ←
            decodeStructLayoutMembers name qualLabel word types subTy
          members' := members' ++ subMembers
          names := names ++ subNames
          skipped := skipped ++ subSkipped
          booleanMembers := booleanMembers ++ subBools
          structFixedArrays := structFixedArrays ++ subFixed
          structMappings := structMappings ++ subMaps
          structDynamicArrays := structDynamicArrays ++ subDyns
          subStructs := subStructs ++ subSubs
        else
          let item : OpaqRec := ⟨name, qualLabel, rawSolcType, word, byteOff⟩
          modify fun e => { e with opaqueMembers := e.opaqueMembers.push item }
          skipped := skipped.push qualLabel
      else
        let item : OpaqRec := ⟨name, qualLabel, rawSolcType, word, byteOff⟩
        modify fun e => { e with opaqueMembers := e.opaqueMembers.push item }
        skipped := skipped.push qualLabel
    else if solcType.startsWith "t_array" then
      let item : OpaqRec := ⟨name, qualLabel, rawSolcType, word, byteOff⟩
      modify fun e => { e with opaqueMembers := e.opaqueMembers.push item }
      let fixedInfo? : Option StructFixedArrayInfo ← (do
        let some arrTy := field? types rawSolcType | return none
        unless (← mStr (← mField arrTy "encoding")) == "inplace" && byteOff == 0 do
          return none
        let some baseKey := optStr arrTy "base" | return none
        let arrLabel ← mStr (← mField arrTy "label")
        let [elemLabel, suffix] := arrLabel.splitOn "["
          | return none
        unless suffix.endsWith "]" do return none
        let some length := (suffix.dropEnd 1).toNat? | return none
        unless length > 0 do return none
        let some base := field? types baseKey | return none
        let baseLabel ← mStr (← mField base "label")
        unless elemLabel == baseLabel && baseLabel.startsWith "uint" do
          return none
        let some width := bitsOf baseLabel | return none
        unless width > 0 && width ≤ 256 && width % 8 == 0 do
          return none
        unless (← mStr (← mField base "encoding")) == "inplace" &&
            (← mNat (← mField base "numberOfBytes")) * 8 == width do
          return none
        let perWord := 256 / width
        let words := (length + perWord - 1) / perWord
        unless (← mNat (← mField arrTy "numberOfBytes")) == words * 32 do
          return none
        return some {
          member := qualLabel
          solcType := rawSolcType
          wordOffset := word
          byteOffset := byteOff
          length
          elementWidth := width
          arrayType := arrLabel
        })
      let dynInfo? : Option StructDynamicArrayInfo ← (do
        let some arrTy := field? types rawSolcType | return none
        unless (← mStr (← mField arrTy "encoding")) == "dynamic_array" && byteOff == 0 &&
            (← mNat (← mField arrTy "numberOfBytes")) == 32 do
          return none
        let some baseKey := optStr arrTy "base" | return none
        let some base := field? types baseKey | return none
        unless (← mStr (← mField base "encoding")) == "inplace" do
          return none
        let rawBaseLabel ← mStr (← mField base "label")
        let baseLabel := (← get).userValueTypes.find? rawBaseLabel |>.getD rawBaseLabel
        if let some (elemTy, modelElemTy, abiKind) := dynamicStorageArrayElement? baseLabel then
          let (elemBits, _, _) := dynamicStorageArrayElemLayout elemTy
          unless (← mNat (← mField base "numberOfBytes")) * 8 == elemBits do
            return none
          return some {
            member := qualLabel
            solcType := rawSolcType
            wordOffset := word
            elemType := elemTy
            modelElemType := modelElemTy
            abiKind
          }
        if (normalizeSolcLayoutType (← get) baseKey).startsWith "t_struct(" then
          let some sid := resolveStructIdFromSolcType? (← get) baseKey | return none
          let rawInfo ← try resolveRawStructInfo sid Json.null catch _ => return none
          unless rawInfo.mappings.isEmpty && rawInfo.dynamicArrays.isEmpty &&
              rawInfo.subStructs.isEmpty && !rawInfo.scalars.isEmpty && rawInfo.wordCount > 0 do
            return none
          unless (← mNat (← mField base "numberOfBytes")) == rawInfo.wordCount * 32 do
            return none
          return some {
            member := qualLabel
            solcType := rawSolcType
            wordOffset := word
            elemType := rawBaseLabel
            modelElemType := .uint256
            abiKind := .bytes32
            elemStructId := some sid
          }
        return none)
      match fixedInfo?, dynInfo? with
      | some fixedInfo, _ => structFixedArrays := structFixedArrays.push fixedInfo
      | none, some dynInfo => structDynamicArrays := structDynamicArrays.push dynInfo
      | none, none => skipped := skipped.push qualLabel
    else if solcType.startsWith "t_mapping" then
      let item : OpaqRec := ⟨name, qualLabel, rawSolcType, word, byteOff⟩
      modify fun e => { e with opaqueMembers := e.opaqueMembers.push item }
      let mapInfo? : Option StructMappingInfo ← (do
        let some mapTy := field? types rawSolcType | return none
        unless (← mStr (← mField mapTy "encoding")) == "mapping" && byteOff == 0 &&
            (← mNat (← mField mapTy "numberOfBytes")) == 32 do
          return none
        let keyStr := normalizeSolcLayoutType (← get) (← mStr (← mField mapTy "key"))
        let keyType ← try liftM (mappingKey keyStr) catch _ => return none
        let valKey ← mStr (← mField mapTy "value")
        let some leafTy := field? types valKey | return none
        if (normalizeSolcLayoutType (← get) valKey).startsWith "t_struct(" then
          let some valSid := resolveStructIdFromSolcType? (← get) valKey | return none
          let _ ← try resolveRawStructInfo valSid Json.null catch _ => return none
          return some {
            member := qualLabel
            solcType := rawSolcType
            wordOffset := word
            keyType
            valueWidth := 256
            booleanValue := false
            valueStructId := some valSid
          }
        unless (field? leafTy "members").isNone && (optStr leafTy "base").isNone do
          return none
        unless (← mStr (← mField leafTy "encoding")) == "inplace" do
          return none
        let rawLeafLabel ← mStr (← mField leafTy "label")
        let leafLabel := (← get).userValueTypes.find? rawLeafLabel |>.getD rawLeafLabel
        let width? : Option Nat :=
          if leafLabel == "bool" then some 8
          else if leafLabel == "address" || leafLabel == "address payable" || leafLabel.startsWith "contract " then some 160
          else if leafLabel == "bytes32" || leafLabel == "int256" || leafLabel == "int" then some 256
          else if leafLabel.startsWith "uint" then
            match (leafLabel.drop 4).toNat? with
            | some bits => if bits > 0 && bits ≤ 256 && bits % 8 == 0 then some bits else none
            | none => none
          else none
        let some width := width? | return none
        unless (← mNat (← mField leafTy "numberOfBytes")) * 8 == width do
          return none
        return some {
          member := qualLabel
          solcType := rawSolcType
          wordOffset := word
          keyType
          valueWidth := width
          booleanValue := leafLabel == "bool"
        })
      match mapInfo? with
      | some mapInfo => structMappings := structMappings.push mapInfo
      | none => skipped := skipped.push qualLabel
    else if solcType == "t_bool" || solcType == "t_address" || solcType == "t_address_payable" ||
        solcType.startsWith "t_contract(" || solcType == "t_bytes32" || solcType == "t_int256" ||
        solcType.startsWith "t_uint" || solcType.startsWith "t_int" then
      let bits ←
        if solcType == "t_bool" then pure 8
        else if solcType == "t_address" || solcType == "t_address_payable" || solcType.startsWith "t_contract(" then pure 160
        else if solcType == "t_bytes32" || solcType == "t_int256" then pure 256
        else if solcType.startsWith "t_uint" then do
          let some b := (solcType.drop 6).toNat? | throwError "bad uint {solcType}"
          unless b > 0 && b ≤ 256 && b % 8 == 0 do throwError "bad uint {solcType}"
          pure b
        else do
          let some b := (solcType.drop 5).toNat? | throwError "bad int {solcType}"
          unless b > 0 && b ≤ 256 && b % 8 == 0 do throwError "bad int {solcType}"
          pure b
      let bitOff := byteOff * 8
      unless bitOff + bits ≤ 256 do throwError "packed field {qualLabel} does not fit in a word"
      let packed : Option PackedBits :=
        if bits == 256 && bitOff == 0 then none else some { offset := bitOff, width := bits }
      let ty : StructMemberType := if bits == 16 then .uint16 else .uint256
      members' := members'.push { name := qualLabel, ty, wordOffset := word, packed }
      names := names.push qualLabel
      if solcType == "t_bool" then
        booleanMembers := booleanMembers.push qualLabel
    else
      throwError "unsupported layout member {qualLabel} : {rawSolcType}"
  pure (members', names, skipped, booleanMembers, structFixedArrays, structMappings, structDynamicArrays, subStructs)

def rawStructMemberSlot (baseSlot : Expr) (wordOffset : Nat) : Expr :=
  if wordOffset == 0 then baseSlot else .add baseSlot (.literal wordOffset)

def computeSPathBaseSlot (path : SPath) (info : FieldInfo) (wordOffset : Nat) (at_ : Json) :
    M (Array Stmt × Expr) := do
  modify fun e => { e with encodingMemory := true }
  let (count, baseStmts, baseSlot) ← match path with
    | .zero _ => do
        let bSlot ← fresh
        pure (0, #[Stmt.letVar bSlot (.literal info.slot)], bSlot)
    | .one _ k1 => do
        let bSlot ← fresh
        let stmts : Array Stmt := #[
          .mstore (.literal 0) k1,
          .mstore (.literal 32) (.literal info.slot),
          .letVar bSlot (.keccak256 (.literal 0) (.literal 64))
        ]
        pure (1, stmts, bSlot)
    | .two _ k1 k2 => do
        let outerSlot ← fresh
        let bSlot ← fresh
        let stmts : Array Stmt := #[
          .mstore (.literal 0) k1,
          .mstore (.literal 32) (.literal info.slot),
          .letVar outerSlot (.keccak256 (.literal 0) (.literal 64)),
          .mstore (.literal 0) k2,
          .mstore (.literal 32) (.localVar outerSlot),
          .letVar bSlot (.keccak256 (.literal 0) (.literal 64))
        ]
        pure (2, stmts, bSlot)
    | .outer _ _ | .rawSlot _ _ | .bytesSlot _ _ =>
        failAt at_ "storage struct member access requires all outer mapping keys"
  unless info.keyCount == count do
    failAt at_ "storage struct mapping key count differs"
  let slotExpr :=
    if wordOffset == 0 then Expr.localVar baseSlot
    else .add (.localVar baseSlot) (.literal wordOffset)
  return (baseStmts, slotExpr)

def readStorageDynamicArrayLength (pre : Array Stmt) (fieldName : String) (slotExpr : Expr) : M Val := do
  let raw := if fieldName != "" then Expr.storage fieldName else Expr.storageArrayElement rawStorageFieldName slotExpr
  if fieldName != "" then
    markField fieldName
  else
    modify fun e => { e with usedRawStorage := true }
  let dest ← fresh
  pure { pre := pre.push (.letVar dest raw), expr := .localVar dest }

def storageDynamicStructElementPath (pre : Array Stmt) (fieldName : String) (slotExpr : Expr)
    (elemSid : Nat) (indexExpr : Expr) (at_ : Json) (oobStmt : Stmt := .panicCode (.literal 0x32)) :
    M (Array Stmt × SPath) := do
  modify fun e => { e with encodingMemory := true, usedRawStorage := true }
  if fieldName != "" then
    markField fieldName
  let rawInfo ← resolveRawStructInfo elemSid at_
  let capturedIdx ← fresh
  let lenVal ← readStorageDynamicArrayLength (pre.push (.letVar capturedIdx indexExpr)) fieldName slotExpr
  let baseDataSlot ← fresh
  let elemSlot ← fresh
  let idxExpr := Expr.localVar capturedIdx
  let wordOff := if rawInfo.wordCount == 1 then idxExpr else Expr.mul idxExpr (.literal rawInfo.wordCount)
  let stmts : Array Stmt := #[
    .ite (.lt idxExpr lenVal.expr) [] [oobStmt],
    .mstore (.literal 0) slotExpr,
    .letVar baseDataSlot (.keccak256 (.literal 0) (.literal 32)),
    .letVar elemSlot (.add (.localVar baseDataSlot) wordOff)
  ]
  return (lenVal.pre ++ stmts, .rawSlot elemSid (.localVar elemSlot))

def writeStorageDynamicArrayElementAtUnchecked (baseDataSlot : String) (elemTy : String)
    (indexExpr valExpr : Expr) (deleting : Bool) : M (Array Stmt) := do
  let (bits, perWord, isBool) := dynamicStorageArrayElemLayout elemTy
  let elemSlot ← fresh
  let wordOff := if perWord == 1 then indexExpr else Expr.div indexExpr (.literal perWord)
  let cleanVal :=
    if deleting then Expr.literal 0
    else if isBool then Expr.logicalNot (.logicalNot valExpr)
    else if bits < 256 then Expr.bitAnd valExpr (.literal (2 ^ bits - 1))
    else valExpr
  if bits == 256 && perWord == 1 then
    return #[
      .letVar elemSlot (.add (.localVar baseDataSlot) wordOff),
      .setStorageArrayElement rawStorageFieldName (.localVar elemSlot) cleanVal
    ]
  else
    let shiftBits :=
      if perWord == 1 then Expr.literal 0
      else Expr.mul (.mod indexExpr (.literal perWord)) (.literal bits)
    let elemMask :=
      if perWord == 1 then Expr.literal (2 ^ bits - 1)
      else Expr.shl shiftBits (.literal (2 ^ bits - 1))
    let invMask := Expr.bitNot elemMask
    let shiftedVal :=
      if deleting then Expr.literal 0
      else if perWord == 1 then cleanVal
      else Expr.shl shiftBits cleanVal
    let oldWord ← fresh
    let newWord :=
      if deleting then Expr.bitAnd (.localVar oldWord) invMask
      else Expr.bitOr (.bitAnd (.localVar oldWord) invMask) shiftedVal
    return #[
      .letVar elemSlot (.add (.localVar baseDataSlot) wordOff),
      .letVar oldWord (.storageArrayElement rawStorageFieldName (.localVar elemSlot)),
      .setStorageArrayElement rawStorageFieldName (.localVar elemSlot) newWord
    ]

def writeStorageDynamicArrayElement (pre : Array Stmt) (fieldName : String) (slotExpr : Expr)
    (elemTy : String) (indexExpr valExpr : Expr) (deleting : Bool) : M (Array Stmt) := do
  modify fun e => { e with encodingMemory := true, usedRawStorage := true }
  if fieldName != "" then
    markField fieldName
  let lenVal ← readStorageDynamicArrayLength pre fieldName slotExpr
  let baseDataSlot ← fresh
  let writeStmts ← writeStorageDynamicArrayElementAtUnchecked baseDataSlot elemTy indexExpr valExpr deleting
  let stmts : Array Stmt := #[
    .ite (.lt indexExpr lenVal.expr) [] [.panicCode (.literal 0x32)],
    .mstore (.literal 0) slotExpr,
    .letVar baseDataSlot (.keccak256 (.literal 0) (.literal 32))
  ] ++ writeStmts
  return lenVal.pre ++ stmts

def deleteStorageDynamicArray (pre : Array Stmt) (fieldName : String) (slotExpr : Expr)
    (elemTy : String) (elemStructId? : Option Nat := none) (at_ : Json := Json.null) : M (Array Stmt) := do
  modify fun e => { e with encodingMemory := true, usedRawStorage := true }
  if fieldName != "" then
    markField fieldName
  let lenVal ← readStorageDynamicArrayLength pre fieldName slotExpr
  let baseDataSlot ← fresh
  let wordCount ← fresh
  let loopIdx ← fresh
  let wordCountExpr ← match elemStructId? with
    | some elemSid => do
        let rawInfo ← resolveRawStructInfo elemSid at_
        pure (if rawInfo.wordCount == 1 then lenVal.expr else Expr.mul lenVal.expr (.literal rawInfo.wordCount))
    | none => do
        let (_, perWord, _) := dynamicStorageArrayElemLayout elemTy
        pure (if perWord == 1 then lenVal.expr
              else Expr.div (.add lenVal.expr (.literal (perWord - 1))) (.literal perWord))
  let writeLenStmt : Stmt :=
    if fieldName != "" then .setStorage fieldName (.literal 0)
    else .setStorageArrayElement rawStorageFieldName slotExpr (.literal 0)
  let stmts : Array Stmt := #[
    .mstore (.literal 0) slotExpr,
    .letVar baseDataSlot (.keccak256 (.literal 0) (.literal 32)),
    .letVar wordCount wordCountExpr,
    .forEach loopIdx (.localVar wordCount) [
      .setStorageArrayElement rawStorageFieldName (.add (.localVar baseDataSlot) (.localVar loopIdx)) (.literal 0)
    ],
    writeLenStmt
  ]
  return lenVal.pre ++ stmts

/-! ## Layer I: Universal Storage Layout MetaSpec -/

/-- True iff `path` is a raw storage slot reference (`SPath.rawSlot`). -/
def isRawSlotPath : SPath → Bool
  | .rawSlot _ _ => true
  | _ => false

/-- True iff `path` is a packed/dynamic bytes storage slot reference (`SPath.bytesSlot`). -/
def isBytesSlotPath : SPath → Bool
  | .bytesSlot _ _ => true
  | _ => false

/-- **Layer I MetaSpec** for `StorageLayout`:
1. `rawStructMemberSlot baseSlot 0 = baseSlot`.
2. For `w ≠ 0`, `rawStructMemberSlot baseSlot w = .add baseSlot (.literal w)`.
3. `appendSPathSub` preserves `SPath.rawSlot` and `SPath.bytesSlot`. -/
structure StorageLayoutMetaSpec (baseSlot : Expr) (w : Nat) (m : String) : Prop where
  zero_offset_identity :
    rawStructMemberSlot baseSlot 0 = baseSlot
  nonzero_offset_add :
    w ≠ 0 → rawStructMemberSlot baseSlot w = .add baseSlot (.literal w)
  rawSlot_append_invariant :
    ∀ sid e, appendSPathSub (.rawSlot sid e) m = .rawSlot sid e
  bytesSlot_append_invariant :
    ∀ pair isStr, appendSPathSub (.bytesSlot pair isStr) m = .bytesSlot pair isStr

/-- Universal theorem establishing `StorageLayoutMetaSpec` for all `(baseSlot, w, m)`. -/
theorem storageLayout_satisfies_metaSpec (baseSlot : Expr) (w : Nat) (m : String) :
    StorageLayoutMetaSpec baseSlot w m where
  zero_offset_identity := rfl
  nonzero_offset_add hw := by
    simp [rawStructMemberSlot, hw]
  rawSlot_append_invariant _ _ := rfl
  bytesSlot_append_invariant _ _ := rfl

/-! ## Layer II: 1–3 Line Projection Corollaries -/

theorem rawStructMemberSlot_zero (baseSlot : Expr) :
    rawStructMemberSlot baseSlot 0 = baseSlot :=
  (storageLayout_satisfies_metaSpec baseSlot 0 "").zero_offset_identity

theorem rawStructMemberSlot_nonzero (baseSlot : Expr) (w : Nat) (hw : w ≠ 0) :
    rawStructMemberSlot baseSlot w = .add baseSlot (.literal w) :=
  (storageLayout_satisfies_metaSpec baseSlot w "").nonzero_offset_add hw

theorem appendSPathSub_rawSlot (sid : Nat) (e : Expr) (m : String) :
    appendSPathSub (.rawSlot sid e) m = .rawSlot sid e :=
  (storageLayout_satisfies_metaSpec e sid m).rawSlot_append_invariant sid e

theorem appendSPathSub_bytesSlot (pair : String × Expr) (isStr : Bool) (m : String) :
    appendSPathSub (.bytesSlot pair isStr) m = .bytesSlot pair isStr :=
  (storageLayout_satisfies_metaSpec (.literal 0) 0 m).bytesSlot_append_invariant pair isStr

/-! ## Layer III: Concrete `by decide` Witnesses -/

theorem witness_isRawSlotPath_true :
    isRawSlotPath (.rawSlot 7 (.literal 0)) = true := by decide

theorem witness_isRawSlotPath_zero_false :
    isRawSlotPath (.zero "owner") = false := by decide

theorem witness_isBytesSlotPath_true :
    isBytesSlotPath (.bytesSlot ("data", .literal 1) true) = true := by decide

theorem witness_appendSPathSub_preserves_isRawSlotPath :
    isRawSlotPath (appendSPathSub (.rawSlot 3 (.literal 42)) "sub") = true := by decide

end Compiler.CompilationModel.SolidityImport

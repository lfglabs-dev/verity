import Compiler.CompilationModel.Types
import Compiler.CompilationModel.AdtStorageLayout
import Compiler.CompilationModel.DynamicData
import Compiler.CompilationModel.InternalArgs
import Compiler.CompilationModel.InternalNaming
import Compiler.CompilationModel.ValidationHelpers

namespace Compiler.CompilationModel

open Compiler
open Compiler.Yul

-- Helpers for building common Yul patterns (defined outside mutual block for termination).
-- Exposed (non-private) so that bridge/closure proofs in `Compiler.Proofs.*` can
-- reference their definitional shape via `simp`/`unfold`.
def yulBinOp (op : String) (a b : YulExpr) : YulExpr :=
  YulExpr.call op [a, b]

def yulNegatedBinOp (op : String) (a b : YulExpr) : YulExpr :=
  YulExpr.call "iszero" [YulExpr.call op [a, b]]

def yulToBool (e : YulExpr) : YulExpr :=
  YulExpr.call "iszero" [YulExpr.call "iszero" [e]]

-- Exposed so proof modules can name the exact mapping-read lowering shape.
def compileMappingSlotRead (fields : List Field) (field : String) (keyExpr : YulExpr)
    (label : String) (wordOffset : Nat := 0) : Except String YulExpr :=
  if !isMapping fields field then
    throw s!"Compilation error: field '{field}' is not a mapping"
  else
    match findFieldWithResolvedSlot fields field with
    | some (f, slot) =>
      let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyExpr]
      let finalSlot := if wordOffset == 0 then mappingBase else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset]
      let loadBuiltin := if f.isTransient then "tload" else "sload"
      pure (YulExpr.call loadBuiltin [finalSlot])
    | none => throw s!"Compilation error: unknown mapping field '{field}' in {label}"

-- Exposed so proof modules can name the exact nested mapping-chain lowering shape.
def compileMappingSlotChain (baseSlot : YulExpr) (keys : List YulExpr) : YulExpr :=
  keys.foldl (fun slotExpr keyExpr => YulExpr.call "mappingSlot" [slotExpr, keyExpr]) baseSlot

def findInternalFunctionForCall? (functions : List FunctionSpec) (name : String) : Option FunctionSpec :=
  match functions.filter (fun fn => fn.isInternal && fn.name == name) with
  | [fn] => some fn
  | _ => none

-- Compile expression to Yul (using mutual recursion for lists)
set_option maxHeartbeats 800000 in
mutual
def compileExprListWithInternals (fields : List Field)
    (dynamicSource : DynamicDataSource := .calldata)
    (internalFunctions : List FunctionSpec := []) :
    List Expr → Except String (List YulExpr)
  | [] => pure []
  | e :: es => do
      let head ← compileExprWithInternals fields dynamicSource internalFunctions e
      let tail ← compileExprListWithInternals fields dynamicSource internalFunctions es
      pure (head :: tail)

def compileInternalCallArg (fields : List Field) (dynamicSource : DynamicDataSource)
    (internalFunctions : List FunctionSpec) (calleeName : String) (param : Param) (arg : Expr) :
    Except String (List YulExpr) := do
  if isExpandedInternalParamType param.ty then
    match directForwardedInternalArgName? arg with
    | some name =>
        pure ((internalCallYulArgNamesForParam name param).map YulExpr.ident)
    | none =>
        throw s!"Compilation error: internal call '{calleeName}' argument for parameter '{param.name}' with type {repr param.ty} must be a direct parameter forwarding expression (issue #1889)."
  else
    pure [← compileExprWithInternals fields dynamicSource internalFunctions arg]

def compileInternalCallArgsWithParams (fields : List Field) (dynamicSource : DynamicDataSource)
    (internalFunctions : List FunctionSpec) (calleeName : String) : List Param → List Expr →
    Except String (List YulExpr)
  | [], [] => pure []
  | param :: params, arg :: args => do
      let head ← compileInternalCallArg fields dynamicSource internalFunctions calleeName param arg
      let tail ← compileInternalCallArgsWithParams fields dynamicSource internalFunctions calleeName params args
      pure (head ++ tail)
  | params, args =>
      throw s!"Compilation error: internal call '{calleeName}' received {args.length} source arg(s), expected {params.length} (issue #1889)."

def compileExpandedInternalCallArgsWithParams
    (fields : List Field) (dynamicSource : DynamicDataSource)
    (internalFunctions : List FunctionSpec) (calleeName : String) : List Param → List Expr →
    Except String (List YulExpr)
  | [], [] => pure []
  | param :: params, args => do
      let expectedNames := internalFunctionYulParamNames [param]
      let head := args.take expectedNames.length
      let tail := args.drop expectedNames.length
      let compileForwardedIndex : Expr → Except String YulExpr
        | Expr.param name => pure (YulExpr.ident name)
        | Expr.localVar name => pure (YulExpr.ident name)
        | Expr.literal n => pure (YulExpr.lit (n % uint256Modulus))
        | _ =>
            throw s!"Compilation error: internal call '{calleeName}' checked dynamic-member projection uses an unsupported computed index (issue #1889)."
      let dynamicMemberHelperNames
          (lengthCalldata lengthMemory offsetCalldata offsetMemory : String)
          (isLength : Bool) : String :=
        match dynamicSource with
        | .calldata => if isLength then lengthCalldata else offsetCalldata
        | .memory => if isLength then lengthMemory else offsetMemory
      let compileProjection : Expr → Except String YulExpr
        | Expr.paramDynamicMemberDataOffset name wordOffset =>
            pure (YulExpr.call
              (dynamicMemberHelperNames
                checkedParamDynamicMemberLengthCalldataHelperName
                checkedParamDynamicMemberLengthMemoryHelperName
                checkedParamDynamicMemberDataOffsetCalldataHelperName
                checkedParamDynamicMemberDataOffsetMemoryHelperName
                false)
              [YulExpr.ident s!"{name}_data_offset", YulExpr.lit wordOffset])
        | Expr.paramDynamicMemberLength name wordOffset =>
            pure (YulExpr.call
              (dynamicMemberHelperNames
                checkedParamDynamicMemberLengthCalldataHelperName
                checkedParamDynamicMemberLengthMemoryHelperName
                checkedParamDynamicMemberDataOffsetCalldataHelperName
                checkedParamDynamicMemberDataOffsetMemoryHelperName
                true)
              [YulExpr.ident s!"{name}_data_offset", YulExpr.lit wordOffset])
        | Expr.arrayElementDynamicMemberDataOffset name index wordOffset => do
            let indexExpr ← compileForwardedIndex index
            pure (YulExpr.call
              (dynamicMemberHelperNames
                checkedArrayElementDynamicMemberLengthCalldataHelperName
                checkedArrayElementDynamicMemberLengthMemoryHelperName
                checkedArrayElementDynamicMemberDataOffsetCalldataHelperName
                checkedArrayElementDynamicMemberDataOffsetMemoryHelperName
                false)
              [YulExpr.ident s!"{name}_data_offset", YulExpr.ident s!"{name}_length", indexExpr, YulExpr.lit wordOffset])
        | Expr.arrayElementDynamicMemberLength name index wordOffset => do
            let indexExpr ← compileForwardedIndex index
            pure (YulExpr.call
              (dynamicMemberHelperNames
                checkedArrayElementDynamicMemberLengthCalldataHelperName
                checkedArrayElementDynamicMemberLengthMemoryHelperName
                checkedArrayElementDynamicMemberDataOffsetCalldataHelperName
                checkedArrayElementDynamicMemberDataOffsetMemoryHelperName
                true)
              [YulExpr.ident s!"{name}_data_offset", YulExpr.ident s!"{name}_length", indexExpr, YulExpr.lit wordOffset])
        | _ =>
            throw s!"Compilation error: internal call '{calleeName}' expanded arguments must be direct parameters or checked dynamic-member projections (issue #1889)."
      let rec compileExpanded : List Expr → Except String (List YulExpr)
        | [] => pure []
        | Expr.param argName :: rest => do
            let compiledRest ← compileExpanded rest
            pure (YulExpr.ident argName :: compiledRest)
        | e@(Expr.paramDynamicMemberDataOffset _ _) :: rest
        | e@(Expr.paramDynamicMemberLength _ _) :: rest
        | e@(Expr.arrayElementDynamicMemberDataOffset _ _ _) :: rest
        | e@(Expr.arrayElementDynamicMemberLength _ _ _) :: rest => do
            let compiledHead ← compileProjection e
            let compiledRest ← compileExpanded rest
            pure (compiledHead :: compiledRest)
        | _ :: _ =>
            throw s!"Compilation error: internal call '{calleeName}' expanded arguments must be direct parameters or checked dynamic-member projections (issue #1889)."
      let headExprs ← compileExpanded head
      let tailExprs ← compileExpandedInternalCallArgsWithParams fields dynamicSource internalFunctions calleeName params tail
      pure (headExprs ++ tailExprs)
  | [], _ :: _ =>
      throw s!"Compilation error: internal call '{calleeName}' received extra expanded argument(s) (issue #1889)."

def compileInternalCallArgs (fields : List Field) (dynamicSource : DynamicDataSource)
    (internalFunctions : List FunctionSpec) (calleeName : String) (args : List Expr) :
    Except String (List YulExpr) :=
  match findInternalFunctionForCall? internalFunctions calleeName with
  | some callee =>
      let expandedArgCount :=
        callee.params.foldl (fun acc param => acc + (internalFunctionYulParamNames [param]).length) 0
      if args.length == callee.params.length then
        compileInternalCallArgsWithParams fields dynamicSource internalFunctions calleeName callee.params args
      else if args.length == expandedArgCount then
        compileExpandedInternalCallArgsWithParams fields dynamicSource internalFunctions calleeName callee.params args
      else
        compileInternalCallArgsWithParams fields dynamicSource internalFunctions calleeName callee.params args
  | none => compileExprListWithInternals fields dynamicSource internalFunctions args

def compileExprWithInternals (fields : List Field)
    (dynamicSource : DynamicDataSource := .calldata)
    (internalFunctions : List FunctionSpec := []) :
    Expr → Except String YulExpr
  | Expr.literal n => pure (YulExpr.lit (n % uint256Modulus))
  | Expr.param name => pure (YulExpr.ident name)
  | Expr.constructorArg idx => pure (YulExpr.ident s!"arg{idx}")
  | Expr.immutable name => pure (YulExpr.call "loadimmutable" [YulExpr.str name])
  | Expr.storage field =>
    if isMapping fields field then
      throw s!"Compilation error: field '{field}' is a mapping; use Expr.mapping, Expr.mappingWord, or Expr.mappingPackedWord"
    else
      match findFieldWithResolvedSlot fields field with
      | some (f, slot) =>
          let loadBuiltin := if f.isTransient then "tload" else "sload"
          match f.packedBits with
          | none =>
              pure (YulExpr.call loadBuiltin [YulExpr.lit slot])
          | some packed =>
              pure (YulExpr.call "and" [
                YulExpr.call "shr" [YulExpr.lit packed.offset, YulExpr.call loadBuiltin [YulExpr.lit slot]],
                YulExpr.lit (packedMaskNat packed)
              ])
      | none => throw s!"Compilation error: unknown storage field '{field}'"
  | Expr.storageAddr field =>
    if isMapping fields field then
      throw s!"Compilation error: field '{field}' is a mapping; use Expr.mapping, Expr.mappingWord, or Expr.mappingPackedWord"
    else
      match findFieldWithResolvedSlot fields field with
      | some (f, slot) =>
          let loadBuiltin := if f.isTransient then "tload" else "sload"
          match f.ty with
          | .address =>
              match f.packedBits with
              | none =>
                  pure (YulExpr.call loadBuiltin [YulExpr.lit slot])
              | some packed =>
                  pure (YulExpr.call "and" [
                    YulExpr.call "shr" [YulExpr.lit packed.offset, YulExpr.call loadBuiltin [YulExpr.lit slot]],
                    YulExpr.lit (packedMaskNat packed)
                  ])
          | _ =>
              throw s!"Compilation error: field '{field}' is not address-typed; use Expr.storage instead"
      | none => throw s!"Compilation error: unknown storage field '{field}'"
  | Expr.mapping field key => do
      compileMappingSlotRead fields field (← compileExprWithInternals fields dynamicSource internalFunctions key) "mapping"
  | Expr.mappingWord field key wordOffset => do
      compileMappingSlotRead fields field (← compileExprWithInternals fields dynamicSource internalFunctions key) "mappingWord" wordOffset
  | Expr.mappingPackedWord field key wordOffset packed => do
      if !packedBitsValid packed then
        throw s!"Compilation error: Expr.mappingPackedWord for field '{field}' has invalid packed range offset={packed.offset} width={packed.width}. Require 0 < width <= 256, offset < 256, and offset + width <= 256."
      else do
        let slotWord ← compileMappingSlotRead fields field (← compileExprWithInternals fields dynamicSource internalFunctions key) "mappingPackedWord" wordOffset
        pure (YulExpr.call "and" [
          YulExpr.call "shr" [YulExpr.lit packed.offset, slotWord],
          YulExpr.lit (packedMaskNat packed)
        ])
  | Expr.mapping2 field key1 key2 =>
    if !isMapping2 fields field then
      throw s!"Compilation error: field '{field}' is not a double mapping"
    else
      match findFieldWithResolvedSlot fields field with
      | some (f, slot) => do
        let loadBuiltin := if f.isTransient then "tload" else "sload"
        let key1Expr ← compileExprWithInternals fields dynamicSource internalFunctions key1
        let key2Expr ← compileExprWithInternals fields dynamicSource internalFunctions key2
        let innerSlot := YulExpr.call "mappingSlot" [YulExpr.lit slot, key1Expr]
        pure (YulExpr.call loadBuiltin [YulExpr.call "mappingSlot" [innerSlot, key2Expr]])
      | none => throw s!"Compilation error: unknown mapping field '{field}'"
  | Expr.mapping2Word field key1 key2 wordOffset =>
    if !isMapping2 fields field then
      throw s!"Compilation error: field '{field}' is not a double mapping"
    else
      match findFieldWithResolvedSlot fields field with
      | some (f, slot) => do
        let loadBuiltin := if f.isTransient then "tload" else "sload"
        let key1Expr ← compileExprWithInternals fields dynamicSource internalFunctions key1
        let key2Expr ← compileExprWithInternals fields dynamicSource internalFunctions key2
        let innerSlot := YulExpr.call "mappingSlot" [YulExpr.lit slot, key1Expr]
        let outerSlot := YulExpr.call "mappingSlot" [innerSlot, key2Expr]
        let finalSlot := if wordOffset == 0 then outerSlot else YulExpr.call "add" [outerSlot, YulExpr.lit wordOffset]
        pure (YulExpr.call loadBuiltin [finalSlot])
      | none => throw s!"Compilation error: unknown mapping field '{field}'"
  | Expr.mappingUint field key => do
      compileMappingSlotRead fields field (← compileExprWithInternals fields dynamicSource internalFunctions key) "mappingUint"
  | Expr.mappingChain field keys =>
      if !isMapping fields field then
        throw s!"Compilation error: field '{field}' is not a mapping"
      else
        match findFieldWithResolvedSlot fields field with
        | some (f, slot) => do
            let keyExprs ← compileExprListWithInternals fields dynamicSource internalFunctions keys
            let loadBuiltin := if f.isTransient then "tload" else "sload"
            pure (YulExpr.call loadBuiltin [compileMappingSlotChain (YulExpr.lit slot) keyExprs])
        | none => throw s!"Compilation error: unknown mapping field '{field}'"
  | Expr.structMember field key memberName => do
      if isMapping2 fields field then
        throw s!"Compilation error: field '{field}' is a double mapping; use Expr.structMember2 instead of Expr.structMember"
      match findStructMembers fields field with
      | none => throw s!"Compilation error: field '{field}' is not a mappingStruct"
      | some members =>
        match findStructMember members memberName with
        | none => throw s!"Compilation error: struct field '{field}' has no member '{memberName}'"
        | some member =>
          match member.packed with
          | none =>
            compileMappingSlotRead fields field (← compileExprWithInternals fields dynamicSource internalFunctions key) s!"structMember.{memberName}" member.wordOffset
          | some packed =>
            let slotWord ← compileMappingSlotRead fields field (← compileExprWithInternals fields dynamicSource internalFunctions key) s!"structMember.{memberName}" member.wordOffset
            pure (YulExpr.call "and" [
              YulExpr.call "shr" [YulExpr.lit packed.offset, slotWord],
              YulExpr.lit (packedMaskNat packed)
            ])
  | Expr.structMember2 field key1 key2 memberName =>
      if !isMapping2 fields field then
        throw s!"Compilation error: field '{field}' is not a double mapping; use Expr.structMember instead of Expr.structMember2"
      else
        match findStructMembers fields field with
        | none => throw s!"Compilation error: field '{field}' is not a mappingStruct"
        | some members =>
          match findStructMember members memberName with
          | none => throw s!"Compilation error: struct field '{field}' has no member '{memberName}'"
          | some member =>
            match findFieldWithResolvedSlot fields field with
            | some (f, slot) => do
              let loadBuiltin := if f.isTransient then "tload" else "sload"
              let key1Expr ← compileExprWithInternals fields dynamicSource internalFunctions key1
              let key2Expr ← compileExprWithInternals fields dynamicSource internalFunctions key2
              let innerSlot := YulExpr.call "mappingSlot" [YulExpr.lit slot, key1Expr]
              let outerSlot := YulExpr.call "mappingSlot" [innerSlot, key2Expr]
              let finalSlot := if member.wordOffset == 0 then outerSlot else YulExpr.call "add" [outerSlot, YulExpr.lit member.wordOffset]
              match member.packed with
              | none =>
                pure (YulExpr.call loadBuiltin [finalSlot])
              | some packed =>
                pure (YulExpr.call "and" [
                  YulExpr.call "shr" [YulExpr.lit packed.offset, YulExpr.call loadBuiltin [finalSlot]],
                  YulExpr.lit (packedMaskNat packed)
                ])
            | none => throw s!"Compilation error: unknown mapping field '{field}'"
  | Expr.caller => pure (YulExpr.call "caller" [])
  | Expr.contractAddress => pure (YulExpr.call "address" [])
  | Expr.txOrigin => pure (YulExpr.call "origin" [])
  | Expr.chainid => pure (YulExpr.call "chainid" [])
  | Expr.extcodesize addr => do
      pure (YulExpr.call "extcodesize" [← compileExprWithInternals fields dynamicSource internalFunctions addr])
  | Expr.msgValue => pure (YulExpr.call "callvalue" [])
  | Expr.selfBalance => pure (YulExpr.call "selfbalance" [])
  | Expr.blockTimestamp => pure (YulExpr.call "timestamp" [])
  | Expr.blockNumber => pure (YulExpr.call "number" [])
  | Expr.blobbasefee => pure (YulExpr.call "blobbasefee" [])
  | Expr.mload offset => do
      pure (YulExpr.call "mload" [← compileExprWithInternals fields dynamicSource internalFunctions offset])
  | Expr.tload offset => do
      pure (YulExpr.call "tload" [← compileExprWithInternals fields dynamicSource internalFunctions offset])
  | Expr.keccak256 offset size => do
      pure (YulExpr.call "keccak256" [
        ← compileExprWithInternals fields dynamicSource internalFunctions offset,
        ← compileExprWithInternals fields dynamicSource internalFunctions size
      ])
  | Expr.call gas target value inOffset inSize outOffset outSize => do
      pure (YulExpr.call "call" [
        ← compileExprWithInternals fields dynamicSource internalFunctions gas,
        ← compileExprWithInternals fields dynamicSource internalFunctions target,
        ← compileExprWithInternals fields dynamicSource internalFunctions value,
        ← compileExprWithInternals fields dynamicSource internalFunctions inOffset,
        ← compileExprWithInternals fields dynamicSource internalFunctions inSize,
        ← compileExprWithInternals fields dynamicSource internalFunctions outOffset,
        ← compileExprWithInternals fields dynamicSource internalFunctions outSize
      ])
  | Expr.staticcall gas target inOffset inSize outOffset outSize => do
      pure (YulExpr.call "staticcall" [
        ← compileExprWithInternals fields dynamicSource internalFunctions gas,
        ← compileExprWithInternals fields dynamicSource internalFunctions target,
        ← compileExprWithInternals fields dynamicSource internalFunctions inOffset,
        ← compileExprWithInternals fields dynamicSource internalFunctions inSize,
        ← compileExprWithInternals fields dynamicSource internalFunctions outOffset,
        ← compileExprWithInternals fields dynamicSource internalFunctions outSize
      ])
  | Expr.delegatecall gas target inOffset inSize outOffset outSize => do
      pure (YulExpr.call "delegatecall" [
        ← compileExprWithInternals fields dynamicSource internalFunctions gas,
        ← compileExprWithInternals fields dynamicSource internalFunctions target,
        ← compileExprWithInternals fields dynamicSource internalFunctions inOffset,
        ← compileExprWithInternals fields dynamicSource internalFunctions inSize,
        ← compileExprWithInternals fields dynamicSource internalFunctions outOffset,
        ← compileExprWithInternals fields dynamicSource internalFunctions outSize
      ])
  | Expr.calldatasize => pure (YulExpr.call "calldatasize" [])
  | Expr.calldataload offset => do
      pure (YulExpr.call "calldataload" [← compileExprWithInternals fields dynamicSource internalFunctions offset])
  | Expr.returndataSize => pure (YulExpr.call "returndatasize" [])
  | Expr.returndataOptionalBoolAt outOffset => do
      let outOffsetExpr ← compileExprWithInternals fields dynamicSource internalFunctions outOffset
      let rdSize := YulExpr.call "returndatasize" []
      pure (YulExpr.call "or" [
        YulExpr.call "eq" [rdSize, YulExpr.lit 0],
        YulExpr.call "and" [
          YulExpr.call "eq" [rdSize, YulExpr.lit 32],
          YulExpr.call "eq" [YulExpr.call "mload" [outOffsetExpr], YulExpr.lit 1]
        ]
      ])
  | Expr.localVar name => pure (YulExpr.ident name)
  | Expr.externalCall name args => do
      let argExprs ← compileExprListWithInternals fields dynamicSource internalFunctions args
      if name == builtinExpName then
        match argExprs with
        | [base, exponent] => pure (YulExpr.call "exp" [base, exponent])
        | _ => throw s!"Compilation error: builtin exp expects 2 args, got {argExprs.length}"
      else
        pure (YulExpr.call name argExprs)
  | Expr.internalCall functionName args => do
      let argExprs ← compileInternalCallArgs fields dynamicSource internalFunctions functionName args
      pure (YulExpr.call (internalFunctionYulName functionName) argExprs)
  | Expr.arrayLength name => pure (YulExpr.ident s!"{name}_length")
  | Expr.memoryArrayLength name => pure (YulExpr.ident s!"{name}_length")
  | Expr.arrayElement name index => do
      let indexExpr ← compileExprWithInternals fields dynamicSource internalFunctions index
      let helperName := match dynamicSource with
        | .calldata => checkedArrayElementCalldataHelperName
        | .memory => checkedArrayElementMemoryHelperName
      pure (YulExpr.call helperName [
        YulExpr.ident s!"{name}_data_offset",
        YulExpr.ident s!"{name}_length",
        indexExpr
      ])
  | Expr.memoryArrayElement name index => do
      let indexExpr ← compileExprWithInternals fields dynamicSource internalFunctions index
      pure (YulExpr.call checkedArrayElementMemoryHelperName [
        YulExpr.ident s!"{name}_data_offset",
        YulExpr.ident s!"{name}_length",
        indexExpr
      ])
  | Expr.arrayElementWord name index elementWords wordOffset => do
      if elementWords == 0 then
        throw s!"Compilation error: Expr.arrayElementWord '{name}' requires elementWords > 0"
      else if wordOffset >= elementWords then
        throw s!"Compilation error: Expr.arrayElementWord '{name}' wordOffset {wordOffset} is outside element width {elementWords}"
      else
        let indexExpr ← compileExprWithInternals fields dynamicSource internalFunctions index
        let helperName := match dynamicSource with
          | .calldata => checkedArrayElementWordCalldataHelperName
          | .memory => checkedArrayElementWordMemoryHelperName
        pure (YulExpr.call helperName [
          YulExpr.ident s!"{name}_data_offset",
          YulExpr.ident s!"{name}_length",
          indexExpr,
          YulExpr.lit elementWords,
          YulExpr.lit wordOffset
        ])
  | Expr.arrayElementDynamicWord name index wordOffset => do
      let indexExpr ← compileExprWithInternals fields dynamicSource internalFunctions index
      let helperName := match dynamicSource with
        | .calldata => checkedArrayElementDynamicWordCalldataHelperName
        | .memory => checkedArrayElementDynamicWordMemoryHelperName
      pure (YulExpr.call helperName [
        YulExpr.ident s!"{name}_data_offset",
        YulExpr.ident s!"{name}_length",
        indexExpr,
        YulExpr.lit wordOffset
      ])
  | Expr.arrayElementDynamicDataOffset name index => do
      let indexExpr ← compileExprWithInternals fields dynamicSource internalFunctions index
      let helperName := match dynamicSource with
        | .calldata => checkedArrayElementDynamicDataOffsetCalldataHelperName
        | .memory => checkedArrayElementDynamicDataOffsetMemoryHelperName
      pure (YulExpr.call helperName [
        YulExpr.ident s!"{name}_data_offset",
        YulExpr.ident s!"{name}_length",
        indexExpr
      ])
  | Expr.paramDynamicHeadWord name wordOffset => do
      let helperName := match dynamicSource with
        | .calldata => checkedParamDynamicHeadWordCalldataHelperName
        | .memory => checkedParamDynamicHeadWordMemoryHelperName
      pure (YulExpr.call helperName [
        YulExpr.ident s!"{name}_data_offset",
        YulExpr.lit wordOffset
      ])
  | Expr.paramDynamicMemberLength name wordOffset => do
      let helperName := match dynamicSource with
        | .calldata => checkedParamDynamicMemberLengthCalldataHelperName
        | .memory => checkedParamDynamicMemberLengthMemoryHelperName
      pure (YulExpr.call helperName [
        YulExpr.ident s!"{name}_data_offset",
        YulExpr.lit wordOffset
      ])
  | Expr.paramDynamicMemberDataOffset name wordOffset => do
      let helperName := match dynamicSource with
        | .calldata => checkedParamDynamicMemberDataOffsetCalldataHelperName
        | .memory => checkedParamDynamicMemberDataOffsetMemoryHelperName
      pure (YulExpr.call helperName [
        YulExpr.ident s!"{name}_data_offset",
        YulExpr.lit wordOffset
      ])
  | Expr.paramDynamicMemberElement name wordOffset innerIndex => do
      let innerIndexExpr ← compileExprWithInternals fields dynamicSource internalFunctions innerIndex
      let helperName := match dynamicSource with
        | .calldata => checkedParamDynamicMemberElementCalldataHelperName
        | .memory => checkedParamDynamicMemberElementMemoryHelperName
      pure (YulExpr.call helperName [
        YulExpr.ident s!"{name}_data_offset",
        YulExpr.lit wordOffset,
        innerIndexExpr
      ])
  | Expr.paramDynamicStaticComposite name wordOffset =>
      pure (YulExpr.call "add" [
        YulExpr.ident s!"{name}_data_offset",
        YulExpr.lit (wordOffset * 32)
      ])
  | Expr.arrayElementDynamicMemberLength name index wordOffset => do
      let indexExpr ← compileExprWithInternals fields dynamicSource internalFunctions index
      let helperName := match dynamicSource with
        | .calldata => checkedArrayElementDynamicMemberLengthCalldataHelperName
        | .memory => checkedArrayElementDynamicMemberLengthMemoryHelperName
      pure (YulExpr.call helperName [
        YulExpr.ident s!"{name}_data_offset",
        YulExpr.ident s!"{name}_length",
        indexExpr,
        YulExpr.lit wordOffset
      ])
  | Expr.arrayElementDynamicMemberDataOffset name index wordOffset => do
      let indexExpr ← compileExprWithInternals fields dynamicSource internalFunctions index
      let helperName := match dynamicSource with
        | .calldata => checkedArrayElementDynamicMemberDataOffsetCalldataHelperName
        | .memory => checkedArrayElementDynamicMemberDataOffsetMemoryHelperName
      pure (YulExpr.call helperName [
        YulExpr.ident s!"{name}_data_offset",
        YulExpr.ident s!"{name}_length",
        indexExpr,
        YulExpr.lit wordOffset
      ])
  | Expr.arrayElementDynamicMemberElement name index wordOffset innerIndex => do
      let indexExpr ← compileExprWithInternals fields dynamicSource internalFunctions index
      let innerIndexExpr ← compileExprWithInternals fields dynamicSource internalFunctions innerIndex
      let helperName := match dynamicSource with
        | .calldata => checkedArrayElementDynamicMemberElementCalldataHelperName
        | .memory => checkedArrayElementDynamicMemberElementMemoryHelperName
      pure (YulExpr.call helperName [
        YulExpr.ident s!"{name}_data_offset",
        YulExpr.ident s!"{name}_length",
        indexExpr,
        YulExpr.lit wordOffset,
        innerIndexExpr
      ])
  | Expr.storageArrayLength field =>
      match findFieldWithResolvedSlot fields field with
      | some (f, slot) =>
          match f.ty with
          | .dynamicArray _ =>
              pure (YulExpr.call "sload" [YulExpr.lit slot])
          | _ =>
              throw s!"Compilation error: field '{field}' is not a storage dynamic array; use Expr.storageArrayLength only with FieldType.dynamicArray"
      | none =>
          throw s!"Compilation error: unknown storage field '{field}'"
  | Expr.storageArrayElement field index =>
      match findFieldWithResolvedSlot fields field with
      | some (f, slot) =>
          match f.ty with
          | .dynamicArray _ => do
              pure (YulExpr.call checkedStorageArrayElementHelperName [
                YulExpr.lit slot,
                ← compileExprWithInternals fields dynamicSource internalFunctions index
              ])
          | _ =>
              throw s!"Compilation error: field '{field}' is not a storage dynamic array; use Expr.storageArrayElement only with FieldType.dynamicArray"
      | none =>
          throw s!"Compilation error: unknown storage field '{field}'"
  | Expr.dynamicBytesEq lhsName rhsName =>
      let helperName := match dynamicSource with
        | .calldata => dynamicBytesEqCalldataHelperName
        | .memory => dynamicBytesEqMemoryHelperName
      pure (YulExpr.call helperName [
        YulExpr.ident s!"{lhsName}_data_offset",
        YulExpr.ident s!"{lhsName}_length",
        YulExpr.ident s!"{rhsName}_data_offset",
        YulExpr.ident s!"{rhsName}_length"
      ])
  | Expr.add a b     => return yulBinOp "add" (← compileExprWithInternals fields dynamicSource internalFunctions a) (← compileExprWithInternals fields dynamicSource internalFunctions b)
  | Expr.sub a b     => return yulBinOp "sub" (← compileExprWithInternals fields dynamicSource internalFunctions a) (← compileExprWithInternals fields dynamicSource internalFunctions b)
  | Expr.mul a b     => return yulBinOp "mul" (← compileExprWithInternals fields dynamicSource internalFunctions a) (← compileExprWithInternals fields dynamicSource internalFunctions b)
  | Expr.div a b     => return yulBinOp "div" (← compileExprWithInternals fields dynamicSource internalFunctions a) (← compileExprWithInternals fields dynamicSource internalFunctions b)
  | Expr.sdiv a b    => return yulBinOp "sdiv" (← compileExprWithInternals fields dynamicSource internalFunctions a) (← compileExprWithInternals fields dynamicSource internalFunctions b)
  | Expr.mod a b     => return yulBinOp "mod" (← compileExprWithInternals fields dynamicSource internalFunctions a) (← compileExprWithInternals fields dynamicSource internalFunctions b)
  | Expr.smod a b    => return yulBinOp "smod" (← compileExprWithInternals fields dynamicSource internalFunctions a) (← compileExprWithInternals fields dynamicSource internalFunctions b)
  | Expr.bitAnd a b  => return yulBinOp "and" (← compileExprWithInternals fields dynamicSource internalFunctions a) (← compileExprWithInternals fields dynamicSource internalFunctions b)
  | Expr.bitOr a b   => return yulBinOp "or"  (← compileExprWithInternals fields dynamicSource internalFunctions a) (← compileExprWithInternals fields dynamicSource internalFunctions b)
  | Expr.bitXor a b  => return yulBinOp "xor" (← compileExprWithInternals fields dynamicSource internalFunctions a) (← compileExprWithInternals fields dynamicSource internalFunctions b)
  | Expr.bitNot a    => return YulExpr.call "not" [← compileExprWithInternals fields dynamicSource internalFunctions a]
  | Expr.shl s v     => return yulBinOp "shl" (← compileExprWithInternals fields dynamicSource internalFunctions s) (← compileExprWithInternals fields dynamicSource internalFunctions v)
  | Expr.shr s v     => return yulBinOp "shr" (← compileExprWithInternals fields dynamicSource internalFunctions s) (← compileExprWithInternals fields dynamicSource internalFunctions v)
  | Expr.sar s v     => return yulBinOp "sar" (← compileExprWithInternals fields dynamicSource internalFunctions s) (← compileExprWithInternals fields dynamicSource internalFunctions v)
  | Expr.byte i v    => return yulBinOp "byte" (← compileExprWithInternals fields dynamicSource internalFunctions i) (← compileExprWithInternals fields dynamicSource internalFunctions v)
  | Expr.signextend b v =>
      return yulBinOp "signextend" (← compileExprWithInternals fields dynamicSource internalFunctions b) (← compileExprWithInternals fields dynamicSource internalFunctions v)
  | Expr.intrinsic name lowering _minFork args => do
      let argExprs ← compileExprListWithInternals fields dynamicSource internalFunctions args
      match lowering with
      | .verbatim inArity outArity opcodeHex =>
          if outArity != 1 then
            throw s!"Compilation error: intrinsic {name} must produce exactly 1 output, got {outArity}"
          if args.length != inArity then
            throw s!"Compilation error: intrinsic {name} expects {inArity} arg(s), got {args.length}"
          pure (YulExpr.call (Verity.Core.Intrinsics.YulLowering.callName lowering)
            (YulExpr.verbatimHex opcodeHex :: argExprs))
      | .builtin builtinName =>
          let some (inArity, outArity) := Verity.Core.Intrinsics.yulBuiltinArity? builtinName
            | throw s!"Compilation error: intrinsic {name} targets unknown Yul builtin '{builtinName}'"
          if outArity != 1 then
            throw s!"Compilation error: intrinsic {name} builtin {builtinName} must produce exactly 1 output, got {outArity}"
          if args.length != inArity then
            throw s!"Compilation error: intrinsic {name} builtin {builtinName} expects {inArity} arg(s), got {args.length}"
          pure (YulExpr.call builtinName argExprs)
  | Expr.forkIfAtLeast required _thenExpr _elseExpr =>
      throw s!"Compilation error: unresolved fork_if_at_least {required}; compile through compileSpecsWithOptions so the branch can be selected from --target-fork before Yul emission"
  | Expr.eq a b      => return yulBinOp "eq"  (← compileExprWithInternals fields dynamicSource internalFunctions a) (← compileExprWithInternals fields dynamicSource internalFunctions b)
  | Expr.gt a b      => return yulBinOp "gt"  (← compileExprWithInternals fields dynamicSource internalFunctions a) (← compileExprWithInternals fields dynamicSource internalFunctions b)
  | Expr.sgt a b     => return yulBinOp "sgt" (← compileExprWithInternals fields dynamicSource internalFunctions a) (← compileExprWithInternals fields dynamicSource internalFunctions b)
  | Expr.lt a b      => return yulBinOp "lt"  (← compileExprWithInternals fields dynamicSource internalFunctions a) (← compileExprWithInternals fields dynamicSource internalFunctions b)
  | Expr.slt a b     => return yulBinOp "slt" (← compileExprWithInternals fields dynamicSource internalFunctions a) (← compileExprWithInternals fields dynamicSource internalFunctions b)
  | Expr.ge a b      => return yulNegatedBinOp "lt" (← compileExprWithInternals fields dynamicSource internalFunctions a) (← compileExprWithInternals fields dynamicSource internalFunctions b)
  | Expr.le a b      => return yulNegatedBinOp "gt" (← compileExprWithInternals fields dynamicSource internalFunctions a) (← compileExprWithInternals fields dynamicSource internalFunctions b)
  | Expr.logicalAnd a b => return yulBinOp "and" (yulToBool (← compileExprWithInternals fields dynamicSource internalFunctions a)) (yulToBool (← compileExprWithInternals fields dynamicSource internalFunctions b))
  | Expr.logicalOr a b  => return yulBinOp "or"  (yulToBool (← compileExprWithInternals fields dynamicSource internalFunctions a)) (yulToBool (← compileExprWithInternals fields dynamicSource internalFunctions b))
  | Expr.logicalNot a   => return YulExpr.call "iszero" [← compileExprWithInternals fields dynamicSource internalFunctions a]
  | Expr.ceilDiv a b => do
      let ca ← compileExprWithInternals fields dynamicSource internalFunctions a
      let cb ← compileExprWithInternals fields dynamicSource internalFunctions b
      -- mul(iszero(iszero(a)), add(div(sub(a, 1), b), 1))
      -- When a == 0: iszero(iszero(0)) = 0, so result = 0
      -- When a > 0: iszero(iszero(a)) = 1, so result = (a-1)/b + 1
      pure (YulExpr.call "mul" [
        YulExpr.call "iszero" [YulExpr.call "iszero" [ca]],
        YulExpr.call "add" [
          YulExpr.call "div" [YulExpr.call "sub" [ca, YulExpr.lit 1], cb],
          YulExpr.lit 1
        ]
      ])
  | Expr.mulDivDown a b c => do
      let ca ← compileExprWithInternals fields dynamicSource internalFunctions a
      let cb ← compileExprWithInternals fields dynamicSource internalFunctions b
      let cc ← compileExprWithInternals fields dynamicSource internalFunctions c
      -- div(mul(a, b), c)
      pure (YulExpr.call "div" [YulExpr.call "mul" [ca, cb], cc])
  | Expr.mulDivUp a b c => do
      let ca ← compileExprWithInternals fields dynamicSource internalFunctions a
      let cb ← compileExprWithInternals fields dynamicSource internalFunctions b
      let cc ← compileExprWithInternals fields dynamicSource internalFunctions c
      -- div(add(mul(a, b), sub(c, 1)), c)
      pure (YulExpr.call "div" [
        YulExpr.call "add" [
          YulExpr.call "mul" [ca, cb],
          YulExpr.call "sub" [cc, YulExpr.lit 1]
        ],
        cc
      ])
  -- verity#1761: full-precision `a * b / c` using the OpenZeppelin /
  -- Solmate `FullMath.mulDiv` algorithm. The intermediate product is
  -- handled at 512-bit precision; the helper reverts on zero divisor
  -- or when the quotient does not fit in `uint256`.
  | Expr.mulDiv512Down a b c => do
      let ca ← compileExprWithInternals fields dynamicSource internalFunctions a
      let cb ← compileExprWithInternals fields dynamicSource internalFunctions b
      let cc ← compileExprWithInternals fields dynamicSource internalFunctions c
      pure (YulExpr.call fullMulDivHelperName [ca, cb, cc])
  | Expr.mulDiv512Up a b c => do
      let ca ← compileExprWithInternals fields dynamicSource internalFunctions a
      let cb ← compileExprWithInternals fields dynamicSource internalFunctions b
      let cc ← compileExprWithInternals fields dynamicSource internalFunctions c
      pure (YulExpr.call fullMulDivUpHelperName [ca, cb, cc])
  | Expr.wMulDown a b => do
      let ca ← compileExprWithInternals fields dynamicSource internalFunctions a
      let cb ← compileExprWithInternals fields dynamicSource internalFunctions b
      -- div(mul(a, b), 1000000000000000000)
      pure (YulExpr.call "div" [YulExpr.call "mul" [ca, cb], YulExpr.lit 1000000000000000000])
  | Expr.wDivUp a b => do
      let ca ← compileExprWithInternals fields dynamicSource internalFunctions a
      let cb ← compileExprWithInternals fields dynamicSource internalFunctions b
      -- div(add(mul(a, 1000000000000000000), sub(b, 1)), b)
      pure (YulExpr.call "div" [
        YulExpr.call "add" [
          YulExpr.call "mul" [ca, YulExpr.lit 1000000000000000000],
          YulExpr.call "sub" [cb, YulExpr.lit 1]
        ],
        cb
      ])
  | Expr.min a b => do
      let ca ← compileExprWithInternals fields dynamicSource internalFunctions a
      let cb ← compileExprWithInternals fields dynamicSource internalFunctions b
      -- sub(a, mul(sub(a, b), gt(a, b)))
      pure (YulExpr.call "sub" [ca,
        YulExpr.call "mul" [
          YulExpr.call "sub" [ca, cb],
          YulExpr.call "gt" [ca, cb]
        ]
      ])
  | Expr.max a b => do
      let ca ← compileExprWithInternals fields dynamicSource internalFunctions a
      let cb ← compileExprWithInternals fields dynamicSource internalFunctions b
      -- add(a, mul(sub(b, a), gt(b, a)))
      pure (YulExpr.call "add" [ca,
        YulExpr.call "mul" [
          YulExpr.call "sub" [cb, ca],
          YulExpr.call "gt" [cb, ca]
        ]
      ])
  | Expr.ite cond thenVal elseVal => do
      let condExpr ← compileExprWithInternals fields dynamicSource internalFunctions cond
      let thenExpr ← compileExprWithInternals fields dynamicSource internalFunctions thenVal
      let elseExpr ← compileExprWithInternals fields dynamicSource internalFunctions elseVal
      -- Branchless ternary: add(mul(iszero(iszero(cond)), thenVal), mul(iszero(cond), elseVal))
      let condBool := YulExpr.call "iszero" [YulExpr.call "iszero" [condExpr]]
      let condNeg := YulExpr.call "iszero" [condExpr]
      pure (YulExpr.call "add" [
        YulExpr.call "mul" [condBool, thenExpr],
        YulExpr.call "mul" [condNeg, elseExpr]
      ])
  -- ADT expressions: storage-backed tagged unions (#1727 Steps 5c/5d)
  | Expr.adtConstruct adtName variantName _args =>
      throw s!"Compilation error: ADT construct '{adtName}.{variantName}' cannot be used in expression position. ADT construction expands to multiple sstores and must be compiled at the statement level."
  | Expr.adtTag _adtName storageField =>
      -- Tag byte: sload(baseSlot) & 0xFF
      match findFieldSlot fields storageField with
      | some baseSlot =>
          pure (compileAdtTagRead (YulExpr.lit baseSlot))
      | none => throw s!"Compilation error: unknown storage field '{storageField}' for ADT tag read"
  | Expr.adtField _adtName _variantName _fieldName fieldIndex storageField =>
      -- Field read: sload(baseSlot + fieldIndex + 1)
      match findFieldSlot fields storageField with
      | some baseSlot =>
          pure (compileAdtFieldRead (YulExpr.lit baseSlot) fieldIndex)
      | none => throw s!"Compilation error: unknown storage field '{storageField}' for ADT field read"
end

def compileExprList (fields : List Field)
    (dynamicSource : DynamicDataSource := .calldata) (exprs : List Expr) :
    Except String (List YulExpr) :=
  compileExprListWithInternals fields dynamicSource [] exprs

def compileExpr (fields : List Field)
    (dynamicSource : DynamicDataSource := .calldata) (expr : Expr) :
    Except String YulExpr :=
  compileExprWithInternals fields dynamicSource [] expr

-- Compile require condition to a "failure" predicate to avoid double-negation.
def compileRequireFailCondWithInternals (fields : List Field)
    (dynamicSource : DynamicDataSource := .calldata)
    (internalFunctions : List FunctionSpec := []) :
    Expr → Except String YulExpr
  | Expr.ge a b => return yulBinOp "lt" (← compileExprWithInternals fields dynamicSource internalFunctions a) (← compileExprWithInternals fields dynamicSource internalFunctions b)
  | Expr.le a b => return yulBinOp "gt" (← compileExprWithInternals fields dynamicSource internalFunctions a) (← compileExprWithInternals fields dynamicSource internalFunctions b)
  | cond => return YulExpr.call "iszero" [← compileExprWithInternals fields dynamicSource internalFunctions cond]

def compileRequireFailCond (fields : List Field)
    (dynamicSource : DynamicDataSource := .calldata) (cond : Expr) :
    Except String YulExpr :=
  compileRequireFailCondWithInternals fields dynamicSource [] cond

theorem compileExprWithInternals_nil_eq
    (fields : List Field) (dynamicSource : DynamicDataSource) (expr : Expr) :
    compileExprWithInternals fields dynamicSource [] expr =
      compileExpr fields dynamicSource expr := rfl

theorem compileExprListWithInternals_nil_eq
    (fields : List Field) (dynamicSource : DynamicDataSource) (exprs : List Expr) :
    compileExprListWithInternals fields dynamicSource [] exprs =
      compileExprList fields dynamicSource exprs := rfl

theorem compileRequireFailCondWithInternals_nil_eq
    (fields : List Field) (dynamicSource : DynamicDataSource) (cond : Expr) :
    compileRequireFailCondWithInternals fields dynamicSource [] cond =
      compileRequireFailCond fields dynamicSource cond := rfl

end Compiler.CompilationModel

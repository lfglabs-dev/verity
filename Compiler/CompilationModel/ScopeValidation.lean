import Compiler.CompilationModel.Types
import Compiler.CompilationModel.AbiTypeLayout
import Compiler.CompilationModel.InternalArgs
import Compiler.CompilationModel.IssueRefs
import Compiler.CompilationModel.LogicalPurity
import Compiler.CompilationModel.EcmAxiomCollection

set_option maxHeartbeats 800000

namespace Compiler.CompilationModel

def findParamType (params : List Param) (name : String) : Option ParamType :=
  (params.find? (fun p => p.name == name)).map (·.ty)

mutual
  def isDynamicParamTypeForScope : ParamType → Bool
    | ParamType.uint256 => false
    | ParamType.int256 => false
    | ParamType.uint8 => false
    | ParamType.uint16 => false
    | ParamType.address => false
    | ParamType.bool => false
    | ParamType.bytes32 => false
    | ParamType.string => true
    | ParamType.array _ => true
    | ParamType.bytes => true
    | ParamType.fixedArray elemTy _ => isDynamicParamTypeForScope elemTy
    | ParamType.tuple elemTys => paramTypeListAnyDynamicForScope elemTys
    | ParamType.adt _ _ => false
    | ParamType.newtypeOf _ baseType => isDynamicParamTypeForScope baseType
termination_by ty => sizeOf ty
decreasing_by all_goals simp_wf; all_goals omega

def paramTypeListAnyDynamicForScope : List ParamType → Bool
  | [] => false
  | ty :: rest => isDynamicParamTypeForScope ty || paramTypeListAnyDynamicForScope rest
termination_by tys => sizeOf tys
decreasing_by all_goals simp_wf; all_goals omega
end

def isScalarParamTypeForScope : ParamType → Bool
  | ParamType.uint256 | ParamType.int256 | ParamType.uint8 | ParamType.uint16 | ParamType.address | ParamType.bool | ParamType.bytes32 => true
  | _ => false

def paramBindingNames (param : Param) : List String :=
  let names :=
    if isDynamicParamTypeForScope param.ty then
      dynamicParamBindingNames param.name ++ [param.name]
    else
      match param.ty with
      | ParamType.fixedArray elemTy n =>
          let staticNames := staticParamBindingNames param.name param.ty
          if n == 0 then
            staticNames
          else if isScalarParamTypeForScope elemTy then
            -- Keep `<name>` in scope for backward-compatible scalar fixed-array aliasing.
            staticNames ++ [param.name]
          else
            staticNames
      | _ =>
          staticParamBindingNames param.name param.ty
  if names.contains param.name then names else names ++ [param.name]

def paramScopeNames (params : List Param) : List String :=
  params.flatMap paramBindingNames

def dynamicParamBases (params : List Param) : List String :=
  (params.filter (fun p => isDynamicParamTypeForScope p.ty)).map (·.name)

mutual
def validateScopedExprIdentifiers
    (context : String) (params : List Param) (paramScope : List String) (dynamicParams : List String)
    (immutableNames : List String) (localScope : List String) (constructorArgCount : Option Nat) : Expr → Except String Unit
  | Expr.param name =>
      if paramScope.contains name then
        pure ()
      else
        throw s!"Compilation error: {context} references unknown parameter '{name}'"
  | Expr.constructorArg idx =>
      match constructorArgCount with
      | some count =>
          if idx < count then
            pure ()
          else
            throw s!"Compilation error: constructor Expr.constructorArg {idx} is out of bounds for {count} constructor parameter(s)"
      | none =>
          throw s!"Compilation error: {context} uses Expr.constructorArg outside constructor scope"
  | Expr.immutable name =>
      if immutableNames.isEmpty || immutableNames.contains name then
        pure ()
      else
        throw s!"Compilation error: {context} references unknown immutable '{name}'"
  | Expr.localVar name =>
      if localScope.contains name then
        pure ()
      else
        throw s!"Compilation error: {context} references unknown local variable '{name}'"
  | Expr.arrayLength name =>
      match findParamType params name with
      | some (ParamType.array _) => pure ()
      | some ty =>
          throw s!"Compilation error: {context} Expr.arrayLength '{name}' requires array parameter, got {repr ty}"
      | none =>
          throw s!"Compilation error: {context} references unknown parameter '{name}' in Expr.arrayLength"
  | Expr.memoryArrayLength name =>
      if localScope.contains s!"{name}_data_offset" && localScope.contains s!"{name}_length" then
        pure ()
      else
        throw s!"Compilation error: {context} Expr.memoryArrayLength '{name}' requires local bindings '{name}_data_offset' and '{name}_length'"
  | Expr.storageArrayLength _ =>
      pure ()
  | Expr.storageArrayElement _ index => do
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount index
  | Expr.arrayElement name index => do
      match findParamType params name with
      | some ty@(ParamType.array elemTy) =>
          if isSingleWordStaticParamType elemTy then
            pure ()
          else
            throw s!"Compilation error: {context} Expr.arrayElement '{name}' requires an array with single-word static elements, got {repr ty}"
      | some ty =>
          throw s!"Compilation error: {context} Expr.arrayElement '{name}' requires array parameter, got {repr ty}"
      | none =>
          throw s!"Compilation error: {context} references unknown parameter '{name}' in Expr.arrayElement"
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount index
  | Expr.memoryArrayElement name index => do
      if localScope.contains s!"{name}_data_offset" && localScope.contains s!"{name}_length" then
        pure ()
      else
        throw s!"Compilation error: {context} Expr.memoryArrayElement '{name}' requires local bindings '{name}_data_offset' and '{name}_length'"
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount index
  | Expr.arrayElementWord name index elementWords wordOffset => do
      if elementWords == 0 then
        throw s!"Compilation error: {context} Expr.arrayElementWord '{name}' requires elementWords > 0"
      else if wordOffset >= elementWords then
        throw s!"Compilation error: {context} Expr.arrayElementWord '{name}' wordOffset {wordOffset} is outside element width {elementWords}"
      match findParamType params name with
      | some ty@(ParamType.array elemTy) =>
          if isDynamicParamType elemTy then
            throw s!"Compilation error: {context} Expr.arrayElementWord '{name}' requires an array parameter with static ABI-word elements, got {repr ty}"
          else
            let expectedWords := paramLocalHeadWords elemTy
            if elementWords == expectedWords then
              pure ()
            else
              throw s!"Compilation error: {context} Expr.arrayElementWord '{name}' element width {elementWords} does not match ABI width {expectedWords} for {repr ty}"
      | some ty =>
          throw s!"Compilation error: {context} Expr.arrayElementWord '{name}' requires array parameter, got {repr ty}"
      | none =>
          throw s!"Compilation error: {context} references unknown parameter '{name}' in Expr.arrayElementWord"
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount index
  | Expr.arrayElementDynamicWord name index wordOffset => do
      match findParamType params name with
      | some ty@(ParamType.array elemTy) =>
          if isDynamicParamType elemTy then
            let expectedWords := paramLocalHeadWords elemTy
            if wordOffset < expectedWords then
              pure ()
            else
              throw s!"Compilation error: {context} Expr.arrayElementDynamicWord '{name}' wordOffset {wordOffset} is outside dynamic element head width {expectedWords} for {repr ty}"
          else
            throw s!"Compilation error: {context} Expr.arrayElementDynamicWord '{name}' requires an array parameter with dynamic ABI elements, got {repr ty}"
      | some ty =>
          throw s!"Compilation error: {context} Expr.arrayElementDynamicWord '{name}' requires array parameter, got {repr ty}"
      | none =>
          throw s!"Compilation error: {context} references unknown parameter '{name}' in Expr.arrayElementDynamicWord"
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount index
  | Expr.arrayElementDynamicDataOffset name index => do
      match findParamType params name with
      | some ty@(ParamType.array elemTy) =>
          if isDynamicParamType elemTy then
            pure ()
          else
            throw s!"Compilation error: {context} Expr.arrayElementDynamicDataOffset '{name}' requires an array parameter with dynamic ABI elements, got {repr ty}"
      | some ty =>
          throw s!"Compilation error: {context} Expr.arrayElementDynamicDataOffset '{name}' requires array parameter, got {repr ty}"
      | none =>
          throw s!"Compilation error: {context} references unknown parameter '{name}' in Expr.arrayElementDynamicDataOffset"
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount index
  | Expr.arrayElementDynamicMemberLength name index wordOffset => do
      match findParamType params name with
      | some ty@(ParamType.array elemTy) =>
          if isDynamicParamType elemTy then
            let expectedWords := paramLocalHeadWords elemTy
            if wordOffset < expectedWords then
              pure ()
            else
              throw s!"Compilation error: {context} Expr.arrayElementDynamicMemberLength '{name}' wordOffset {wordOffset} is outside dynamic element head width {expectedWords} for {repr ty}"
          else
            throw s!"Compilation error: {context} Expr.arrayElementDynamicMemberLength '{name}' requires an array parameter with dynamic ABI elements, got {repr ty}"
      | some ty =>
          throw s!"Compilation error: {context} Expr.arrayElementDynamicMemberLength '{name}' requires array parameter, got {repr ty}"
      | none =>
          throw s!"Compilation error: {context} references unknown parameter '{name}' in Expr.arrayElementDynamicMemberLength"
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount index
  | Expr.arrayElementDynamicMemberDataOffset name index wordOffset => do
      match findParamType params name with
      | some ty@(ParamType.array elemTy) =>
          if isDynamicParamType elemTy then
            let expectedWords := paramLocalHeadWords elemTy
            if wordOffset < expectedWords then
              pure ()
            else
              throw s!"Compilation error: {context} Expr.arrayElementDynamicMemberDataOffset '{name}' wordOffset {wordOffset} is outside dynamic element head width {expectedWords} for {repr ty}"
          else
            throw s!"Compilation error: {context} Expr.arrayElementDynamicMemberDataOffset '{name}' requires an array parameter with dynamic ABI elements, got {repr ty}"
      | some ty =>
          throw s!"Compilation error: {context} Expr.arrayElementDynamicMemberDataOffset '{name}' requires array parameter, got {repr ty}"
      | none =>
          throw s!"Compilation error: {context} references unknown parameter '{name}' in Expr.arrayElementDynamicMemberDataOffset"
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount index
  | Expr.arrayElementDynamicMemberElement name index wordOffset innerIndex => do
      match findParamType params name with
      | some ty@(ParamType.array elemTy) =>
          if isDynamicParamType elemTy then
            let expectedWords := paramLocalHeadWords elemTy
            if wordOffset < expectedWords then
              pure ()
            else
              throw s!"Compilation error: {context} Expr.arrayElementDynamicMemberElement '{name}' wordOffset {wordOffset} is outside dynamic element head width {expectedWords} for {repr ty}"
          else
            throw s!"Compilation error: {context} Expr.arrayElementDynamicMemberElement '{name}' requires an array parameter with dynamic ABI elements, got {repr ty}"
      | some ty =>
          throw s!"Compilation error: {context} Expr.arrayElementDynamicMemberElement '{name}' requires array parameter, got {repr ty}"
      | none =>
          throw s!"Compilation error: {context} references unknown parameter '{name}' in Expr.arrayElementDynamicMemberElement"
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount index
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount innerIndex
  | Expr.paramDynamicHeadWord name wordOffset => do
      match findParamType params name with
      | some ty@(ParamType.tuple _) =>
          if isDynamicParamType ty then
            let expectedWords := paramLocalHeadWords ty
            if wordOffset < expectedWords then
              pure ()
            else
              throw s!"Compilation error: {context} Expr.paramDynamicHeadWord '{name}' wordOffset {wordOffset} is outside head width {expectedWords} for {repr ty}"
          else
            throw s!"Compilation error: {context} Expr.paramDynamicHeadWord '{name}' requires a dynamically-encoded tuple parameter, got {repr ty}"
      | some ty =>
          throw s!"Compilation error: {context} Expr.paramDynamicHeadWord '{name}' requires a tuple parameter, got {repr ty}"
      | none =>
          throw s!"Compilation error: {context} references unknown parameter '{name}' in Expr.paramDynamicHeadWord"
  | Expr.paramDynamicStaticComposite name wordOffset => do
      match findParamType params name with
      | some ty@(ParamType.tuple _) =>
          if isDynamicParamType ty then
            let expectedWords := paramLocalHeadWords ty
            if wordOffset < expectedWords then
              pure ()
            else
              throw s!"Compilation error: {context} Expr.paramDynamicStaticComposite '{name}' wordOffset {wordOffset} is outside head width {expectedWords} for {repr ty}"
          else
            throw s!"Compilation error: {context} Expr.paramDynamicStaticComposite '{name}' requires a dynamically-encoded tuple parameter, got {repr ty}"
      | some ty =>
          throw s!"Compilation error: {context} Expr.paramDynamicStaticComposite '{name}' requires a tuple parameter, got {repr ty}"
      | none =>
          throw s!"Compilation error: {context} references unknown parameter '{name}' in Expr.paramDynamicStaticComposite"
  | Expr.paramDynamicMemberLength name wordOffset
  | Expr.paramDynamicMemberDataOffset name wordOffset => do
      match findParamType params name with
      | some ty@(ParamType.tuple _) =>
          if isDynamicParamType ty then
            let expectedWords := paramLocalHeadWords ty
            if wordOffset < expectedWords then
              pure ()
            else
              throw s!"Compilation error: {context} dynamic member projection '{name}' wordOffset {wordOffset} is outside head width {expectedWords} for {repr ty}"
          else
            throw s!"Compilation error: {context} dynamic member projection '{name}' requires a dynamically-encoded tuple parameter, got {repr ty}"
      | some ty =>
          throw s!"Compilation error: {context} dynamic member projection '{name}' requires a tuple parameter, got {repr ty}"
      | none =>
          throw s!"Compilation error: {context} references unknown parameter '{name}' in dynamic member projection"
  | Expr.paramDynamicMemberElement name wordOffset innerIndex => do
      match findParamType params name with
      | some ty@(ParamType.tuple _) =>
          if isDynamicParamType ty then
            let expectedWords := paramLocalHeadWords ty
            if wordOffset < expectedWords then
              pure ()
            else
              throw s!"Compilation error: {context} Expr.paramDynamicMemberElement '{name}' wordOffset {wordOffset} is outside head width {expectedWords} for {repr ty}"
          else
            throw s!"Compilation error: {context} Expr.paramDynamicMemberElement '{name}' requires a dynamically-encoded tuple parameter, got {repr ty}"
      | some ty =>
          throw s!"Compilation error: {context} Expr.paramDynamicMemberElement '{name}' requires a tuple parameter, got {repr ty}"
      | none =>
          throw s!"Compilation error: {context} references unknown parameter '{name}' in Expr.paramDynamicMemberElement"
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount innerIndex
  | Expr.mapping _ key | Expr.mappingWord _ key _ | Expr.mappingPackedWord _ key _ _ | Expr.mappingUint _ key
  | Expr.structMember _ key _ =>
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount key
  | Expr.mappingChain _ keys =>
      validateScopedExprIdentifiersList context params paramScope dynamicParams immutableNames localScope constructorArgCount keys
  | Expr.mapping2 _ key1 key2 | Expr.mapping2Word _ key1 key2 _
  | Expr.structMember2 _ key1 key2 _ => do
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount key1
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount key2
  | Expr.call gas target value inOffset inSize outOffset outSize => do
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount gas
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount target
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount value
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount inOffset
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount inSize
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount outOffset
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount outSize
  | Expr.staticcall gas target inOffset inSize outOffset outSize => do
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount gas
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount target
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount inOffset
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount inSize
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount outOffset
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount outSize
  | Expr.delegatecall gas target inOffset inSize outOffset outSize => do
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount gas
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount target
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount inOffset
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount inSize
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount outOffset
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount outSize
  | Expr.extcodesize addr =>
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount addr
  | Expr.mload offset | Expr.tload offset =>
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount offset
  | Expr.calldataload offset =>
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount offset
  | Expr.keccak256 offset size => do
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount offset
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount size
  | Expr.returndataOptionalBoolAt outOffset =>
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount outOffset
  | Expr.externalCall _ args | Expr.internalCall _ args =>
      validateScopedExprIdentifiersList context params paramScope dynamicParams immutableNames localScope constructorArgCount args
  | Expr.dynamicBytesEq lhsName rhsName => do
      let ensureDynamicParam (name : String) : Except String Unit := do
        match findParamType params name with
        | some ParamType.bytes | some ParamType.string => pure ()
        | some ty =>
            throw s!"Compilation error: {context} Expr.dynamicBytesEq '{name}' requires bytes/string parameter, got {repr ty}"
        | none =>
            throw s!"Compilation error: {context} Expr.dynamicBytesEq references unknown parameter '{name}'"
      ensureDynamicParam lhsName
      ensureDynamicParam rhsName
  | Expr.add a b | Expr.sub a b | Expr.mul a b | Expr.div a b | Expr.sdiv a b | Expr.mod a b | Expr.smod a b |
    Expr.bitAnd a b | Expr.bitOr a b | Expr.bitXor a b | Expr.shl a b | Expr.shr a b |
    Expr.sar a b | Expr.signextend a b | Expr.byte a b |
    Expr.eq a b | Expr.ge a b | Expr.gt a b | Expr.sgt a b | Expr.lt a b | Expr.slt a b | Expr.le a b |
    Expr.wMulDown a b => do
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount a
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount b
  | Expr.intrinsic _ _ _ args =>
      validateScopedExprIdentifiersList context params paramScope dynamicParams immutableNames localScope constructorArgCount args
  | Expr.forkIfAtLeast _ thenExpr elseExpr => do
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount thenExpr
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount elseExpr
  | Expr.wDivUp a b => do
      validateArithDuplicatedOperandPurity context [b]
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount a
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount b
  | Expr.min a b | Expr.max a b => do
      validateArithDuplicatedOperandPurity context [a, b]
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount a
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount b
  | Expr.ceilDiv a b => do
      validateArithDuplicatedOperandPurity context [a]
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount a
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount b
  | Expr.mulDivDown a b c => do
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount a
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount b
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount c
  | Expr.mulDivUp a b c => do
      validateArithDuplicatedOperandPurity context [c]
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount a
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount b
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount c
  | Expr.mulDiv512Down a b c => do
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount a
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount b
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount c
  | Expr.mulDiv512Up a b c => do
      -- Unlike `mulDivUp` (which inlines `cc` twice in the emitted Yul),
      -- `mulDiv512Up` lowers to a single function call
      -- `__verity_full_mul_div_up(ca, cb, cc)` where each operand is
      -- evaluated exactly once at the call site. The `denominator`
      -- duplication only exists between the helper's local copies, so we
      -- do NOT need `validateArithDuplicatedOperandPurity` here. (verity#1761)
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount a
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount b
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount c
  | Expr.logicalAnd a b | Expr.logicalOr a b => do
      validateLogicalOperandPurity context a b
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount a
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount b
  | Expr.bitNot a | Expr.logicalNot a =>
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount a
  | Expr.ite cond thenVal elseVal => do
      if exprContainsCallLike cond || exprContainsCallLike thenVal || exprContainsCallLike elseVal then
        throw s!"Compilation error: {context} uses Expr.ite with call-like operand(s), which are eagerly evaluated ({issue748Ref}). Both branches execute regardless of the condition. Move call-like expressions into Stmt.letVar/Stmt.ite before using Expr.ite."
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount cond
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount thenVal
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount elseVal
  | Expr.adtConstruct _ _ args =>
      validateScopedExprIdentifiersList context params paramScope dynamicParams immutableNames localScope constructorArgCount args
  | Expr.adtTag _ _ =>
      pure ()
  | Expr.adtField _ _ _ _ _ =>
      pure ()
  | Expr.literal _ | Expr.storage _ | Expr.storageAddr _ | Expr.caller | Expr.contractAddress | Expr.txOrigin | Expr.chainid
  | Expr.msgValue | Expr.selfBalance | Expr.blockTimestamp | Expr.blockNumber | Expr.blobbasefee
  | Expr.calldatasize | Expr.returndataSize =>
      pure ()
termination_by e => sizeOf e
decreasing_by all_goals simp_wf; all_goals omega

def validateScopedExprIdentifiersList
    (context : String) (params : List Param) (paramScope : List String) (dynamicParams : List String)
    (immutableNames : List String) (localScope : List String) (constructorArgCount : Option Nat) : List Expr → Except String Unit
  | [] => pure ()
  | e :: es => do
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount e
      validateScopedExprIdentifiersList context params paramScope dynamicParams immutableNames localScope constructorArgCount es
termination_by es => sizeOf es
decreasing_by all_goals simp_wf; all_goals omega

def validateScopedStmtIdentifiers
    (context : String) (params : List Param) (paramScope : List String) (dynamicParams : List String)
    (immutableNames : List String) (localScope : List String) (constructorArgCount : Option Nat) : Stmt → Except String (List String)
  | Stmt.letVar name value => do
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount value
      if paramScope.contains name then
        throw s!"Compilation error: {context} declares local variable '{name}' that shadows a parameter"
      if localScope.contains name then
        throw s!"Compilation error: {context} redeclares local variable '{name}' in the same scope"
      pure (name :: localScope)
  | Stmt.assignVar name value => do
      if !localScope.contains name then
        throw s!"Compilation error: {context} assigns to undeclared local variable '{name}'"
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount value
      pure localScope
  | Stmt.setStorage _ value | Stmt.setStorageAddr _ value | Stmt.setStorageWord _ _ value
  | Stmt.return value | Stmt.require value _ => do
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount value
      pure localScope
  | Stmt.setImmutable name value => do
      match constructorArgCount with
      | some _ => pure ()
      | none =>
          throw s!"Compilation error: {context} uses Stmt.setImmutable '{name}' outside constructor scope"
      if immutableNames.isEmpty || immutableNames.contains name then
        pure ()
      else
        throw s!"Compilation error: {context} sets unknown immutable '{name}'"
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount value
      pure localScope
  | Stmt.storageArrayPush _ value => do
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount value
      pure localScope
  | Stmt.storageArrayPop _ =>
      pure localScope
  | Stmt.setStorageArrayElement _ index value => do
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount index
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount value
      pure localScope
  | Stmt.setMapping _ key value | Stmt.setMappingWord _ key _ value | Stmt.setMappingPackedWord _ key _ _ value | Stmt.setMappingUint _ key value
  | Stmt.setStructMember _ key _ value => do
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount key
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount value
      pure localScope
  | Stmt.setMappingChain _ keys value => do
      validateScopedExprIdentifiersList context params paramScope dynamicParams immutableNames localScope constructorArgCount keys
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount value
      pure localScope
  | Stmt.setMapping2 _ key1 key2 value | Stmt.setMapping2Word _ key1 key2 _ value
  | Stmt.setStructMember2 _ key1 key2 _ value => do
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount key1
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount key2
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount value
      pure localScope
  | Stmt.requireError cond _ args => do
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount cond
      validateScopedExprIdentifiersList context params paramScope dynamicParams immutableNames localScope constructorArgCount args
      pure localScope
  | Stmt.revertError _ args | Stmt.emit _ args | Stmt.returnValues args => do
      validateScopedExprIdentifiersList context params paramScope dynamicParams immutableNames localScope constructorArgCount args
      pure localScope
  | Stmt.mstore offset value => do
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount offset
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount value
      pure localScope
  | Stmt.tstore offset value => do
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount offset
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount value
      pure localScope
  | Stmt.calldatacopy destOffset sourceOffset size => do
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount destOffset
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount sourceOffset
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount size
      pure localScope
  | Stmt.returndataCopy destOffset sourceOffset size => do
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount destOffset
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount sourceOffset
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount size
      pure localScope
  | Stmt.ite cond thenBranch elseBranch => do
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount cond
      let _ ← validateScopedStmtListIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount thenBranch
      let _ ← validateScopedStmtListIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount elseBranch
      pure localScope
  | Stmt.forEach varName count body => do
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount count
      let _ ← validateScopedStmtListIdentifiers context params paramScope dynamicParams immutableNames (varName :: localScope) constructorArgCount body
      pure localScope
  | Stmt.forEachSetBit varName bitmap body => do
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount bitmap
      let _ ← validateScopedStmtListIdentifiers context params paramScope dynamicParams immutableNames (varName :: localScope) constructorArgCount body
      pure localScope
  | Stmt.unsafeBlock _ body => do
      let _ ← validateScopedStmtListIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount body
      pure localScope
  | Stmt.matchAdt _ scrutinee branches => do
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount scrutinee
      validateScopedMatchBranches context params paramScope dynamicParams immutableNames localScope constructorArgCount branches
      pure localScope
  | Stmt.internalCall _ args => do
      validateScopedExprIdentifiersList context params paramScope dynamicParams immutableNames localScope constructorArgCount args
      pure localScope
  | Stmt.internalCallAssign names _ args => do
      validateScopedExprIdentifiersList context params paramScope dynamicParams immutableNames localScope constructorArgCount args
      pure (names.reverse ++ localScope)
  | Stmt.rawLog topics dataOffset dataSize => do
      validateScopedExprIdentifiersList context params paramScope dynamicParams immutableNames localScope constructorArgCount topics
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount dataOffset
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount dataSize
      pure localScope
  | Stmt.externalCallBind resultVars _ args => do
      validateScopedExprIdentifiersList context params paramScope dynamicParams immutableNames localScope constructorArgCount args
      pure (resultVars.reverse ++ localScope)
  | Stmt.tryExternalCallBind successVar resultVars _ args => do
      validateScopedExprIdentifiersList context params paramScope dynamicParams immutableNames localScope constructorArgCount args
      pure ((successVar :: resultVars).reverse ++ localScope)
  | Stmt.ecm mod args => do
      if args.length != mod.numArgs then
        throw s!"Compilation error: {context} uses ECM '{mod.name}' with {args.length} arguments but it expects {mod.numArgs}"
      validateScopedExprIdentifiersList context params paramScope dynamicParams immutableNames localScope constructorArgCount args
      let mut scope := localScope
      for rv in mod.resultVars do
        if paramScope.contains rv then
          throw s!"Compilation error: {context} ECM '{mod.name}' result '{rv}' shadows a parameter"
        if scope.contains rv then
          throw s!"Compilation error: {context} ECM '{mod.name}' redeclares result '{rv}' in the same scope"
        scope := rv :: scope
      pure scope
  | Stmt.returnArray name =>
      match findParamType params name with
      | some (ParamType.array _) => pure localScope
      | some ty =>
          throw s!"Compilation error: {context} Stmt.returnArray '{name}' requires array parameter or memory-array local, got {repr ty}"
      | none =>
          if localScope.contains s!"{name}_data_offset" && localScope.contains s!"{name}_length" then
            pure localScope
          else
            throw s!"Compilation error: {context} Stmt.returnArray '{name}' requires parameter '{name}' or local bindings '{name}_data_offset' and '{name}_length'"
  | Stmt.returnCodeData pointer => do
      validateScopedExprIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount pointer
      pure localScope
  | Stmt.returnBytes _ | Stmt.returnStorageWords _
  | Stmt.revertReturndata | Stmt.stop =>
      pure localScope
  | Stmt.unsafeYul fragment => do
      let mut scope := localScope
      for name in fragment.scopeEffects.bindNames do
        if paramScope.contains name then
          throw s!"Compilation error: {context} unsafe Yul fragment '{fragment.label}' result '{name}' shadows a parameter"
        if scope.contains name then
          throw s!"Compilation error: {context} unsafe Yul fragment '{fragment.label}' redeclares result '{name}' in the same scope"
        scope := name :: scope
      for name in fragment.scopeEffects.assignNames do
        if !scope.contains name then
          throw s!"Compilation error: {context} unsafe Yul fragment '{fragment.label}' assigns to undeclared local variable '{name}'"
      pure scope
termination_by s => sizeOf s
decreasing_by all_goals simp_wf; all_goals omega

def validateScopedStmtListIdentifiers
    (context : String) (params : List Param) (paramScope : List String) (dynamicParams : List String)
    (immutableNames : List String) (localScope : List String) (constructorArgCount : Option Nat) : List Stmt → Except String (List String)
  | [] => pure localScope
  | stmt :: rest => do
      let nextScope ← validateScopedStmtIdentifiers context params paramScope dynamicParams immutableNames localScope constructorArgCount stmt
      validateScopedStmtListIdentifiers context params paramScope dynamicParams immutableNames nextScope constructorArgCount rest
termination_by ss => sizeOf ss
decreasing_by all_goals simp_wf; all_goals omega

def validateScopedMatchBranches
    (context : String) (params : List Param) (paramScope : List String) (dynamicParams : List String)
    (immutableNames : List String) (localScope : List String) (constructorArgCount : Option Nat) :
    List (String × List String × List Stmt) → Except String Unit
  | [] => pure ()
  | (_, varNames, body) :: rest => do
      let branchScope := varNames.reverse ++ localScope
      let _ ← validateScopedStmtListIdentifiers context params paramScope dynamicParams immutableNames branchScope constructorArgCount body
      validateScopedMatchBranches context params paramScope dynamicParams immutableNames localScope constructorArgCount rest
termination_by bs => sizeOf bs
decreasing_by all_goals simp_wf; all_goals omega
end

def validateFunctionIdentifierReferencesWithImmutables
    (immutableNames : List String) (spec : FunctionSpec) : Except String Unit := do
  let _ ← validateScopedStmtListIdentifiers
    s!"function '{spec.name}'"
    spec.params
    (paramScopeNames spec.params)
    (dynamicParamBases spec.params)
    immutableNames
    []
    none
    spec.body
  pure ()

def validateFunctionIdentifierReferences (spec : FunctionSpec) : Except String Unit :=
  validateFunctionIdentifierReferencesWithImmutables [] spec

theorem validateScopedStmtListIdentifiers_append_ok_inv
    {context : String}
    {params : List Param}
    {paramScope dynamicParams immutableNames localScope : List String}
    {constructorArgCount : Option Nat}
    {pre post : List Stmt}
    {finalScope : List String}
    (hvalidate :
      validateScopedStmtListIdentifiers
        context params paramScope dynamicParams immutableNames localScope constructorArgCount
        (pre ++ post) = Except.ok finalScope) :
    ∃ midScope,
      validateScopedStmtListIdentifiers
        context params paramScope dynamicParams immutableNames localScope constructorArgCount
        pre = Except.ok midScope ∧
      validateScopedStmtListIdentifiers
        context params paramScope dynamicParams immutableNames midScope constructorArgCount
        post = Except.ok finalScope := by
  induction pre generalizing localScope with
  | nil =>
      refine ⟨localScope, ?_, ?_⟩
      · unfold validateScopedStmtListIdentifiers
        rfl
      · simpa using hvalidate
  | cons stmt rest ih =>
      simp [validateScopedStmtListIdentifiers] at hvalidate
      cases hnext :
          validateScopedStmtIdentifiers
            context params paramScope dynamicParams immutableNames localScope constructorArgCount stmt with
      | error err =>
          simp [hnext] at hvalidate
          cases hvalidate
      | ok nextScope =>
          simp [hnext] at hvalidate
          rcases ih (localScope := nextScope) hvalidate with
            ⟨midScope, hprefix, hsuffix⟩
          refine ⟨midScope, ?_, hsuffix⟩
          simpa [validateScopedStmtListIdentifiers, hnext] using hprefix

theorem validateScopedStmtListIdentifiers_cons_ok_inv
    {context : String}
    {params : List Param}
    {paramScope dynamicParams immutableNames localScope : List String}
    {constructorArgCount : Option Nat}
    {stmt : Stmt}
    {rest : List Stmt}
    {finalScope : List String}
    (hvalidate :
      validateScopedStmtListIdentifiers
        context params paramScope dynamicParams immutableNames localScope constructorArgCount
        (stmt :: rest) = Except.ok finalScope) :
    ∃ nextScope,
      validateScopedStmtIdentifiers
        context params paramScope dynamicParams immutableNames localScope constructorArgCount
        stmt = Except.ok nextScope ∧
      validateScopedStmtListIdentifiers
        context params paramScope dynamicParams immutableNames nextScope constructorArgCount
        rest = Except.ok finalScope := by
  simp [validateScopedStmtListIdentifiers] at hvalidate
  cases hnext :
      validateScopedStmtIdentifiers
        context params paramScope dynamicParams immutableNames localScope constructorArgCount stmt with
  | error err =>
      simp [hnext] at hvalidate
      cases hvalidate
  | ok nextScope =>
      simp [hnext] at hvalidate
      refine ⟨nextScope, ?_, hvalidate⟩
      simp

theorem validateScopedStmtListIdentifiers_singleton_ok_inv
    {context : String}
    {params : List Param}
    {paramScope dynamicParams immutableNames localScope : List String}
    {constructorArgCount : Option Nat}
    {stmt : Stmt}
    {finalScope : List String}
    (hvalidate :
      validateScopedStmtListIdentifiers
        context params paramScope dynamicParams immutableNames localScope constructorArgCount
        [stmt] = Except.ok finalScope) :
    validateScopedStmtIdentifiers
      context params paramScope dynamicParams immutableNames localScope constructorArgCount
      stmt = Except.ok finalScope := by
  rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
    ⟨nextScope, hstmt, hnil⟩
  have hEq : nextScope = finalScope := by
    simp [validateScopedStmtListIdentifiers] at hnil
    injection hnil with hEq
  simpa [hEq] using hstmt

theorem validateFunctionIdentifierReferences_prefix_ok
    {spec : FunctionSpec}
    {pre post : List Stmt}
    (hvalidate : validateFunctionIdentifierReferences spec = Except.ok ())
    (hbody : spec.body = pre ++ post) :
    ∃ localScope,
      validateScopedStmtListIdentifiers
        s!"function '{spec.name}'"
        spec.params
        (paramScopeNames spec.params)
        (dynamicParamBases spec.params)
        []
        []
        none
        pre = Except.ok localScope := by
  unfold validateFunctionIdentifierReferences validateFunctionIdentifierReferencesWithImmutables at hvalidate
  rw [hbody] at hvalidate
  cases hscoped :
      validateScopedStmtListIdentifiers
        s!"function '{spec.name}'"
        spec.params
        (paramScopeNames spec.params)
        (dynamicParamBases spec.params)
        []
        []
        none
        (pre ++ post) with
  | error err =>
      simp [hscoped] at hvalidate
      cases hvalidate
  | ok finalScope =>
      simp [hscoped] at hvalidate
      rcases validateScopedStmtListIdentifiers_append_ok_inv hscoped with
        ⟨localScope, hprefix, _⟩
      exact ⟨localScope, hprefix⟩

theorem validateFunctionIdentifierReferences_prefix_stmt_ok
    {spec : FunctionSpec}
    {pre post : List Stmt}
    {stmt : Stmt}
    (hvalidate : validateFunctionIdentifierReferences spec = Except.ok ())
    (hbody : spec.body = pre ++ stmt :: post) :
    ∃ localScope nextScope,
      validateScopedStmtListIdentifiers
        s!"function '{spec.name}'"
        spec.params
        (paramScopeNames spec.params)
        (dynamicParamBases spec.params)
        []
        []
        none
        pre = Except.ok localScope ∧
      validateScopedStmtIdentifiers
        s!"function '{spec.name}'"
        spec.params
        (paramScopeNames spec.params)
        (dynamicParamBases spec.params)
        []
        localScope
        none
        stmt = Except.ok nextScope := by
  have hprefix :
      ∃ midScope,
        validateScopedStmtListIdentifiers
          s!"function '{spec.name}'"
          spec.params
          (paramScopeNames spec.params)
          (dynamicParamBases spec.params)
          []
          []
          none
          (pre ++ stmt :: []) = Except.ok midScope := by
    have hbody' : spec.body = (pre ++ stmt :: []) ++ post := by
      simpa [List.append_assoc] using hbody
    rcases validateFunctionIdentifierReferences_prefix_ok hvalidate hbody' with
      ⟨midScope, hprefix'⟩
    exact ⟨midScope, hprefix'⟩
  rcases hprefix with ⟨midScope, hprefix⟩
  rcases validateScopedStmtListIdentifiers_append_ok_inv hprefix with
    ⟨localScope, hprefixOnly, hstmtOnly⟩
  simp [validateScopedStmtListIdentifiers] at hstmtOnly
  cases hnext :
      validateScopedStmtIdentifiers
        s!"function '{spec.name}'"
        spec.params
        (paramScopeNames spec.params)
        (dynamicParamBases spec.params)
        []
        localScope
        none
        stmt with
  | error err =>
      simp [hnext] at hstmtOnly
  | ok nextScope =>
      simp [hnext] at hstmtOnly
      refine ⟨localScope, nextScope, hprefixOnly, ?_⟩
      simp [hnext]

def validateConstructorIdentifierReferencesWithImmutables
    (immutableNames : List String) (ctor : Option ConstructorSpec) : Except String Unit := do
  match ctor with
  | none => pure ()
  | some spec =>
      let _ ← validateScopedStmtListIdentifiers
        "constructor"
        spec.params
        (paramScopeNames spec.params)
        (dynamicParamBases spec.params)
        immutableNames
        []
        (some spec.params.length)
        spec.body
      pure ()

def validateConstructorIdentifierReferences (ctor : Option ConstructorSpec) : Except String Unit :=
  validateConstructorIdentifierReferencesWithImmutables [] ctor

end Compiler.CompilationModel

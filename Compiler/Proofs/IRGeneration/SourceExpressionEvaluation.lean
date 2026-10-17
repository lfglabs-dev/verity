import Compiler.Proofs.IRGeneration.SourceExpressionOutcome

/-! Recursive typed source expression execution. The typed body executor is an
explicit callback until all statement consumers are migrated. No Option helper
execution, preflight or duplicated execution is used. -/
namespace Compiler.Proofs.IRGeneration.SourceExpressionEvaluation
open Compiler.CompilationModel
open SourceSemantics SourceExpressionOutcome

def primitive (fields : List Field) (state : RuntimeState) (expr : Expr) : Result Nat :=
  match SourceSemantics.evalExpr fields state expr with
  | some value => .value value state
  | none => .interpretationError "typed source primitive evaluation refused"

mutual
def eval (runBody : RuntimeState → List Stmt → StmtResult)
    (spec : CompilationModel) (fields : List Field) :
    Nat → RuntimeState → Expr → Result Nat
  | 0, _, _ => .interpretationError "typed source expression evaluation fuel exhausted"
  | fuel + 1, state, expr =>
      match expr with
      | .internalCall name args =>
          (evalArgs runBody spec fields fuel state args).bind
            (fun values next => invoke runBody spec next name values)
      | .ite cond thenValue elseValue =>
          (eval runBody spec fields fuel state cond).bind (fun condition next =>
            eval runBody spec fields fuel next (if condition != 0 then thenValue else elseValue))
      | .externalCall name args =>
          if name == builtinExpName then
            (evalArgs runBody spec fields fuel state args).bind (fun values next =>
              match values with
              | [base, exponent] => primitive fields next (.externalCall name [.literal base, .literal exponent])
              | _ => .interpretationError "typed source exp requires two arguments")
          else .interpretationError s!"unsupported typed source external expression: {name}"
      | .literal n =>
          primitive fields state (.literal n)
      | .param name =>
          primitive fields state (.param name)
      | .constructorArg index =>
          primitive fields state (.constructorArg index)
      | .immutable name =>
          primitive fields state (.immutable name)
      | .storage field =>
          primitive fields state (.storage field)
      | .storageAddr field =>
          primitive fields state (.storageAddr field)
      | .mapping field key =>
          (eval runBody spec fields fuel state key).bind (fun keyValue keyState =>
            primitive fields keyState (.mapping field (.literal keyValue)))
      | .mappingWord field key wordOffset =>
          (eval runBody spec fields fuel state key).bind (fun keyValue keyState =>
            primitive fields keyState (.mappingWord field (.literal keyValue) wordOffset))
      | .mappingPackedWord field key wordOffset packed =>
          (eval runBody spec fields fuel state key).bind (fun keyValue keyState =>
            primitive fields keyState (.mappingPackedWord field (.literal keyValue) wordOffset packed))
      | .mapping2 field key1 key2 =>
          (eval runBody spec fields fuel state key1).bind (fun key1Value key1State =>
            (eval runBody spec fields fuel key1State key2).bind (fun key2Value key2State =>
              primitive fields key2State (.mapping2 field (.literal key1Value) (.literal key2Value))))
      | .mapping2Word field key1 key2 wordOffset =>
          (eval runBody spec fields fuel state key1).bind (fun key1Value key1State =>
            (eval runBody spec fields fuel key1State key2).bind (fun key2Value key2State =>
              primitive fields key2State (.mapping2Word field (.literal key1Value) (.literal key2Value) wordOffset)))
      | .mappingUint field key =>
          (eval runBody spec fields fuel state key).bind (fun keyValue keyState =>
            primitive fields keyState (.mappingUint field (.literal keyValue)))
      | .structMember field key memberName =>
          (eval runBody spec fields fuel state key).bind (fun keyValue keyState =>
            primitive fields keyState (.structMember field (.literal keyValue) memberName))
      | .structMember2 field key1 key2 memberName =>
          (eval runBody spec fields fuel state key1).bind (fun key1Value key1State =>
            (eval runBody spec fields fuel key1State key2).bind (fun key2Value key2State =>
              primitive fields key2State (.structMember2 field (.literal key1Value) (.literal key2Value) memberName)))
      | .caller =>
          primitive fields state (.caller)
      | .contractAddress =>
          primitive fields state (.contractAddress)
      | .txOrigin =>
          primitive fields state (.txOrigin)
      | .chainid =>
          primitive fields state (.chainid)
      | .msgValue =>
          primitive fields state (.msgValue)
      | .selfBalance =>
          primitive fields state (.selfBalance)
      | .blockTimestamp =>
          primitive fields state (.blockTimestamp)
      | .blockNumber =>
          primitive fields state (.blockNumber)
      | .blobbasefee =>
          primitive fields state (.blobbasefee)
      | .mload offset =>
          (eval runBody spec fields fuel state offset).bind (fun offsetValue offsetState =>
            primitive fields offsetState (.mload (.literal offsetValue)))
      | .tload offset =>
          (eval runBody spec fields fuel state offset).bind (fun offsetValue offsetState =>
            primitive fields offsetState (.tload (.literal offsetValue)))
      | .keccak256 offset size =>
          (eval runBody spec fields fuel state offset).bind (fun offsetValue offsetState =>
            (eval runBody spec fields fuel offsetState size).bind (fun sizeValue sizeState =>
              primitive fields sizeState (.keccak256 (.literal offsetValue) (.literal sizeValue))))
      | .calldatasize =>
          primitive fields state (.calldatasize)
      | .calldataload offset =>
          (eval runBody spec fields fuel state offset).bind (fun offsetValue offsetState =>
            primitive fields offsetState (.calldataload (.literal offsetValue)))
      | .returndataSize =>
          primitive fields state (.returndataSize)
      | .extcodesize addr =>
          (eval runBody spec fields fuel state addr).bind (fun addrValue addrState =>
            primitive fields addrState (.extcodesize (.literal addrValue)))
      | .returndataOptionalBoolAt outOffset =>
          (eval runBody spec fields fuel state outOffset).bind (fun outOffsetValue outOffsetState =>
            primitive fields outOffsetState (.returndataOptionalBoolAt (.literal outOffsetValue)))
      | .localVar name =>
          primitive fields state (.localVar name)
      | .arrayLength name =>
          primitive fields state (.arrayLength name)
      | .arrayElement name index =>
          (eval runBody spec fields fuel state index).bind (fun indexValue indexState =>
            primitive fields indexState (.arrayElement name (.literal indexValue)))
      | .memoryArrayLength name =>
          primitive fields state (.memoryArrayLength name)
      | .memoryArrayElement name index =>
          (eval runBody spec fields fuel state index).bind (fun indexValue indexState =>
            primitive fields indexState (.memoryArrayElement name (.literal indexValue)))
      | .arrayElementDynamicWord name index wordOffset =>
          (eval runBody spec fields fuel state index).bind (fun indexValue indexState =>
            primitive fields indexState (.arrayElementDynamicWord name (.literal indexValue) wordOffset))
      | .arrayElementDynamicDataOffset name index =>
          (eval runBody spec fields fuel state index).bind (fun indexValue indexState =>
            primitive fields indexState (.arrayElementDynamicDataOffset name (.literal indexValue)))
      | .arrayElementDynamicMemberLength name index wordOffset =>
          (eval runBody spec fields fuel state index).bind (fun indexValue indexState =>
            primitive fields indexState (.arrayElementDynamicMemberLength name (.literal indexValue) wordOffset))
      | .arrayElementDynamicMemberDataOffset name index wordOffset =>
          (eval runBody spec fields fuel state index).bind (fun indexValue indexState =>
            primitive fields indexState (.arrayElementDynamicMemberDataOffset name (.literal indexValue) wordOffset))
      | .arrayElementDynamicMemberElement name index wordOffset innerIndex =>
          (eval runBody spec fields fuel state index).bind (fun indexValue indexState =>
            (eval runBody spec fields fuel indexState innerIndex).bind (fun innerIndexValue innerIndexState =>
              primitive fields innerIndexState (.arrayElementDynamicMemberElement name (.literal indexValue) wordOffset (.literal innerIndexValue))))
      | .storageArrayLength field =>
          primitive fields state (.storageArrayLength field)
      | .storageArrayElement field index =>
          (eval runBody spec fields fuel state index).bind (fun indexValue indexState =>
            primitive fields indexState (.storageArrayElement field (.literal indexValue)))
      | .dynamicBytesEq lhsName rhsName =>
          primitive fields state (.dynamicBytesEq lhsName rhsName)
      | .add a b =>
          (eval runBody spec fields fuel state a).bind (fun aValue aState =>
            (eval runBody spec fields fuel aState b).bind (fun bValue bState =>
              primitive fields bState (.add (.literal aValue) (.literal bValue))))
      | .sub a b =>
          (eval runBody spec fields fuel state a).bind (fun aValue aState =>
            (eval runBody spec fields fuel aState b).bind (fun bValue bState =>
              primitive fields bState (.sub (.literal aValue) (.literal bValue))))
      | .mul a b =>
          (eval runBody spec fields fuel state a).bind (fun aValue aState =>
            (eval runBody spec fields fuel aState b).bind (fun bValue bState =>
              primitive fields bState (.mul (.literal aValue) (.literal bValue))))
      | .div a b =>
          (eval runBody spec fields fuel state a).bind (fun aValue aState =>
            (eval runBody spec fields fuel aState b).bind (fun bValue bState =>
              primitive fields bState (.div (.literal aValue) (.literal bValue))))
      | .sdiv a b =>
          (eval runBody spec fields fuel state a).bind (fun aValue aState =>
            (eval runBody spec fields fuel aState b).bind (fun bValue bState =>
              primitive fields bState (.sdiv (.literal aValue) (.literal bValue))))
      | .mod a b =>
          (eval runBody spec fields fuel state a).bind (fun aValue aState =>
            (eval runBody spec fields fuel aState b).bind (fun bValue bState =>
              primitive fields bState (.mod (.literal aValue) (.literal bValue))))
      | .smod a b =>
          (eval runBody spec fields fuel state a).bind (fun aValue aState =>
            (eval runBody spec fields fuel aState b).bind (fun bValue bState =>
              primitive fields bState (.smod (.literal aValue) (.literal bValue))))
      | .bitAnd a b =>
          (eval runBody spec fields fuel state a).bind (fun aValue aState =>
            (eval runBody spec fields fuel aState b).bind (fun bValue bState =>
              primitive fields bState (.bitAnd (.literal aValue) (.literal bValue))))
      | .bitOr a b =>
          (eval runBody spec fields fuel state a).bind (fun aValue aState =>
            (eval runBody spec fields fuel aState b).bind (fun bValue bState =>
              primitive fields bState (.bitOr (.literal aValue) (.literal bValue))))
      | .bitXor a b =>
          (eval runBody spec fields fuel state a).bind (fun aValue aState =>
            (eval runBody spec fields fuel aState b).bind (fun bValue bState =>
              primitive fields bState (.bitXor (.literal aValue) (.literal bValue))))
      | .bitNot a =>
          (eval runBody spec fields fuel state a).bind (fun aValue aState =>
            primitive fields aState (.bitNot (.literal aValue)))
      | .shl shift value =>
          (eval runBody spec fields fuel state shift).bind (fun shiftValue shiftState =>
            (eval runBody spec fields fuel shiftState value).bind (fun valueValue valueState =>
              primitive fields valueState (.shl (.literal shiftValue) (.literal valueValue))))
      | .shr shift value =>
          (eval runBody spec fields fuel state shift).bind (fun shiftValue shiftState =>
            (eval runBody spec fields fuel shiftState value).bind (fun valueValue valueState =>
              primitive fields valueState (.shr (.literal shiftValue) (.literal valueValue))))
      | .sar shift value =>
          (eval runBody spec fields fuel state shift).bind (fun shiftValue shiftState =>
            (eval runBody spec fields fuel shiftState value).bind (fun valueValue valueState =>
              primitive fields valueState (.sar (.literal shiftValue) (.literal valueValue))))
      | .byte index value =>
          (eval runBody spec fields fuel state index).bind (fun indexValue indexState =>
            (eval runBody spec fields fuel indexState value).bind (fun valueValue valueState =>
              primitive fields valueState (.byte (.literal indexValue) (.literal valueValue))))
      | .signextend byteIndex value =>
          (eval runBody spec fields fuel state byteIndex).bind (fun byteIndexValue byteIndexState =>
            (eval runBody spec fields fuel byteIndexState value).bind (fun valueValue valueState =>
              primitive fields valueState (.signextend (.literal byteIndexValue) (.literal valueValue))))
      | .eq a b =>
          (eval runBody spec fields fuel state a).bind (fun aValue aState =>
            (eval runBody spec fields fuel aState b).bind (fun bValue bState =>
              primitive fields bState (.eq (.literal aValue) (.literal bValue))))
      | .ge a b =>
          (eval runBody spec fields fuel state a).bind (fun aValue aState =>
            (eval runBody spec fields fuel aState b).bind (fun bValue bState =>
              primitive fields bState (.ge (.literal aValue) (.literal bValue))))
      | .gt a b =>
          (eval runBody spec fields fuel state a).bind (fun aValue aState =>
            (eval runBody spec fields fuel aState b).bind (fun bValue bState =>
              primitive fields bState (.gt (.literal aValue) (.literal bValue))))
      | .sgt a b =>
          (eval runBody spec fields fuel state a).bind (fun aValue aState =>
            (eval runBody spec fields fuel aState b).bind (fun bValue bState =>
              primitive fields bState (.sgt (.literal aValue) (.literal bValue))))
      | .lt a b =>
          (eval runBody spec fields fuel state a).bind (fun aValue aState =>
            (eval runBody spec fields fuel aState b).bind (fun bValue bState =>
              primitive fields bState (.lt (.literal aValue) (.literal bValue))))
      | .slt a b =>
          (eval runBody spec fields fuel state a).bind (fun aValue aState =>
            (eval runBody spec fields fuel aState b).bind (fun bValue bState =>
              primitive fields bState (.slt (.literal aValue) (.literal bValue))))
      | .le a b =>
          (eval runBody spec fields fuel state a).bind (fun aValue aState =>
            (eval runBody spec fields fuel aState b).bind (fun bValue bState =>
              primitive fields bState (.le (.literal aValue) (.literal bValue))))
      | .logicalAnd a b =>
          (eval runBody spec fields fuel state a).bind (fun aValue aState =>
            (eval runBody spec fields fuel aState b).bind (fun bValue bState =>
              primitive fields bState (.logicalAnd (.literal aValue) (.literal bValue))))
      | .logicalOr a b =>
          (eval runBody spec fields fuel state a).bind (fun aValue aState =>
            (eval runBody spec fields fuel aState b).bind (fun bValue bState =>
              primitive fields bState (.logicalOr (.literal aValue) (.literal bValue))))
      | .logicalNot a =>
          (eval runBody spec fields fuel state a).bind (fun aValue aState =>
            primitive fields aState (.logicalNot (.literal aValue)))
      | .ceilDiv a b =>
          (eval runBody spec fields fuel state a).bind (fun aValue aState =>
            (eval runBody spec fields fuel aState b).bind (fun bValue bState =>
              primitive fields bState (.ceilDiv (.literal aValue) (.literal bValue))))
      | .mulDivDown a b c =>
          (eval runBody spec fields fuel state a).bind (fun aValue aState =>
            (eval runBody spec fields fuel aState b).bind (fun bValue bState =>
              (eval runBody spec fields fuel bState c).bind (fun cValue cState =>
                primitive fields cState (.mulDivDown (.literal aValue) (.literal bValue) (.literal cValue)))))
      | .mulDivUp a b c =>
          (eval runBody spec fields fuel state a).bind (fun aValue aState =>
            (eval runBody spec fields fuel aState b).bind (fun bValue bState =>
              (eval runBody spec fields fuel bState c).bind (fun cValue cState =>
                primitive fields cState (.mulDivUp (.literal aValue) (.literal bValue) (.literal cValue)))))
      | .wMulDown a b =>
          (eval runBody spec fields fuel state a).bind (fun aValue aState =>
            (eval runBody spec fields fuel aState b).bind (fun bValue bState =>
              primitive fields bState (.wMulDown (.literal aValue) (.literal bValue))))
      | .wDivUp a b =>
          (eval runBody spec fields fuel state a).bind (fun aValue aState =>
            (eval runBody spec fields fuel aState b).bind (fun bValue bState =>
              primitive fields bState (.wDivUp (.literal aValue) (.literal bValue))))
      | .min a b =>
          (eval runBody spec fields fuel state a).bind (fun aValue aState =>
            (eval runBody spec fields fuel aState b).bind (fun bValue bState =>
              primitive fields bState (.min (.literal aValue) (.literal bValue))))
      | .max a b =>
          (eval runBody spec fields fuel state a).bind (fun aValue aState =>
            (eval runBody spec fields fuel aState b).bind (fun bValue bState =>
              primitive fields bState (.max (.literal aValue) (.literal bValue))))
      | _ => .interpretationError "unsupported typed source expression construct"

def evalArgs (runBody : RuntimeState → List Stmt → StmtResult)
    (spec : CompilationModel) (fields : List Field) :
    Nat → RuntimeState → List Expr → Result (List Nat)
  | _, state, [] => .value [] state
  | 0, _, _ :: _ => .interpretationError "typed source expression argument fuel exhausted"
  | fuel + 1, state, expr :: rest =>
      (eval runBody spec fields fuel state expr).bind (fun value next =>
        (evalArgs runBody spec fields fuel next rest).bind
          (fun values final => .value (value :: values) final))
end

theorem eval_fuel_zero (runBody : RuntimeState → List Stmt → StmtResult)
    (spec : CompilationModel) (fields : List Field) (state : RuntimeState) (expr : Expr) :
    eval runBody spec fields 0 state expr =
      .interpretationError "typed source expression evaluation fuel exhausted" := rfl

theorem eval_add (runBody : RuntimeState → List Stmt → StmtResult)
    (spec : CompilationModel) (fields : List Field) (fuel : Nat)
    (state : RuntimeState) (left right : Expr) :
    eval runBody spec fields (fuel + 1) state (.add left right) =
      (eval runBody spec fields fuel state left).bind (fun leftValue leftState =>
        (eval runBody spec fields fuel leftState right).bind (fun rightValue rightState =>
          primitive fields rightState (.add (.literal leftValue) (.literal rightValue)))) := rfl

theorem eval_ite (runBody : RuntimeState → List Stmt → StmtResult)
    (spec : CompilationModel) (fields : List Field) (fuel : Nat)
    (state : RuntimeState) (cond thenValue elseValue : Expr) :
    eval runBody spec fields (fuel + 1) state (.ite cond thenValue elseValue) =
      (eval runBody spec fields fuel state cond).bind (fun condition next =>
        eval runBody spec fields fuel next (if condition != 0 then thenValue else elseValue)) := rfl

theorem eval_internal_call (runBody : RuntimeState → List Stmt → StmtResult)
    (spec : CompilationModel) (fields : List Field) (fuel : Nat)
    (state : RuntimeState) (name : String) (args : List Expr) :
    eval runBody spec fields (fuel + 1) state (.internalCall name args) =
      (evalArgs runBody spec fields fuel state args).bind
        (fun values next => invoke runBody spec next name values) := rfl

end Compiler.Proofs.IRGeneration.SourceExpressionEvaluation

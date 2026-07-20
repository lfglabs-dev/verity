import Compiler.CompilationModel

namespace Compiler.Proofs.GeneratedTransition

open Compiler.CompilationModel

structure TransitionSummary where
  reads : List String := []
  writes : List String := []
  guards : List String := []
  events : List String := []
  deriving Repr, BEq, Inhabited

private def dedup (xs : List String) : List String :=
  xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

private def merge (a b : TransitionSummary) : TransitionSummary :=
  { reads := dedup (a.reads ++ b.reads)
    writes := dedup (a.writes ++ b.writes)
    guards := dedup (a.guards ++ b.guards)
    events := dedup (a.events ++ b.events) }

private partial def exprReads : Expr → List String
  | .storage field => [field]
  | .storageAddr field => [field]
  | .mapping field key => field :: exprReads key
  | .mapping2 field key1 key2 => field :: exprReads key1 ++ exprReads key2
  | .mappingUint field key => field :: exprReads key
  | .mappingChain field keys => field :: keys.flatMap exprReads
  | .structMember field key _ => field :: exprReads key
  | .structMember2 field key1 key2 _ => field :: exprReads key1 ++ exprReads key2
  | .mload a | .tload a | .calldataload a | .extcodesize a | .returndataOptionalBoolAt a
  | .storageArrayElement _ a | .memoryArrayElement _ a =>
      exprReads a
  | .keccak256 a b | .add a b | .sub a b | .mul a b | .div a b | .sdiv a b
  | .mod a b | .smod a b | .eq a b | .ge a b | .gt a b | .sgt a b | .lt a b
  | .slt a b | .le a b | .logicalAnd a b | .logicalOr a b | .bitAnd a b
  | .bitOr a b | .bitXor a b | .shl a b | .shr a b | .sar a b | .byte a b
  | .signextend a b | .ceilDiv a b | .wMulDown a b | .wDivUp a b
  | .min a b | .max a b =>
      exprReads a ++ exprReads b
  | .call gas target value inOffset inSize outOffset outSize =>
      [gas, target, value, inOffset, inSize, outOffset, outSize].flatMap exprReads
  | .staticcall gas target inOffset inSize outOffset outSize
  | .delegatecall gas target inOffset inSize outOffset outSize =>
      [gas, target, inOffset, inSize, outOffset, outSize].flatMap exprReads
  | .bitNot a | .logicalNot a => exprReads a
  | .externalCall _ args | .internalCall _ args => args.flatMap exprReads
  | .intrinsic _ _ _ args => args.flatMap exprReads
  | .forkIfAtLeast _ t e => exprReads t ++ exprReads e
  | .arrayLength name => [name ++ ".length"]
  | .arrayElement name idx => name :: exprReads idx
  | .memoryArrayLength name => [name ++ ".length"]
  | .arrayElementWord name idx _ _ => name :: exprReads idx
  | .arrayElementDynamicWord name idx _ => name :: exprReads idx
  | .arrayElementDynamicDataOffset name idx => name :: exprReads idx
  | .arrayElementDynamicMemberLength name idx _ => name :: exprReads idx
  | .arrayElementDynamicMemberDataOffset name idx _ => name :: exprReads idx
  | .arrayElementDynamicMemberElement name idx _ memberIdx => name :: (exprReads idx ++ exprReads memberIdx)
  | .paramDynamicHeadWord name _ => [name]
  | .paramDynamicStaticComposite name _ => [name]
  | .paramDynamicMemberLength name _ => [name]
  | .paramDynamicMemberDataOffset name _ => [name]
  | .paramDynamicMemberElement name _ _ => [name]
  | .storageArrayLength field => [field ++ ".length"]
  | .dynamicBytesEq lhs rhs => [lhs, rhs]
  | .ite c t e => exprReads c ++ exprReads t ++ exprReads e
  | .adtConstruct _ _ args => args.flatMap exprReads
  | .adtTag _ field => [field]
  | .adtField _ _ _ _ field => [field]
  | .mulDivDown a b c | .mulDivUp a b c | .mulDiv512Down a b c | .mulDiv512Up a b c =>
      exprReads a ++ exprReads b ++ exprReads c
  | _ => []

mutual
private partial def stmtSummary : Stmt → TransitionSummary
  | .setStorage field value | .setStorageAddr field value =>
      { reads := dedup (exprReads value), writes := [field] }
  | .setImmutable name value =>
      { reads := dedup (exprReads value), writes := ["immutable:" ++ name] }
  | .setStorageWord field offset value =>
      { reads := dedup (exprReads value), writes := [field ++ "+" ++ toString offset] }
  | .storageArrayPush field value =>
      { reads := dedup ((field ++ ".length") :: exprReads value), writes := [field] }
  | .storageArrayPop field =>
      { reads := [field ++ ".length"], writes := [field] }
  | .setStorageArrayElement field idx value =>
      { reads := dedup (exprReads idx ++ exprReads value), writes := [field ++ "[]"] }
  | .setMapping field key value | .setMappingUint field key value =>
      { reads := dedup (exprReads key ++ exprReads value), writes := [field] }
  | .setMappingWord field key offset value =>
      { reads := dedup (exprReads key ++ exprReads value), writes := [field ++ "+" ++ toString offset] }
  | .setMappingPackedWord field key offset _ value =>
      { reads := dedup (field :: (exprReads key ++ exprReads value)), writes := [field ++ "+" ++ toString offset] }
  | .setMapping2 field key1 key2 value =>
      { reads := dedup (exprReads key1 ++ exprReads key2 ++ exprReads value), writes := [field] }
  | .setMapping2Word field key1 key2 offset value =>
      { reads := dedup (exprReads key1 ++ exprReads key2 ++ exprReads value), writes := [field ++ "+" ++ toString offset] }
  | .setMappingChain field keys value =>
      { reads := dedup (keys.flatMap exprReads ++ exprReads value), writes := [field] }
  | .setStructMember field key member value =>
      { reads := dedup (exprReads key ++ exprReads value), writes := [field ++ "." ++ member] }
  | .setStructMember2 field key1 key2 member value =>
      { reads := dedup (exprReads key1 ++ exprReads key2 ++ exprReads value), writes := [field ++ "." ++ member] }
  | .require cond label =>
      { reads := dedup (exprReads cond), guards := [label] }
  | .requireError cond label args =>
      { reads := dedup (exprReads cond ++ args.flatMap exprReads), guards := [label] }
  | .revertError label args =>
      { reads := dedup (args.flatMap exprReads), guards := [label] }
  | .panicCode code =>
      { reads := dedup (exprReads code), guards := ["panic"] }
  | .emit eventName args =>
      { reads := dedup (args.flatMap exprReads), events := [eventName] }
  | .rawLog topics dataOffset dataSize =>
      { reads := dedup (topics.flatMap exprReads ++ exprReads dataOffset ++ exprReads dataSize), events := ["rawLog"] }
  | .externalCallBind results externalName args =>
      { reads := dedup (args.flatMap exprReads), writes := results.map ("local:" ++ ·), events := ["external:" ++ externalName] }
  | .tryExternalCallBind success results externalName args =>
      { reads := dedup (args.flatMap exprReads), writes := ("local:" ++ success) :: results.map ("local:" ++ ·), events := ["external:" ++ externalName] }
  | .ecm mod args =>
      { reads := if mod.readsState then ["ecm:" ++ mod.name] else dedup (args.flatMap exprReads)
        writes := if mod.writesState then ["ecm:" ++ mod.name] else []
        events := ["ecm:" ++ mod.name] }
  | .ite cond t e =>
      merge { reads := dedup (exprReads cond), guards := ["branch"] } (merge (stmtsSummary t) (stmtsSummary e))
  | .forEach name count body =>
      merge { reads := dedup (exprReads count), guards := ["loop:" ++ name] } (stmtsSummary body)
  | .forEachSetBit name bitmap body =>
      merge { reads := dedup (exprReads bitmap), guards := ["setBitLoop:" ++ name] } (stmtsSummary body)
  | .letVar _ value | .assignVar _ value | .return value | .mstore _ value | .tstore _ value =>
      { reads := dedup (exprReads value) }
  | .returnValues values => { reads := dedup (values.flatMap exprReads) }
  | .returnArray name | .returnBytes name | .returnStorageWords name => { reads := [name] }
  | .returnCodeData pointer => { reads := dedup (exprReads pointer), events := ["returnCodeData"] }
  | .calldatacopy dest src size | .returndataCopy dest src size =>
      { reads := dedup (exprReads dest ++ exprReads src ++ exprReads size) }
  | .internalCall _ args | .internalCallAssign _ _ args =>
      { reads := dedup (args.flatMap exprReads) }
  | .unsafeBlock reason body =>
      merge { guards := ["unsafe:" ++ reason] } (stmtsSummary body)
  | .unsafeYul _ => { events := ["unsafeYul"] }
  | .matchAdt adtName scrutinee branches =>
      merge { reads := dedup (exprReads scrutinee), guards := ["match:" ++ adtName] }
        (branches.foldl (fun acc (_, _, body) => merge acc (stmtsSummary body)) {})
  | .stop | .revertReturndata => {}

private partial def stmtsSummary (stmts : List Stmt) : TransitionSummary :=
  stmts.foldl (fun acc stmt => merge acc (stmtSummary stmt)) {}
end

def extract (stmts : List Stmt) : TransitionSummary :=
  stmts.foldl (fun acc stmt => merge acc (stmtSummary stmt)) {}

def enoughForMidnightRcfTotalUnits (summary : TransitionSummary) : Bool :=
  !summary.reads.isEmpty || !summary.writes.isEmpty || !summary.guards.isEmpty || !summary.events.isEmpty

end Compiler.Proofs.GeneratedTransition

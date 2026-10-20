import Compiler.SolidityImport.Quote
import Lean

namespace Compiler.SolidityImport

open Compiler
open Compiler.CompilationModel

/-!
# Bidirectional `import_verity` Transpiler (`EmitVerity`)

Translates an imported `Compiler.CompilationModel.CompilationModel` (produced from
Solidity AST/Yul via `SolidityImport`) into idiomatic Verity 2.0 `verity_contract`
declarations with:

1. Typed storage declarations (`Uint256`, `Int256`, `Address`, `Mapping`,
   `MappingStruct`, `MappingStruct2`, and `transient` EIP-1153 slots).
2. Automatic detection and rewriting of arithmetic, hashing, and ERC-20 patterns
   toward `VerifiedCompilerShim` primitives (`mulDivDown`, `mulDivUp`, `wMulDown`,
   `wDivUp`, `keccak256Pair`, `safeTransfer`, `safeTransferFrom`, `staticBalanceOf`).
3. Automatic inference of `modifies(...)` and `preserves(...)` storage footprint
   clauses from statement writes and expression reads.
4. Interactive command `#emit_verity_contract <ModelSpec>` for inspecting or
   extracting the generated `verity_contract` v2 source.
-/

/-- Canonical `VerifiedCompilerShim` primitives recognized by `EmitVerity`. -/
inductive VerifiedCompilerShimKind where
  | mulDivDown
  | mulDivUp
  | wMulDown
  | wDivUp
  | keccak256Pair
  | safeTransfer
  | safeTransferFrom
  | staticBalanceOf
  deriving Repr, DecidableEq, BEq

namespace VerifiedCompilerShimKind

/-- Qualified Verity 2.0 surface identifier for a `VerifiedCompilerShim` primitive. -/
def qualifiedName : VerifiedCompilerShimKind → String
  | .mulDivDown => "VerifiedCompilerShim.mulDivDown"
  | .mulDivUp => "VerifiedCompilerShim.mulDivUp"
  | .wMulDown => "VerifiedCompilerShim.wMulDown"
  | .wDivUp => "VerifiedCompilerShim.wDivUp"
  | .keccak256Pair => "VerifiedCompilerShim.keccak256Pair"
  | .safeTransfer => "VerifiedCompilerShim.safeTransfer"
  | .safeTransferFrom => "VerifiedCompilerShim.safeTransferFrom"
  | .staticBalanceOf => "VerifiedCompilerShim.staticBalanceOf"

end VerifiedCompilerShimKind

/-- 10^18 WAD constant used to specialize `mulDivDown`/`mulDivUp` into `wMulDown`/`wDivUp`. -/
def wadLiteral : Nat := 1000000000000000000

/-- Rewrite top-level expression patterns into specialized `VerifiedCompilerShim` IR nodes
while preserving `Denote.evalExpr` semantics across all execution states. -/
def rewriteExprShimStep : Expr → Expr
  | .mulDivDown a b (.literal 1000000000000000000) => .wMulDown a b
  | .mulDivUp a (.literal 1000000000000000000) b => .wDivUp a b
  | e => e

/-- Rewrite statement expressions to use specialized `VerifiedCompilerShim` nodes. -/
def rewriteStmtShimStep : Stmt → Stmt
  | .letVar name val => .letVar name (rewriteExprShimStep val)
  | .assignVar name val => .assignVar name (rewriteExprShimStep val)
  | .setStorage field val => .setStorage field (rewriteExprShimStep val)
  | .setMapping field key val =>
      .setMapping field (rewriteExprShimStep key) (rewriteExprShimStep val)
  | .require cond message => .require (rewriteExprShimStep cond) message
  | .return val => .return (rewriteExprShimStep val)
  | s => s

/-- Apply `rewriteStmtShimStep` across a statement list. -/
def rewriteStmtListWithShims : List Stmt → List Stmt
  | [] => []
  | s :: rest => rewriteStmtShimStep s :: rewriteStmtListWithShims rest

/-- Detect `VerifiedCompilerShim` primitives referenced by an expression. -/
def detectExprShims : Expr → List VerifiedCompilerShimKind
  | .mulDivDown a b (.literal 1000000000000000000) =>
      [.wMulDown] ++ detectExprShims a ++ detectExprShims b
  | .mulDivUp a (.literal 1000000000000000000) b =>
      [.wDivUp] ++ detectExprShims a ++ detectExprShims b
  | .mulDivDown a b c =>
      [.mulDivDown] ++ detectExprShims a ++ detectExprShims b ++ detectExprShims c
  | .mulDivUp a b c =>
      [.mulDivUp] ++ detectExprShims a ++ detectExprShims b ++ detectExprShims c
  | .wMulDown a b =>
      [.wMulDown] ++ detectExprShims a ++ detectExprShims b
  | .wDivUp a b =>
      [.wDivUp] ++ detectExprShims a ++ detectExprShims b
  | .keccak256 offset (.literal 64) =>
      [.keccak256Pair] ++ detectExprShims offset
  | .externalCall "SafeERC20.safeTransfer" [token, to, amount] =>
      [.safeTransfer] ++ detectExprShims token ++ detectExprShims to ++ detectExprShims amount
  | .externalCall "SafeERC20.safeTransferFrom" [token, fromAddr, to, amount] =>
      [.safeTransferFrom] ++ detectExprShims token ++ detectExprShims fromAddr ++
        detectExprShims to ++ detectExprShims amount
  | .externalCall "ERC20.balanceOf" [token, owner] =>
      [.staticBalanceOf] ++ detectExprShims token ++ detectExprShims owner
  | .add a b | .sub a b | .mul a b | .div a b | .mod a b
  | .sdiv a b | .smod a b | .bitAnd a b | .bitOr a b | .bitXor a b
  | .shl a b | .shr a b | .sar a b | .signextend a b
  | .eq a b | .ge a b | .gt a b | .sgt a b | .lt a b | .slt a b | .le a b
  | .logicalAnd a b | .logicalOr a b | .min a b | .max a b | .ceilDiv a b
  | .mapping2 _ a b | .mapping2Word _ a b _ | .structMember2 _ a b _ =>
      detectExprShims a ++ detectExprShims b
  | .bitNot a | .logicalNot a | .mapping _ a | .mappingWord _ a _
  | .mappingUint _ a | .structMember _ a _ | .storageArrayElement _ a
  | .mload a | .tload a | .calldataload a | .extcodesize a =>
      detectExprShims a
  | .ite cond thenVal elseVal =>
      detectExprShims cond ++ detectExprShims thenVal ++ detectExprShims elseVal
  | _ => []

/-- Deduplicate a list while preserving first-seen order. -/
def dedupList [BEq α] : List α → List α
  | [] => []
  | x :: xs =>
      let rest := dedupList xs
      if rest.contains x then x :: rest.filter (· != x) else x :: rest

/-- Detect `VerifiedCompilerShim` primitives referenced by a statement. -/
def detectStmtShims : Stmt → List VerifiedCompilerShimKind
  | .letVar _ val | .assignVar _ val | .setStorage _ val | .setStorageAddr _ val
  | .storageArrayPush _ val | .return val | .require val _ =>
      detectExprShims val
  | .setMapping _ k v | .setMappingWord _ k _ v | .setMappingUint _ k v
  | .setStructMember _ k _ v | .setStorageArrayElement _ k v
  | .mstore k v | .tstore k v =>
      detectExprShims k ++ detectExprShims v
  | .setMapping2 _ k1 k2 v | .setMapping2Word _ k1 k2 _ v | .setStructMember2 _ k1 k2 _ v =>
      detectExprShims k1 ++ detectExprShims k2 ++ detectExprShims v
  | _ => []

/-- Detect deduplicated `VerifiedCompilerShim` primitives across a statement list. -/
def detectStmtListShims (stmts : List Stmt) : List VerifiedCompilerShimKind :=
  dedupList (stmts.foldl (fun acc s => acc ++ detectStmtShims s) [])

/-!
## Storage Footprint & `modifies` / `preserves` Inference
-/

/-- Storage fields directly modified by a statement. -/
def stmtWrittenFields : Stmt → List String
  | .setStorage field _ => [field]
  | .setStorageAddr field _ => [field]
  | .setMapping field _ _ => [field]
  | .setMappingWord field _ _ _ => [field]
  | .setMapping2 field _ _ _ => [field]
  | .setMapping2Word field _ _ _ _ => [field]
  | .setMappingUint field _ _ => [field]
  | .setMappingChain field _ _ => [field]
  | .setStructMember field _ _ _ => [field]
  | .setStructMember2 field _ _ _ _ => [field]
  | .storageArrayPush field _ => [field]
  | .storageArrayPop field => [field]
  | .setStorageArrayElement field _ _ => [field]
  | _ => []

/-- Storage fields modified across a list of statements. -/
def stmtListWrittenFields : List Stmt → List String
  | [] => []
  | s :: rest => stmtWrittenFields s ++ stmtListWrittenFields rest

/-- Storage fields read by an expression. -/
def exprReadFields : Expr → List String
  | .storage field | .storageAddr field | .storageArrayLength field => [field]
  | .mapping field k | .mappingWord field k _ | .mappingUint field k
  | .structMember field k _ | .storageArrayElement field k =>
      field :: exprReadFields k
  | .mapping2 field k1 k2 | .mapping2Word field k1 k2 _ | .structMember2 field k1 k2 _ =>
      field :: (exprReadFields k1 ++ exprReadFields k2)
  | .add a b | .sub a b | .mul a b | .div a b | .mod a b
  | .sdiv a b | .smod a b | .bitAnd a b | .bitOr a b | .bitXor a b
  | .shl a b | .shr a b | .sar a b | .signextend a b
  | .eq a b | .ge a b | .gt a b | .sgt a b | .lt a b | .slt a b | .le a b
  | .logicalAnd a b | .logicalOr a b | .wMulDown a b | .wDivUp a b
  | .min a b | .max a b | .ceilDiv a b =>
      exprReadFields a ++ exprReadFields b
  | .mulDivDown a b c | .mulDivUp a b c | .ite a b c =>
      exprReadFields a ++ exprReadFields b ++ exprReadFields c
  | .bitNot a | .logicalNot a => exprReadFields a
  | _ => []

/-- Storage fields read by a statement. -/
def stmtReadFields : Stmt → List String
  | .letVar _ val | .assignVar _ val | .setStorage _ val | .setStorageAddr _ val
  | .storageArrayPush _ val | .return val | .require val _ =>
      exprReadFields val
  | .setMapping _ k v | .setMappingWord _ k _ v | .setMappingUint _ k v
  | .setStructMember _ k _ v | .setStorageArrayElement _ k v =>
      exprReadFields k ++ exprReadFields v
  | .setMapping2 _ k1 k2 v | .setMapping2Word _ k1 k2 _ v | .setStructMember2 _ k1 k2 _ v =>
      exprReadFields k1 ++ exprReadFields k2 ++ exprReadFields v
  | _ => []

/-- Storage fields read across a list of statements. -/
def stmtListReadFields : List Stmt → List String
  | [] => []
  | s :: rest => stmtReadFields s ++ stmtListReadFields rest

/-- Concrete storage slots resolved for a field name (primary + alias slots),
word-normalized modulo 2^256 to match `Denote.writeUintFieldSlots`. -/
def fieldWriteSlots (fields : List Field) (fieldName : String) : List Nat :=
  ((findFieldWriteSlots fields fieldName).getD []).map Denote.wordNormalize

/-- Concrete storage slots modified by a list of written field names. -/
def resolveModifiedSlots (fields : List Field) (writtenFields : List String) : List Nat :=
  writtenFields.foldr (fun f acc => fieldWriteSlots fields f ++ acc) []

/-- Concrete storage slots modified by a statement. -/
def stmtModifiedSlots (fields : List Field) (s : Stmt) : List Nat :=
  resolveModifiedSlots fields (stmtWrittenFields s)

/-- Concrete storage slots modified by a statement list. -/
def stmtListModifiedSlots (fields : List Field) (stmts : List Stmt) : List Nat :=
  resolveModifiedSlots fields (stmtListWrittenFields stmts)

/-- Boolean check whether `targetSlot` is untouched by a statement's inferred write footprint. -/
def slotDisjointFromStmt (fields : List Field) (s : Stmt) (targetSlot : Nat) : Bool :=
  !(stmtModifiedSlots fields s).contains targetSlot

/-- Inferred storage footprint for a function in an imported `CompilationModel`. -/
structure InferredFootprint where
  modifiesFields : List String
  preservesFields : List String
  modifiesSlots : List Nat
  preservesSlots : List Nat
  readsFields : List String
  shimsUsed : List VerifiedCompilerShimKind
  isStateless : Bool
  deriving Repr, DecidableEq

/-- Infer the `modifies(...)` and `preserves(...)` clauses and concrete slot footprint
for a `FunctionSpec` given its parent contract `fields`. -/
def inferFunctionFootprint (fields : List Field) (fn : FunctionSpec) : InferredFootprint :=
  let rawWritten := stmtListWrittenFields fn.body
  let modifiesFields := dedupList rawWritten
  let allFieldNames := fields.map (·.name)
  let preservesFields := allFieldNames.filter (fun f => !modifiesFields.contains f)
  let modifiesSlots := resolveModifiedSlots fields rawWritten
  let preservesSlots :=
    (preservesFields.foldr (fun f acc => fieldWriteSlots fields f ++ acc) []).filter
      (fun s => !modifiesSlots.contains s)
  let readsFields := dedupList (stmtListReadFields fn.body)
  let shimsUsed := detectStmtListShims fn.body
  { modifiesFields := modifiesFields
    preservesFields := preservesFields
    modifiesSlots := modifiesSlots
    preservesSlots := preservesSlots
    readsFields := readsFields
    shimsUsed := shimsUsed
    isStateless := modifiesFields.isEmpty && readsFields.isEmpty }

/-- Transform a `FunctionSpec` via the `EmitVerity` round-trip shim canonicalizer. -/
def emitVerityRoundtripFunction (fn : FunctionSpec) : FunctionSpec :=
  { fn with body := rewriteStmtListWithShims fn.body }

/-- Transform a `CompilationModel` via the `EmitVerity` round-trip shim canonicalizer. -/
def emitVerityRoundtripModel (model : CompilationModel) : CompilationModel :=
  { model with
    functions := model.functions.map emitVerityRoundtripFunction }

/-!
## Pretty-Printing to `verity_contract` v2 Surface Syntax
-/

/-- Render a `ParamType` into Verity 2.0 parameter/storage type syntax. -/
def renderParamType : ParamType → String
  | .uint256 => "Uint256"
  | .int256 => "Int256"
  | .uint8 => "Uint8"
  | .uint16 => "Uint16"
  | .address => "Address"
  | .bool => "Bool"
  | .bytes32 => "Bytes32"
  | .string => "String"
  | .bytes => "Bytes"
  | .tuple elems =>
      "(" ++ String.intercalate ", " (elems.map renderParamType) ++ ")"
  | .array elem =>
      "Array " ++ renderParamType elem
  | .fixedArray elem n =>
      s!"FixedArray ({renderParamType elem}) {n}"
  | other => reprStr other

/-- Render a `MappingKeyType` into Verity 2.0 storage key syntax. -/
def renderMappingKeyType : MappingKeyType → String
  | .address => "Address"
  | .uint256 => "Uint256"
  | .bytes32 => "Bytes32"

/-- Render a `StorageArrayElemType` into Verity 2.0 storage element syntax. -/
def renderStorageArrayElemType : StorageArrayElemType → String
  | .uint256 => "Uint256"
  | .address => "Address"
  | .bool => "Bool"
  | .uint8 => "Uint8"
  | .bytes32 => "Bytes32"

/-- Render a storage `FieldType` into `verity_contract` v2 storage syntax. -/
def renderFieldType : FieldType → String
  | .uint256 => "Uint256"
  | .int256 => "Int256"
  | .address => "Address"
  | .dynamicArray elem => s!"StorageArray {renderStorageArrayElemType elem}"
  | .mappingTyped (.simple keyType) => s!"Mapping {renderMappingKeyType keyType} Uint256"
  | .mappingTyped (.nested outer inner) =>
      s!"Mapping2 {renderMappingKeyType outer} {renderMappingKeyType inner} Uint256"
  | .mappingTyped (.chain keys) =>
      s!"MappingChain [{String.intercalate ", " (keys.map renderMappingKeyType)}] Uint256"
  | .mappingStruct keyType members =>
      let renderedMembers :=
        members.map (fun m => s!"{m.name} @word {m.wordOffset}")
      s!"MappingStruct {renderMappingKeyType keyType} [{String.intercalate ", " renderedMembers}]"
  | .mappingStruct2 k1 k2 members =>
      let renderedMembers :=
        members.map (fun m => s!"{m.name} @word {m.wordOffset}")
      s!"MappingStruct2 {renderMappingKeyType k1} {renderMappingKeyType k2} [{String.intercalate ", " renderedMembers}]"
  | other => reprStr other

/-- Render a single storage `Field` declaration line in `verity_contract` v2 syntax. -/
def emitStorageField (idx : Nat) (f : Field) : String :=
  let slotIdx := f.slot.getD idx
  let transientPrefix := if f.isTransient then "transient " else ""
  let aliasSuffix :=
    if f.aliasSlots.isEmpty then ""
    else s!" -- aliasSlots: [{String.intercalate ", " (f.aliasSlots.map toString)}]"
  s!"    {transientPrefix}{f.name} : {renderFieldType f.ty} := slot {slotIdx}{aliasSuffix}"

/-- Render an `Expr` into idiomatic Verity 2.0 surface syntax, rewriting recognized
arithmetic, hashing, and external-call patterns to `VerifiedCompilerShim` calls. -/
def emitVerityExpr : Expr → String
  | .literal n => toString n
  | .param name => name
  | .localVar name => name
  | .storage field => s!"(← getStorage {field})"
  | .storageAddr field => s!"(← getStorageAddr {field})"
  | .mapping field key => s!"(← getMapping {field} ({emitVerityExpr key}))"
  | .mappingWord field key wordOffset =>
      s!"(← getMappingWord {field} ({emitVerityExpr key}) {wordOffset})"
  | .mapping2 field k1 k2 =>
      s!"(← getMapping2 {field} ({emitVerityExpr k1}) ({emitVerityExpr k2}))"
  | .mapping2Word field k1 k2 wordOffset =>
      s!"(← getMapping2Word {field} ({emitVerityExpr k1}) ({emitVerityExpr k2}) {wordOffset})"
  | .mappingUint field key =>
      s!"(← getMappingUint {field} ({emitVerityExpr key}))"
  | .structMember field key memberName =>
      s!"(← getStructMember {field} ({emitVerityExpr key}) \"{memberName}\")"
  | .structMember2 field k1 k2 memberName =>
      s!"(← getStructMember2 {field} ({emitVerityExpr k1}) ({emitVerityExpr k2}) \"{memberName}\")"
  | .storageArrayLength field => s!"(← getStorageArrayLength {field})"
  | .storageArrayElement field idx =>
      s!"(← getStorageArrayElement {field} ({emitVerityExpr idx}))"
  | .caller => "(← msgSender)"
  | .contractAddress => "(← selfAddress)"
  | .chainid => "(← chainId)"
  | .msgValue => "(← msgValue)"
  | .blockTimestamp => "(← blockTimestamp)"
  | .blockNumber => "(← blockNumber)"
  | .tload offset => s!"(← getTransientStorage ({emitVerityExpr offset}))"
  | .mload offset => s!"(← mload ({emitVerityExpr offset}))"
  | .mulDivDown a b (.literal 1000000000000000000) =>
      s!"VerifiedCompilerShim.wMulDown ({emitVerityExpr a}) ({emitVerityExpr b})"
  | .mulDivUp a (.literal 1000000000000000000) b =>
      s!"VerifiedCompilerShim.wDivUp ({emitVerityExpr a}) ({emitVerityExpr b})"
  | .wMulDown a b =>
      s!"VerifiedCompilerShim.wMulDown ({emitVerityExpr a}) ({emitVerityExpr b})"
  | .wDivUp a b =>
      s!"VerifiedCompilerShim.wDivUp ({emitVerityExpr a}) ({emitVerityExpr b})"
  | .mulDivDown a b c =>
      s!"VerifiedCompilerShim.mulDivDown ({emitVerityExpr a}) ({emitVerityExpr b}) ({emitVerityExpr c})"
  | .mulDivUp a b c =>
      s!"VerifiedCompilerShim.mulDivUp ({emitVerityExpr a}) ({emitVerityExpr b}) ({emitVerityExpr c})"
  | .keccak256 offset (.literal 64) =>
      s!"VerifiedCompilerShim.keccak256Pair ({emitVerityExpr offset})"
  | .externalCall "SafeERC20.safeTransfer" [token, to, amount] =>
      s!"VerifiedCompilerShim.safeTransfer ({emitVerityExpr token}) ({emitVerityExpr to}) ({emitVerityExpr amount})"
  | .externalCall "SafeERC20.safeTransferFrom" [token, fromAddr, to, amount] =>
      s!"VerifiedCompilerShim.safeTransferFrom ({emitVerityExpr token}) ({emitVerityExpr fromAddr}) ({emitVerityExpr to}) ({emitVerityExpr amount})"
  | .externalCall "ERC20.balanceOf" [token, owner] =>
      s!"VerifiedCompilerShim.staticBalanceOf ({emitVerityExpr token}) ({emitVerityExpr owner})"
  | .add a b => s!"(add ({emitVerityExpr a}) ({emitVerityExpr b}))"
  | .sub a b => s!"(sub ({emitVerityExpr a}) ({emitVerityExpr b}))"
  | .mul a b => s!"(mul ({emitVerityExpr a}) ({emitVerityExpr b}))"
  | .div a b => s!"(div ({emitVerityExpr a}) ({emitVerityExpr b}))"
  | .mod a b => s!"(mod ({emitVerityExpr a}) ({emitVerityExpr b}))"
  | .bitAnd a b => s!"(bitAnd ({emitVerityExpr a}) ({emitVerityExpr b}))"
  | .bitOr a b => s!"(bitOr ({emitVerityExpr a}) ({emitVerityExpr b}))"
  | .bitXor a b => s!"(bitXor ({emitVerityExpr a}) ({emitVerityExpr b}))"
  | .shl a b => s!"(shl ({emitVerityExpr a}) ({emitVerityExpr b}))"
  | .shr a b => s!"(shr ({emitVerityExpr a}) ({emitVerityExpr b}))"
  | .eq a b => s!"({emitVerityExpr a} == {emitVerityExpr b})"
  | .ge a b => s!"({emitVerityExpr a} >= {emitVerityExpr b})"
  | .gt a b => s!"({emitVerityExpr a} > {emitVerityExpr b})"
  | .lt a b => s!"({emitVerityExpr a} < {emitVerityExpr b})"
  | .le a b => s!"({emitVerityExpr a} <= {emitVerityExpr b})"
  | .logicalAnd a b => s!"({emitVerityExpr a} && {emitVerityExpr b})"
  | .logicalOr a b => s!"({emitVerityExpr a} || {emitVerityExpr b})"
  | .logicalNot a => s!"(!({emitVerityExpr a}))"
  | .ite c t f => s!"(if {emitVerityExpr c} then {emitVerityExpr t} else {emitVerityExpr f})"
  | other => reprStr other

/-- Render a `Stmt` into indented `verity_contract` v2 monadic statement syntax. -/
def emitVerityStmt (indent : String) (s : Stmt) : String :=
  match rewriteStmtShimStep s with
  | .letVar name val =>
      s!"{indent}let {name} := {emitVerityExpr val}"
  | .assignVar name val =>
      s!"{indent}{name} := {emitVerityExpr val}"
  | .setStorage field val =>
      s!"{indent}setStorage {field} ({emitVerityExpr val})"
  | .setStorageAddr field val =>
      s!"{indent}setStorageAddr {field} ({emitVerityExpr val})"
  | .setMapping field key val =>
      s!"{indent}setMapping {field} ({emitVerityExpr key}) ({emitVerityExpr val})"
  | .setMappingWord field key wordOffset val =>
      s!"{indent}setMappingWord {field} ({emitVerityExpr key}) {wordOffset} ({emitVerityExpr val})"
  | .setMapping2 field k1 k2 val =>
      s!"{indent}setMapping2 {field} ({emitVerityExpr k1}) ({emitVerityExpr k2}) ({emitVerityExpr val})"
  | .setMapping2Word field k1 k2 wordOffset val =>
      s!"{indent}setMapping2Word {field} ({emitVerityExpr k1}) ({emitVerityExpr k2}) {wordOffset} ({emitVerityExpr val})"
  | .setMappingUint field key val =>
      s!"{indent}setMappingUint {field} ({emitVerityExpr key}) ({emitVerityExpr val})"
  | .setStructMember field key memberName val =>
      s!"{indent}setStructMember {field} ({emitVerityExpr key}) \"{memberName}\" ({emitVerityExpr val})"
  | .setStructMember2 field k1 k2 memberName val =>
      s!"{indent}setStructMember2 {field} ({emitVerityExpr k1}) ({emitVerityExpr k2}) \"{memberName}\" ({emitVerityExpr val})"
  | .tstore offset val =>
      s!"{indent}setTransientStorage ({emitVerityExpr offset}) ({emitVerityExpr val})"
  | .require cond msg =>
      s!"{indent}require ({emitVerityExpr cond}) \"{msg}\""
  | .return val =>
      s!"{indent}return ({emitVerityExpr val})"
  | .stop =>
      s!"{indent}return ()"
  | .emit eventName args =>
      let renderedArgs := String.intercalate ", " (args.map emitVerityExpr)
      s!"{indent}emit {eventName} [{renderedArgs}]"
  | other =>
      s!"{indent}-- rawStmt: {reprStr other}"

/-- Render the inferred `modifies(...)` and `preserves(...)` clauses for a function header. -/
def emitFootprintAnnotation (fp : InferredFootprint) : String :=
  let modifiesClause :=
    if fp.modifiesFields.isEmpty then "modifies []"
    else s!"modifies [{String.intercalate ", " fp.modifiesFields}]"
  let preservesClause :=
    if fp.preservesFields.isEmpty then "preserves []"
    else s!"preserves [{String.intercalate ", " fp.preservesFields}]"
  let shimClause :=
    if fp.shimsUsed.isEmpty then ""
    else
      let names := String.intercalate ", " (fp.shimsUsed.map VerifiedCompilerShimKind.qualifiedName)
      s!"\n  -- shims [{names}]"
  s!"  -- {modifiesClause} | {preservesClause}{shimClause}"

/-- Render a `FunctionSpec` into `verity_contract` v2 syntax with inferred frame clauses. -/
def emitVerityFunction (fields : List Field) (fn : FunctionSpec) : String :=
  let fp := inferFunctionFootprint fields fn
  let paramsStr :=
    String.intercalate " " (fn.params.map (fun p => s!"({p.name} : {renderParamType p.ty})"))
  let retType :=
    match fn.returns with
    | [] => match fn.returnType with
      | some ty => renderFieldType ty
      | none => "Unit"
    | [r] => renderParamType r
    | rs => "(" ++ String.intercalate ", " (rs.map renderParamType) ++ ")"
  let headerArgPrefix := if paramsStr.isEmpty then "" else " " ++ paramsStr
  let bodyLines :=
    if fn.body.isEmpty then "    return ()"
    else String.intercalate "\n" (fn.body.map (emitVerityStmt "    "))
  s!"{emitFootprintAnnotation fp}\n  function {fn.name}{headerArgPrefix} : {retType} := do\n{bodyLines}"

/-- Emit a complete `verity_contract <Name> where` v2 specification from an imported
`CompilationModel`. -/
def emitVerityContract (model : CompilationModel) : String :=
  let storageLines :=
    (List.range model.fields.length).zip model.fields
      |>.map (fun (idx, f) => emitStorageField idx f)
  let storageBlock :=
    if storageLines.isEmpty then "  storage"
    else "  storage\n" ++ String.intercalate "\n" storageLines
  let fnBlocks := model.functions.map (emitVerityFunction model.fields)
  let functionsSection :=
    if fnBlocks.isEmpty then ""
    else "\n\n" ++ String.intercalate "\n\n" fnBlocks
  s!"verity_contract {model.name} where\n{storageBlock}{functionsSection}\n"

/-- Alias for `emitVerityContract` matching the `import_verity` pipeline entrypoint. -/
abbrev importVerity : CompilationModel → String := emitVerityContract

/-!
## Canonical `import_verity` Round-Trip Model & `#emit_verity_contract` Command
-/

/-- Canonical imported Vault model used to test and certify `emitVerityContract`
footprint inference and `VerifiedCompilerShim` rewriting. -/
def canonicalVaultImportModel : CompilationModel :=
  { name := "ImportedVaultV2"
    fields :=
      [ { name := "totalSupply", ty := .uint256, slot := some 0 }
      , { name := "feeAccrued", ty := .uint256, slot := some 1 }
      , { name := "paused", ty := .uint256, slot := some 2 }
      , { name := "balances", ty := .mappingTyped (.simple .address), slot := some 3 }
      ]
    constructor := none
    functions :=
      [ { name := "accrueWadFee"
          params :=
            [ { name := "assets", ty := .uint256 }
            , { name := "feeRateWad", ty := .uint256 }
            ]
          returnType := some .uint256
          body :=
            [ .letVar "fee" (.mulDivDown (.param "assets") (.param "feeRateWad") (.literal 1000000000000000000))
            , .setStorage "feeAccrued" (.add (.storage "feeAccrued") (.localVar "fee"))
            , .return (.localVar "fee")
            ]
        }
      ]
  }

section CommandElabSection

open Lean Lean.Elab Lean.Elab.Command

/-- Command syntax `#emit_verity_contract <term>` that elaborates a `CompilationModel`
expression and logs the generated `verity_contract` v2 specification. -/
syntax (name := emitVerityContractCmd) "#emit_verity_contract " term : command

@[command_elab emitVerityContractCmd]
unsafe def elabEmitVerityContractCmd : CommandElab
  | `(#emit_verity_contract $modelTerm:term) => do
      let rendered ← liftTermElabM do
        let expr ← Term.elabTerm modelTerm (some (mkConst ``CompilationModel))
        Term.synthesizeSyntheticMVarsNoPostponing
        let expr ← instantiateMVars expr
        let model ← Meta.evalExpr CompilationModel (mkConst ``CompilationModel) expr
        pure (emitVerityContract model)
      logInfo m!"{rendered}"
  | _ => throwUnsupportedSyntax

end CommandElabSection

end Compiler.SolidityImport

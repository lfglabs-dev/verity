import Lean

namespace Verity.Macro

open Lean

declare_syntax_cat verityStorageField
declare_syntax_cat verityStorageItem
declare_syntax_cat verityStorageStructMember
declare_syntax_cat verityStructMember
declare_syntax_cat verityParam
declare_syntax_cat verityError
declare_syntax_cat verityEventParam
declare_syntax_cat verityEvent
declare_syntax_cat verityConstant
declare_syntax_cat verityImmutable
declare_syntax_cat verityExternal
declare_syntax_cat verityExternalLinkMode
declare_syntax_cat verityInterface
declare_syntax_cat verityInterfaceFunction
declare_syntax_cat verityInterfaceParam
declare_syntax_cat verityLocalObligation
declare_syntax_cat verityLocalObligations
declare_syntax_cat verityConstructor
declare_syntax_cat verityMutability
declare_syntax_cat verityInitGuard
declare_syntax_cat verityModifies
declare_syntax_cat verityRequiresRole
declare_syntax_cat verityNewtype
declare_syntax_cat verityStructDecl
declare_syntax_cat verityAdtVariant
declare_syntax_cat verityAdtDecl
declare_syntax_cat verityNamespaceSpec
declare_syntax_cat veritySpecialEntrypoint
declare_syntax_cat verityModifier
declare_syntax_cat verityModifierUse
declare_syntax_cat verityFunction
declare_syntax_cat verityIntrinsicClause
declare_syntax_cat verityIntrinsicYul
declare_syntax_cat verityIntrinsicObligation

syntax ident " : " term " := " "slot" num : verityStorageField
syntax ident " : " term " := " "slot" num : verityStorageItem
syntax "transient " ident " : " term " := " "slot" num : verityStorageItem
syntax ident " : " term " @word " num : verityStorageStructMember
syntax ident " : " term " @word " num " packed(" num "," num ")" : verityStorageStructMember
syntax ident " : " "StorageStruct" "[" sepBy(verityStorageStructMember, ",") "]" " @word " num : verityStorageStructMember
syntax ident " : " "StorageStruct" "[" sepBy(verityStorageStructMember, ",") "]" " := " "slot" num : verityStorageItem
syntax "storage_namespace " : verityStorageItem
syntax "storage_namespace " str : verityStorageItem
syntax "storage_namespace " "erc7201 " str : verityStorageItem
syntax ident " @word " num : verityStructMember
syntax ident " @word " num " packed(" num "," num ")" : verityStructMember
syntax ident " : " term " @word " num : verityStructMember
syntax ident " : " term " @word " num " packed(" num "," num ")" : verityStructMember
syntax "MappingStruct(" term "," "[" sepBy(verityStructMember, ",") "]" ")" : term
syntax "MappingStruct2(" term "," term "," "[" sepBy(verityStructMember, ",") "]" ")" : term
syntax ident " : " term : verityParam
syntax "error " ident "(" sepBy(term, ",") ")" : verityError
syntax ident " : " term : verityEventParam
syntax "@indexed " ident " : " term : verityEventParam
syntax "event " ident "(" sepBy(verityEventParam, ",") ")" : verityEvent
syntax ident " : " term:max " := " term:max : verityConstant
syntax ident " : " term:max " := " term:max : verityImmutable
syntax "external" : verityExternalLinkMode
syntax "internal_yul" : verityExternalLinkMode
syntax "object_linked" : verityExternalLinkMode
syntax "inline" : verityExternalLinkMode
syntax "compiler_runtime" : verityExternalLinkMode
syntax "external " ident "(" sepBy(term, ",") ")" : verityExternal
syntax "external " ident "(" sepBy(term, ",") ")" " -> " "(" sepBy(term, ",") ")" : verityExternal
syntax "external " ident "(" sepBy(term, ",") ")" ppSpace "linked_as" " := " verityExternalLinkMode : verityExternal
syntax "external " ident "(" sepBy(term, ",") ")" " -> " "(" sepBy(term, ",") ")" ppSpace "linked_as" " := " verityExternalLinkMode : verityExternal
syntax ident " : " term : verityInterfaceParam
syntax "function " ident "(" sepBy(term, ",") ")" verityMutability* ident "(" sepBy(term, ",") ")" : verityInterfaceFunction
syntax "function " ident " (" sepBy(term, ",") ")" verityMutability* ident "(" sepBy(term, ",") ")" : verityInterfaceFunction
syntax "function " ident "(" sepBy(verityInterfaceParam, ",") ")" verityMutability* ident "(" sepBy(term, ",") ")" : verityInterfaceFunction
syntax "function " ident " (" sepBy(verityInterfaceParam, ",") ")" verityMutability* ident "(" sepBy(term, ",") ")" : verityInterfaceFunction
-- void interface methods: no returns clause (e.g. aave supply/borrow are `void`)
syntax "function " ident "(" sepBy(term, ",") ")" verityMutability* : verityInterfaceFunction
syntax "function " ident " (" sepBy(term, ",") ")" verityMutability* : verityInterfaceFunction
syntax "function " ident "(" sepBy(verityInterfaceParam, ",") ")" verityMutability* : verityInterfaceFunction
syntax "function " ident " (" sepBy(verityInterfaceParam, ",") ")" verityMutability* : verityInterfaceFunction
syntax "interface " ident " where " verityInterfaceFunction* "end" : verityInterface
syntax ident " := " ident ppSpace str : verityLocalObligation
syntax "local_obligations " "[" sepBy(verityLocalObligation, ",") "]" : verityLocalObligations
syntax "payable" : verityMutability
syntax "view" : verityMutability
syntax "internal" : verityMutability
syntax pureMutabilityMarker := &"pure"
syntax "no_external_calls" : verityMutability
syntax "allow_post_interaction_writes" : verityMutability
syntax "nonreentrant(" ident ")" : verityMutability
syntax "cei_safe" : verityMutability
syntax "modifies(" sepBy1(ident, ",") ")" : verityModifies
syntax "requires(" ident ")" : verityRequiresRole
syntax ident " : " term:max : verityNewtype
syntax "struct " ident " where " sepBy1(verityParam, ",") : verityStructDecl
syntax "| " ident "(" sepBy(verityParam, ",") ")" : verityAdtVariant
syntax "| " ident : verityAdtVariant
syntax ident " := " verityAdtVariant+ : verityAdtDecl
syntax "storage_namespace " : verityNamespaceSpec
syntax "storage_namespace " "legacy" : verityNamespaceSpec
syntax "storage_namespace " str : verityNamespaceSpec
syntax "storage_namespace " "erc7201 " str : verityNamespaceSpec
syntax "initializer(" ident ")" : verityInitGuard
syntax "reinitializer(" ident ", " num ")" : verityInitGuard
syntax "ecmCall " term:max ppSpace term:max : term
syntax "ecmDo " term:max ppSpace term:max : term
syntax "intrinsic " term:max ppSpace term:max ppSpace term:max : term
syntax "intrinsic_cancun " term:max ppSpace term:max ppSpace term:max : term
syntax "intrinsic_prague " term:max ppSpace term:max ppSpace term:max : term
syntax "intrinsic_fusaka " term:max ppSpace term:max ppSpace term:max : term
syntax "intrinsic_osaka " term:max ppSpace term:max ppSpace term:max : term
syntax "fork_if_at_least " ident ppSpace "then " term:max ppSpace "else " term:max : term
syntax "adt " str : term
syntax "adt " str " [" sepBy(term, ",") "]" : term
syntax "tryCatch " term:max ppSpace term:max : doElem

-- Compile-time Keccak-256 of a string literal (#1973). The hash is
-- materialised at elaboration time (outside contracts) or contract
-- translation time (inside `verity_contract` bodies). Non-literal
-- arguments are rejected by the parser. Declared at `:max` precedence so
-- it fits the right-hand side of `verity_contract` `constants` /
-- `immutable` declarations, which require a `term:max` term.
syntax:max (name := keccakStringTerm) "keccakString " str : term

macro_rules
  | `(intrinsic $_name:term $_lowering:term $_args:term) =>
      `(panic! "verity intrinsic has no default EDSL semantics; add a consumer macro_rules override")
  | `(intrinsic_cancun $_name:term $_lowering:term $_args:term) =>
      `(panic! "verity intrinsic has no default EDSL semantics; add a consumer macro_rules override")
  | `(intrinsic_prague $_name:term $_lowering:term $_args:term) =>
      `(panic! "verity intrinsic has no default EDSL semantics; add a consumer macro_rules override")
  | `(intrinsic_fusaka $_name:term $_lowering:term $_args:term) =>
      `(panic! "verity intrinsic has no default EDSL semantics; add a consumer macro_rules override")
  | `(intrinsic_osaka $_name:term $_lowering:term $_args:term) =>
      `(panic! "verity intrinsic has no default EDSL semantics; add a consumer macro_rules override")
  | `(fork_if_at_least $_fork:ident then $thenExpr:term else $_elseExpr:term) =>
      `($thenExpr)
  | `(adt $_variant:str) => `(0)
  | `(adt $_variant:str [ $[$_args:term],* ]) => `(0)
syntax "revert " ident "(" sepBy(term, ",") ")" : doElem
syntax "revertError " ident "(" sepBy(term, ",") ")" : doElem
syntax "requireError " term:max ppSpace ident "(" sepBy(term, ",") ")" : doElem
syntax (name := requireSomeUintErrorTerm) "requireSomeUintError " term:max ppSpace ident "(" sepBy(term, ",") ")" : term
syntax "ecmBind " term:max ppSpace term:max ppSpace term:max : doElem
syntax (priority := high) "unsafe " str " do " doSeq : doElem
syntax "constructor " "(" sepBy(verityParam, ",") ")" (ppSpace verityLocalObligations)? " := " term : verityConstructor
syntax "constructor " "(" sepBy(verityParam, ",") ")" " payable" (ppSpace verityLocalObligations)? " := " term : verityConstructor
syntax "receive" (ppSpace verityLocalObligations)? " := " term : veritySpecialEntrypoint
syntax "fallback" (ppSpace verityLocalObligations)? " := " term : veritySpecialEntrypoint
syntax "modifier " ident " := " term : verityModifier
syntax "with " sepBy1(ident, ",") : verityModifierUse
syntax "function " verityMutability* (pureMutabilityMarker)? verityMutability* ident " (" sepBy(verityParam, ",") ")" (ppSpace verityInitGuard)? (ppSpace verityModifierUse)? (ppSpace verityRequiresRole)? (ppSpace verityModifies)? (ppSpace verityLocalObligations)? " : " term " := " term : verityFunction

-- verity_intrinsic syntax (minimal one-argument shape for consumer-owned intrinsics)
-- `pure` is parsed as an identifier here to avoid reserving it as a global
-- keyword and breaking ordinary `pure` calls in imported Lean code.
syntax (priority := low) ident : verityIntrinsicClause
syntax &"yul" " := " verityIntrinsicYul : verityIntrinsicClause
syntax &"min_fork" " := " ident : verityIntrinsicClause
syntax &"semantics" " := " term : verityIntrinsicClause
syntax &"obligation" "[" sepBy(verityIntrinsicObligation, ",") "]" : verityIntrinsicClause

syntax ident num num "(" ident str ")" : verityIntrinsicYul
syntax ident str : verityIntrinsicYul
syntax ident " := " ident str : verityIntrinsicObligation

syntax (name := verityIntrinsicCmd)
  "verity_intrinsic " ident " (" sepBy(verityParam, ",") ")" " : " term
  " where " ident ";" ident " := " verityIntrinsicYul ";" ident " := " ident ";"
  ident " := " term ";" ident "[" sepBy(verityIntrinsicObligation, ",") "]" : command

syntax (name := verityContractCmd)
  "verity_contract " ident " where "
  ("types " verityNewtype+)?
  ("inductive " verityAdtDecl+)?
  (verityNamespaceSpec)?
  "storage " verityStorageItem*
  (verityStructDecl)*
  ("errors " verityError+)?
  ("event_defs " verityEvent+)?
  ("constants " verityConstant+)?
  ("immutables " verityImmutable+)?
  ("interfaces " verityInterface+)?
  ("linked_externals " verityExternal+)?
  (verityConstructor)?
  (veritySpecialEntrypoint)*
  (verityModifier)*
  verityFunction* : command

syntax (name := checkContractCmd)
  "#check_contract " ident : command

end Verity.Macro

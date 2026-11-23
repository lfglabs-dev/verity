#!/usr/bin/env python3
r"""Fail if the Solidity importer selects a lowering by a user-chosen name (#2828).

The importer must lower what the source does, not what it is called. A lowering that is not a
translation of the source (a "shortcut") is allowed only through the trusted shortcut registry
`trustedImporterShortcuts` in `Compiler/SolidityImport/InlineAssemblyShims.lean`, which selects
an inline-assembly block by the exact fingerprint of its Yul AST.

Checks, over every non-test `.lean` file under `Compiler/SolidityImport/` (test files end in
`Test.lean` or `Tests.lean`, as in `SourceDigest.lean`; a non-test importer file may not import
one, so skipped code cannot reach the importer):

1. Name selection. A string literal that is exactly an identifier, a dotted identifier or a
   fragment of one with a leading or trailing dot (`"callHook"`, `"TickBitmap.flipTick"`,
   `".flipTick"`, `"Hooks."`, also when written with escapes) is a name wherever it
   occurs: compared, matched, bound by `let` or `if let`, held in a constant, tested with `∈`,
   passed to a helper or used as a JSON key. Every such literal may name only what
   `ALLOWED_IDENTIFIERS` lists: the solc AST node types, AST, storage-layout and standard-JSON
   field names and values, Solidity and Yul builtins and keywords, type words, EVM versions, and
   the importer's own generated bindings, JSON keys, build-tool and driver names. The run fails
   on an entry no literal needs, so the lists hold only what the importer uses. Any other
   literal (with spaces or punctuation) is checked the same way, token by token, in a selection
   position: either operand of `==`, `!=`, `=` or `≠`, a `match` pattern, `.isPrefixOf` /
   `.isSuffixOf` (also `String.startsWith n "..."` and the like), `.contains` / `.startsWith` /
   `.endsWith` / `.find?`, an element of a literal list tested for membership (`.contains`,
   `.elem`, `.any`, `.all`, `.find?`, `∈`); the operand after the operator may be built with `++`
   and parentheses (`n == lib ++ ".flipTick"`); a name or name fragment before it is caught by
   the rule above wherever it is. Lean name literals (`` `foo ``, `` ``foo ``) must be generated
   declaration or syntax names (`ALLOWED_NAME_LITERALS`); the registry module may also name its
   `*YulFingerprint` constants. A function, library, contract or Yul variable name of user code
   (`callHook`, `CurrencyLibrary`, ...) is not listed, so writing one fails here.
   Exempt: literals outside a selection position inside a `theorem` / `lemma` / `example` (up
   to the next line starting in column 0 or starting, at any indent, with a command keyword,
   or a `where` / `let rec` helper), which are test data of a statement; and the reasoned
   `FILE_EXCEPTIONS` (EmitVerity's printed names and example model, the model responder's
   harness id), each an exact literal in one file; Legacy's ABI coder pragma tokens, only inside
   the exact `literals == some #[Json.str ..., Json.str ...]` comparisons of a guarded
   PragmaDirective expression (`PRAGMA_PAIRS`); the importer's synthetic statement kinds
   (`NODE_KIND_MARKERS`), only where Import.lean builds them as a `nodeType` or matches them on
   `mKind`; and a pinned solc release string of the exact
   shape `<major>.<minor>.<patch>+commit.<8 hex>` (`"0.7.6+commit.7338295f"`), which names a
   compiler build and cannot be an identifier. Raw strings (`r"..."`, `r#"..."#`) are read as
   strings without escapes; string gaps (`\` at a line end) and interpolations of nothing or of a
   literal are joined, so a name split by them is one name.
   Scope: only `Compiler/SolidityImport/`; a helper elsewhere under `Compiler/` is not read.
   Not detected, so left to review: a selection by a function selector or other hash of a name
   (`sel == 0xa9059cbb`: number literals are not names to this check, and the importer compares
   selectors such as `Error(string)`'s); a name built at run time (`"call" ++ "Hook"`, `String.mk`),
   a name inside a longer literal outside a selection position, and a listed builtin or JSON
   name that user code may also give its own declaration (e.g. `transfer`, `push`, `add`,
   `target`): the importer compares those only as builtins or reads them as JSON keys, which
   this text check cannot tell apart.
2. Registry-gated names. `startSlot` and `nSlots` are the Yul variable names of the registered
   range-read block. They may occur only in `rangeReadBindings?`, after it has matched the block
   through the registry (`matchTrustedShortcut?`, then `guard` on `.rangeStorageRead`): there
   they locate the inputs of a block already selected by its fingerprint.
3. Registry. Every `trustedImporterShortcuts` entry names its fingerprint constant through a
   quoted name of that same constant, which is a 64-hex-digit `def ...YulFingerprint`; the
   fingerprints are distinct; every evidence path exists and mentions the constant. The match
   type `TrustedShortcutMatch` keeps a private constructor, and every `lower*` definition of the
   registry module takes one and records the shortcut (`recordShortcut m decl_name%`).
4. Routing. Outside the registry module, no importer code names a `*YulFingerprint` constant,
   compares a `yulBlockFingerprint`, or defines (`def`, `abbrev`, with any attributes or
   modifiers, or a `where` / `let rec` helper) a `lower...Shim...` / `lower...Shortcut...`.
   A fixed lowering that is not named as one and is selected by code shape cannot be told
   from a translation by text; the registry's lowerings are bound to it by type (they take a
   `TrustedShortcutMatch`), and anything else is for review.
"""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
IMPORTER_DIR = Path("Compiler/SolidityImport")
REGISTRY_FILE = IMPORTER_DIR / "InlineAssemblyShims.lean"

# Identifiers that may appear in a selection literal. Grouped by where they come from; none is a
# name chosen by the author of the imported code.
# `nodeType` values of solc's AST JSON (libsolidity/ast/ASTJsonExporter.cpp, `ASTJsonConverter.cpp`
# before 0.8.10): the node kinds the importer reads, including those the Solidity 0.7.6 slice
# (`Legacy.lean`) admits or inspects (`ParameterList`, `OverrideSpecifier`,
# `StructuredDocumentation`, `PragmaDirective`), all emitted by both solc 0.7.6 and 0.8.x.
SOLC_AST_NODE_TYPES = {
    "ArrayTypeName", "Assignment", "BinaryOperation", "Block", "Break", "Conditional", "Continue",
    "ContractDefinition", "ElementaryTypeName", "ElementaryTypeNameExpression", "EmitStatement",
    "EnumDefinition", "ErrorDefinition", "EventDefinition", "ExpressionStatement", "ForStatement",
    "FunctionCall", "FunctionCallOptions", "FunctionDefinition", "FunctionTypeName", "Identifier",
    "IfStatement", "IndexAccess", "IndexRangeAccess", "InlineAssembly", "Literal", "Mapping",
    "MemberAccess", "ModifierDefinition", "ModifierInvocation", "NewExpression",
    "OverrideSpecifier", "ParameterList", "PlaceholderStatement", "PragmaDirective", "Return",
    "RevertStatement", "StructDefinition", "StructuredDocumentation", "TryStatement",
    "TupleExpression", "UnaryOperation", "UncheckedBlock", "UserDefinedTypeName",
    "UserDefinedValueTypeDefinition", "VariableDeclaration", "VariableDeclarationStatement",
    "WhileStatement", "YulAssignment", "YulBlock", "YulExpressionStatement", "YulFunctionCall",
    "YulIdentifier", "YulIf", "YulLiteral", "YulVariableDeclaration",
}
# Values of solc AST fields (`kind`, `visibility`, `stateMutability`, `storageLocation`,
# `mutability`, `contractKind`, literal kinds, ...).
SOLC_AST_FIELD_VALUES = {
    "baseConstructorSpecifier", "bool", "calldata", "constant", "constructor", "contract",
    "default", "error", "external", "function", "functionCall", "hexString", "immutable",
    "interface", "internal", "library", "memory", "modifierInvocation", "nonpayable", "number",
    "payable", "private", "public", "pure", "storage", "string", "structConstructorCall",
    "transient", "typeConversion", "unicodeString", "view", "virtual",
    "mutable",
}
# solc's `typeString` / `typeIdentifier` vocabulary.
SOLC_TYPE_WORDS = {
    "address", "block", "bool", "byte", "calldata", "contract", "delegatecall",
    "dynamic_array", "enum", "external", "function", "inplace", "int_const", "interface",
    "internal", "library", "literal_string", "mapping", "memory", "nonpayable", "payable",
    "pointer", "pure", "ref", "returns", "slice", "storage", "string", "struct", "super", "tuple",
    "type", "view",
}
SOLC_TYPE_PREFIXES = ("t_",)
SOLC_SIZED_TYPE = re.compile(r"(?:u?int|bytes|u?fixed)(?:\d+(?:x\d+)?)?\Z")
# Solidity global names, members and builtin functions.
SOLIDITY_BUILTINS = {
    "abi", "addmod", "address", "balance", "basefee", "block", "call", "chainid", "code",
    "codehash", "concat", "data", "days", "decode", "delegatecall", "delete", "ecrecover", "encode",
    "encodeCall", "encodePacked", "encodeWithSelector", "encodeWithSignature", "ether", "false",
    "gas", "gasprice", "gwei", "hours", "interfaceId", "keccak256", "length", "max", "min",
    "minutes", "msg", "mulmod", "name", "number", "origin", "pop", "push", "require", "return",
    "revert", "seconds", "selector", "send", "sender", "sig", "slot", "staticcall", "super", "this",
    "timestamp", "transfer", "true", "tx", "type", "unwrap", "value", "weeks", "wei", "wrap",
}
# EVM dialect builtins of Yul.
YUL_BUILTINS = {
    "add", "addmod", "address", "and", "balance", "basefee", "byte", "call", "callcode",
    "calldatacopy", "caller", "chainid", "clz", "codecopy", "create2", "delegatecall", "div", "eq",
    "exp", "extcodecopy", "extcodesize", "gas", "gasprice", "gt", "invalid", "iszero", "keccak256",
    "lt", "mcopy", "mload", "mod", "mstore", "mstore8", "mul", "mulmod", "not", "number", "or",
    "origin", "pop", "return", "returndatacopy", "returndatasize", "revert", "sar", "sdiv",
    "selfbalance", "sgt", "shl", "shr", "signextend", "sload", "slt", "smod", "sstore",
    "staticcall", "sub", "timestamp", "tload", "tstore", "xor",
}
# Operators and keys solc writes into the AST JSON (compared as JSON keys or operator words).
SOLC_JSON_KEYS = {
    "declaration", "errorName", "id", "kind", "memberName", "modifiers", "mutability", "name",
    "nativeSrc", "nodeType", "operator", "referencedDeclaration", "reorderedReadOnlyArguments",
    "reorderedScalarArguments", "src", "stateMutability", "storageLocation", "suffix", "tryCall",
    "type", "typeIdentifier", "value", "visibility",
}
# Names the importer itself generates for bindings, temporaries and model fields.
IMPORTER_GENERATED = {
    "__solidity_struct_array_", "_verity_memret_", "_verity_raw_storage",
    "_verity_slice_tmp", "_verity_struct_", "_calldata_ptr",
    "_memory_ptr", "_storage", "_storage_ptr", "_pure", "_view", "none", "ok",
    # Binder names of generated Verity code that a source name must not take (`EmitVerity`).
    "oracle", "world",
    # Key of the transient layout the importer stores in its own JSON.
    "verityTransientLayout",
}
# Build-tool names (Foundry remapping inference, source digest file set).
BUILD_TOOL_NAMES = {
    "auto_detect_remappings", "contracts", "demo", "extends", "foundry", "toml", "lib",
    "node_modules", "profile", "remappings", "src", "test", "tests", "txt", "lean", "sol",
    "Test", "Tests", "import", "default", "from",
}
# Names of the importer's own call-responder and oracle modules (differential instruments).
INSTRUMENT_NAMES = {
    "checked", "static", "oracle", "v1", "ecrecover", "precompile", "recording", "call",
    "responder", "selector", "word", "raw",
}
# Exponent markers of Solidity number literals (`1e18`, `2E3`).
SOLIDITY_LITERAL_SYNTAX = {"E", "e"}
# Subcommands of the importer's own differential driver (`Differential.run`).
DRIVER_COMMANDS = {"status", "describe", "run"}
# Keys of solc's AST and storage-layout JSON read as data, and of solc's standard JSON input.
SOLC_JSON_FIELDS = {
    "AST", "Solidity", "arguments", "ast", "baseType", "body", "bytecodeHash", "components",
    "condition", "content", "declarations", "enabled", "evmVersion", "expression", "falseBody",
    "indexed", "initialValue", "initializationExpression", "isInlineArray", "label", "language",
    "leftHandSide", "literals", "members", "metadata", "names", "optimizer", "outputSelection",
    "parameterTypes", "parameters", "runs", "settings", "sources", "statements", "storageLayout",
    "subExpression",
    "transientStorageLayout", "trueBody", "typeDescriptions", "typeName", "typeString", "types",
    "variableNames", "viaIR",
}
# Keys of solc's AST, storage-layout and compiler-output JSON read by the importer.
SOLC_JSON_FIELDS |= {
    "abstract", "anonymous", "astId", "base", "baseContracts", "baseExpression", "baseFunctions",
    "clauses", "commonType", "contractKind", "encoding", "endExpression", "errorCall",
    "errorSelector", "errors", "eventCall", "eventSelector", "externalCall", "externalReferences",
    "falseExpression", "functionName", "functionReturnParameters", "functionSelector", "hexValue",
    "immutables", "implemented", "indexExpression", "isOffset", "isSlot", "key", "keyName",
    "keyType", "leftExpression", "linearizedBaseContracts", "loopExpression", "modifierName",
    "nodes", "numberOfBytes", "offset", "overloadedDeclarations", "overrides", "prefix",
    "returnParameters", "rightExpression", "rightHandSide", "scope", "severity",
    "startExpression", "stateVariable", "subdenomination", "trueExpression", "underlyingType",
    "valueSize", "valueType", "variables",
}
# EVM hard-fork names (solc `evmVersion` values).
EVM_VERSIONS = {
    "berlin", "byzantium", "cancun", "constantinople", "homestead", "istanbul", "london", "osaka",
    "paris", "petersburg", "prague", "shanghai", "spuriousDragon", "tangerineWhistle",
}
# Yul keywords.
YUL_KEYWORDS = {"break", "case", "continue", "default", "for", "function", "if", "leave", "let", "switch"}
# Stems, prefixes and binding names the importer generates for model locals, parameters and
# fields; theorem-family tags it attaches; and its own syntax keywords.
IMPORTER_BINDINGS = {
    "$", "_$", "__solidity_value", "_array", "_bytes", "_calldata", "_data",
    "_element", "_element_next", "_head", "_header", "_index", "_len", "_length", "_memory",
    "_memory_ptr_$dyn_memory_ptr", "_next", "_offset", "_source", "_struct", "_val", "arr_len",
    "arr_ptr", "array", "bytes_ptr", "key1", "key2", "param", "raw_slot", "ret_struct", "str_ptr",
    "struct_param", "node", "denote_prefix", "denote_step", "solidity_closed_transport_cei",
    "solidity_create2_initcode_reentrancy", "solidity_explicit_abi", "solidity_scalar_abi_entry",
    "solidity_static_call_cei", "solidity_trailing_low_level_call_reentrancy", "entry",
}
# Keys of the importer's own JSON (report, differential driver, sequence runner, remapping scan).
IMPORTER_JSON_KEYS = {
    "account", "accounts", "blockNumber", "compilable", "compileError", "compilerProof",
    "configs", "creator", "denoteCovered", "deployment", "digest", "events", "full", "functions",
    "importable", "importerSources", "importerVersion", "member", "modelParam", "nonce",
    "panicPayloadObserved", "parameter", "params", "projections", "shortcuts", "solcInput",
    "solcVersion", "target", "topics", "touched", "words", "libs", "script", "lakefile",
    # Differential driver and sequence-runner input (`args`, `observe`, account setup, mocks).
    "accountBalance", "accountCode", "accountNonce", "args", "byteCallEnvironment",
    "emptyAccounts", "externalStorage", "foreignNonce", "observe", "observeAccounts", "program",
    "transactions",
}

ALLOWED_IDENTIFIERS = (
    SOLC_AST_NODE_TYPES | SOLC_AST_FIELD_VALUES | SOLC_TYPE_WORDS | SOLIDITY_BUILTINS
    | YUL_BUILTINS | SOLC_JSON_KEYS | IMPORTER_GENERATED | BUILD_TOOL_NAMES | INSTRUMENT_NAMES
    | DRIVER_COMMANDS | SOLIDITY_LITERAL_SYNTAX | SOLC_JSON_FIELDS | EVM_VERSIONS | YUL_KEYWORDS | IMPORTER_BINDINGS
    | IMPORTER_JSON_KEYS
)

# Lean name literals of the declarations `solidity_import` generates (`x.model`, `x.report`, ...).
ALLOWED_NAME_LITERALS = {
    "_root_", "model", "report", "covered", "sourceDigest", "Lean.Parser.Term.structInstField",
    "Compiler.SolidityImport.Import",
    # Resolved syntax and type names the importer's commands build terms with.
    "CompilationModel", "Profile", "ImportReport", "Lean.Parser.Command.docComment",
    "Lean.Parser.Term.bracketedBinder",
}

# Exact literals allowed in one file, with why. Each is a name of something other than imported
# Solidity code; a new one needs a new entry here, reviewed with its reason.
_EMIT = "Compiler/SolidityImport/EmitVerity.lean"
_LEGACY = "Compiler/SolidityImport/Legacy.lean"
_RESPONDERS = "Compiler/SolidityImport/ModelResponders.lean"
FILE_EXCEPTIONS = {
    (_RESPONDERS, "imported-model-static-v1"): (
        "program id of the imported-model static responder harness config, a differential "
        "validation instrument (docs/TRUST_ASSUMPTIONS.md, \"Validation instrument: imported-model "
        "static responder\"), not imported by the importer; it selects the harness, not a lowering"),
    **{(_EMIT, lit): (
        "EmitVerity (CompilationModel -> verity_contract printer) matches CompilationModel "
        "`.externalCall` names of linked external functions, which a model author names; the "
        "importer never lowers Solidity source to these names")
       for lit in ("SafeERC20.safeTransfer", "SafeERC20.safeTransferFrom", "ERC20.balanceOf")},
    **{(_EMIT, lit): "EmitVerity prints these Verity type and VerifiedCompilerShim API names"
       for lit in ("Address", "Bool", "Bytes", "Bytes32", "Int256", "String", "Uint16",
                   "Uint256", "Uint8", "Unit", "VerifiedCompilerShim.keccak256Pair",
                   "VerifiedCompilerShim.mulDivDown", "VerifiedCompilerShim.mulDivUp",
                   "VerifiedCompilerShim.safeTransfer", "VerifiedCompilerShim.safeTransferFrom",
                   "VerifiedCompilerShim.staticBalanceOf", "VerifiedCompilerShim.wDivUp",
                   "VerifiedCompilerShim.wMulDown")},
    **{(_EMIT, lit): "names in the hand-written example model `canonicalVaultImportModel`"
       for lit in ("ImportedVaultV2", "totalSupply", "feeAccrued", "paused", "balances",
                   "accrueWadFee", "assets", "feeRateWad", "fee")},
}

# ABI coder pragma tokens: allowed only in Legacy.lean, and only as the exact `literals`
# comparisons of a PragmaDirective. solc splits `pragma experimental ABIEncoderV2;` into
# ["experimental", "ABIEncoderV2"] and, from 0.7.5, `pragma abicoder v2;` into ["abicoder", "v2"]
# (Solidity docs, "Layout of a Source File" > Pragmas). The comparisons count only inside the
# whole guarded expression `optStr n "nodeType" == some "PragmaDirective" && (let literals :=
# (field? n "literals").bind (·.getArr?.toOption); literals == some #[...] || ...)`, so `literals`
# is solc's pragma field and nothing else. Elsewhere, even in Legacy.lean, each token is an
# ordinary (user-nameable) identifier and is checked as such.
PRAGMA_PAIRS = {_LEGACY: (("experimental", "ABIEncoderV2"), ("abicoder", "v2"))}


def _pragma_pair(pair: tuple[str, str]) -> str:
    return (r'literals\s*==\s*some\s*#\[\s*Json\.str\s+"' + pair[0]
            + r'"\s*,\s*Json\.str\s+"' + pair[1] + r'"\s*\]')


def _pragma_block(pairs: tuple[tuple[str, str], ...]) -> re.Pattern[str]:
    cmp = "(?:" + "|".join(_pragma_pair(pair) for pair in pairs) + ")"
    return re.compile(
        r'optStr\s+(\w+)\s+"nodeType"\s*==\s*some\s+"PragmaDirective"\s*&&\s*'
        r'\(\s*let\s+literals\s*:=\s*\(\s*field\?\s+\1\s+"literals"\s*\)'
        r'\.bind\s*\(\s*·\.getArr\?\.toOption\s*\)\s*'
        + cmp + r'(?:\s*\|\|\s*' + cmp + r')*\s*\)')


def pragma_literal_spans(rel: str, code: str) -> list[tuple[int, int]]:
    """Spans of the allowed comparisons in `code` (comments blanked, so a comment cannot keep an
    entry in use), each inside a whole guarded PragmaDirective expression."""
    pairs = PRAGMA_PAIRS.get(rel, ())
    if not pairs:
        return []
    spans = []
    for block in _pragma_block(pairs).finditer(code):
        for pair in pairs:
            for m in re.finditer(_pragma_pair(pair), block.group(0)):
                USED.add(("pragma", f"{rel}:{pair[0]} {pair[1]}"))
                spans.append((block.start() + m.start(), block.start() + m.end()))
    return spans


# The importer's own synthetic statement kinds (`uncheckedEnd`, `scopeEnd` in Import.lean): marker
# nodes it splices into a flattened statement list to restore a recorded scope. The AST reaches the
# importer only as `solc --standard-json` output (the compiler's sha256 is checked before and after
# the run), so every `nodeType` it reads is one of solc's fixed node kinds: Solidity source cannot
# set a `nodeType`, and solc never emits these. A marker literal is allowed only in its file and
# only in two forms: built as `("nodeType", Json.str "<marker>")`, or as a `match` arm pattern
# whose enclosing `match` is `match ← mKind <stmt> with` (no earlier arm or deeper line opens
# alternatives that could own the arm, and the file does not rebind `mKind`). Left to review: a
# node the importer builds with a non-literal `nodeType` (every synthetic `nodeType` in Import.lean
# is a literal today), a use of a marker-building `def` (e.g. `scopeEnd`) other than splicing it
# into a statement list, and a change to `mKind` itself (ExprHelpers.lean) or an `open` that
# replaces it. Anywhere else (a name comparison, a
# `nodeType` read of another field, another file) it is an ordinary identifier and is checked.
_IMPORT = "Compiler/SolidityImport/Import.lean"
NODE_KIND_MARKERS = {(_IMPORT, "VerityScopeEnd"), (_IMPORT, "VerityUncheckedEnd")}
# Built only as the whole body of a `def ... : Json :=` that is `Json.mkObj [("nodeType", Json.str
# "<marker>"), ...]`: the marker is then a node's `nodeType` and nothing else (not a tuple or
# object projected, compared or tested for membership).
_MARKER_CREATE = re.compile(
    r'(?:^|\n)[ \t]*(?:private\s+)?def\s+\w+[^\n]*:\s*Json\s*:=\s*'
    r'Json\.mkObj\s*\[\s*\(\s*"nodeType"\s*,\s*Json\.str\s*\Z')
_MARKER_CREATE_END = re.compile(r'\s*\)\s*[,\]]')
# A local binding that could shadow `mKind` (ExprHelpers.lean's AST `nodeType` reader).
_MKIND_BINDING = re.compile(
    r'\b(?:let|have|fun|λ|def|abbrev|where)\s+(?:rec\s+)?mKind\b|\(\s*mKind\s*:|\bmKind\s*:=')
# A line that opens alternatives on the following lines (`match ... with`, `fun`, `function`).
_OPENS_ALTS = re.compile(r'(?:\bwith|\bfun|\bfunction|λ)\s*\Z')
_MATCH_ARM = re.compile(r'\s*\|\s*(?:"\w+"\s*\|\s*)*\Z')
_MATCH_ARM_END = re.compile(r'(?:\s*\|\s*"\w+")*\s*=>')
_KIND_MATCH_HEAD = re.compile(r'^\s*match\s+←\s*mKind\s+\w+\s+with\s*\Z')


def node_kind_marker_form(code: str, start: int, end: int) -> str | None:
    """`create` or `kind arm` when the literal at code[start:end] is in an allowed marker form."""
    line_start = code.rfind("\n", 0, start) + 1
    line_end = code.find("\n", end)
    line_end = len(code) if line_end < 0 else line_end
    before, after = code[line_start:start], code[end:line_end]
    if _MARKER_CREATE.search(code[max(0, start - 300):start]) and _MARKER_CREATE_END.match(after):
        # The list must close the definition: nothing but whitespace after its `]` up to the
        # next line starting in column 0 (or the end of the file).
        depth, i = 1, code.rfind("[", 0, start) + 1
        while i < len(code) and depth:
            depth += {"[": 1, "]": -1}.get(code[i], 0)
            i += 1
        if not depth and re.match(r"[ \t]*(?:\n[ \t]*)*(?:\n(?=\S)|\Z)", code[i:]):
            return "create"
        return None
    if not (_MATCH_ARM.fullmatch(before) and _MATCH_ARM_END.match(after)):
        return None
    if _MKIND_BINDING.search(code):
        return None
    indent = len(before) - len(before.lstrip())
    lines = code[:line_start].split("\n")
    # Walk up over the earlier arms (`|` at the arm's indent) and their bodies (deeper); the first
    # other line must be the head of this arm's `match`, and that head must match on `mKind`. An
    # earlier arm that opens a `match`, `fun` or `function` itself, or a deeper line opening
    # alternatives that could reach this arm's column, could own this arm: rejected.
    for i in range(len(lines) - 1, -1, -1):
        line = lines[i]
        if not line.strip():
            continue
        line_indent = len(line) - len(line.lstrip())
        if line_indent == indent and line.lstrip().startswith("|"):
            if re.search(r"\bmatch\b|\bfun\b|\bfunction\b|λ", line):
                return None
            continue
        if line_indent > indent:
            if _OPENS_ALTS.search(line.rstrip()):
                nxt = next((l for l in lines[i + 1:] if l.strip()), None)
                if nxt is None or len(nxt) - len(nxt.lstrip()) <= indent:
                    return None
            continue
        return "kind arm" if _KIND_MATCH_HEAD.match(line) else None
    return None


# A pinned solc release, `<major>.<minor>.<patch>+commit.<8 hex digits>` (solc `--version`, the
# standard-JSON `longVersion`; e.g. "0.7.6+commit.7338295f"). It names a compiler build, never
# imported code: a Solidity identifier cannot contain `.` or `+`, so no user name has this shape.
SOLC_RELEASE = re.compile(r"\d+\.\d+\.\d+\+commit\.[0-9a-f]{8}")

# Yul variable names of the registered range-read block (`extsloadRangeYulFingerprint`), read
# only after `rangeReadBindings?` matched the block through the registry.
REGISTRY_GATED = {"startSlot": "rangeReadBindings?", "nSlots": "rangeReadBindings?"}
REGISTRY_GATE = re.compile(
    r"let\s+(\w+)\s*←\s*matchTrustedShortcut\?\s+\w+\s*\n\s*guard\s*\(\s*\1\.shortcut\.lowering\s*==\s*\.rangeStorageRead\s*\)"
)

# A name, a dotted name, or a fragment of one (`".flipTick"`, `"Hooks."`).
IDENT_LITERAL = re.compile(r"\.?[A-Za-z_$][\w$]*(?:\.[A-Za-z_$][\w$]*)*\.?")
HEX_DIGEST = re.compile(r"[0-9a-f]{40,64}")
# Lean name literals: `` `foo `` and resolved `` ``foo ``.
NAME_LITERAL = re.compile(r"(?<![`\w])(``?)(?![`(\[])([A-Za-z_][\w.']*)")
PROOF_END = re.compile(
    r"(?m)^(?=\S)|^\s*(?:where|mutual|def|abbrev|instance|class|structure|inductive|theorem|lemma|"
    r"example|private|protected|public|noncomputable|nonrec|partial|unsafe|namespace|section|end|open|"
    r"set_option|initialize|builtin_initialize|macro|macro_rules|syntax|elab|elab_rules|local|"
    r"scoped|attribute|opaque|axiom|@\[|#)(?![\w'?!])|\blet\s+rec\b|\bwhere[ \t]*$")
DECL_START = re.compile(
    r"(?m)^(?:/--|@\[|(?:private\s+|partial\s+|protected\s+|noncomputable\s+|unsafe\s+)*"
    r"(?:def|theorem|lemma|example|structure|inductive|abbrev|instance|namespace|end|section|syntax|"
    r"macro|elab|open|set_option|#)\b)")
IDENT = re.compile(r"(?<![0-9A-Za-z_$])[A-Za-z_$][A-Za-z0-9_$]*")
NUMBER = re.compile(r"\b0x[0-9a-fA-F]*\b|\b\d\w*")


def is_test_file(path: Path) -> bool:
    return path.name.endswith("Test.lean") or path.name.endswith("Tests.lean")


def importer_files(root: Path) -> list[Path]:
    base = root / IMPORTER_DIR
    return sorted(p for p in base.rglob("*.lean") if p.is_file() and not is_test_file(p))


INTERESTING = re.compile(r"/-|--|(?<![\w'])r#*\"|[\"'{}]")


# Lean string escapes: `\xHH`, `\uHHHH`, `\n`, `\t`, `\r`, `\\`, `\"`, `\'`.
ESCAPE = re.compile(r"\\(?:x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|[ntr\\\"'])")


def decode_escape(esc: str) -> str:
    """The character a Lean string escape stands for, so an escaped name is checked as a name."""
    if esc[1] in "xu":
        return chr(int(esc[2:], 16))
    return {"n": "\n", "t": "\t", "r": "\r"}.get(esc[1], esc[1])


# Opening of a Lean raw string: `r"..."` or `r#"..."#` (no escapes inside).
RAW_OPEN = re.compile(r'r(#*)"')


class Literal:
    """A string literal: `start`/`end` offsets of the quotes, `text` without escapes and with
    interpolations (`{...}` of `s!` / `m!` / `f!` strings) blanked."""

    def __init__(self, start: int, end: int, text: str) -> None:
        self.start, self.end, self.text = start, end, text


def scan(text: str) -> tuple[str, list[Literal]]:
    """Blank out Lean comments (nested `/- -/`, `--`), keeping offsets and newlines, and list the
    string literals, including those inside interpolations."""
    out = list(text)
    literals: list[Literal] = []
    n = len(text)

    def blank(i: int) -> None:
        if text[i] != "\n":
            out[i] = " "

    def string(i: int, interpolated: bool) -> int:
        """`text[i]` is an opening quote; return the offset after the closing one."""
        start = i
        i += 1
        body: list[str] = []
        while i < n and text[i] != '"':
            if text[i] == "\\" and i + 1 < n and text[i + 1] == "\n":
                # String gap: `\` at a line end drops the newline and the next line's indent.
                i += 2
                while i < n and text[i] in " \t\n":
                    i += 1
            elif text[i] == "\\":
                esc = ESCAPE.match(text, i)
                if esc is None:
                    body.append(" ")
                    i += 2
                else:
                    body.append(decode_escape(esc.group(0)))
                    i = esc.end()
            elif interpolated and text[i] == "{":
                inner = i + 1
                i = code(i + 1, closing="}")
                # An interpolation of nothing or of a literal adds no separator, so a name split
                # around it (`s!"call{""}Hook"`) is still read as one name.
                hole = text[inner:i - 1].strip()
                body.append("" if hole == "" or re.fullmatch(r'"[^"\\]*"', hole) else " ")
                if re.fullmatch(r'"[^"\\]*"', hole):
                    body.append(hole[1:-1])
            else:
                body.append(text[i])
                i += 1
        literals.append(Literal(start, i + 1, "".join(body)))
        return i + 1

    def code(i: int, closing: str | None = None) -> int:
        depth = 0
        while i < n:
            nxt = INTERESTING.search(text, i)
            if nxt is None:
                return n
            i = nxt.start()
            c = text[i]
            if text.startswith("/-", i):
                d = 1
                blank(i); blank(i + 1)
                i += 2
                while i < n and d > 0:
                    if text.startswith("/-", i):
                        d += 1
                        blank(i); blank(i + 1)
                        i += 2
                    elif text.startswith("-/", i):
                        d -= 1
                        blank(i); blank(i + 1)
                        i += 2
                    else:
                        blank(i)
                        i += 1
            elif text.startswith("--", i):
                while i < n and text[i] != "\n":
                    blank(i)
                    i += 1
            elif c == '"' or (c == "r" and RAW_OPEN.match(text, i) and
                              (i == 0 or not (text[i - 1].isalnum() or text[i - 1] in "_'"))):
                raw = RAW_OPEN.match(text, i) if c == "r" else None
                if raw is not None:
                    hashes = raw.group(1)
                    close = text.find('"' + hashes, raw.end())
                    close = n if close < 0 else close
                    literals.append(Literal(i + len(hashes) + 1, close + 1, text[raw.end():close]))
                    i = close + 1 + len(hashes)
                    continue
                interpolated = i >= 2 and text[i - 2:i] in ("s!", "m!", "f!")
                i = string(i, interpolated)
            elif c == "'" and i + 2 < n and text[i + 2] == "'" and text[i + 1] != "\\":
                i += 3
            elif c == "'" and i + 3 < n and text[i + 1] == "\\" and text[i + 3] == "'":
                i += 4
            elif closing is not None and c == "{":
                depth += 1
                i += 1
            elif closing is not None and c == "}":
                if depth == 0:
                    return i + 1
                depth -= 1
                i += 1
            else:
                i += 1
        return i

    code(0)
    literals.sort(key=lambda lit: lit.start)
    return "".join(out), literals


def literal_identifiers(body: str) -> list[str]:
    return [i for i in IDENT.findall(NUMBER.sub(" ", body)) if i.strip("_")]


def line_of(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def operand_head(before: str) -> str:
    """`before` (the text up to a literal) without what still belongs to the literal's operand: an
    interpolation prefix (`s!`), opening parentheses, and leading `x ++` pieces, so that in
    `n == lib ++ ".f"` or `n.endsWith (".f")` the literal is seen next to the operator."""
    while True:
        trimmed = re.sub(r"(?<![\w'])[smf]!\Z|\(\s*\Z", "", before)
        trimmed = re.sub(r"(?:[\w.?!']+|\([^()\n]*\)|\"(?:[^\"\\\n]|\\.)*\")\s*\+\+\s*\Z", "", trimmed)
        if trimmed == before:
            return before
        before = trimmed


def selection_kind(code: str, start: int, end: int,
                   membership_lists: list[tuple[int, int]]) -> str | None:
    """Why the string literal at `code[start:end]` is in a selection position, if it is."""
    before = operand_head(code[max(0, start - 200):start])
    after = code[end:end + 40]
    if re.search(r"(?:==|!=|≠|(?<![:=!<>])=(?![=>]))\s*(?:\.?some\s+)?\(?\s*\Z", before):
        return "compared with == / != / = / ≠"
    if re.match(r"\s*(?:==|!=|≠|=(?![=>])|\.isPrefixOf\b|\.isSuffixOf\b)", after):
        return "compared with == / != / = / ≠ or a prefix test"
    body = code[start + 1:end - 1]
    if re.fullmatch(r"[A-Za-z_$][\w$.]*", body) and not re.fullmatch(r"[0-9a-f]{64}", body) and \
            re.search(r"(?m)^(?:private\s+|protected\s+)?(?:def|abbrev)\s+\S+\s*(?::\s*String\s*)?:=\s*\Z",
                      code[max(0, start - 200):start]):
        return "named string constant (its uses are not traced)"
    if re.search(r"\.(?:contains|startsWith|endsWith|find\?|findD|contains\?|elem)\s+\Z", before) or \
            re.search(r"\bString\.(?:startsWith|endsWith|isPrefixOf|isSuffixOf)\s+(?:\S+\s+)?\Z", before):
        return "argument of a name lookup or membership test"
    if re.search(r"(?:inlineAssemblyIdentDecl\?\s+\S+|yulIdentifierSrcs)\s+\Z", before):
        return "Yul identifier name lookup"
    line_start = code.rfind("\n", 0, start) + 1
    line_end = code.find("\n", end)
    line = code[line_start:line_end if line_end >= 0 else len(code)]
    head = code[line_start:start]
    if head.lstrip().startswith("|") and "=>" in line[len(head):] and "=>" not in head:
        return "match pattern"
    for lo, hi in membership_lists:
        if lo < start < hi:
            return "element of a literal list membership test"
    return None


def without_strings(code: str, literals: list[Literal]) -> str:
    """`code` with every string literal's contents blanked (quotes kept)."""
    out = list(code)
    for lit in literals:
        for k in range(lit.start + 1, lit.end - 1):
            if out[k] != "\n":
                out[k] = " "
    return "".join(out)


def membership_list_spans(code: str, literals: list[Literal]) -> list[tuple[int, int]]:
    """Spans of literal lists tested for membership: `[...]` in `["a", "b"].contains x`."""
    bare = without_strings(code, literals)
    spans = []
    for m in re.finditer(r"∈\s*\[", bare):
        depth = 0
        for j in range(m.end() - 1, len(bare)):
            if bare[j] == "[":
                depth += 1
            elif bare[j] == "]":
                depth -= 1
                if depth == 0:
                    spans.append((m.end() - 1, j))
                    break
    for m in re.finditer(r"\]\s*\.(?:contains|elem|any|all|find\?)\b", bare):
        depth = 0
        for j in range(m.start(), -1, -1):
            if bare[j] == "]":
                depth += 1
            elif bare[j] == "[":
                depth -= 1
                if depth == 0:
                    spans.append((j, m.start()))
                    break
    return spans


def def_span(code: str, name: str) -> tuple[int, int] | None:
    m = re.search(r"(?m)^(?:private\s+|partial\s+|protected\s+)*def\s+" + re.escape(name) + r"(?=[\s(:])", code)
    if not m:
        return None
    nxt = re.search(r"(?m)^(?:/--|@\[|(?:private\s+|partial\s+|protected\s+|noncomputable\s+|unsafe\s+)*(?:def|theorem|structure|inductive|abbrev|instance|namespace|end|section)\b)", code[m.end():])
    return m.start(), (m.end() + nxt.start()) if nxt else len(code)


def proof_spans(code: str) -> list[tuple[int, int]]:
    """Spans of `theorem` / `lemma` / `example` declarations: their literals are test data of a
    statement and cannot select a lowering. A span ends at the next line that starts in column 0
    (the next command, whatever it is) or at a `where` / `let rec` helper, which is checked."""
    spans = []
    for m in re.finditer(r"(?m)^(?:@\[[^\]\n]*\]\s*)?(?:private\s+|protected\s+)?(?:theorem|lemma|example)\b",
                         code):
        nxt = PROOF_END.search(code, m.end())
        spans.append((m.start(), nxt.start() if nxt else len(code)))
    return spans


# Allowlist entries a run has needed: the run fails on an entry it never needed, so each list
# holds only what the importer uses.
USED: set[tuple[str, str]] = set()


def is_allowed(ident: str) -> bool:
    if ident.startswith(SOLC_TYPE_PREFIXES) or SOLC_SIZED_TYPE.match(ident):
        return True
    if ident in ALLOWED_IDENTIFIERS:
        USED.add(("ident", ident))
        return True
    return False


def check_names(root: Path, errors: list[str]) -> None:
    for path in importer_files(root):
        rel = path.relative_to(root)
        raw = path.read_text(encoding="utf-8")
        code, literals = scan(raw)
        lists = membership_list_spans(code, literals)
        proofs = proof_spans(code)
        pragmas = pragma_literal_spans(rel.as_posix(), code)
        for m in literals:
            body = m.text
            idents = literal_identifiers(body)
            if not idents:
                continue
            if (rel.as_posix(), body) in FILE_EXCEPTIONS:
                USED.add(("file", f"{rel.as_posix()}:{body}"))
                continue
            if SOLC_RELEASE.fullmatch(body):
                continue
            if any(lo <= m.start and m.end <= hi for lo, hi in pragmas):
                continue
            if (rel.as_posix(), body) in NODE_KIND_MARKERS:
                form = node_kind_marker_form(code, m.start, m.end)
                if form is not None:
                    USED.add(("marker", f"{rel.as_posix()}:{body}:{form}"))
                    continue
            kind = selection_kind(code, m.start, m.end, lists)
            if kind is None and any(lo <= m.start < hi for lo, hi in proofs):
                continue
            if kind is None:
                # A literal that is exactly an identifier (or a dotted one) is a name wherever it
                # is: held in a constant, bound by `let`, matched by `if let`, tested with `∈`,
                # passed to a helper. Only a JSON key read from solc's or the importer's own JSON
                # is exempt.
                if not IDENT_LITERAL.fullmatch(body) or HEX_DIGEST.fullmatch(body):
                    continue
                kind = "identifier-shaped string literal"
            for ident in idents:
                if is_allowed(ident):
                    continue
                where = f"{rel}:{line_of(code, m.start)}"
                gate = REGISTRY_GATED.get(ident)
                if gate is not None:
                    span = def_span(code, gate)
                    if span and span[0] <= m.start < span[1]:
                        gated = REGISTRY_GATE.search(code, span[0], span[1])
                        if gated and gated.end() <= m.start:
                            continue
                        errors.append(
                            f"{where}: `{ident}` is read in {gate} before the block matched the "
                            f"trusted shortcut registry (`let m ← matchTrustedShortcut? asm` then "
                            f"`guard (m.shortcut.lowering == .rangeStorageRead)`)")
                        continue
                    errors.append(
                        f"{where}: `{ident}` ({kind}) is a Yul variable name of a registered block; "
                        f"it may be read only in {gate}, after the registry matched the block")
                    continue
                errors.append(
                    f"{where}: string literal \"{body}\" ({kind}) contains `{ident}`, which is not a "
                    f"solc AST, Solidity or Yul builtin, type or importer name: the importer must not "
                    f"select a lowering by a user-chosen name. A fixed lowering of user code goes "
                    f"through trustedImporterShortcuts ({REGISTRY_FILE}), keyed by fingerprint. If "
                    f"`{ident}` is a builtin or the importer's own name, add it to "
                    f"scripts/check_importer_name_selection.py with its category; if the "
                    f"literal is a message, write it as a sentence.")
        bare = without_strings(code, literals)
        for nm in NAME_LITERAL.finditer(bare):
            quote, name = nm.group(1), nm.group(2)
            if any(lo <= nm.start() < hi for lo, hi in proofs):
                continue
            if quote == "``" and rel == REGISTRY_FILE and name.endswith("YulFingerprint"):
                continue  # the registry names its fingerprint constants (checked below)
            if name in ALLOWED_NAME_LITERALS:
                USED.add(("name", name))
                continue
            errors.append(
                f"{rel}:{line_of(code, nm.start())}: Lean name literal {quote}{name} is not one of "
                f"the importer's generated declaration or syntax names (ALLOWED_NAME_LITERALS): a "
                f"name literal must not select a lowering")


def check_registry(root: Path, errors: list[str]) -> None:
    path = root / REGISTRY_FILE
    if not path.is_file():
        errors.append(f"{REGISTRY_FILE}: missing (the trusted shortcut registry)")
        return
    code, _ = scan(path.read_text(encoding="utf-8"))
    constants = dict(re.findall(
        r"(?m)^def\s+(\w+YulFingerprint)\s*:\s*String\s*:=\s*\"([0-9a-f]{64})\"", code))
    span = def_span(code, "trustedImporterShortcuts")
    if span is None:
        errors.append(f"{REGISTRY_FILE}: no `def trustedImporterShortcuts`")
        return
    registry = code[span[0]:span[1]]
    entries = re.split(r"\n\s*,\s*\{|\[\s*\{", registry)[1:]
    if not entries:
        errors.append(f"{REGISTRY_FILE}: trustedImporterShortcuts has no entries")
    seen: dict[str, str] = {}
    for entry in entries:
        name_m = re.search(r"fingerprintName\s*:=\s*\(``(\w+)\)\.getString!", entry)
        fp_m = re.search(r"\bfingerprint\s*:=\s*(\w+)", entry)
        ev_m = re.search(r"evidence\s*:=\s*\[([^\]]*)\]", entry)
        low_m = re.search(r"lowering\s*:=\s*\.(\w+)", entry)
        label = (fp_m.group(1) if fp_m else entry.strip()[:40])
        if not (name_m and fp_m and ev_m and low_m):
            errors.append(f"{REGISTRY_FILE}: entry {label}: needs fingerprintName := (``C).getString!, "
                          f"fingerprint := C, lowering := .<ctor> and a non-empty evidence list")
            continue
        const = fp_m.group(1)
        if name_m.group(1) != const:
            errors.append(f"{REGISTRY_FILE}: entry {const}: fingerprintName names {name_m.group(1)}, "
                          f"not the constant its fingerprint reads")
        if const not in constants:
            errors.append(f"{REGISTRY_FILE}: entry {const}: not a `def {const} : String := "
                          f"\"<64 hex digits>\"` of this file")
            continue
        if constants[const] in seen:
            errors.append(f"{REGISTRY_FILE}: entries {seen[constants[const]]} and {const} have the "
                          f"same fingerprint")
        seen[constants[const]] = const
        paths = re.findall(r'"([^"]+)"', ev_m.group(1))
        if not paths:
            errors.append(f"{REGISTRY_FILE}: entry {const}: no evidence path")
        for ev in paths:
            ev_path = root / ev
            if not ev_path.is_file():
                errors.append(f"{REGISTRY_FILE}: entry {const}: evidence {ev} does not exist")
            elif const not in ev_path.read_text(encoding="utf-8") and \
                    low_m.group(1) not in ev_path.read_text(encoding="utf-8"):
                errors.append(f"{REGISTRY_FILE}: entry {const}: evidence {ev} mentions neither "
                              f"{const} nor .{low_m.group(1)}")
    unused = sorted(set(constants) - set(seen.values()))
    for const in unused:
        errors.append(f"{REGISTRY_FILE}: {const} is defined but no registry entry uses it")
    if not re.search(r"structure\s+TrustedShortcutMatch\s+where\s*\n\s*private\s+mk\s*::", code):
        errors.append(f"{REGISTRY_FILE}: TrustedShortcutMatch must keep `private mk ::` so that only "
                      f"matchTrustedShortcut? builds one")
    for m in re.finditer(r"(?m)^(?:private\s+)?(?:partial\s+)?def\s+(lower\w*)([^:]*(?::(?!=)[^:]*)*?):=", code):
        name, sig = m.group(1), m.group(2)
        body_span = def_span(code, name)
        body = code[body_span[0]:body_span[1]] if body_span else ""
        if not re.match(r"\s*\(\s*m\s*:\s*TrustedShortcutMatch\s*\)", sig):
            errors.append(f"{REGISTRY_FILE}: {name} must take `(m : TrustedShortcutMatch)` first")
        if "recordShortcut m decl_name%" not in body:
            errors.append(f"{REGISTRY_FILE}: {name} must record its use (`recordShortcut m decl_name%`)")


def check_routing(root: Path, errors: list[str]) -> None:
    for path in importer_files(root):
        rel = path.relative_to(root)
        for imp in re.finditer(r"(?m)^\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?([\w.]+)", path.read_text(encoding="utf-8")):
            if imp.group(1).endswith(("Test", "Tests")):
                errors.append(f"{rel}: imports the test module {imp.group(1)}, which this check "
                              f"skips; importer code must not depend on a test module")
        if rel == REGISTRY_FILE:
            continue
        code, literals = scan(path.read_text(encoding="utf-8"))
        code_no_strings = without_strings(code, literals)
        for m in re.finditer(r"\b\w+YulFingerprint\b", code_no_strings):
            errors.append(f"{rel}:{line_of(code, m.start())}: {m.group(0)} outside the registry: "
                          f"select a shortcut with matchTrustedShortcut?")
        for m in re.finditer(r"\byulBlockFingerprint\b", code_no_strings):
            lo = code_no_strings.rfind("\n", 0, m.start()) + 1
            hi = code_no_strings.find("\n", m.end())
            if re.search(r"==|!=|\.contains|\.find\?", code_no_strings[lo:hi if hi >= 0 else None]):
                errors.append(f"{rel}:{line_of(code, m.start())}: compares a yulBlockFingerprint "
                              f"outside the registry: select a shortcut with matchTrustedShortcut?")
        for m in re.finditer(r"\b(lower\w*(?:Shim|Shortcut)\w*)(?=[\s(:])", code_no_strings):
            head = code_no_strings[code_no_strings.rfind("\n", 0, m.start()) + 1:m.start()]
            if not re.search(r"(?:\bdef|\babbrev|\bwhere|\blet\s+rec)\s+\Z|\A\s*\Z", head):
                continue
            errors.append(f"{rel}:{line_of(code, m.start())}: {m.group(1)} defined outside the "
                          f"registry module {REGISTRY_FILE}")


def check_unused(errors: list[str]) -> None:
    for ident in sorted(ALLOWED_IDENTIFIERS):
        if ("ident", ident) not in USED:
            errors.append(f"allowlist entry `{ident}` is not needed by any importer literal: "
                          f"remove it from scripts/check_importer_name_selection.py")
    for name in sorted(ALLOWED_NAME_LITERALS):
        if ("name", name) not in USED:
            errors.append(f"ALLOWED_NAME_LITERALS entry `{name}` is not used: remove it")
    for file, marker in sorted(NODE_KIND_MARKERS):
        for form in ("create", "kind arm"):
            if ("marker", f"{file}:{marker}:{form}") not in USED:
                errors.append(f"NODE_KIND_MARKERS entry {file}: \"{marker}\" has no {form} "
                              f"site: a marker is built as a nodeType and matched on mKind")
    for file, pairs in sorted(PRAGMA_PAIRS.items()):
        for pair in pairs:
            if ("pragma", f"{file}:{pair[0]} {pair[1]}") not in USED:
                errors.append(f"PRAGMA_PAIRS entry {file}: {pair} is not used in a guarded "
                              f"PragmaDirective `literals` comparison: remove it")
    for file, lit in sorted(FILE_EXCEPTIONS):
        if ("file", f"{file}:{lit}") not in USED:
            errors.append(f"FILE_EXCEPTIONS entry {file}: \"{lit}\" is not used: remove it")


def run(root: Path) -> list[str]:
    errors: list[str] = []
    USED.clear()
    check_names(root, errors)
    check_unused(errors)
    check_registry(root, errors)
    check_routing(root, errors)
    return errors


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--root", type=Path, default=ROOT)
    args = parser.parse_args(argv)
    errors = run(args.root)
    if errors:
        print("importer name-selection check failed:", file=sys.stderr)
        for e in errors:
            print(f"  {e}", file=sys.stderr)
        return 1
    print("importer name-selection check passed "
          f"({len(importer_files(args.root))} importer files; shortcuts only via trustedImporterShortcuts)")
    return 0


if __name__ == "__main__":
    sys.exit(main())

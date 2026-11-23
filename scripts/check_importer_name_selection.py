#!/usr/bin/env python3
"""Fail if the Solidity importer selects a lowering by a user-chosen name (#2828).

The importer must lower what the source does, not what it is called. A lowering that is not a
translation of the source (a "shortcut") is allowed only through the trusted shortcut registry
`trustedImporterShortcuts` in `Compiler/SolidityImport/InlineAssemblyShims.lean`, which selects
an inline-assembly block by the exact fingerprint of its Yul AST.

Checks, over every non-test `.lean` file under `Compiler/SolidityImport/` (test files end in
`Test.lean` or `Tests.lean`, as in `SourceDigest.lean`):

1. Name selection. A string literal in a selection position (either operand of `==`, `!=`,
   `=` or `≠`, a `match` pattern, the receiver of `.isPrefixOf` / `.isSuffixOf`, the argument
   of `.contains` / `.startsWith` / `.endsWith` / `.find?`, an element of a literal list tested
   with `.contains` / `.elem` / `.any` / `.all`, the name argument of `inlineAssemblyIdentDecl?`
   / `yulIdentifierSrcs`, or the value of an identifier-shaped `def`/`abbrev` string constant)
   may contain only identifiers listed in `ALLOWED_IDENTIFIERS`: the solc AST node types, AST
   field values, Solidity and Yul builtins, type words, importer-generated names and build-tool
   names the importer compares today (the list holds no unused entry). A function, library,
   contract or Yul variable name of user code (`callHook`, `CurrencyLibrary`, ...) is not
   there, so comparing one fails here.
   Not detected, so left to review: a literal passed to a helper that compares it inside (only
   the helpers above are known); a comparison with a value built at run time; and a listed
   builtin name that user code may also choose for its own declaration (e.g. `transfer`,
   `push`, `add`): the importer compares those only for builtins (e.g. members without a
   `referencedDeclaration`), which this text check cannot see.
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
   compares a `yulBlockFingerprint`, or defines a `lower...Shim...` / `lower...Shortcut...`.
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
SOLC_AST_NODE_TYPES = {
    "ArrayTypeName", "Assignment", "BinaryOperation", "Block", "Break", "Conditional", "Continue",
    "ContractDefinition", "ElementaryTypeName", "ElementaryTypeNameExpression", "EmitStatement",
    "EnumDefinition", "ErrorDefinition", "EventDefinition", "ExpressionStatement", "ForStatement",
    "FunctionCall", "FunctionCallOptions", "FunctionDefinition", "FunctionTypeName", "Identifier",
    "IfStatement", "IndexAccess", "IndexRangeAccess", "InlineAssembly", "Literal", "Mapping",
    "MemberAccess", "ModifierDefinition", "ModifierInvocation", "NewExpression",
    "PlaceholderStatement", "Return", "RevertStatement", "StructDefinition", "TryStatement",
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
}
# solc's `typeString` / `typeIdentifier` vocabulary.
SOLC_TYPE_WORDS = {
    "address", "block", "bool", "byte", "bytes", "calldata", "contract", "delegatecall",
    "dynamic_array", "enum", "external", "function", "inplace", "int", "int_const", "interface",
    "internal", "library", "literal_string", "mapping", "memory", "nonpayable", "payable",
    "pointer", "pure", "ref", "returns", "slice", "storage", "string", "struct", "super", "tuple",
    "type", "uint", "view",
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
    "_verity_slice_tmp", "_verity_struct_", "VerityUncheckedEnd", "_calldata_ptr",
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
# Subcommands of the importer's own differential driver (`Differential.run`).
DRIVER_COMMANDS = {"status", "describe", "run"}

ALLOWED_IDENTIFIERS = (
    SOLC_AST_NODE_TYPES | SOLC_AST_FIELD_VALUES | SOLC_TYPE_WORDS | SOLIDITY_BUILTINS
    | YUL_BUILTINS | SOLC_JSON_KEYS | IMPORTER_GENERATED | BUILD_TOOL_NAMES | INSTRUMENT_NAMES
    | DRIVER_COMMANDS
)

# Exact literals allowed in one file, with why. Each is a name of something other than imported
# Solidity code; a new one needs a new entry here, reviewed with its reason.
FILE_EXCEPTIONS = {
    ("Compiler/SolidityImport/EmitVerity.lean", lit): (
        "EmitVerity (CompilationModel -> verity_contract printer) matches CompilationModel "
        "`.externalCall` names of linked external functions, which a model author names; the "
        "importer never lowers Solidity source to these names")
    for lit in ("SafeERC20.safeTransfer", "SafeERC20.safeTransferFrom", "ERC20.balanceOf")
}

# Yul variable names of the registered range-read block (`extsloadRangeYulFingerprint`), read
# only after `rangeReadBindings?` matched the block through the registry.
REGISTRY_GATED = {"startSlot": "rangeReadBindings?", "nSlots": "rangeReadBindings?"}
REGISTRY_GATE = re.compile(
    r"let\s+(\w+)\s*←\s*matchTrustedShortcut\?\s+\w+\s*\n\s*guard\s*\(\s*\1\.shortcut\.lowering\s*==\s*\.rangeStorageRead\s*\)"
)

IDENT = re.compile(r"(?<![0-9A-Za-z_$])[A-Za-z_$][A-Za-z0-9_$]*")
NUMBER = re.compile(r"\b0x[0-9a-fA-F]*\b|\b\d\w*")


def is_test_file(path: Path) -> bool:
    return path.name.endswith("Test.lean") or path.name.endswith("Tests.lean")


def importer_files(root: Path) -> list[Path]:
    base = root / IMPORTER_DIR
    return sorted(p for p in base.rglob("*.lean") if p.is_file() and not is_test_file(p))


INTERESTING = re.compile(r"/-|--|[\"'{}]")


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
            if text[i] == "\\":
                body.append(" ")
                i += 2
            elif interpolated and text[i] == "{":
                i = code(i + 1, closing="}")
                body.append(" ")
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
            elif c == '"':
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


def selection_kind(code: str, start: int, end: int,
                   membership_lists: list[tuple[int, int]]) -> str | None:
    """Why the string literal at `code[start:end]` is in a selection position, if it is."""
    before = code[max(0, start - 80):start]
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
    if re.search(r"\.(?:contains|startsWith|endsWith|find\?|findD|contains\?|elem)\s+\Z", before):
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


def check_names(root: Path, errors: list[str]) -> None:
    for path in importer_files(root):
        rel = path.relative_to(root)
        raw = path.read_text(encoding="utf-8")
        code, literals = scan(raw)
        lists = membership_list_spans(code, literals)
        for m in literals:
            body = m.text
            idents = literal_identifiers(body)
            if not idents:
                continue
            kind = selection_kind(code, m.start, m.end, lists)
            if kind is None or (rel.as_posix(), body) in FILE_EXCEPTIONS:
                continue
            for ident in idents:
                if ident in ALLOWED_IDENTIFIERS or ident.startswith(SOLC_TYPE_PREFIXES) \
                        or SOLC_SIZED_TYPE.match(ident):
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
                    f"`{ident}` is a builtin, add it to scripts/check_importer_name_selection.py.")


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
        for m in re.finditer(r"(?m)^(?:private\s+|partial\s+)*def\s+(lower\w*(?:Shim|Shortcut)\w*)",
                             code_no_strings):
            errors.append(f"{rel}:{line_of(code, m.start())}: {m.group(1)} defined outside the "
                          f"registry module {REGISTRY_FILE}")


def run(root: Path) -> list[str]:
    errors: list[str] = []
    check_names(root, errors)
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

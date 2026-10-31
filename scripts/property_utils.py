#!/usr/bin/env python3
"""Shared utilities for property manifest and coverage checking."""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

# Path constants
ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "test" / "property_manifest.json"
EXCLUSIONS = ROOT / "test" / "property_exclusions.json"
TEST_DIR = ROOT / "test"
PROOFS_DIR = ROOT / "Contracts"
EXAMPLES_DIR = ROOT / "Contracts"
YUL_DIR = ROOT / "compiler" / "yul"

# Regex patterns for extracting property tags from test files
PROPERTY_WITH_NUM_RE = re.compile(
    r"^\s*(?:///|\*)\s*Property\s+\d+[A-Za-z]*\s*:\s*([A-Za-z0-9_']+)(?:\s*\(.*\))?\s*$"
)
PROPERTY_SIMPLE_RE = re.compile(
    r"^\s*(?:///|\*)\s*Property\s*:\s*([A-Za-z0-9_']+)(?:\s*\(.*\))?\s*$"
)
FILE_RE = re.compile(r"^Property(.+)\.t\.sol$")
CONTRACT_NAME_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*$")
THEOREM_NAME_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_.']*$")
LEAN_PRELUDE_RE = re.compile(r"^\s*prelude\b")
LEAN_IMPORT_RE = re.compile(
    r"^\s*(?:public\s+)?(?:meta\s+)?import(?:\s+all)?\b(?P<body>.*)$"
)
_LEAN_LETTER_LIKE_PAT = (
    r"[\u00c0-\u00d6\u00d8-\u00f6\u00f8-\u017f"
    r"\u0391-\u039f\u03a1-\u03a2\u03a4-\u03a9"
    r"\u03b1-\u03ba\u03bc-\u03fb"
    r"\u1f00-\u1ffe\u2100-\u214f\U0001d49c-\U0001d59f]"
)
_LEAN_SUBSCRIPT_PAT = r"[\u1d62-\u1d6a\u2080-\u2089\u2090-\u209c\u2c7c]"
_LEAN_ID_FIRST_PAT = rf"(?:[A-Za-z_]|{_LEAN_LETTER_LIKE_PAT})"
_LEAN_ID_REST_PAT = (
    rf"(?:[A-Za-z0-9_!'?]|{_LEAN_LETTER_LIKE_PAT}|{_LEAN_SUBSCRIPT_PAT})"
)
_LEAN_IDENT_SEG_PAT = rf"(?:«[^»]+»|{_LEAN_ID_FIRST_PAT}{_LEAN_ID_REST_PAT}*)"
LEAN_MODULE_NAME_RE = re.compile(rf"^{_LEAN_IDENT_SEG_PAT}(?:\.{_LEAN_IDENT_SEG_PAT})*$")
_LEAN_HEADER_TOKEN_RE = re.compile(
    rf"{_LEAN_IDENT_SEG_PAT}(?:\.{_LEAN_IDENT_SEG_PAT})*|\S+"
)

# Regex pattern for theorem/lemma declarations with optional Lean prefixes.
THEOREM_RE = re.compile(
    r"^\s*(?P<attrs>(?:@\[[^\]]*\]\s*)*)(?P<visibility>(?:(?:private|protected)\s+)*)"
    r"(?P<kind>theorem|lemma)\s+(?P<name>[A-Za-z_][A-Za-z0-9_.']*)\b"
)


def _require_contract_identifier(contract: str, source: Path) -> str:
    """Validate and return a contract identifier from a filesystem-derived source."""
    if contract != contract.strip() or not CONTRACT_NAME_RE.fullmatch(contract):
        raise SystemExit(
            f"Invalid contract identifier from {source}: {contract!r}"
        )
    return contract


def _require_theorem_identifier(
    theorem: str, source: Path, *, context: str | None = None
) -> str:
    """Validate and return a theorem identifier from a filesystem-derived source."""
    if theorem != theorem.strip() or not THEOREM_NAME_RE.fullmatch(theorem):
        location = f"{source} ({context})" if context else str(source)
        raise SystemExit(
            f"Invalid theorem identifier from {location}: {theorem!r}"
        )
    return theorem


def load_manifest() -> dict[str, set[str]]:
    """Load property manifest from JSON file.

    Returns:
        Dictionary mapping contract names to sets of theorem names.

    Raises:
        SystemExit: If manifest file does not exist.
    """
    return _load_contract_name_sets(MANIFEST, missing_ok=False)


def load_exclusions() -> dict[str, set[str]]:
    """Load property exclusions from JSON file.

    Returns:
        Dictionary mapping contract names to sets of excluded theorem names.
        Returns empty dict if exclusions file does not exist.
    """
    return _load_contract_name_sets(EXCLUSIONS, missing_ok=True)


def _unquote_lean_module_name(token: str) -> str:
    return token.replace("«", "").replace("»", "")


def extract_lean_import_modules(line: str) -> list[str]:
    """Extract imported module names from a Lean `import` line.

    Supports `[public] [meta] import [all]`, guillemet-escaped identifiers,
    multiple modules on one line, and ignores `as Alias` clauses. Returns an
    empty list for non-import lines.
    """
    match = LEAN_IMPORT_RE.match(line)
    if match is None:
        return []

    modules: list[str] = []
    tokens = _LEAN_HEADER_TOKEN_RE.findall(match.group("body"))
    skip_alias = False
    for token in tokens:
        if skip_alias:
            skip_alias = False
            continue
        if token == "as":
            skip_alias = True
            continue
        if LEAN_MODULE_NAME_RE.fullmatch(token):
            modules.append(_unquote_lean_module_name(token))
    return modules


def extract_lean_header_imports_with_lines(text: str) -> list[tuple[str, int]]:
    """Extract ``(module_name, import_line_1based)`` from a Lean file's module header.

    Follows Lean 4's module-header token grammar (`Lean/Parser/Module/Syntax.lean`):
      ``optional "module" >> optional "prelude" >> many ([public] [meta] "import" [all] ident)``
    across arbitrary whitespace and newlines after scrubbing comments and string literals,
    unquoting guillemet-escaped identifiers (`«...»`), and failing closed via ``ValueError``
    on incomplete or malformed ``import`` clauses in the header.
    """
    scrubbed = scrub_lean_code(text)
    tokens: list[tuple[str, int]] = []
    for line_no, line in enumerate(scrubbed.splitlines(), 1):
        for match in _LEAN_HEADER_TOKEN_RE.finditer(line):
            tokens.append((match.group(0), line_no))

    i = 0
    n = len(tokens)
    if i < n and tokens[i][0] == "module":
        i += 1
    if i < n and tokens[i][0] == "prelude":
        i += 1

    imports: list[tuple[str, int]] = []
    while i < n:
        start = i
        if i < n and tokens[i][0] == "public":
            i += 1
        if i < n and tokens[i][0] == "meta":
            i += 1
        if i >= n or tokens[i][0] != "import":
            # `public section`, `public def`, `meta def`, or ordinary command: header ended.
            i = start
            break
        imp_line = tokens[i][1]
        i += 1
        if i < n and tokens[i][0] == "all":
            i += 1
        if i >= n:
            raise ValueError(f"incomplete Lean import statement at line {imp_line}")
        mod_tok = tokens[i][0]
        if mod_tok in {"import", "public", "meta", "all", "prelude", "module"} or not LEAN_MODULE_NAME_RE.fullmatch(mod_tok):
            raise ValueError(
                f"invalid Lean import target {mod_tok!r} at line {tokens[i][1]}"
            )
        imports.append((_unquote_lean_module_name(mod_tok), imp_line))
        i += 1
        # Also tolerate legacy multi-target `import A B` / `import A as Alias` in synthetic fixtures
        # when kept on the same `import` line.
        while i < n and tokens[i][1] == imp_line:
            extra_tok = tokens[i][0]
            if extra_tok == "as":
                i += 2
                continue
            if extra_tok in {"import", "public", "meta"}:
                break
            if LEAN_MODULE_NAME_RE.fullmatch(extra_tok):
                imports.append((_unquote_lean_module_name(extra_tok), imp_line))
                i += 1
                continue
            break

    # Fail closed if any standalone `import` keyword appears later in the scrubbed body
    # (outside strings/comments, Lean does not allow `import` after commands).
    while i < n:
        if tokens[i][0] == "import":
            raise ValueError(
                f"unexpected `import` keyword outside module header at line {tokens[i][1]}"
            )
        i += 1

    return imports


def extract_lean_header_imports(text: str) -> list[str]:
    """Extract imported module names from a Lean file's module header only."""
    return [mod for mod, _ in extract_lean_header_imports_with_lines(text)]


def _load_contract_name_sets(path: Path, *, missing_ok: bool) -> dict[str, set[str]]:
    """Load and validate a `{contract: [name, ...]}` JSON object."""
    if not path.exists():
        if missing_ok:
            return {}
        raise SystemExit(f"Missing property manifest: {path}")

    try:
        raw: object = json.loads(
            path.read_text(encoding="utf-8"),
            object_pairs_hook=_reject_duplicate_object_keys,
        )
    except (json.JSONDecodeError, ValueError) as exc:
        raise SystemExit(f"Invalid JSON in {path}: {exc}") from exc

    if not isinstance(raw, dict):
        raise SystemExit(
            f"Invalid schema in {path}: expected top-level object "
            "mapping contract names to string arrays."
        )

    validated: dict[str, set[str]] = {}
    for contract, names in raw.items():
        if not isinstance(contract, str) or not contract:
            raise SystemExit(
                f"Invalid schema in {path}: contract key {contract!r} must be a non-empty string."
            )
        if contract != contract.strip() or not CONTRACT_NAME_RE.fullmatch(contract):
            raise SystemExit(
                f"Invalid schema in {path}: contract key {contract!r} must match {CONTRACT_NAME_RE.pattern!r}."
            )
        if not isinstance(names, list):
            raise SystemExit(
                f"Invalid schema in {path}: value for {contract!r} must be an array of strings."
            )
        for name in names:
            if not isinstance(name, str) or not name:
                raise SystemExit(
                    f"Invalid schema in {path}: entry {name!r} in {contract!r} must be a non-empty string."
                )
            _require_theorem_identifier(name, path, context=f"contract {contract!r}")
        duplicate_names = _find_duplicates(names)
        if duplicate_names:
            raise SystemExit(
                f"Invalid schema in {path}: value for {contract!r} contains duplicate name(s): {', '.join(duplicate_names)}."
            )
        validated[contract] = set(names)

    return validated


def _reject_duplicate_object_keys(pairs: list[tuple[str, object]]) -> dict[str, object]:
    """Reject JSON objects with duplicate keys."""
    seen: set[str] = set()
    duplicates: list[str] = []
    out: dict[str, object] = {}
    for key, value in pairs:
        if key in seen:
            duplicates.append(repr(key))
        else:
            seen.add(key)
        out[key] = value
    if duplicates:
        raise ValueError(f"duplicate object key(s): {', '.join(sorted(set(duplicates)))}")
    return out


def _find_duplicates(items: list[str]) -> list[str]:
    """Return sorted duplicate values in insertion-insensitive order."""
    seen: set[str] = set()
    duplicates: set[str] = set()
    for item in items:
        if item in seen:
            duplicates.add(item)
        else:
            seen.add(item)
    return sorted(duplicates)


def extract_property_names(path: Path) -> list[str]:
    """Extract property theorem names from a Solidity test file.

    Parses comments like:
    - /// Property 1: theorem_name
    - /// Property: theorem_name

    Args:
        path: Path to Solidity test file.

    Returns:
        List of theorem names found in property tags.
    """
    text = path.read_text(encoding="utf-8")
    names: list[str] = []
    for line in text.splitlines():
        match = PROPERTY_WITH_NUM_RE.search(line)
        if match:
            names.append(_require_theorem_identifier(match.group(1), path))
            continue
        match = PROPERTY_SIMPLE_RE.search(line)
        if match:
            names.append(_require_theorem_identifier(match.group(1), path))
    return names


def collect_covered() -> dict[str, set[str]]:
    """Collect all property tests from test directory.

    Scans Property*.t.sol files and extracts property tags.

    Returns:
        Dictionary mapping contract names to sets of covered theorem names.
    """
    covered: dict[str, set[str]] = {}
    for path in sorted(TEST_DIR.glob("Property*.t.sol")):
        match = FILE_RE.match(path.name)
        if not match:
            continue
        contract = _require_contract_identifier(match.group(1), path)
        covered.setdefault(contract, set()).update(extract_property_names(path))
    return covered


def _is_helper_declaration(attrs: str, visibility: str) -> bool:
    """Return True for declarations intentionally excluded from manifest coverage.

    The property manifest tracks externally-audited contract properties, not local
    helper lemmas. We treat `private`/`protected` declarations and declarations
    tagged with `simp` as helper-only by default.
    """
    if visibility.strip():
        return True
    # Keep this simple and conservative: if any attribute block mentions simp,
    # treat the theorem as a helper declaration for manifest purposes.
    return bool(re.search(r"@\[[^\]]*\bsimp\b[^\]]*\]", attrs))


def collect_theorems(path: Path, *, include_helpers: bool = False) -> list[str]:
    """Extract theorem/lemma names from a Lean proof file.

    Args:
        path: Path to Lean file.

    Returns:
        List of theorem/lemma names found in the file.
        By default helper declarations (`private`/`protected` and `@[simp]`)
        are excluded to preserve property-manifest semantics.
    """
    names: list[str] = []
    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError) as exc:
        raise SystemExit(f"Cannot read Lean proof file {path}: {exc}") from exc
    stripped = strip_lean_comments(text)
    for line in stripped.splitlines():
        match = THEOREM_RE.match(line)
        if match:
            attrs = match.group("attrs")
            visibility = match.group("visibility")
            if not include_helpers and _is_helper_declaration(attrs, visibility):
                continue
            names.append(_require_theorem_identifier(match.group("name"), path))
    return names


def extract_manifest_from_proofs() -> dict[str, list[str]]:
    """Extract theorem names from Lean proof files.

    Scans Contracts/<Contract>/Proofs/ directories and Contracts/<Contract>/<Contract>.lean
    files that contain inline theorems (e.g., ReentrancyExample).

    Returns:
        Dictionary mapping contract names to sorted, deduplicated lists of theorem names.
    """
    if not PROOFS_DIR.exists():
        raise SystemExit(f"Missing contracts dir: {PROOFS_DIR}")
    manifest: dict[str, list[str]] = {}
    for contract_dir in sorted(PROOFS_DIR.iterdir()):
        if not contract_dir.is_dir():
            continue
        contract = _require_contract_identifier(contract_dir.name, contract_dir)
        proofs_subdir = contract_dir / "Proofs"
        theorems: list[str] = []
        if proofs_subdir.is_dir():
            for lean in sorted(proofs_subdir.rglob("*.lean")):
                theorems.extend(collect_theorems(lean))
        for lean in sorted(contract_dir.rglob("Proofs.lean")):
            if proofs_subdir.is_dir() and proofs_subdir in lean.parents:
                continue
            theorems.extend(collect_theorems(lean))
        if theorems:
            manifest[contract] = sorted(dict.fromkeys(theorems))

    # Also scan Contracts/<Contract>/<Contract>.lean for contracts with inline theorems (no separate Proofs dir)
    if EXAMPLES_DIR.exists():
        for contract_dir in sorted(EXAMPLES_DIR.iterdir()):
            if not contract_dir.is_dir():
                continue
            contract = _require_contract_identifier(contract_dir.name, contract_dir)
            if contract in manifest:
                continue  # Already found via Proofs/
            contract_lean = contract_dir / f"{contract}.lean"
            if not contract_lean.exists():
                contract_lean = contract_dir / "Contract.lean"
            if contract_lean.exists():
                theorems = collect_theorems(contract_lean)
                if theorems:
                    manifest[contract] = sorted(dict.fromkeys(theorems))

    return manifest


def die(msg: str) -> None:
    """Print error message and exit with status 1.

    Args:
        msg: Error message to print.
    """
    print(f"error: {msg}", file=sys.stderr)
    raise SystemExit(1)


def _is_lean_ascii_alpha(ch: str) -> bool:
    """Match Lean ``Char.isAlpha`` (``Init/Data/Char/Basic.lean`` — ASCII only)."""
    return ("a" <= ch <= "z") or ("A" <= ch <= "Z")


def _is_lean_ascii_digit(ch: str) -> bool:
    """Match Lean ``Char.isDigit`` (``Init/Data/Char/Basic.lean`` — ASCII only)."""
    return "0" <= ch <= "9"


def _is_lean_ascii_alnum(ch: str) -> bool:
    """Match Lean ``Char.isAlphanum`` (``Init/Data/Char/Basic.lean`` — ASCII only)."""
    return _is_lean_ascii_alpha(ch) or _is_lean_ascii_digit(ch)


def _is_lean_id_first(ch: str) -> bool:
    """Match Lean ``isIdFirst`` (``Init/Meta/Defs.lean``).

    Lean's ``Char.isAlpha`` is ASCII-only; non-ASCII identifier letters are
    defined strictly by ``isLetterLike`` (which excludes ``λ`` U+03BB, ``Π``
    U+03A0, ``Σ`` U+03A3, ``×`` U+00D7, and ``÷`` U+00F7).
    """
    if _is_lean_ascii_alpha(ch) or ch == "_":
        return True
    cp = ord(ch)
    if 0x3B1 <= cp <= 0x3C9 and cp != 0x3BB:
        return True
    if 0x391 <= cp <= 0x3A9 and cp not in (0x3A0, 0x3A3):
        return True
    if 0x3CA <= cp <= 0x3FB or 0x1F00 <= cp <= 0x1FFE:
        return True
    if 0x2100 <= cp <= 0x214F or 0x1D49C <= cp <= 0x1D59F:
        return True
    if 0x00C0 <= cp <= 0x00FF and cp not in (0x00D7, 0x00F7):
        return True
    return 0x0100 <= cp <= 0x017F


def _is_lean_id_rest(ch: str) -> bool:
    """Match Lean ``isIdRest`` (``Init/Meta/Defs.lean``)."""
    if _is_lean_ascii_alnum(ch) or ch in "_!'?":
        return True
    cp = ord(ch)
    if 0x2080 <= cp <= 0x2089 or 0x2090 <= cp <= 0x209C or 0x1D62 <= cp <= 0x1D6A or cp == 0x2C7C:
        return True
    return _is_lean_id_first(ch) and ch != "_"


def _is_lean_id_begin_escape(ch: str) -> bool:
    return ch == "«"


def _is_lean_whitespace(ch: str) -> bool:
    """Match Lean ``Char.isWhitespace`` (``Init/Data/Char/Basic.lean``)."""
    return ch in " \t\r\n"


def _skip_lean_whitespace(text: str, i: int) -> int:
    n = len(text)
    while i < n and _is_lean_whitespace(text[i]):
        i += 1
    return i


def _consume_lean_char_literal(text: str, i: int) -> int | None:
    """Consume a Lean character literal starting at ``'``.

    Mirrors ``Lean.Parser.tokenFn`` / ``charLitFnAux`` / ``quotedCharFn``
    (``Lean/Parser/Basic.lean``): ``'x'``, ``'\\''``, ``'\\n'``, ``'\\xNN'``,
    ``'\\uNNNN'``. Returns the index after the closing quote, or ``None`` when
    the span is not a character literal (so ``'`` stays an ordinary character,
    as in ``a'`` or ``'ident``).
    """
    n = len(text)
    if i >= n or text[i] != "'" or i + 1 >= n or text[i + 1] == "'":
        return None
    j = i + 1
    if text[j] == "\\":
        j += 1
        if j >= n:
            return None
        esc = text[j]
        if esc in "\\\"'rnt":
            j += 1
        elif esc == "x":
            if j + 2 >= n or not all(c in "0123456789abcdefABCDEF" for c in text[j + 1 : j + 3]):
                return None
            j += 3
        elif esc == "u":
            if j + 4 >= n or not all(c in "0123456789abcdefABCDEF" for c in text[j + 1 : j + 5]):
                return None
            j += 5
        else:
            return None
    else:
        j += 1
    if j >= n or text[j] != "'":
        return None
    return j + 1


def _consume_lean_string_escape(text: str, j: int, *, allow_interp_brace: bool) -> int | None:
    """Consume a Lean string escape sequence starting immediately after ``\\``."""
    n = len(text)
    if j >= n:
        return None
    esc = text[j]
    if esc in "\\\"'rnt" or (allow_interp_brace and esc == "{"):
        return j + 1
    if esc == "x":
        if j + 2 >= n or not all(c in "0123456789abcdefABCDEF" for c in text[j + 1 : j + 3]):
            return None
        return j + 3
    if esc == "u":
        if j + 4 >= n or not all(c in "0123456789abcdefABCDEF" for c in text[j + 1 : j + 5]):
            return None
        return j + 5
    if esc == "\n":
        j += 1
        while j < n and text[j] != "\n" and _is_lean_whitespace(text[j]):
            j += 1
        return j
    return None


def _consume_lean_string_literal(text: str, i: int) -> int | None:
    """Consume a Lean string literal starting at ``"``.

    Mirrors ``strLitFnAux`` / ``quotedStringFn``, including string gaps
    (backslash, newline, whitespace). Returns the index after the closing
    quote, or ``None`` if the literal is unterminated.
    """
    n = len(text)
    if i >= n or text[i] != '"':
        return None
    j = i + 1
    while j < n:
        ch = text[j]
        if ch == '"':
            return j + 1
        if ch == "\\":
            after_esc = _consume_lean_string_escape(text, j + 1, allow_interp_brace=False)
            if after_esc is None:
                return None
            j = after_esc
            continue
        j += 1
    return None


_LEAN_INTERP_PREFIX_IDS: frozenset[str] = frozenset({"s!", "m!", "f!"})
_LEAN_INTERP_DIRECT_KEYWORDS: frozenset[str] = frozenset(
    {
        "throwError",
        "logError",
        "logWarning",
        "logInfo",
        "println!",
        "dbg_trace",
        "reportIssue!",
        "reportDbgIssue!",
        "reportEMatchIssue!",
    }
)
_LEAN_INTERP_ONE_ARG_KEYWORDS: frozenset[str] = frozenset(
    {
        "throwErrorAt",
        "logErrorAt",
        "logWarningAt",
        "logInfoAt",
        "throwNamedError",
        "logNamedError",
        "logNamedWarning",
    }
)
_LEAN_INTERP_TWO_ARG_KEYWORDS: frozenset[str] = frozenset(
    {
        "throwNamedErrorAt",
        "logNamedErrorAt",
        "logNamedWarningAt",
    }
)
_LEAN_INTERP_BRACKET_KEYWORDS: frozenset[str] = frozenset(
    {"trace", "trace_goal", "Macro.trace"}
)
_LEAN_CUSTOM_OPERATOR_DECL_KEYWORDS: frozenset[str] = frozenset(
    {"infix", "infixl", "infixr", "prefix", "postfix", "notation", "macro", "syntax", "elab"}
)
_LEAN_PARSER_COMBINATOR_DECL_KEYWORDS: frozenset[str] = frozenset(
    {
        "leading_parser",
        "trailing_parser",
        "symbol",
        "unicodeSymbol",
        "nonReservedSymbol",
        "ParserDescr.symbol",
        "ParserDescr.unicodeSymbol",
        "ParserDescr.nonReservedSymbol",
        "Lean.ParserDescr.symbol",
        "Lean.ParserDescr.unicodeSymbol",
        "Lean.ParserDescr.nonReservedSymbol",
        "Lean.Parser.symbol",
        "Lean.Parser.unicodeSymbol",
        "Lean.Parser.nonReservedSymbol",
        "Lean.Parser.leadingNode",
        "Lean.Parser.trailingNode",
    }
)
# Core Lean builtin non-identifier tokens whose body can absorb a delimiter-starting
# character (`'`, `"`, `-`, `/`, `r`, `` ` ``, `«`) via `Lean.Parser.tokenFnAux`'s
# `c.tokens.matchPrefix` longest-match rule. File-local custom atoms are registered
# dynamically from `syntax`/`notation`/`infix`/`macro`/`elab`/`leading_parser` literals.
_LEAN_BUILTIN_PRIME_SYMBOL_TOKENS: frozenset[str] = frozenset(
    {
        "]'",
        "×'",
        "Σ'",
        "⊕'",
        "#[" ,
        "#v[",
        "%[",
        ".(",
        ".{",
        "@[" ,
        "`(arg_val|",
        "`(binderPred|",
        "`(block|",
        "`(conv|",
        "`(desc_item|",
        "`(doc_arg|",
        "`(grind_filter|",
        "`(grind_ref|",
        "`(grind|",
        "`(inline|",
        "`(json|",
        "`(link_target|",
        "`(list_item|",
        "`(mcasesPat|",
        "`(mintroPat|",
        "`(mrefinePat|",
        "`(mrevertPat|",
        "`(rawStx|",
        "`(rcasesPat|",
        "`(rintroPat|",
        "`(sym_discharger|",
        "`(sym_dsimp_field|",
        "`(sym_dsimproc|",
        "`(sym_simp_field|",
        "`(sym_simproc|",
        "`(tactic|",
        "`(",
    }
)
_LEAN_MULTI_CHAR_GROUP_OPENERS: dict[str, str] = {
    "#[": "]",
    "#v[": "]",
    "%[": "]",
    ".(": ")",
    ".{": "}",
    "@[": "]",
}
_LEAN_UNICODE_GROUP_PAIRS: dict[str, str] = {
    "⟨": "⟩",
    "‹": "›",
}
_LEAN_UNICODE_GROUP_CLOSERS: frozenset[str] = frozenset(_LEAN_UNICODE_GROUP_PAIRS.values())
_LEAN_TERM_MAX_PREFIX_CHARS: frozenset[str] = frozenset({"@", "↑", "⇑", "?", "!"})


def _build_symbols_by_first_char(symbols: frozenset[str] | set[str]) -> dict[str, tuple[str, ...]]:
    grouped: dict[str, list[str]] = {}
    for sym in symbols:
        if sym:
            grouped.setdefault(sym[0], []).append(sym)
    return {ch: tuple(sorted(vals, key=len, reverse=True)) for ch, vals in grouped.items()}


_LEAN_BUILTIN_SYMBOLS_BY_FIRST: dict[str, tuple[str, ...]] = _build_symbols_by_first_char(
    _LEAN_BUILTIN_PRIME_SYMBOL_TOKENS
)


def _register_custom_symbol(custom_symbols_by_first: dict[str, list[str]], sym: str) -> None:
    if not sym:
        return
    bucket = custom_symbols_by_first.setdefault(sym[0], [])
    if sym not in bucket:
        bucket.append(sym)
        bucket.sort(key=len, reverse=True)


def _match_longest_symbol_prefix_fast(
    text: str,
    i: int,
    custom_symbols_by_first: dict[str, list[str]],
    *,
    include_builtins: bool = True,
) -> str | None:
    if i >= len(text):
        return None
    ch = text[i]
    best: str | None = None
    best_len = 0
    custom_bucket = custom_symbols_by_first.get(ch)
    if custom_bucket:
        for sym in custom_bucket:
            slen = len(sym)
            if slen <= best_len:
                break
            if text.startswith(sym, i):
                best = sym
                best_len = slen
                break
    if include_builtins:
        builtin_bucket = _LEAN_BUILTIN_SYMBOLS_BY_FIRST.get(ch)
        if builtin_bucket:
            for sym in builtin_bucket:
                slen = len(sym)
                if slen <= best_len:
                    break
                if text.startswith(sym, i):
                    best = sym
                    best_len = slen
                    break
    return best


def _symbol_needs_token_table_tracking(sym: str) -> bool:
    """Return True when `sym` could alter downstream comment/literal tokenization."""
    if len(sym) <= 1:
        return False
    return any(
        ch in sym
        for ch in ("'", '"', "-", "/", "`", "«", "r", "(", ")", "[", "]", "{", "}", "⟨", "⟩", "‹", "›")
    )


def _decode_lean_raw_string_literal_value(raw: str) -> str:
    """Decode a Lean raw string literal ``r#*"..."#*``."""
    if len(raw) < 3 or raw[0] != "r":
        return ""
    j = 1
    hashes = 0
    while j < len(raw) and raw[j] == "#":
        hashes += 1
        j += 1
    if j >= len(raw) or raw[j] != '"':
        return ""
    suffix_len = 1 + hashes
    if len(raw) < j + 1 + suffix_len:
        return ""
    return raw[j + 1 : len(raw) - suffix_len]


def _decode_lean_string_literal_value(raw: str) -> str:
    """Best-effort decode of a Lean double-quoted literal token ``"..."``."""
    if len(raw) < 2 or raw[0] != '"' or raw[-1] != '"':
        return ""
    chars: list[str] = []
    i = 1
    end = len(raw) - 1
    while i < end:
        ch = raw[i]
        if ch != "\\":
            chars.append(ch)
            i += 1
            continue
        i += 1
        if i >= end:
            break
        esc = raw[i]
        if esc in '\\"\'':
            chars.append(esc)
            i += 1
        elif esc == "n":
            chars.append("\n")
            i += 1
        elif esc == "r":
            chars.append("\r")
            i += 1
        elif esc == "t":
            chars.append("\t")
            i += 1
        elif esc == "x" and i + 2 < end:
            chars.append(chr(int(raw[i + 1 : i + 3], 16)))
            i += 3
        elif esc == "u" and i + 4 < end:
            chars.append(chr(int(raw[i + 1 : i + 5], 16)))
            i += 5
        elif esc == "\n":
            i += 1
            while i < end and raw[i] != "\n" and _is_lean_whitespace(raw[i]):
                i += 1
        else:
            chars.append(esc)
            i += 1
    return "".join(chars)


def _advance_interp_state(interp_state: str | None) -> str | None:
    if interp_state is None:
        return None
    if interp_state == "varargs":
        return "varargs"
    if interp_state.startswith("skip_"):
        rem = int(interp_state.split("_", 1)[1]) - 1
        return "ready" if rem <= 0 else f"skip_{rem}"
    return None


def _is_skip_interp_state(interp_state: str | None) -> bool:
    return interp_state is not None and (interp_state == "varargs" or interp_state.startswith("skip_"))


_LEAN_SYNTAX_IGNORED_COMBINATORS: frozenset[str] = frozenset(
    {"ppSpace", "ppLine", "ppDedent", "ppGroup", "ppIndent", "noWs", "lineEq", "colGe", "colGt", "colEq", "withPosition"}
)


def _custom_interp_spec_to_state(spec: int | str) -> str:
    if isinstance(spec, str):
        return spec
    return "ready" if spec <= 0 else f"skip_{spec}"


def _consume_lean_arg_postfix_chain(
    text: str,
    i: int,
    *,
    blank_literals: bool,
    out: list[str],
    custom_doc_like_tokens: set[str],
    custom_interp_tokens: dict[str, int | str],
    custom_symbols_by_first: dict[str, list[str]],
    custom_syntax_abbrevs: dict[str, tuple[list[str], int, bool, str | None]],
) -> int:
    """Consume contiguous maxPrec postfix projections/indexing after an argument atom."""
    n = len(text)
    while i < n:
        if text.startswith(".{", i):
            out.append(".{")
            i = _scan_lean_tokens_until(
                text,
                i + 2,
                blank_literals=blank_literals,
                stop_on_interp_close=False,
                stop_on_close_bracket="}",
                out=out,
                custom_doc_like_tokens=custom_doc_like_tokens,
                custom_interp_tokens=custom_interp_tokens,
                custom_symbols_by_first=custom_symbols_by_first,
                custom_syntax_abbrevs=custom_syntax_abbrevs,
            )
            if i < n and text[i] == "}":
                out.append("}")
                i += 1
                continue
            return i
        if text[i] == "#" and i > 0 and _is_lean_ascii_digit(text[i - 1]) and i + 1 < n:
            if _is_lean_ascii_digit(text[i + 1]):
                j = i + 2
                while j < n and _is_lean_ascii_digit(text[j]):
                    j += 1
                out.append(text[i:j])
                i = j
                continue
            if text[i + 1] == "(":
                out.append("#(")
                i = _scan_lean_tokens_until(
                    text,
                    i + 2,
                    blank_literals=blank_literals,
                    stop_on_interp_close=False,
                    stop_on_close_bracket=")",
                    out=out,
                    custom_doc_like_tokens=custom_doc_like_tokens,
                    custom_interp_tokens=custom_interp_tokens,
                    custom_symbols_by_first=custom_symbols_by_first,
                    custom_syntax_abbrevs=custom_syntax_abbrevs,
                )
                if i < n and text[i] == ")":
                    out.append(")")
                    i += 1
                    continue
                return i
            ident_end = _consume_lean_ident_or_name_lit(text, i + 1)
            if ident_end is not None and ident_end > i + 1 and text[i + 1] != "`":
                out.append(text[i:ident_end])
                i = ident_end
                continue
        if text[i] == "." and i + 1 < n and text[i + 1] != ".":
            if _is_lean_ascii_digit(text[i + 1]):
                j = i + 2
                while j < n and _is_lean_ascii_digit(text[j]):
                    j += 1
                out.append(text[i:j])
                i = j
                continue
            ident_end = _consume_lean_ident_or_name_lit(text, i + 1)
            if ident_end is not None and ident_end > i + 1 and text[i + 1] != "`":
                out.append(text[i:ident_end])
                i = ident_end
                continue
        if text[i] == "[":
            out.append("[")
            i = _scan_lean_tokens_until(
                text,
                i + 1,
                blank_literals=blank_literals,
                stop_on_interp_close=False,
                stop_on_close_bracket="]",
                out=out,
                custom_doc_like_tokens=custom_doc_like_tokens,
                custom_interp_tokens=custom_interp_tokens,
                custom_symbols_by_first=custom_symbols_by_first,
                custom_syntax_abbrevs=custom_syntax_abbrevs,
            )
            if i < n and text[i] == "]":
                if text.startswith("]'", i):
                    out.append("]'")
                    i += 2
                    break
                out.append("]")
                i += 1
                while i < n and text[i] in "!?":
                    out.append(text[i])
                    i += 1
                continue
            return i
        break
    return i


def _scan_lean_interpolated_string(
    text: str,
    i: int,
    *,
    blank_literals: bool,
    out: list[str],
    custom_doc_like_tokens: set[str],
    custom_interp_tokens: dict[str, int | str],
    custom_symbols_by_first: dict[str, list[str]],
    custom_syntax_abbrevs: dict[str, tuple[list[str], int, bool, str | None]],
) -> int:
    """Scan a Lean ``interpolatedStr`` starting at ``"`` and append scrubbed output."""
    n = len(text)
    out.append('"')
    j = i + 1
    while j < n:
        ch = text[j]
        if ch == '"':
            out.append('"')
            return j + 1
        if ch == "\\":
            after_esc = _consume_lean_string_escape(text, j + 1, allow_interp_brace=True)
            if after_esc is None:
                if blank_literals:
                    out.append(_blank_span(text, j, n))
                else:
                    out.append(text[j:n])
                return n
            if blank_literals:
                out.append(_blank_span(text, j, after_esc))
            else:
                out.append(text[j:after_esc])
            j = after_esc
            continue
        if ch == "{":
            out.append(" " if blank_literals else "{")
            j = _scan_lean_tokens_until(
                text,
                j + 1,
                blank_literals=blank_literals,
                stop_on_interp_close=True,
                stop_on_close_bracket=None,
                out=out,
                custom_doc_like_tokens=custom_doc_like_tokens,
                custom_interp_tokens=custom_interp_tokens,
                custom_symbols_by_first=custom_symbols_by_first,
                custom_syntax_abbrevs=custom_syntax_abbrevs,
            )
            if j < n and text[j] == "}":
                out.append(" " if blank_literals else "}")
                j += 1
                continue
            return j
        if blank_literals:
            out.append("\n" if ch == "\n" else " ")
        else:
            out.append(ch)
        j += 1
    return n


def _consume_lean_raw_string_literal(text: str, i: int) -> int | None:
    """Consume a Lean raw string ``r#*"..."#*`` starting at ``r``."""
    n = len(text)
    if i >= n or text[i] != "r":
        return None
    j = i + 1
    hashes = 0
    while j < n and text[j] == "#":
        hashes += 1
        j += 1
    if j >= n or text[j] != '"':
        return None
    j += 1
    closer = '"' + ("#" * hashes)
    end = text.find(closer, j)
    if end < 0:
        return None
    return end + len(closer)


def _blank_span(text: str, start: int, end: int) -> str:
    """Replace ``text[start:end]`` with spaces, keeping newlines."""
    return "".join("\n" if ch == "\n" else " " for ch in text[start:end])


def report_errors(errors: list[str], message: str) -> None:
    """Print error list to stderr and exit with code 1."""
    if errors:
        print(f"{message}:", file=sys.stderr)
        for item in errors:
            print(f"  - {item}", file=sys.stderr)
        raise SystemExit(1)


def _consume_lean_ident_or_name_lit(text: str, i: int) -> int | None:
    """Consume a Lean identifier or backtick/double-backtick name literal starting at ``i``."""
    n = len(text)
    if i >= n:
        return None
    j = i
    if text[j] == "`":
        if j + 1 < n and text[j + 1] == "`":
            if j + 2 >= n or not (_is_lean_id_first(text[j + 2]) or _is_lean_id_begin_escape(text[j + 2])):
                return None
            j += 2
        else:
            if j + 1 >= n or not (_is_lean_id_first(text[j + 1]) or _is_lean_id_begin_escape(text[j + 1])):
                return None
            j += 1
    elif not (_is_lean_id_first(text[j]) or _is_lean_id_begin_escape(text[j])):
        return None

    while j < n:
        if _is_lean_id_begin_escape(text[j]):
            end = text.find("»", j + 1)
            if end < 0:
                return n
            j = end + 1
        elif _is_lean_id_first(text[j]):
            j += 1
            while j < n and _is_lean_id_rest(text[j]):
                j += 1
        else:
            break
        if j + 1 < n and text[j] == "." and (
            _is_lean_id_first(text[j + 1]) or _is_lean_id_begin_escape(text[j + 1])
        ):
            j += 1
            continue
        break
    return j


def _unquote_lean_guillemets(tok: str) -> str:
    return tok.replace("«", "").replace("»", "")


def _is_quotation_group_opener(sym: str) -> bool:
    return sym == "`(" or (sym.startswith("`(") and sym.endswith("|"))


def _group_closer_for_symbol(sym: str) -> str | None:
    if sym in _LEAN_MULTI_CHAR_GROUP_OPENERS:
        return _LEAN_MULTI_CHAR_GROUP_OPENERS[sym]
    if _is_quotation_group_opener(sym):
        return ")"
    return None


def _is_sep_interp_state(interp_state: str | None) -> bool:
    return interp_state is not None and interp_state.startswith("sep:")


def _parse_sep_interp_state(interp_state: str) -> tuple[str, int]:
    rest = interp_state[4:]
    sep, count_str = rest.rsplit(":", 1)
    return sep, int(count_str)


def _scan_lean_tokens_until(
    text: str,
    i: int,
    *,
    blank_literals: bool,
    stop_on_interp_close: bool,
    stop_on_close_bracket: str | None,
    out: list[str],
    custom_doc_like_tokens: set[str],
    custom_interp_tokens: dict[str, int | str],
    custom_symbols_by_first: dict[str, list[str]],
    custom_syntax_abbrevs: dict[str, tuple[list[str], int, bool, str | None]],
) -> int:
    """Scan Lean tokens from ``i``, appending scrubbed text to ``out``."""
    n = len(text)
    brace_depth = 0
    bracket_depth = 0
    # Pending interpolated-string state across whitespace/comments/args:
    # - "ready": next `"` is an `interpolatedStr`
    # - "skip_N": skip N maxPrec argument tokens/groups, then become "ready"
    # - "bracket": expect `[...]` trace tag, then become "ready"
    # - "varargs": zero or more atoms/groups until `"`, keeping `,` / `;` alive
    # - "sep:<tok>:<k>": scan until unnested separator `<tok>` (after `<k>` `fun` arrows)
    interp_state: str | None = None
    group_stack: list[tuple[str, str | None]] = []

    in_syntax_decl = False
    in_parser_expr = False
    syntax_leads: list[str] = []
    syntax_slots = 0
    syntax_varargs = False
    syntax_awaiting_prec = False
    syntax_pending_sep: str | None = None
    syntax_saw_nonmax_arg = False
    syntax_saw_leading_item = False
    syntax_in_bracket_item = False
    syntax_bracket_groups = 0
    syntax_alt_pending = False
    syntax_unicode_depth: int | None = None
    syntax_nonlead_paren_depth: int | None = None
    syntax_abbrev_name: str | None = None
    syntax_abbrev_rhs = False
    syntax_saw_interp = False

    def register_custom_interp_token(tok: str, spec: int | str) -> None:
        if not tok:
            return
        custom_interp_tokens[tok] = spec
        if not (_is_lean_id_first(tok[0]) or _is_lean_id_begin_escape(tok[0])) or any(
            not (_is_lean_id_rest(ch) or ch == ".") for ch in tok[1:]
        ):
            _register_custom_symbol(custom_symbols_by_first, tok)

    def advance_arg_slot() -> None:
        nonlocal interp_state
        if _is_sep_interp_state(interp_state):
            return
        interp_state = _advance_interp_state(interp_state)

    def reset_syntax_decl() -> None:
        nonlocal in_syntax_decl, in_parser_expr, syntax_slots, syntax_varargs
        nonlocal syntax_awaiting_prec, syntax_pending_sep, syntax_saw_nonmax_arg
        nonlocal syntax_saw_leading_item, syntax_in_bracket_item, syntax_bracket_groups, syntax_alt_pending
        nonlocal syntax_unicode_depth, syntax_nonlead_paren_depth
        nonlocal syntax_abbrev_name, syntax_abbrev_rhs, syntax_saw_interp
        in_syntax_decl = False
        in_parser_expr = False
        syntax_leads.clear()
        syntax_slots = 0
        syntax_varargs = False
        syntax_awaiting_prec = False
        syntax_pending_sep = None
        syntax_saw_nonmax_arg = False
        syntax_saw_leading_item = False
        syntax_in_bracket_item = False
        syntax_bracket_groups = 0
        syntax_alt_pending = False
        syntax_unicode_depth = None
        syntax_nonlead_paren_depth = None
        syntax_abbrev_name = None
        syntax_abbrev_rhs = False
        syntax_saw_interp = False

    def in_syntax_any_paren() -> bool:
        return (in_syntax_decl or in_parser_expr) and all(c == ")" for c, _ in group_stack)

    def record_token_table_literal(decoded: str) -> None:
        if not decoded:
            return
        if (decoded.startswith("/--") or decoded.startswith("/-!")) and len(decoded) > 3:
            custom_doc_like_tokens.add(decoded)
        if _symbol_needs_token_table_tracking(decoded):
            _register_custom_symbol(custom_symbols_by_first, decoded)

    def note_syntax_literal(decoded: str) -> None:
        nonlocal syntax_slots, syntax_varargs, syntax_awaiting_prec, syntax_pending_sep
        nonlocal syntax_saw_nonmax_arg, syntax_saw_leading_item
        nonlocal syntax_in_bracket_item, syntax_bracket_groups, syntax_alt_pending
        if not decoded:
            return
        record_token_table_literal(decoded)
        if syntax_nonlead_paren_depth is not None and len(group_stack) >= syntax_nonlead_paren_depth:
            return
        if syntax_unicode_depth is not None and len(group_stack) >= syntax_unicode_depth:
            if decoded not in syntax_leads:
                syntax_leads.append(decoded)
            syntax_awaiting_prec = False
            return
        if syntax_alt_pending:
            if decoded not in syntax_leads:
                syntax_leads.append(decoded)
            syntax_alt_pending = False
            syntax_awaiting_prec = False
            return
        if syntax_leads:
            if decoded == "[":
                syntax_in_bracket_item = True
                syntax_awaiting_prec = False
                return
            if decoded == "][" and (syntax_in_bracket_item or (len(syntax_leads) == 1 and syntax_leads[0].endswith("["))):
                if not syntax_in_bracket_item:
                    syntax_in_bracket_item = True
                    syntax_bracket_groups = 2
                else:
                    syntax_bracket_groups += 1
                syntax_awaiting_prec = False
                return
            if decoded == "]":
                if syntax_in_bracket_item:
                    syntax_in_bracket_item = False
                    if len(syntax_leads) == 1 and syntax_leads[0].endswith("[") and len(syntax_leads[0]) > 1:
                        pass
                    else:
                        syntax_slots += max(syntax_bracket_groups, 1)
                        syntax_bracket_groups = 0
                    syntax_awaiting_prec = False
                    return
                if len(syntax_leads) == 1 and syntax_leads[0].endswith("[") and len(syntax_leads[0]) > 1:
                    syntax_bracket_groups = max(syntax_bracket_groups, 1)
                    syntax_awaiting_prec = False
                    return
            if syntax_saw_nonmax_arg or syntax_slots > 0 or syntax_varargs:
                syntax_pending_sep = decoded
                syntax_awaiting_prec = False
                return
        syntax_leads.clear()
        syntax_leads.append(decoded)
        syntax_slots = 0
        syntax_varargs = False
        syntax_awaiting_prec = False
        syntax_pending_sep = None
        syntax_saw_nonmax_arg = False
        syntax_saw_leading_item = False
        syntax_in_bracket_item = False
        syntax_bracket_groups = 0

    def register_lead_spec(lead: str, slots: int, varargs: bool, sep: str | None) -> None:
        if not lead:
            return
        if sep is not None:
            register_custom_interp_token(lead, f"sep:{sep}:0")
            return
        if varargs:
            register_custom_interp_token(lead, "varargs")
            return
        prev = custom_interp_tokens.get(lead)
        if prev is None or (isinstance(prev, int) and slots < prev):
            register_custom_interp_token(lead, slots)

    def finish_syntax_interp(extra_slots: int = 0, extra_varargs: bool = False, extra_sep: str | None = None) -> None:
        nonlocal syntax_saw_interp
        syntax_saw_interp = True
        total_slots = syntax_slots + extra_slots
        total_varargs = syntax_varargs or extra_varargs
        eff_sep = extra_sep if extra_sep is not None else syntax_pending_sep
        if syntax_abbrev_name is not None and syntax_abbrev_rhs:
            custom_syntax_abbrevs[syntax_abbrev_name] = (
                list(syntax_leads),
                total_slots,
                total_varargs,
                eff_sep,
            )
        if not syntax_leads:
            return
        if syntax_saw_leading_item:
            for lead in syntax_leads:
                if lead not in {"=>", ":=", "->", "<-", "|", ":", ",", ";"}:
                    register_lead_spec(lead, total_slots, total_varargs, eff_sep)
            return
        if (
            len(syntax_leads) == 1
            and syntax_leads[0].endswith("[")
            and len(syntax_leads[0]) > 1
            and syntax_bracket_groups > 0
        ):
            stem = syntax_leads[0][:-1]
            if syntax_bracket_groups == 1 and total_slots == 0 and not total_varargs and eff_sep is None:
                register_custom_interp_token(stem, "bracket")
            else:
                register_custom_interp_token(stem, f"bracket_{syntax_bracket_groups + total_slots}")
            return
        for lead in syntax_leads:
            register_lead_spec(lead, total_slots, total_varargs, eff_sep)

    def push_group_opener(closer: str, token_text: str, next_idx: int) -> int:
        nonlocal brace_depth, bracket_depth, interp_state
        if closer == "}":
            brace_depth += 1
        if stop_on_close_bracket is not None:
            bracket_depth += 1
        if token_text == "[" and interp_state == "bracket":
            saved: str | None = "ready"
        elif _is_skip_interp_state(interp_state):
            saved = _advance_interp_state(interp_state)
        elif _is_sep_interp_state(interp_state):
            saved = interp_state
        else:
            saved = None
        group_stack.append((closer, saved))
        interp_state = None
        out.append(token_text)
        return next_idx

    def after_atom(end: int) -> int:
        if _is_skip_interp_state(interp_state):
            return _consume_lean_arg_postfix_chain(
                text,
                end,
                blank_literals=blank_literals,
                out=out,
                custom_doc_like_tokens=custom_doc_like_tokens,
                custom_interp_tokens=custom_interp_tokens,
                custom_symbols_by_first=custom_symbols_by_first,
                custom_syntax_abbrevs=custom_syntax_abbrevs,
            )
        return end

    def consume_term_max_atom(start: int) -> int | None:
        if start >= n:
            return None
        c = text[start]
        if c in {"·", "∅"}:
            out.append(c)
            return start + 1
        if c == "*" and text.startswith("*...*", start):
            out.append("*...*")
            return start + 5
        if c == "`":
            if start + 1 < n and text[start + 1] == "(":
                return None
            ident_end = _consume_lean_ident_or_name_lit(text, start)
            if ident_end is not None and ident_end > start:
                out.append(text[start:ident_end])
                return ident_end
        if c in _LEAN_TERM_MAX_PREFIX_CHARS:
            out.append(c)
            rest = _skip_lean_whitespace(text, start + 1)
            if rest > start + 1:
                out.append(text[start + 1 : rest])
            if c == "?" and rest < n and text[rest] == "_":
                out.append("_")
                return rest + 1
            ident_end = _consume_lean_ident_or_name_lit(text, rest)
            if ident_end is not None and ident_end > rest:
                out.append(text[rest:ident_end])
                return ident_end
            sub_end = consume_term_max_atom(rest)
            if sub_end is not None:
                return sub_end
            return rest
        if c == "." and start + 1 < n and (
            _is_lean_id_first(text[start + 1]) or _is_lean_id_begin_escape(text[start + 1])
        ):
            ident_end = _consume_lean_ident_or_name_lit(text, start + 1)
            if ident_end is not None:
                out.append(text[start:ident_end])
                return ident_end
        return None

    def apply_matched_symbol(sym: str) -> None:
        nonlocal interp_state
        if _is_sep_interp_state(interp_state):
            sep, arrows = _parse_sep_interp_state(interp_state)
            if sym == sep:
                if arrows > 0:
                    interp_state = f"sep:{sep}:{arrows - 1}"
                else:
                    interp_state = "ready"
                return
            return
        if sym in custom_interp_tokens:
            interp_state = _custom_interp_spec_to_state(custom_interp_tokens[sym])
        elif interp_state == "varargs":
            interp_state = None
        else:
            advance_arg_slot()

    while i < n:
        ws_end = _skip_lean_whitespace(text, i)
        if ws_end > i:
            out.append(text[i:ws_end])
            i = ws_end
            continue

        if text.startswith("/-", i):
            is_doc_token = text.startswith("/--", i) or text.startswith("/-!", i)
            if is_doc_token and custom_doc_like_tokens:
                matched_op = next(
                    (
                        op
                        for op in sorted(custom_doc_like_tokens, key=len, reverse=True)
                        if text.startswith(op, i)
                    ),
                    None,
                )
                if matched_op is not None:
                    after_op = i + len(matched_op)
                    ident_end = _consume_lean_ident_or_name_lit(text, i)
                    if ident_end is None or ident_end <= after_op:
                        apply_matched_symbol(matched_op)
                        out.append(matched_op)
                        i = after_op
                        continue
            depth = 1
            j = i + (3 if is_doc_token else 2)
            while j < n and depth > 0:
                if text.startswith("/-", j):
                    depth += 1
                    j += 2
                elif text.startswith("-/", j):
                    depth -= 1
                    j += 2
                else:
                    j += 1
            out.append(_blank_span(text, i, j))
            if is_doc_token:
                interp_state = None
            i = j
            continue

        if text.startswith("--", i):
            nl = text.find("\n", i + 2)
            j = n if nl < 0 else nl
            out.append(" " * (j - i))
            i = j
            continue

        ch = text[i]

        if stop_on_interp_close and ch == "}" and brace_depth == 0:
            return i
        if stop_on_close_bracket is not None and ch == stop_on_close_bracket and bracket_depth == 0:
            return i

        if ch in _LEAN_UNICODE_GROUP_PAIRS:
            matched_uni = _match_longest_symbol_prefix_fast(text, i, custom_symbols_by_first)
            if matched_uni is not None and len(matched_uni) > 1:
                apply_matched_symbol(matched_uni)
                out.append(matched_uni)
                i += len(matched_uni)
                continue
            i = push_group_opener(_LEAN_UNICODE_GROUP_PAIRS[ch], ch, i + 1)
            continue

        if ch in "([{":
            matched_open_sym = _match_longest_symbol_prefix_fast(
                text, i, custom_symbols_by_first, include_builtins=False
            )
            if (
                matched_open_sym is not None
                and len(matched_open_sym) > 1
                and not (matched_open_sym.endswith("[") and matched_open_sym[:-1] in custom_interp_tokens)
            ):
                apply_matched_symbol(matched_open_sym)
                out.append(matched_open_sym)
                i += len(matched_open_sym)
                continue
            if ch == "(" and in_syntax_any_paren() and syntax_nonlead_paren_depth is None:
                after_lp = _skip_lean_whitespace(text, i + 1)
                kw_end = _consume_lean_ident_or_name_lit(text, after_lp)
                kw_tok = _unquote_lean_guillemets(text[after_lp:kw_end]) if kw_end else ""
                if kw_tok in {"name", "priority"}:
                    after_kw = _skip_lean_whitespace(text, kw_end) if kw_end else after_lp
                    if text.startswith(":=", after_kw):
                        syntax_nonlead_paren_depth = len(group_stack) + 1
            closer = ")" if ch == "(" else ("]" if ch == "[" else "}")
            i = push_group_opener(closer, ch, i + 1)
            continue

        if ch in ")]}" or ch in _LEAN_UNICODE_GROUP_CLOSERS:
            matched_close_sym = (
                _match_longest_symbol_prefix_fast(text, i, custom_symbols_by_first)
                if ch not in _LEAN_UNICODE_GROUP_CLOSERS
                else None
            )
            if matched_close_sym is not None and len(matched_close_sym) > 1:
                if ch == "}" and brace_depth > 0:
                    brace_depth -= 1
                if stop_on_close_bracket is not None and bracket_depth > 0:
                    bracket_depth -= 1
                restored_sym: str | None = None
                if group_stack and group_stack[-1][0] == ch:
                    _, restored_sym = group_stack.pop()
                if matched_close_sym == "][" and (
                    restored_sym == "ready" or _is_skip_interp_state(restored_sym) or _is_sep_interp_state(restored_sym)
                ):
                    if stop_on_close_bracket is not None:
                        bracket_depth += 1
                    next_saved = (
                        _advance_interp_state(restored_sym)
                        if _is_skip_interp_state(restored_sym)
                        else restored_sym
                    )
                    group_stack.append(("]", next_saved))
                    interp_state = None
                    out.append(matched_close_sym)
                    i += len(matched_close_sym)
                    continue
                out.append(matched_close_sym)
                i += len(matched_close_sym)
                if matched_close_sym in custom_interp_tokens:
                    interp_state = _custom_interp_spec_to_state(custom_interp_tokens[matched_close_sym])
                elif restored_sym == "ready" or _is_skip_interp_state(restored_sym) or _is_sep_interp_state(restored_sym):
                    interp_state = restored_sym
                elif interp_state == "varargs":
                    interp_state = None
                else:
                    advance_arg_slot()
                continue
            if ch == "}" and brace_depth > 0:
                brace_depth -= 1
            if stop_on_close_bracket is not None and bracket_depth > 0:
                bracket_depth -= 1
            restored: str | None = None
            if group_stack and group_stack[-1][0] == ch:
                _, restored = group_stack.pop()
            if syntax_unicode_depth is not None and len(group_stack) < syntax_unicode_depth:
                syntax_unicode_depth = None
            if syntax_nonlead_paren_depth is not None and len(group_stack) < syntax_nonlead_paren_depth:
                syntax_nonlead_paren_depth = None
            out.append(ch)
            i += 1
            if restored == "ready" or _is_skip_interp_state(restored):
                i = _consume_lean_arg_postfix_chain(
                    text,
                    i,
                    blank_literals=blank_literals,
                    out=out,
                    custom_doc_like_tokens=custom_doc_like_tokens,
                    custom_interp_tokens=custom_interp_tokens,
                    custom_symbols_by_first=custom_symbols_by_first,
                    custom_syntax_abbrevs=custom_syntax_abbrevs,
                )
            interp_state = restored
            continue

        if ch == '"':
            if interp_state in ("ready", "varargs"):
                interp_state = None
                i = _scan_lean_interpolated_string(
                    text,
                    i,
                    blank_literals=blank_literals,
                    out=out,
                    custom_doc_like_tokens=custom_doc_like_tokens,
                    custom_interp_tokens=custom_interp_tokens,
                    custom_symbols_by_first=custom_symbols_by_first,
                    custom_syntax_abbrevs=custom_syntax_abbrevs,
                )
                continue
            str_end = _consume_lean_string_literal(text, i)
            if str_end is None:
                if blank_literals:
                    out.append('"')
                    out.append(_blank_span(text, i + 1, n))
                else:
                    out.append(text[i:n])
                return n
            raw_lit = text[i:str_end]
            if in_syntax_any_paren():
                note_syntax_literal(_decode_lean_string_literal_value(raw_lit).strip())
            if blank_literals:
                out.append('"')
                out.append(_blank_span(text, i + 1, str_end - 1))
                out.append('"')
            else:
                out.append(raw_lit)
            i = after_atom(str_end)
            advance_arg_slot()
            continue

        if ch == "'":
            if i + 1 < n and text[i + 1] == "'":
                matched_quote_sym = _match_longest_symbol_prefix_fast(text, i, custom_symbols_by_first)
                if matched_quote_sym is not None:
                    apply_matched_symbol(matched_quote_sym)
                    out.append(matched_quote_sym)
                    i += len(matched_quote_sym)
                    continue
                interp_state = None
                out.append(ch)
                i += 1
                continue
            char_end = _consume_lean_char_literal(text, i)
            if char_end is not None:
                if blank_literals:
                    out.append("'")
                    out.append(_blank_span(text, i + 1, char_end - 1))
                    out.append("'")
                else:
                    out.append(text[i:char_end])
                i = after_atom(char_end)
                advance_arg_slot()
                continue
            interp_state = None
            out.append(ch)
            i += 1
            continue

        if ch == "r" or (ch == "&" and i + 1 < n and text[i + 1] == '"'):
            raw_start = i
            raw_end = (
                _consume_lean_raw_string_literal(text, i)
                if ch == "r"
                else _consume_lean_string_literal(text, i + 1)
            )
            if raw_end is not None:
                if ch == "r":
                    hashes = 0
                    k = i + 1
                    while k < n and text[k] == "#":
                        hashes += 1
                        k += 1
                    prefix_end = k + 1
                    suffix_start = raw_end - (1 + hashes)
                    decoded = _decode_lean_raw_string_literal_value(text[i:raw_end]).strip()
                else:
                    prefix_end = i + 2
                    suffix_start = raw_end - 1
                    decoded = _decode_lean_string_literal_value(text[i + 1 : raw_end]).strip()
                if in_syntax_any_paren():
                    note_syntax_literal(decoded)
                if blank_literals:
                    out.append(text[raw_start:prefix_end])
                    out.append(_blank_span(text, prefix_end, suffix_start))
                    out.append(text[suffix_start:raw_end])
                else:
                    out.append(text[raw_start:raw_end])
                i = after_atom(raw_end)
                advance_arg_slot()
                continue
            if ch == "r":
                k = i + 1
                while k < n and text[k] == "#":
                    k += 1
                if k < n and text[k] == '"':
                    if blank_literals:
                        out.append(text[i : k + 1])
                        out.append(_blank_span(text, k + 1, n))
                    else:
                        out.append(text[i:n])
                    return n

        matched_symbol = _match_longest_symbol_prefix_fast(text, i, custom_symbols_by_first)
        if matched_symbol is not None and not _is_lean_id_first(matched_symbol[0]):
            closer = _group_closer_for_symbol(matched_symbol)
            if closer is not None:
                i = push_group_opener(closer, matched_symbol, i + len(matched_symbol))
                continue
            apply_matched_symbol(matched_symbol)
            out.append(matched_symbol)
            i += len(matched_symbol)
            continue

        if _is_skip_interp_state(interp_state):
            atom_end = consume_term_max_atom(i)
            if atom_end is not None:
                i = after_atom(atom_end)
                advance_arg_slot()
                continue

        if _is_sep_interp_state(interp_state):
            sep, arrows = _parse_sep_interp_state(interp_state)
            if ch == "λ" and sep == "=>":
                interp_state = f"sep:{sep}:{arrows + 1}"
                out.append(ch)
                i += 1
                continue
            if not (_is_lean_id_first(sep[0]) or _is_lean_id_begin_escape(sep[0])) and text.startswith(sep, i):
                interp_state = f"sep:{sep}:{arrows - 1}" if arrows > 0 else "ready"
                out.append(sep)
                i += len(sep)
                continue

        ident_end = _consume_lean_ident_or_name_lit(text, i)
        if (
            matched_symbol is not None
            and (ident_end is None or len(matched_symbol) >= (ident_end - i))
            and not (matched_symbol.endswith("[") and matched_symbol[:-1] in custom_interp_tokens)
        ):
            closer = _group_closer_for_symbol(matched_symbol)
            if closer is not None:
                i = push_group_opener(closer, matched_symbol, i + len(matched_symbol))
                continue
            apply_matched_symbol(matched_symbol)
            out.append(matched_symbol)
            i += len(matched_symbol)
            continue

        if ident_end is not None and ident_end > i:
            tok = text[i:ident_end]
            bare = _unquote_lean_guillemets(tok)
            is_interp_combinator = bare == "interpolatedStr" or bare.endswith(".interpolatedStr")

            if not group_stack and bare == "declare_simp_like_tactic":
                tac_ws = _skip_lean_whitespace(text, ident_end)
                tac_end = _consume_lean_ident_or_name_lit(text, tac_ws)
                if tac_end is not None and tac_end > tac_ws:
                    lit_ws = _skip_lean_whitespace(text, tac_end)
                    if lit_ws < n and text[lit_ws] == '"':
                        lit_end = _consume_lean_string_literal(text, lit_ws)
                        if lit_end is not None:
                            record_token_table_literal(
                                _decode_lean_string_literal_value(text[lit_ws:lit_end]).strip()
                            )
                    elif lit_ws < n and text[lit_ws] == "r":
                        raw_end = _consume_lean_raw_string_literal(text, lit_ws)
                        if raw_end is not None:
                            record_token_table_literal(
                                _decode_lean_raw_string_literal_value(text[lit_ws:raw_end]).strip()
                            )
                interp_state = None
                out.append(tok)
                i = ident_end
                continue

            if not group_stack and bare == "declare_syntax_cat":
                cat_ws = _skip_lean_whitespace(text, ident_end)
                cat_end = _consume_lean_ident_or_name_lit(text, cat_ws)
                if cat_end is not None and cat_end > cat_ws:
                    cat = _unquote_lean_guillemets(text[cat_ws:cat_end])
                    if cat:
                        _register_custom_symbol(custom_symbols_by_first, f"`({cat}|")
                        _register_custom_symbol(custom_symbols_by_first, f"`(«{cat}»|")
                interp_state = None
                out.append(tok)
                i = ident_end
                continue

            if not group_stack and bare in _LEAN_CUSTOM_OPERATOR_DECL_KEYWORDS:
                reset_syntax_decl()
                in_syntax_decl = True
            elif bare in _LEAN_PARSER_COMBINATOR_DECL_KEYWORDS:
                in_parser_expr = True
            elif in_syntax_any_paren() and is_interp_combinator:
                finish_syntax_interp()
            elif in_syntax_any_paren() and bare in custom_syntax_abbrevs:
                sub_leads, sub_slots, sub_varargs, sub_sep = custom_syntax_abbrevs[bare]
                if sub_leads:
                    if not syntax_leads:
                        syntax_leads.extend(sub_leads)
                    finish_syntax_interp(extra_slots=sub_slots, extra_varargs=sub_varargs, extra_sep=sub_sep)
                else:
                    finish_syntax_interp(extra_slots=sub_slots, extra_varargs=sub_varargs, extra_sep=sub_sep)
            elif (in_syntax_decl or in_parser_expr) and not group_stack and bare in {
                "def",
                "theorem",
                "lemma",
                "axiom",
                "opaque",
                "abbrev",
                "structure",
                "inductive",
                "class",
                "instance",
                "example",
                "section",
                "namespace",
                "end",
                "macro_rules",
                "elab_rules",
            }:
                reset_syntax_decl()
            elif in_syntax_any_paren():
                after_tok_ws = _skip_lean_whitespace(text, ident_end)
                if bare == "unicode" and after_tok_ws < n and text[after_tok_ws] == "(":
                    syntax_unicode_depth = len(group_stack) + 1
                elif bare in {"sepBy", "sepBy1", "sepByIndent", "sepBy1Indent"}:
                    if syntax_leads or syntax_abbrev_rhs:
                        syntax_varargs = True
                    if after_tok_ws < n and text[after_tok_ws] == "(" and syntax_nonlead_paren_depth is None:
                        syntax_nonlead_paren_depth = len(group_stack) + 1
                elif bare in {"many", "many1", "optional", "manyIndent", "many1Indent", "optConfig", "optSemicolon"}:
                    if syntax_leads or syntax_abbrev_rhs:
                        syntax_varargs = True
                elif (
                    in_syntax_decl
                    and not syntax_leads
                    and not group_stack
                    and syntax_abbrev_name is None
                    and after_tok_ws + 1 < n
                    and text.startswith(":=", after_tok_ws)
                ):
                    syntax_abbrev_name = bare
                elif (
                    in_syntax_decl
                    and not syntax_leads
                    and not syntax_abbrev_rhs
                    and bare not in _LEAN_SYNTAX_IGNORED_COMBINATORS
                    and bare not in _LEAN_PARSER_COMBINATOR_DECL_KEYWORDS
                    and bare not in {"local", "scoped"}
                ):
                    syntax_saw_leading_item = True
                elif (syntax_leads or syntax_abbrev_rhs) and not syntax_in_bracket_item and not (
                len(syntax_leads) == 1 and syntax_leads[0].endswith("[") and len(syntax_leads[0]) > 1 and syntax_bracket_groups == 0
            ) and (
                    syntax_nonlead_paren_depth is None or len(group_stack) < syntax_nonlead_paren_depth
                ):
                    if syntax_awaiting_prec:
                        syntax_awaiting_prec = False
                    elif in_parser_expr and not in_syntax_decl:
                        if bare in {"termParser", "ident", "rawIdent", "numLit", "strLit", "charLit"} or bare.endswith(".termParser"):
                            syntax_slots += 1
                    elif bare not in _LEAN_SYNTAX_IGNORED_COMBINATORS and bare not in _LEAN_PARSER_COMBINATOR_DECL_KEYWORDS:
                        if after_tok_ws < n and text[after_tok_ws] == ":" and text[after_tok_ws : after_tok_ws + 2] != ":=":
                            after_colon_ws = _skip_lean_whitespace(text, after_tok_ws + 1)
                            prec_end = _consume_lean_ident_or_name_lit(text, after_colon_ws)
                            prec_bare = _unquote_lean_guillemets(text[after_colon_ws:prec_end]) if prec_end else ""
                            if prec_bare != "interpolatedStr" and not prec_bare.endswith(".interpolatedStr"):
                                syntax_slots += 1
                                if bare == "term" and prec_bare not in {"max", "arg"}:
                                    syntax_saw_nonmax_arg = True
                        else:
                            syntax_slots += 1
                            if bare == "term":
                                syntax_saw_nonmax_arg = True

            if _is_sep_interp_state(interp_state):
                sep, arrows = _parse_sep_interp_state(interp_state)
                if bare == sep:
                    interp_state = f"sep:{sep}:{arrows - 1}" if arrows > 0 else "ready"
                    out.append(tok)
                    i = ident_end
                    continue
                if bare == "fun" and sep == "=>":
                    interp_state = f"sep:{sep}:{arrows + 1}"
                    out.append(tok)
                    i = ident_end
                    continue
                if bare in {
                    "def",
                    "theorem",
                    "lemma",
                    "axiom",
                    "opaque",
                    "abbrev",
                    "structure",
                    "inductive",
                    "class",
                    "instance",
                    "example",
                    "section",
                    "namespace",
                    "end",
                }:
                    interp_state = None
                out.append(tok)
                i = ident_end
                continue

            short_tok = bare.rsplit(".", 1)[-1] if tok[0] != "`" else ""
            if tok in _LEAN_INTERP_PREFIX_IDS or tok in _LEAN_INTERP_DIRECT_KEYWORDS or short_tok in _LEAN_INTERP_DIRECT_KEYWORDS:
                interp_state = "ready"
                out.append(tok)
                i = ident_end
                continue
            if bare in custom_interp_tokens or tok in custom_interp_tokens:
                spec = custom_interp_tokens.get(bare, custom_interp_tokens.get(tok))
                if spec == "bracket":
                    if ident_end < n and text[ident_end] == "[":
                        interp_state = "bracket"
                        out.append(tok)
                        i = ident_end
                        continue
                elif isinstance(spec, str) and spec.startswith("bracket_"):
                    after_stem = _skip_lean_whitespace(text, ident_end)
                    if after_stem < n and text[after_stem] == "[":
                        interp_state = f"skip_{int(spec.split('_', 1)[1])}"
                        out.append(tok)
                        i = ident_end
                        continue
                else:
                    interp_state = _custom_interp_spec_to_state(spec if spec is not None else 0)
                    out.append(tok)
                    i = ident_end
                    continue
            if tok in _LEAN_INTERP_ONE_ARG_KEYWORDS or short_tok in _LEAN_INTERP_ONE_ARG_KEYWORDS:
                interp_state = "skip_1"
                out.append(tok)
                i = ident_end
                continue
            if tok in _LEAN_INTERP_TWO_ARG_KEYWORDS or short_tok in _LEAN_INTERP_TWO_ARG_KEYWORDS:
                interp_state = "skip_2"
                out.append(tok)
                i = ident_end
                continue
            if (tok in _LEAN_INTERP_BRACKET_KEYWORDS or short_tok in _LEAN_INTERP_BRACKET_KEYWORDS) and ident_end < n and text[ident_end] == "[":
                interp_state = "bracket"
                out.append(tok)
                i = ident_end
                continue
            if bare in {
                "def",
                "theorem",
                "lemma",
                "axiom",
                "opaque",
                "abbrev",
                "structure",
                "inductive",
                "class",
                "instance",
                "example",
                "section",
                "namespace",
                "end",
                "where",
                "by",
                "do",
                "fun",
                "let",
                "have",
                "if",
                "then",
                "else",
                "match",
                "with",
                "return",
            }:
                interp_state = None
                out.append(tok)
                i = ident_end
                continue
            out.append(tok)
            i = after_atom(ident_end)
            advance_arg_slot()
            continue

        if _is_lean_ascii_digit(ch):
            j = i + 1
            while j < n and (_is_lean_ascii_alnum(text[j]) or text[j] in "_."):
                if text[j] == "." and (j + 1 >= n or not _is_lean_ascii_digit(text[j + 1])):
                    break
                j += 1
            if in_syntax_any_paren() and syntax_awaiting_prec:
                syntax_awaiting_prec = False
            out.append(text[i:j])
            i = after_atom(j)
            advance_arg_slot()
            continue

        if in_syntax_any_paren():
            if text.startswith("<|>", i):
                if syntax_leads:
                    syntax_alt_pending = True
                interp_state = None
                out.append("<|>")
                i += 3
                continue
            if (syntax_leads or syntax_abbrev_rhs) and ch in "*+?!":
                syntax_varargs = True
                if not _is_sep_interp_state(interp_state):
                    interp_state = None
                out.append(ch)
                i += 1
                continue
            if (syntax_leads or syntax_abbrev_rhs) and ch == "," and i + 1 < n and text[i + 1] in "+*":
                syntax_varargs = True
                if not _is_sep_interp_state(interp_state):
                    interp_state = None
                out.append(text[i : i + 2])
                i += 2
                continue

        if in_syntax_decl and all(c == ")" for c, _ in group_stack):
            if not group_stack and text.startswith(":=", i):
                if syntax_abbrev_name is not None and not syntax_leads and not syntax_abbrev_rhs:
                    syntax_abbrev_rhs = True
                else:
                    reset_syntax_decl()
                if not _is_sep_interp_state(interp_state):
                    interp_state = None
                out.append(":=")
                i += 2
                continue
            if not group_stack and text.startswith("=>", i):
                reset_syntax_decl()
                if not _is_sep_interp_state(interp_state):
                    interp_state = None
                out.append("=>")
                i += 2
                continue
            if ch == ":" and (syntax_leads or syntax_abbrev_rhs or syntax_saw_interp):
                after_colon = _skip_lean_whitespace(text, i + 1)
                cat_end = _consume_lean_ident_or_name_lit(text, after_colon)
                cat_tok = _unquote_lean_guillemets(text[after_colon:cat_end]) if cat_end else ""
                after_cat_ws = _skip_lean_whitespace(text, cat_end) if cat_end else after_colon
                if (
                    not group_stack
                    and cat_tok
                    and cat_tok not in {"max", "arg", "lead", "min", "interpolatedStr"}
                    and not cat_tok.endswith(".interpolatedStr")
                    and (
                        after_cat_ws >= n
                        or text[after_cat_ws] == "\n"
                        or text.startswith("=>", after_cat_ws)
                        or text.startswith(":=", after_cat_ws)
                    )
                ):
                    if syntax_saw_interp and not syntax_leads and cat_tok not in {"term", "command", "tactic", "conv", "attr", "stx", "prio", "prec"}:
                        custom_syntax_abbrevs[cat_tok] = (
                            [],
                            syntax_slots,
                            syntax_varargs,
                            syntax_pending_sep,
                        )
                    reset_syntax_decl()
                else:
                    syntax_awaiting_prec = True

        if interp_state == "varargs" and ch in ",;":
            out.append(ch)
            i += 1
            continue

        if not _is_sep_interp_state(interp_state):
            interp_state = None
        out.append(ch)
        i += 1

    return n


def _scan_lean_tokens(text: str, *, blank_literals: bool) -> str:
    """Token-aware Lean comment (and optional literal) scrubber."""
    out: list[str] = []
    _scan_lean_tokens_until(
        text,
        0,
        blank_literals=blank_literals,
        stop_on_interp_close=False,
        stop_on_close_bracket=None,
        out=out,
        custom_doc_like_tokens=set(),
        custom_interp_tokens={},
        custom_symbols_by_first={},
        custom_syntax_abbrevs={},
    )
    return "".join(out)


def strip_lean_comments(text: str) -> str:
    """Strip Lean line/block comments while preserving line structure.

    Token-aware for Lean strings, raw strings, character literals (such as ``'"'``),
    and identifiers (such as ``x'`` or ``«...»``), so comment markers inside literals
    are preserved and ``'"'`` never enters string mode.
    """
    return _scan_lean_tokens(text, blank_literals=False)


def _strip_lean_strings(text: str) -> str:
    """Replace string and char literal contents with spaces, preserving line structure."""
    return _scan_lean_tokens(text, blank_literals=True)


def scrub_lean_code(text: str) -> str:
    """Remove comments and string/char literal contents from Lean source text."""
    return _scan_lean_tokens(text, blank_literals=True)

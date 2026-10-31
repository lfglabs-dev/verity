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


_LEAN_INTERP_PREFIX_IDS: frozenset[str] = frozenset({"s!", "m!", "f!", "v!"})
_LEAN_INTERP_DIRECT_KEYWORDS: frozenset[str] = frozenset(
    {"throwError", "println!", "dbg_trace", "reportIssue!", "reportDbgIssue!", "reportEMatchIssue!"}
)
_LEAN_INTERP_ONE_ARG_KEYWORDS: frozenset[str] = frozenset(
    {
        "throwErrorAt",
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
    {"leading_parser", "trailing_parser", "symbol", "unicodeSymbol", "nonReservedSymbol"}
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


def _match_longest_symbol_prefix(
    text: str,
    i: int,
    symbol_sets: tuple[set[str] | frozenset[str], ...],
) -> str | None:
    best: str | None = None
    best_len = 0
    for s in symbol_sets:
        for sym in s:
            slen = len(sym)
            if slen > best_len and text.startswith(sym, i):
                best = sym
                best_len = slen
    return best


def _symbol_needs_token_table_tracking(sym: str) -> bool:
    """Return True when `sym` could alter downstream comment/literal tokenization."""
    if len(sym) <= 1:
        return False
    return any(ch in sym for ch in ("'", '"', "-", "/", "`", "«", "r", "(", ")", "[", "]", "{", "}"))


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
    custom_symbol_tokens: set[str],
) -> int:
    """Consume contiguous maxPrec postfix projections/indexing after an argument atom.

    For `throwErrorAt ref msg` (and the named-error/warning variants), Lean parses
    `ref` with `term:max`, which absorbs contiguous field projections (`p.1`, `p.fst`,
    `p.1.1`) and array indexing (`stx[0]`, `arr[0]!`, `arr[0]?`). Consuming those
    before advancing the pending argument slot keeps `interp_state == "ready"` aligned
    with `msg`.
    """
    n = len(text)
    while i < n:
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
                custom_symbol_tokens=custom_symbol_tokens,
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
    custom_symbol_tokens: set[str],
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
                custom_symbol_tokens=custom_symbol_tokens,
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
    """Print error list to stderr and exit with code 1.

    Args:
        errors: List of error messages to report.
        message: Header message to print before error list.
    """
    if errors:
        print(f"{message}:", file=sys.stderr)
        for item in errors:
            print(f"  - {item}", file=sys.stderr)
        raise SystemExit(1)


def _consume_lean_ident_or_name_lit(text: str, i: int) -> int | None:
    """Consume a Lean identifier or backtick name literal starting at ``i``."""
    n = len(text)
    if i >= n:
        return None
    j = i
    if text[j] == "`":
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
    custom_symbol_tokens: set[str],
) -> int:
    """Scan Lean tokens from ``i``, appending scrubbed text to ``out``.

    When ``stop_on_interp_close`` is True, stops at the matching unnested ``}``
    that closes an ``interpolatedStr`` hole (while allowing nested ``{ ... }``
    term braces inside the hole). When ``stop_on_close_bracket`` is set (e.g.
    ``"]"``), stops at the matching unnested closing bracket.
    """
    n = len(text)
    brace_depth = 0
    bracket_depth = 0
    # Pending interpolated-string state across whitespace/comments/args:
    # - "ready": next `"` is an `interpolatedStr`
    # - "skip_N": skip N maxPrec argument tokens/groups, then become "ready"
    # - "bracket": expect `[...]` trace tag, then become "ready"
    interp_state: str | None = None
    group_stack: list[tuple[str, str | None]] = []
    in_syntax_decl = False
    in_parser_expr = False
    syntax_decl_strings: list[str] = []
    syntax_arg_slots_after_str = 0
    syntax_has_varargs_after_str = False
    syntax_awaiting_prec = False

    def advance_arg_slot() -> None:
        nonlocal interp_state
        interp_state = _advance_interp_state(interp_state)

    def reset_syntax_decl() -> None:
        nonlocal in_syntax_decl, in_parser_expr, syntax_arg_slots_after_str, syntax_has_varargs_after_str, syntax_awaiting_prec
        in_syntax_decl = False
        in_parser_expr = False
        syntax_decl_strings.clear()
        syntax_arg_slots_after_str = 0
        syntax_has_varargs_after_str = False
        syntax_awaiting_prec = False

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
                        if matched_op in custom_interp_tokens:
                            interp_state = _custom_interp_spec_to_state(custom_interp_tokens[matched_op])
                        else:
                            advance_arg_slot()
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

        if ch in "([{":
            matched_open_sym = (
                _match_longest_symbol_prefix(text, i, (_LEAN_BUILTIN_PRIME_SYMBOL_TOKENS, custom_symbol_tokens))
                if custom_symbol_tokens
                else None
            )
            if (
                matched_open_sym is not None
                and len(matched_open_sym) > 1
                and not (matched_open_sym.endswith("[") and matched_open_sym[:-1] in custom_interp_tokens)
            ):
                if matched_open_sym in custom_interp_tokens:
                    interp_state = _custom_interp_spec_to_state(custom_interp_tokens[matched_open_sym])
                elif interp_state == "varargs":
                    interp_state = None
                else:
                    advance_arg_slot()
                out.append(matched_open_sym)
                i += len(matched_open_sym)
                continue
            if ch == "{":
                brace_depth += 1
            if stop_on_close_bracket is not None:
                bracket_depth += 1
            if ch == "[" and interp_state == "bracket":
                group_stack.append(("]", "ready"))
            elif _is_skip_interp_state(interp_state):
                closer = ")" if ch == "(" else ("]" if ch == "[" else "}")
                group_stack.append((closer, _advance_interp_state(interp_state)))
            else:
                closer = ")" if ch == "(" else ("]" if ch == "[" else "}")
                group_stack.append((closer, None))
            interp_state = None
            out.append(ch)
            i += 1
            continue

        if ch in ")]}":
            matched_close_sym = _match_longest_symbol_prefix(
                text, i, (_LEAN_BUILTIN_PRIME_SYMBOL_TOKENS, custom_symbol_tokens)
            )
            if matched_close_sym is not None and len(matched_close_sym) > 1:
                if ch == "}" and brace_depth > 0:
                    brace_depth -= 1
                if stop_on_close_bracket is not None and bracket_depth > 0:
                    bracket_depth -= 1
                restored_sym: str | None = None
                if group_stack and group_stack[-1][0] == ch:
                    _, restored_sym = group_stack.pop()
                out.append(matched_close_sym)
                i += len(matched_close_sym)
                if matched_close_sym in custom_interp_tokens:
                    interp_state = _custom_interp_spec_to_state(custom_interp_tokens[matched_close_sym])
                elif restored_sym == "ready" or _is_skip_interp_state(restored_sym):
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
            out.append(ch)
            i += 1
            if restored == "ready" or _is_skip_interp_state(restored):
                # Group closed a `term:max` argument (e.g. `(s.getArg 0).1` or `(arr)[0]`);
                # consume any contiguous postfix chain before finalizing the slot.
                i = _consume_lean_arg_postfix_chain(
                    text,
                    i,
                    blank_literals=blank_literals,
                    out=out,
                    custom_doc_like_tokens=custom_doc_like_tokens,
                    custom_interp_tokens=custom_interp_tokens,
                    custom_symbol_tokens=custom_symbol_tokens,
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
                    custom_symbol_tokens=custom_symbol_tokens,
                )
                continue
            str_end = _consume_lean_string_literal(text, i)
            if str_end is None:
                # Unterminated string literal: treat remainder of file as string body.
                if blank_literals:
                    out.append('"')
                    out.append(_blank_span(text, i + 1, n))
                else:
                    out.append(text[i:n])
                return n
            raw_lit = text[i:str_end]
            if (in_syntax_decl or in_parser_expr) and all(c == ")" for c, _ in group_stack):
                decoded = _decode_lean_string_literal_value(raw_lit).strip()
                if decoded:
                    if in_syntax_decl or in_parser_expr:
                        syntax_decl_strings.append(decoded)
                        syntax_arg_slots_after_str = 0
                        syntax_has_varargs_after_str = False
                        syntax_awaiting_prec = False
                    if (decoded.startswith("/--") or decoded.startswith("/-!")) and len(decoded) > 3:
                        custom_doc_like_tokens.add(decoded)
                    if _symbol_needs_token_table_tracking(decoded):
                        custom_symbol_tokens.add(decoded)
            if blank_literals:
                out.append('"')
                out.append(_blank_span(text, i + 1, str_end - 1))
                out.append('"')
            else:
                out.append(raw_lit)
            i = str_end
            if _is_skip_interp_state(interp_state):
                i = _consume_lean_arg_postfix_chain(
                    text,
                    i,
                    blank_literals=blank_literals,
                    out=out,
                    custom_doc_like_tokens=custom_doc_like_tokens,
                    custom_interp_tokens=custom_interp_tokens,
                    custom_symbol_tokens=custom_symbol_tokens,
                )
            advance_arg_slot()
            continue

        if ch == "'":
            if i + 1 < n and text[i + 1] == "'":
                matched_quote_sym = _match_longest_symbol_prefix(
                    text, i, (_LEAN_BUILTIN_PRIME_SYMBOL_TOKENS, custom_symbol_tokens)
                )
                if matched_quote_sym is not None:
                    if matched_quote_sym in custom_interp_tokens:
                        interp_state = _custom_interp_spec_to_state(custom_interp_tokens[matched_quote_sym])
                    else:
                        advance_arg_slot()
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
                i = char_end
                if _is_skip_interp_state(interp_state):
                    i = _consume_lean_arg_postfix_chain(
                        text,
                        i,
                        blank_literals=blank_literals,
                        out=out,
                        custom_doc_like_tokens=custom_doc_like_tokens,
                        custom_interp_tokens=custom_interp_tokens,
                        custom_symbol_tokens=custom_symbol_tokens,
                    )
                advance_arg_slot()
                continue
            interp_state = None
            out.append(ch)
            i += 1
            continue

        if ch == "r":
            raw_end = _consume_lean_raw_string_literal(text, i)
            if raw_end is not None:
                hashes = 0
                k = i + 1
                while k < n and text[k] == "#":
                    hashes += 1
                    k += 1
                prefix_end = k + 1  # after opening `"`
                suffix_start = raw_end - (1 + hashes)  # at closing `"`
                if blank_literals:
                    out.append(text[i:prefix_end])
                    out.append(_blank_span(text, prefix_end, suffix_start))
                    out.append(text[suffix_start:raw_end])
                else:
                    out.append(text[i:raw_end])
                i = raw_end
                advance_arg_slot()
                continue
            # Check for an unterminated raw string token (`r#*"` without matching closer).
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

        matched_symbol = _match_longest_symbol_prefix(
            text, i, (_LEAN_BUILTIN_PRIME_SYMBOL_TOKENS, custom_symbol_tokens)
        )
        if matched_symbol is not None and not _is_lean_id_first(matched_symbol[0]):
            if matched_symbol in custom_interp_tokens:
                interp_state = _custom_interp_spec_to_state(custom_interp_tokens[matched_symbol])
            elif interp_state == "varargs":
                interp_state = None
            else:
                advance_arg_slot()
            out.append(matched_symbol)
            i += len(matched_symbol)
            continue

        if custom_interp_tokens:
            matched_interp_sym = next(
                (
                    sym
                    for sym in sorted(custom_interp_tokens, key=len, reverse=True)
                    if not (_is_lean_id_first(sym[0]) or _is_lean_id_begin_escape(sym[0]))
                    and text.startswith(sym, i)
                ),
                None,
            )
            if matched_interp_sym is not None:
                interp_state = _custom_interp_spec_to_state(custom_interp_tokens[matched_interp_sym])
                out.append(matched_interp_sym)
                i += len(matched_interp_sym)
                continue

        ident_end = _consume_lean_ident_or_name_lit(text, i)
        if (
            matched_symbol is not None
            and (ident_end is None or len(matched_symbol) >= (ident_end - i))
            and not (matched_symbol.endswith("[") and matched_symbol[:-1] in custom_interp_tokens)
        ):
            if matched_symbol in custom_interp_tokens:
                interp_state = _custom_interp_spec_to_state(custom_interp_tokens[matched_symbol])
            elif interp_state == "varargs":
                interp_state = None
            else:
                advance_arg_slot()
            out.append(matched_symbol)
            i += len(matched_symbol)
            continue
        if ident_end is not None and ident_end > i:
            tok = text[i:ident_end]
            if not group_stack and tok in _LEAN_CUSTOM_OPERATOR_DECL_KEYWORDS:
                reset_syntax_decl()
                in_syntax_decl = True
            elif tok in _LEAN_PARSER_COMBINATOR_DECL_KEYWORDS:
                in_parser_expr = True
            elif (in_syntax_decl or in_parser_expr) and tok == "interpolatedStr" and syntax_decl_strings:
                if (
                    len(syntax_decl_strings) >= 2
                    and syntax_decl_strings[-1] == "]"
                    and syntax_decl_strings[-2].endswith("[")
                    and len(syntax_decl_strings[-2]) > 1
                ):
                    custom_interp_tokens[syntax_decl_strings[-2][:-1]] = "bracket"
                else:
                    lead = syntax_decl_strings[-1]
                    if syntax_has_varargs_after_str:
                        custom_interp_tokens[lead] = "varargs"
                    else:
                        prev = custom_interp_tokens.get(lead)
                        if prev is None or (isinstance(prev, int) and syntax_arg_slots_after_str < prev):
                            custom_interp_tokens[lead] = syntax_arg_slots_after_str
            elif (in_syntax_decl or in_parser_expr) and not group_stack and tok in {
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
            elif (in_syntax_decl or in_parser_expr) and all(c == ")" for c, _ in group_stack) and syntax_decl_strings:
                if syntax_awaiting_prec:
                    syntax_awaiting_prec = False
                elif tok in {"many", "many1", "optional", "sepBy", "sepBy1", "manyIndent", "many1Indent"}:
                    syntax_has_varargs_after_str = True
                elif in_parser_expr and not in_syntax_decl:
                    if tok in {"termParser", "ident", "rawIdent", "numLit", "strLit", "charLit"}:
                        syntax_arg_slots_after_str += 1
                elif tok not in _LEAN_SYNTAX_IGNORED_COMBINATORS and tok not in _LEAN_PARSER_COMBINATOR_DECL_KEYWORDS:
                    # A syntax parameter/category item (`term:max`, `x:term:max`, `ident`, etc.)
                    # before `interpolatedStr`. Note `x:interpolatedStr` sets `syntax_awaiting_prec`
                    # on `:`, so when `interpolatedStr` arrives next we undo the tentative slot.
                    next_ws = _skip_lean_whitespace(text, ident_end)
                    if next_ws < n and text[next_ws] == ":" and text[next_ws : next_ws + 2] != ":=":
                        after_colon_ws = _skip_lean_whitespace(text, next_ws + 1)
                        if not text.startswith("interpolatedStr", after_colon_ws):
                            syntax_arg_slots_after_str += 1
                    else:
                        syntax_arg_slots_after_str += 1

            if tok in _LEAN_INTERP_PREFIX_IDS or tok in _LEAN_INTERP_DIRECT_KEYWORDS:
                interp_state = "ready"
                out.append(tok)
                i = ident_end
                continue
            if tok in custom_interp_tokens:
                spec = custom_interp_tokens[tok]
                if spec == "bracket":
                    if ident_end < n and text[ident_end] == "[":
                        interp_state = "bracket"
                        out.append(tok)
                        i = ident_end
                        continue
                else:
                    interp_state = _custom_interp_spec_to_state(spec)
                    out.append(tok)
                    i = ident_end
                    continue
            if tok in _LEAN_INTERP_ONE_ARG_KEYWORDS:
                interp_state = "skip_1"
                out.append(tok)
                i = ident_end
                continue
            if tok in _LEAN_INTERP_TWO_ARG_KEYWORDS:
                interp_state = "skip_2"
                out.append(tok)
                i = ident_end
                continue
            if tok in _LEAN_INTERP_BRACKET_KEYWORDS and ident_end < n and text[ident_end] == "[":
                interp_state = "bracket"
                out.append(tok)
                i = ident_end
                continue
            if tok in {
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
            i = ident_end
            if _is_skip_interp_state(interp_state):
                i = _consume_lean_arg_postfix_chain(
                    text,
                    i,
                    blank_literals=blank_literals,
                    out=out,
                    custom_doc_like_tokens=custom_doc_like_tokens,
                    custom_interp_tokens=custom_interp_tokens,
                    custom_symbol_tokens=custom_symbol_tokens,
                )
            advance_arg_slot()
            continue

        if _is_lean_ascii_digit(ch):
            j = i + 1
            while j < n and (_is_lean_ascii_alnum(text[j]) or text[j] in "_."):
                if text[j] == "." and (j + 1 >= n or not _is_lean_ascii_digit(text[j + 1])):
                    break
                j += 1
            if in_syntax_decl and all(c == ")" for c, _ in group_stack) and syntax_awaiting_prec:
                syntax_awaiting_prec = False
            out.append(text[i:j])
            i = j
            if _is_skip_interp_state(interp_state):
                i = _consume_lean_arg_postfix_chain(
                    text,
                    i,
                    blank_literals=blank_literals,
                    out=out,
                    custom_doc_like_tokens=custom_doc_like_tokens,
                    custom_interp_tokens=custom_interp_tokens,
                    custom_symbol_tokens=custom_symbol_tokens,
                )
            advance_arg_slot()
            continue

        if (in_syntax_decl or in_parser_expr) and syntax_decl_strings and all(c == ")" for c, _ in group_stack):
            if text.startswith("<|>", i):
                syntax_has_varargs_after_str = True
                interp_state = None
                out.append("<|>")
                i += 3
                continue
            if ch in "*+?":
                syntax_has_varargs_after_str = True
                interp_state = None
                out.append(ch)
                i += 1
                continue

        if in_syntax_decl and all(c == ")" for c, _ in group_stack):
            if not group_stack and (text.startswith(":=", i) or text.startswith("=>", i)):
                reset_syntax_decl()
                interp_state = None
                out.append(text[i : i + 2])
                i += 2
                continue
            if ch == ":" and syntax_decl_strings:
                after_colon = _skip_lean_whitespace(text, i + 1)
                # Return category `: term` / `: command` / `: doElem` at end of `syntax ... : cat`
                cat_end = _consume_lean_ident_or_name_lit(text, after_colon)
                cat_tok = text[after_colon:cat_end] if cat_end else ""
                after_cat_ws = _skip_lean_whitespace(text, cat_end) if cat_end else after_colon
                if not group_stack and cat_tok and cat_tok not in {"max", "arg", "lead", "min", "interpolatedStr"} and (
                    after_cat_ws >= n or text[after_cat_ws] == "\n" or text.startswith("=>", after_cat_ws) or text.startswith(":=", after_cat_ws)
                ):
                    reset_syntax_decl()
                else:
                    syntax_awaiting_prec = True

        interp_state = None
        out.append(ch)
        i += 1

    return n


def _scan_lean_tokens(text: str, *, blank_literals: bool) -> str:
    """Token-aware Lean comment (and optional literal) scrubber.

    Mirrors ``Lean.Parser.tokenFnAux`` / ``whitespace`` / ``interpolatedStrFn`` so that:
    - nested ``/- ... -/`` block comments, ``/-- ... -/`` / ``/-! ... -/`` doc comments,
      and ``-- ...`` line comments are blanked using Lean's exact delimiter rules (while
      honoring file-local custom operators starting with ``/--`` / ``/-!``),
    - character literals (including ``'"'``, ``'-'``, ``'\\'``) never open string
      or comment states, and identifier-trailing apostrophes (``foo'``, ``x' = 'a'``)
      are consumed as part of the identifier while non-identifier symbols such as
      ``λ`` (U+03BB) never consume a following ``'``,
    - interpolated strings (``s!"..."``, ``m!"..."``, ``f!"..."``, ``throwError "..."``,
      ``throwErrorAt ref "..."``, ``println! "..."``, ``dbg_trace "..."``, ``trace[...] "..."``,
      and file-local ``interpolatedStr`` syntax/macros) recursively tokenize ``{...}`` holes
      and accept ``\\{`` escapes,
    - guillemet-escaped identifiers (``«...»``) and backtick name literals (`` `«...» ``)
      never open strings on embedded quotes,
    - raw strings (``r#*"..."#*``) only start at token boundaries (not mid-identifier
      as in ``bar"x"``), and
    - line numbers and line counts are preserved identically.
    """
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
        custom_symbol_tokens=set(),
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

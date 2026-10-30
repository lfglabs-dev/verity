#!/usr/bin/env python3
"""Shared utilities for property manifest and coverage checking."""

from __future__ import annotations

import json
import re
import sys
import unicodedata
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
_LEAN_IDENT_SEG_PAT = r"(?:«[^»]+»|[A-Za-z_][A-Za-z0-9_']*)"
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


def _is_lean_id_first(ch: str) -> bool:
    """Match Lean ``isIdFirst`` (``Init/Meta/Defs.lean``)."""
    if ch.isalpha() or ch == "_":
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
    if ch.isalnum() or ch in "_!'?":
        return True
    cp = ord(ch)
    if 0x2080 <= cp <= 0x2089 or 0x2090 <= cp <= 0x209C or 0x1D62 <= cp <= 0x1D6A or cp == 0x2C7C:
        return True
    return _is_lean_id_first(ch) and ch != "_"


def _is_lean_id_begin_escape(ch: str) -> bool:
    return ch == "«"


def _is_lean_whitespace(ch: str) -> bool:
    """Match Lean ``Char.isWhitespace`` (Unicode White_Space, no extra ASCII)."""
    return unicodedata.category(ch) == "Zs" or ch in "\t\n\x0b\x0c\r\x1c\x1d\x1e\x1f"


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
            j += 1
            if j >= n:
                return None
            esc = text[j]
            if esc in "\\\"'rnt":
                j += 1
                continue
            if esc == "x":
                if j + 2 >= n or not all(c in "0123456789abcdefABCDEF" for c in text[j + 1 : j + 3]):
                    return None
                j += 3
                continue
            if esc == "u":
                if j + 4 >= n or not all(c in "0123456789abcdefABCDEF" for c in text[j + 1 : j + 5]):
                    return None
                j += 5
                continue
            if esc == "\n":
                j += 1
                while j < n and text[j] != "\n" and _is_lean_whitespace(text[j]):
                    j += 1
                continue
            return None
        j += 1
    return None


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


def _scan_lean_tokens(text: str, *, blank_literals: bool) -> str:
    """Token-aware Lean comment (and optional literal) scrubber.

    Mirrors ``Lean.Parser.tokenFnAux`` / ``whitespace`` so that:
    - nested ``/- ... -/`` block comments and ``-- ...`` line comments are blanked,
    - character literals (including ``'"'``, ``'-'``, ``'\\'``) never open string
      or comment states, and identifier-trailing apostrophes (``foo'``, ``x' = 'a'``)
      are consumed as part of the identifier rather than starting a bogus char literal,
    - guillemet-escaped identifiers (``«...»``) and backtick name literals (`` `«...» ``)
      never open strings on embedded quotes,
    - raw strings (``r#*"..."#*``) only start at token boundaries (not mid-identifier
      as in ``bar"x"``), and
    - line numbers and line counts are preserved identically.
    """
    out: list[str] = []
    i = 0
    n = len(text)
    while i < n:
        ws_end = _skip_lean_whitespace(text, i)
        if ws_end > i:
            out.append(text[i:ws_end])
            i = ws_end
            continue

        if text.startswith("/-", i):
            depth = 1
            j = i + 2
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
            i = j
            continue

        if text.startswith("--", i):
            nl = text.find("\n", i + 2)
            j = n if nl < 0 else nl
            out.append(" " * (j - i))
            i = j
            continue

        ch = text[i]

        if ch == '"':
            str_end = _consume_lean_string_literal(text, i)
            if str_end is None:
                # Unterminated string literal: treat remainder of file as string body.
                if blank_literals:
                    out.append('"')
                    out.append(_blank_span(text, i + 1, n))
                else:
                    out.append(text[i:n])
                return "".join(out)
            if blank_literals:
                out.append('"')
                out.append(_blank_span(text, i + 1, str_end - 1))
                out.append('"')
            else:
                out.append(text[i:str_end])
            i = str_end
            continue

        if ch == "'":
            char_end = _consume_lean_char_literal(text, i)
            if char_end is not None:
                if blank_literals:
                    out.append("'")
                    out.append(_blank_span(text, i + 1, char_end - 1))
                    out.append("'")
                else:
                    out.append(text[i:char_end])
                i = char_end
                continue
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
                return "".join(out)

        ident_end = _consume_lean_ident_or_name_lit(text, i)
        if ident_end is not None and ident_end > i:
            out.append(text[i:ident_end])
            i = ident_end
            continue

        if ch.isdigit():
            j = i + 1
            while j < n and (text[j].isalnum() or text[j] in "_."):
                if text[j] == "." and (j + 1 >= n or not text[j + 1].isdigit()):
                    break
                j += 1
            out.append(text[i:j])
            i = j
            continue

        out.append(ch)
        i += 1

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

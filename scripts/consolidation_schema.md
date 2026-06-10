# Consolidation Schema

A declarative schema for a generic "sync rule" that a single engine can execute
in both **generate** and **check** modes, eventually replacing all 63 scripts.

## Design Rationale

Every `check_*.py` and `generate_*.py` follows the same three-phase structure:

1. **Extract** — read a source (Lean files, JSON artifacts, Python modules, subprocesses)
   and compute a value.
2. **Serialize** — transform the value into a canonical string (JSON with sort_keys, Lean
   source, plain text).
3. **Write / Compare** — write the string to a target file (`generate` mode) or diff it
   against the committed file and fail on divergence (`check` mode).

A single schema captures this pattern for all families. Extractor type and target
format are the only dimensions that vary meaningfully across clusters.

---

## YAML Schema (annotated)

```yaml
# ── Identity ────────────────────────────────────────────────────────────────
id: string                  # unique kebab-case rule name, used as --rule argument
description: string         # one-line purpose (shows in --list output)
cluster: string             # family label from CONSOLIDATION_INVENTORY.md

# ── Source watching ──────────────────────────────────────────────────────────
# Glob patterns relative to repo root.  Used for cache-invalidation and to
# surface which files an engine pass must read.  Not enforced by the prototype
# but will drive incremental execution in the full engine.
source_globs:
  - string                  # e.g. "Compiler/**/*.lean", "artifacts/*.json"

# ── Extraction ───────────────────────────────────────────────────────────────
extractor:
  # type selects the extraction back-end.  The prototype implements python_function;
  # the others are planned.
  type: python_function     # | regex_scan | lean_scan | subprocess

  # python_function: import module from scripts/ and call function(**args).
  # The return value is passed directly to serialization.
  module: string            # Python module name (on sys.path = scripts/)
  function: string          # callable inside that module
  args: {}                  # optional keyword args forwarded to the function

  # regex_scan (planned): read source_globs files and extract via regex groups.
  # pattern: string
  # group: int | string

  # lean_scan (planned): invoke a Lean elaborator query to extract data.
  # query: string

  # subprocess (planned): run a shell command and capture stdout as the value.
  # command: [string]

# ── Serialization ─────────────────────────────────────────────────────────────
output_format: json         # | text | lean

# Options applied when output_format == json:
json_options:
  indent: 2                 # indentation width
  sort_keys: false          # whether to sort dict keys (matches original script)

# ── Target ───────────────────────────────────────────────────────────────────
target: string              # output path relative to repo root

# ── Original script reference ────────────────────────────────────────────────
# Not used by the engine; documents which script this rule replaces.
original_script: string
```

### Full field reference

| Field | Type | Required | Default | Notes |
|-------|------|----------|---------|-------|
| `id` | string | yes | — | kebab-case, used as `--rule` arg |
| `description` | string | yes | — | shown in `--list` |
| `cluster` | string | yes | — | one of 9 families |
| `source_globs` | list[str] | no | `[]` | for incremental/cache use |
| `extractor.type` | enum | yes | `python_function` | see below |
| `extractor.module` | string | if `python_function` | — | module on `scripts/` path |
| `extractor.function` | string | if `python_function` | — | function to call |
| `extractor.args` | dict | no | `{}` | kwargs forwarded to function |
| `output_format` | enum | no | `json` | `json`, `text`, `lean` |
| `json_options.indent` | int | no | `2` | JSON indent width |
| `json_options.sort_keys` | bool | no | `false` | sort JSON keys |
| `target` | string | yes | — | output path (repo-root relative) |
| `original_script` | string | no | — | documentary only |

---

## Mapping: 4 Representative Scripts → Schema

### 1. `generate_verify_sync_spec.py` → rule `verify-sync-spec`

The simplest rule: one Python function returns a dict; write as JSON.

```yaml
- id: verify-sync-spec
  description: "Regenerate verify workflow sync spec from authoritative Python module"
  cluster: artifact-generator
  source_globs:
    - scripts/verify_sync_spec_source.py
  extractor:
    type: python_function
    module: verify_sync_spec_source
    function: build_spec
  output_format: json
  json_options:
    indent: 2
    sort_keys: false          # original preserves insertion order
  target: scripts/verify_sync_spec.json
  original_script: scripts/generate_verify_sync_spec.py
```

Original logic condensed: `json.dumps(build_spec(), indent=2) + "\n"`.

---

### 2. `generate_layer2_boundary_catalog.py` → rule `layer2-catalog`

Same pattern, with `sort_keys: true` and a different extractor.

```yaml
- id: layer2-catalog
  description: "Regenerate Layer 2 proof-boundary catalog from hardcoded Python dict"
  cluster: artifact-generator
  source_globs:
    - scripts/generate_layer2_boundary_catalog.py
  extractor:
    type: python_function
    module: generate_layer2_boundary_catalog
    function: build_catalog
  output_format: json
  json_options:
    indent: 2
    sort_keys: true
  target: artifacts/layer2_boundary_catalog.json
  original_script: scripts/generate_layer2_boundary_catalog.py
```

Original logic: `json.dumps(build_catalog(), indent=2, sort_keys=True) + "\n"`.

---

### 3. `generate_verification_status.py` → rule `verification-status`

Extractor scans live Lean + test files; serialization identical to case 2.

```yaml
- id: verification-status
  description: "Regenerate verification status artifact from live repository metrics"
  cluster: artifact-generator
  source_globs:
    - Compiler/**/*.lean
    - Verity/**/*.lean
    - Contracts/**/*.lean
    - test/property_manifest.json
    - test/property_exclusions.json
  extractor:
    type: python_function
    module: verification_metrics
    function: collect_metrics
  output_format: json
  json_options:
    indent: 2
    sort_keys: true
  target: artifacts/verification_status.json
  original_script: scripts/generate_verification_status.py
```

---

### 4. `check_verification_status_doc.py` — a `doc-sync` check rule

Not yet implemented in the prototype, but mapped here to illustrate the
`check`-only mode and a `regex_scan` extractor (planned).

```yaml
- id: verification-status-doc
  description: "Check VERIFICATION_STATUS.md text matches the status artifact"
  cluster: doc-sync
  source_globs:
    - artifacts/verification_status.json
    - docs/VERIFICATION_STATUS.md
  extractor:
    type: python_function
    module: check_verification_status_doc
    function: collect_doc_assertions   # planned refactor of main()
  output_format: text
  target: docs/VERIFICATION_STATUS.md
  original_script: scripts/check_verification_status_doc.py
  # NOTE: for check-only rules, mode is fixed to "check" and target is read-only.
  # The engine validates that the file already contains the expected content
  # rather than writing it.
```

---

## Planned Extensions

### `mode` field

Some rules should only ever `generate` (scaffolding) or only ever `check` (doc
validation). A future `mode` field constrains which operations are valid:

```yaml
mode: generate | check | both   # default: both
```

`generate_contract.py` would be `mode: generate` (writes scaffold, never checks).
`check_lean_hygiene.py` would be `mode: check` (reads only, never writes).

### `extractor.type: regex_scan`

For the 11 `doc-sync` scripts that extract snippets via regex from docs and
compare against artifact values, a `regex_scan` extractor would avoid needing
to refactor each original module:

```yaml
extractor:
  type: regex_scan
  files:
    - docs/VERIFICATION_STATUS.md
  patterns:
    total_theorems: '^\| Total\s*\|\s*(\d+)\s*\|'
    coverage_pct:   'Coverage:\s*([\d.]+)%'
```

The engine would return a dict of captured groups for comparison.

### Multi-target rules

`generate_evmyullean_capability_report.py` writes two artifacts atomically.
A `targets` list (plural) would handle this:

```yaml
targets:
  - path: artifacts/evmyullean_capability_report.json
    key: report
  - path: artifacts/evmyullean_unsupported_nodes.json
    key: unsupported_nodes
```

The extractor returns `{"report": {...}, "unsupported_nodes": {...}}` and the
engine routes each key to its target file.

---

## Migration Path

1. **Phase 1 (this PR)** — prototype engine runs the 3 simplest
   `artifact-generator` rules; proves the abstraction is valid.
2. **Phase 2** — convert remaining `artifact-generator` scripts (7 left)
   into rules; delete original scripts after CI green.
3. **Phase 3** — implement `regex_scan` extractor; convert `doc-sync` cluster
   (11 scripts) to declarative rules with no Python logic.
4. **Phase 4** — implement `lean_scan` and `subprocess` extractors;
   convert `axiom-audit`, `selector-gas`, and `workflow-ci` clusters.
5. **Phase 5** — `compiler-boundary`, `package-imports`, `storage-layout`,
   `coverage` — most complex; likely need composite rules or runner delegation.

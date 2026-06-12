"""Helpers for reading the interpreter feature matrix.

The matrix used to expose the source proof paths as SpecInterpreter_* keys.  The
SpecInterpreter module no longer exists, so current artifacts use
SourceInterpreter_* names while this reader still accepts the old keys in local
fixtures and downstream one-shot migration checks.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

CANONICAL_INTERPRETER_KEYS = ("SourceInterpreter_basic", "SourceInterpreter_fuel")
LEGACY_INTERPRETER_KEYS = {
    "SpecInterpreter_basic": "SourceInterpreter_basic",
    "SpecInterpreter_fuel": "SourceInterpreter_fuel",
}


def canonical_interpreter_key(key: str) -> str:
    return LEGACY_INTERPRETER_KEYS.get(key, key)


def normalize_feature_matrix(matrix: dict[str, Any]) -> dict[str, Any]:
    interpreters = matrix.get("interpreters")
    if isinstance(interpreters, dict):
        for legacy, canonical in LEGACY_INTERPRETER_KEYS.items():
            if legacy in interpreters and canonical not in interpreters:
                interpreters[canonical] = interpreters.pop(legacy)
            elif legacy in interpreters:
                interpreters.pop(legacy)

    default_path = matrix.get("default_execution_path")
    if isinstance(default_path, str):
        matrix["default_execution_path"] = canonical_interpreter_key(default_path)

    for section in ("expr_features", "stmt_features"):
        entries = matrix.get(section)
        if not isinstance(entries, list):
            continue
        for entry in entries:
            if not isinstance(entry, dict):
                continue
            for legacy, canonical in LEGACY_INTERPRETER_KEYS.items():
                if legacy in entry and canonical not in entry:
                    entry[canonical] = entry.pop(legacy)
                elif legacy in entry:
                    entry.pop(legacy)

    return matrix


def load_feature_matrix(path: Path) -> dict[str, Any]:
    matrix = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(matrix, dict):
        raise ValueError("interpreter feature matrix must be a JSON object")
    return normalize_feature_matrix(matrix)


def interpreter_status(entry: dict[str, Any], key: str) -> Any:
    return entry.get(canonical_interpreter_key(key))

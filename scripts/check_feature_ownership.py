#!/usr/bin/env python3
"""Validate the feature ownership artifact."""

from __future__ import annotations

import json
from pathlib import Path

from property_utils import ROOT, die

ARTIFACT = ROOT / "artifacts" / "feature_ownership.json"
REQUIRED_FIELDS = {
    "id",
    "name",
    "owner",
    "source_supported",
    "compile_supported",
    "proof_modeled",
    "trust_reported",
    "deprecated",
    "canonical_entrypoints",
    "notes",
}


def main() -> None:
    try:
        data = json.loads(ARTIFACT.read_text(encoding="utf-8"))
    except Exception as exc:
        die(f"{ARTIFACT}: invalid JSON: {exc}")

    statuses = set(data.get("status_values", []))
    if not statuses:
        die("feature ownership artifact is missing status_values")

    surfaces = data.get("surfaces")
    if not isinstance(surfaces, list) or not surfaces:
        die("feature ownership artifact must contain a non-empty surfaces list")

    seen: set[str] = set()
    errors: list[str] = []
    for index, surface in enumerate(surfaces):
        if not isinstance(surface, dict):
            errors.append(f"surface #{index} is not an object")
            continue
        missing = REQUIRED_FIELDS - set(surface)
        if missing:
            errors.append(f"{surface.get('id', f'surface #{index}')}: missing {', '.join(sorted(missing))}")
            continue
        surface_id = surface["id"]
        if not isinstance(surface_id, str) or not surface_id:
            errors.append(f"surface #{index}: id must be a non-empty string")
        elif surface_id in seen:
            errors.append(f"{surface_id}: duplicate id")
        else:
            seen.add(surface_id)
        for field in ("source_supported", "compile_supported", "proof_modeled", "trust_reported"):
            if surface[field] not in statuses:
                errors.append(f"{surface_id}: {field} has unknown status {surface[field]!r}")
        if not isinstance(surface["deprecated"], bool):
            errors.append(f"{surface_id}: deprecated must be boolean")
        entrypoints = surface["canonical_entrypoints"]
        if not isinstance(entrypoints, list) or not entrypoints:
            errors.append(f"{surface_id}: canonical_entrypoints must be a non-empty list")
        elif not all(isinstance(path, str) and path for path in entrypoints):
            errors.append(f"{surface_id}: canonical_entrypoints must contain non-empty strings")

    expected_ids = {
        "source_internal_helpers",
        "typed_external_interface_calls",
        "low_level_call_returndata",
        "foreach_positive_nonempty",
        "legacy_spec_aliases",
        "patched_compiler_entrypoint",
        "external_call_with_return_ecm_name",
    }
    missing_expected = expected_ids - seen
    if missing_expected:
        errors.append(f"missing expected surfaces: {', '.join(sorted(missing_expected))}")

    if errors:
        die("\n".join(errors))
    print(f"Feature ownership artifact ok: {len(surfaces)} surfaces")


if __name__ == "__main__":
    main()

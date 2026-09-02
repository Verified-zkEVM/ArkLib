#!/usr/bin/env python3
"""Write and validate attribution metadata for ArkLib build-timing artifacts."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import pathlib
import re
import subprocess
from typing import Any


SCHEMA_VERSION = 1
SHA_PATTERN = re.compile(r"^[0-9a-f]{40}$")


class MetadataError(ValueError):
    """Raised when timing metadata is malformed or uses an unsupported schema."""


def _optional_string(value: str | None) -> str | None:
    return value if value else None


def _optional_sha(value: str | None, field: str) -> str | None:
    value = _optional_string(value)
    if value is not None and not SHA_PATTERN.fullmatch(value):
        raise MetadataError(f"{field} must be a 40-character lowercase Git SHA")
    return value


def _parse_optional_bool(value: str | None) -> bool | None:
    if not value:
        return None
    lowered = value.lower()
    if lowered == "true":
        return True
    if lowered == "false":
        return False
    raise MetadataError("BUILD_TIMING_CACHE_EXACT_HIT must be true, false, or empty")


def _positive_int(value: str | int | None, field: str, *, optional: bool = False) -> int | None:
    if value is None and optional:
        return None
    if isinstance(value, bool):
        raise MetadataError(f"{field} must be a positive integer")
    try:
        parsed = int(value)  # type: ignore[arg-type]
    except (TypeError, ValueError) as error:
        raise MetadataError(f"{field} must be a positive integer") from error
    if parsed <= 0:
        raise MetadataError(f"{field} must be a positive integer")
    return parsed


def _string(value: Any, field: str, *, optional: bool = False) -> str | None:
    if value is None and optional:
        return None
    if not isinstance(value, str) or not value:
        raise MetadataError(f"{field} must be a non-empty string")
    return value


def _mapping(value: Any, field: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise MetadataError(f"{field} must be an object")
    return value


def _checkout_sha() -> str:
    supplied = os.environ.get("BUILD_TIMING_CHECKOUT_SHA")
    if supplied:
        return supplied
    return subprocess.run(
        ["git", "rev-parse", "HEAD"],
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()


def _manifest_sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def build_metadata() -> dict[str, Any]:
    manifest_path = pathlib.Path(os.environ.get("BUILD_TIMING_MANIFEST", "lake-manifest.json"))
    if not manifest_path.is_file():
        raise MetadataError(f"dependency manifest not found: {manifest_path}")

    metadata = {
        "schema_version": SCHEMA_VERSION,
        "run": {
            "id": _positive_int(os.environ.get("BUILD_TIMING_RUN_ID"), "run.id"),
            "attempt": _positive_int(
                os.environ.get("BUILD_TIMING_RUN_ATTEMPT"), "run.attempt"
            ),
            "event": _string(os.environ.get("BUILD_TIMING_EVENT"), "run.event"),
        },
        "git": {
            "head_sha": _optional_sha(os.environ.get("BUILD_TIMING_HEAD_SHA"), "git.head_sha"),
            "checkout_sha": _optional_sha(_checkout_sha(), "git.checkout_sha"),
            "base_sha": _optional_sha(os.environ.get("BUILD_TIMING_BASE_SHA"), "git.base_sha"),
            "ref": _string(os.environ.get("BUILD_TIMING_REF"), "git.ref"),
        },
        "dependencies": {
            "lake_manifest_sha256": _manifest_sha256(manifest_path),
        },
        "cache": {
            "primary_key": _optional_string(os.environ.get("BUILD_TIMING_CACHE_PRIMARY_KEY")),
            "matched_key": _optional_string(os.environ.get("BUILD_TIMING_CACHE_MATCHED_KEY")),
            "exact_hit": _parse_optional_bool(os.environ.get("BUILD_TIMING_CACHE_EXACT_HIT")),
        },
        "runner": {
            "os": _string(os.environ.get("RUNNER_OS"), "runner.os"),
            "arch": _string(os.environ.get("RUNNER_ARCH"), "runner.arch"),
            "image_os": _optional_string(os.environ.get("ImageOS")),
            "image_version": _optional_string(os.environ.get("ImageVersion")),
            "cores": os.cpu_count(),
        },
    }
    return validate_metadata(metadata)


def validate_metadata(value: Any) -> dict[str, Any]:
    root = _mapping(value, "metadata")
    if root.get("schema_version") != SCHEMA_VERSION:
        raise MetadataError(
            f"unsupported timing metadata schema {root.get('schema_version')!r}; "
            f"expected {SCHEMA_VERSION}"
        )

    run = _mapping(root.get("run"), "run")
    git = _mapping(root.get("git"), "git")
    dependencies = _mapping(root.get("dependencies"), "dependencies")
    cache = _mapping(root.get("cache"), "cache")
    runner = _mapping(root.get("runner"), "runner")

    _positive_int(run.get("id"), "run.id")
    _positive_int(run.get("attempt"), "run.attempt")
    _string(run.get("event"), "run.event")
    _optional_sha(git.get("head_sha"), "git.head_sha")
    _optional_sha(git.get("checkout_sha"), "git.checkout_sha")
    _optional_sha(git.get("base_sha"), "git.base_sha")
    _string(git.get("ref"), "git.ref")

    manifest_hash = _string(
        dependencies.get("lake_manifest_sha256"), "dependencies.lake_manifest_sha256"
    )
    if manifest_hash is None or not re.fullmatch(r"[0-9a-f]{64}", manifest_hash):
        raise MetadataError("dependencies.lake_manifest_sha256 must be a SHA-256 digest")

    for field in ("primary_key", "matched_key"):
        if cache.get(field) is not None:
            _string(cache.get(field), f"cache.{field}")
    if cache.get("exact_hit") is not None and not isinstance(cache.get("exact_hit"), bool):
        raise MetadataError("cache.exact_hit must be true, false, or null")

    _string(runner.get("os"), "runner.os")
    _string(runner.get("arch"), "runner.arch")
    for field in ("image_os", "image_version"):
        if runner.get(field) is not None:
            _string(runner.get(field), f"runner.{field}")
    _positive_int(runner.get("cores"), "runner.cores", optional=True)
    return root


def load_metadata(path: pathlib.Path) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise MetadataError(f"cannot read timing metadata: {error}") from error
    return validate_metadata(value)


def write_metadata(path: pathlib.Path) -> None:
    metadata = build_metadata()
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(metadata, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=pathlib.Path, help="metadata JSON output path")
    args = parser.parse_args()
    try:
        write_metadata(args.output)
    except (MetadataError, OSError, subprocess.CalledProcessError) as error:
        parser.error(str(error))


if __name__ == "__main__":
    main()

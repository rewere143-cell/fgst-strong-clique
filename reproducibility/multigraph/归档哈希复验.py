"""Verify the byte counts and SHA-256 hashes in the fixed phase manifest."""

import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parent


def digest(path):
    with path.open("rb") as contents:
        return hashlib.file_digest(contents, "sha256").hexdigest()


def main():
    manifest = json.loads((ROOT / "阶段核验清单.json").read_bytes())
    failures = []
    for name, expected in manifest["files"].items():
        path = (ROOT / name).resolve()
        if not path.is_relative_to(ROOT):
            failures.append(f"Unsafe path: {name}")
        elif not path.is_file():
            failures.append(f"Missing: {name}")
        elif path.stat().st_size != expected["bytes"] or digest(path) != expected["sha256"]:
            failures.append(f"Digest differs: {name}")
    if failures:
        raise SystemExit("\n".join(failures))
    print(json.dumps({"version": manifest["version"], "files_verified": len(manifest["files"])}))


if __name__ == "__main__":
    main()

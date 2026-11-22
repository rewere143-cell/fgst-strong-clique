"""Verify the extra replay dependencies and entry points in this snapshot."""

import hashlib
import json
from pathlib import Path


def main():
    root = Path(__file__).resolve().parent
    files = json.loads((root / "SUPPLEMENTAL_SHA256.json").read_bytes())
    for relative, expected in files.items():
        path = (root / relative).resolve()
        if not path.is_relative_to(root) or not path.is_file():
            raise SystemExit(f"Missing or invalid path: {relative}")
        with path.open("rb") as stream:
            digest = hashlib.file_digest(stream, "sha256").hexdigest()
        if path.stat().st_size != expected["bytes"] or digest != expected["sha256"]:
            raise SystemExit(f"Digest differs: {relative}")
    print(json.dumps({"supplemental_files_verified": len(files)}))


if __name__ == "__main__":
    main()


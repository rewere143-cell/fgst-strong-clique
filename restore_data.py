"""Verify the v1.0.0 release ZIPs and restore the proof inputs at their original paths."""
import argparse
import hashlib
import json
import os
from pathlib import Path
from tempfile import NamedTemporaryFile
from zipfile import ZipFile


ROOT = Path(__file__).resolve().parent


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def restore_member(archive, info, expected, verify_only):
    target = (ROOT / info.filename).resolve()
    if not target.is_relative_to(ROOT / "reproducibility") or info.file_size != expected["bytes"]:
        raise ValueError(f"Unexpected archive member: {info.filename}")
    if not verify_only and target.exists():
        if not target.is_file() or digest(target) != expected["sha256"]:
            raise ValueError(f"An existing file differs: {target}")
        return
    output = None
    partial = None
    try:
        if not verify_only:
            target.parent.mkdir(parents=True, exist_ok=True)
            output = NamedTemporaryFile(dir=target.parent, delete=False)
            partial = Path(output.name)
        sha = hashlib.sha256()
        with archive.open(info) as source:
            while block := source.read(1024 * 1024):
                sha.update(block)
                if output:
                    output.write(block)
        if sha.hexdigest() != expected["sha256"]:
            raise ValueError(f"Incorrect SHA-256: {info.filename}")
        if output:
            output.close()
            os.replace(partial, target)
    finally:
        if output:
            output.close()
            partial.unlink(missing_ok=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("downloads", type=Path, help="directory containing all three release ZIPs")
    parser.add_argument("--verify-only", action="store_true", help="check the archives and members without extracting")
    args = parser.parse_args()
    manifest = json.loads((ROOT / "release-data.json").read_bytes())
    for part in manifest["archives"]:
        path = args.downloads / part["name"]
        if path.stat().st_size != part["bytes"] or digest(path) != part["sha256"]:
            raise ValueError(f"Incorrect archive: {path}")
        expected = {key: item for key, item in manifest["files"].items() if item["archive"] == part["name"]}
        with ZipFile(path) as archive:
            if set(archive.namelist()) != set(expected) or len(archive.infolist()) != len(expected):
                raise ValueError(f"Incorrect list of files: {path}")
            for info in archive.infolist():
                restore_member(archive, info, expected[info.filename], args.verify_only)
        print(f"Verified {path.name} ({len(expected)} files)", flush=True)


if __name__ == "__main__":
    main()

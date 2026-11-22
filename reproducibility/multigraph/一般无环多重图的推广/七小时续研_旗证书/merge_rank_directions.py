"""Build a reusable numerical search seed from exact rank-one certificates."""
import argparse
import json
from math import fsum, sqrt
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("directions", type=Path)
    parser.add_argument("certificates", nargs="+", type=Path)
    args = parser.parse_args()
    directions = json.loads(args.directions.read_bytes())
    by_block = {}
    for block, direction in directions:
        by_block.setdefault(block, []).append(direction)
    for file in args.certificates:
        for block, directions_for_block in enumerate(json.loads(file.read_bytes())["gram_squared_vectors"]):
            existing = by_block.setdefault(block, [])
            for direction in directions_for_block:
                norm = sqrt(fsum(v*v for v in direction))
                if norm == 0:
                    continue
                unit = [v/norm for v in direction]
                if any(abs(fsum(a*b for a,b in zip(unit, old))) >= 1-1e-10
                       for old in existing if len(unit) == len(old)):
                    continue
                directions.append([block, unit])
                existing.append(unit)
    args.output.write_text(json.dumps(directions,separators=(",",":"))+"\n", encoding="utf-8")
    print(f"Merged {len(directions)} directions.")


if __name__ == "__main__":
    main()

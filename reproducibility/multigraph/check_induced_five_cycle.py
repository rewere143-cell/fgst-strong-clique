"""Check the strict bound on m/D^2 when the support has no induced red five-cycle."""
from fractions import Fraction
import json
import os

from verify import MULTI, run


def main():
    if not __debug__ or os.environ.get("PYTHONOPTIMIZE"):
        raise SystemExit("Run this verifier with Python assertions enabled.")
    output = run(
        MULTI, "multigraph_low_repeat_search.py", "multigraph_weighted_maxdeg_5",
        "--replay", "--certificate", "absence_c5_mass_98_81.json", capture=True,
    )
    result = json.loads(output)
    if result["mode"] != "bound":
        raise RuntimeError("The certificate did not return a bound.")
    bound = Fraction(result["rational_bound"])
    if bound >= Fraction(98, 81):
        raise RuntimeError(f"The verified upper bound {bound} does not exclude 98/81.")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()

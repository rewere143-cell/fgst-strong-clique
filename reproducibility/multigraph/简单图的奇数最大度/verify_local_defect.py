"""Replay the auxiliary 9/20 local-defect penalty in exact arithmetic."""

from fractions import Fraction
from pathlib import Path
import importlib.util
import json

ROOT = Path(__file__).resolve().parent
CERTIFICATE = ROOT / "local_defect_045_certificate.json"
BASE_VERIFIER = ROOT / "source_snapshot/reproducibility/verifiers/check_certificate.py"
EXPECTED_SHA256 = "382d140a2d6bb1d94117566c1f5fcfc372c795d76224637022a074822af7c798"


def main():
    spec = importlib.util.spec_from_file_location("pinned_certificate_verifier", BASE_VERIFIER)
    verifier = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(verifier)
    report = verifier.verify(CERTIFICATE)
    if report["certificate_sha256"] != EXPECTED_SHA256:
        raise ValueError("Unexpected auxiliary certificate hash")
    common = int(report["common_denominator"])
    rows = report["order_three_defect_residual_numerators"]
    if set(rows) != {"0", "2", "3", "4"}:
        raise ValueError("Unexpected defect coordinates")
    residual = {key: Fraction(int(numerator), common) for key, numerator in rows.items()}
    if min(residual.values()) < Fraction(9, 20):
        raise ValueError("The stated 9/20 penalty is not certified")
    print(json.dumps(
        {"certificate": report, "penalty": "9/20",
         "defect_residuals": {key: str(value) for key, value in residual.items()}},
        indent=2,
    ))


if __name__ == "__main__":
    main()


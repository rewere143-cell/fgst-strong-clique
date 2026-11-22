"""Replay the frozen certificates used by the loopless multigraph manuscript."""

import argparse
from fractions import Fraction
import json
import os
from pathlib import Path
import subprocess
import sys


HERE = Path(__file__).resolve().parent
MULTI = HERE / "一般无环多重图的推广"
SIMPLE = HERE / "简单图的奇数最大度"
UNIFORM = MULTI / "三小时续研_旗证书"
PARITY = MULTI / "七小时续研_旗证书"
ODD_SAT = MULTI / "七小时续研_奇偶变换"
ORDER23_OLD = MULTI / "三小时续研_有限度数"
ORDER23_NEW = MULTI / "七小时续研_有限度数"
ANCHORS = MULTI / "三小时续研_九度矩"

FIVE_POSITION = (
    ("multigraph_weighted_maxdeg_general_bound.json", "1.2895"),
    ("multigraph_weighted_maxdeg_high_exclusion.json", "0"),
    ("multigraph_weighted_maxdeg_upper23.json", "0"),
    ("multigraph_weighted_maxdeg_upper225.json", "0"),
    ("multigraph_weighted_maxdeg_upper21875.json", "0"),
    ("multigraph_weighted_maxdeg_mide20_bound.json", "1.2583"),
    ("multigraph_weighted_maxdeg_refit_upper2155.json", "0"),
    ("multigraph_maxdeg5_sample_2125_certificate.json", "1.25"),
    ("multigraph_maxdeg5_sample_21125_refit_certificate.json", "1.25"),
    ("multigraph_maxdeg5_sample_2105_local_refit_certificate.json", "1.25"),
    ("multigraph_maxdeg5_extra_refit_certificate.json", "1.28829"),
    ("multigraph_maxdeg5_extra_near_best_certificate.json", "1.28756"),
    ("multigraph_weighted_maxdeg_mass_refit_1287.json", "1.28746"),
    ("multigraph_maxdeg5_support_near_best_certificate.json", "1.287448"),
    ("multigraph_maxdeg5_sample_odd_124175_refit_certificate.json", "0"),
)
R7_SHAPES = (
    "s01033", "s01105", "s01114", "s01123", "s01132", "s01204", "s01213",
    "s01222", "s01231", "s01303", "s01312", "s01402", "s02023", "s02113",
    "s02122", "s02203",
)


def run(directory, script, *args, capture=False):
    command = [sys.executable, "-X", "utf8", "-B", str(script), *map(str, args)]
    print(f"\n{directory.relative_to(HERE)} / {script} {' '.join(map(str, args))}", flush=True)
    result = subprocess.run(command, cwd=directory, check=True, encoding="utf-8",
                            stdout=subprocess.PIPE if capture else None)
    if capture:
        print(result.stdout, end="", flush=True)
        return result.stdout


def check_flags():
    for name, target in FIVE_POSITION:
        output = run(MULTI, "multigraph_weighted_maxdeg_exact.py",
                     "multigraph_weighted_maxdeg_5", name, capture=True)
        report = json.loads(output)
        assert Fraction(report["rational_bound"]) < Fraction(target), name
        assert target != "0" or report["rigorous_infeasible"], name
    for name in ("baseline_half_refit.json", "direct_half_refit.json"):
        run(UNIFORM, "half_anchor_flag.py", name, "--replay")
    run(UNIFORM, "verify_shadow_chain.py")
    run(PARITY, "replay_parity_family.py")


def check_pentagon(directory, *args, count):
    output = run(MULTI, ODD_SAT / "d9_pentagon.py", "--out", ODD_SAT / directory,
                 "--strengthen", "--verify", *args, capture=True)
    report = json.loads(output.splitlines()[-1])
    assert report == {"cases": count, "verified": count, "unresolved": []}, report


def check_finite(jobs):
    output = run(SIMPLE, "d5_check_lrat.py", "d5_sat", capture=True)
    assert json.loads(output)["verified"] == 48
    output = run(MULTI, "d5_parallel_spoke_bound.py", capture=True)
    report = json.loads(output)
    assert report["template_count"] == 21 and report["maximum_upper_bound"] == 27
    run(MULTI, "d7_verify_parallel.py", "--jobs", jobs)

    env_path = os.environ.get("PYTHONPATH")
    os.environ["PYTHONPATH"] = (str(MULTI) if not env_path else
                               os.pathsep.join((str(MULTI), env_path)))
    output = run(ORDER23_OLD, "d9_order23_blue_chain_sat.py", "--out",
                 "d9_order23_blue_chain", "--verify", "--shape", "matching", "star", "path",
                 "twopaths", "path9", "matching10", capture=True)
    report = json.loads(output[output.index("{"):])
    assert len(report) == 18 and set(report.values()) == {"VERIFIED_UNSAT"}
    output = run(ORDER23_NEW, "d9_blue_ferrers_sat.py", "--out", "chain_n23_broad",
                 "--verify", "--jobs", jobs, capture=True)
    report = json.loads(output[output.index("{"):])
    assert len(report) == 112 and set(report.values()) == {"VERIFIED_UNSAT"}

    output = run(ANCHORS, "d9_anchor_cases.py", "--verify", capture=True)
    report = json.loads(output.splitlines()[-1])
    assert report["cases"] == 60 and not report["unresolved"]
    # The independent two-bundle triangle-free argument also reuses the one-bundle projection input.
    run(ODD_SAT, "verify_d9_two_bundles.py", "--jobs", jobs)
    check_pentagon("d9_b1_triangle", "--degree", 9, "--bundles", 1, "--triangles",
                   "require", "--min-order", 24, "--max-order", 25, "--select", "s11212", count=1)
    check_pentagon("d11_b1", "--degree", 11, "--bundles", 1, "--triangles", "allow",
                   "--min-order", 27, "--select", "s11212", count=1)

    output = run(ANCHORS, "-c",
                 "import d9_anchor_cases as a; print(*[a.case_name(s) for s in a.patterns(9)"
                 " if not a.counted_out(s)], sep=chr(10))", capture=True)
    r9_shapes = tuple(output.splitlines())
    assert len(r9_shapes) == 44
    for degree, shapes, no_triangle, triangle in (
        (7, R7_SHAPES, "d9_r7_zero_triangle_free", "d9_r7_zero_triangle"),
        (9, r9_shapes, "d9_r9_triangle_free", "d9_r9_triangle"),
    ):
        type_args = ("--bundles", 0, "--min-order", 24, "--capacity-cuts", "--jobs", jobs,
                     "--select", *shapes)
        check_pentagon(no_triangle, *type_args, count=len(shapes))
        check_pentagon(triangle, "--triangles", "require", "--max-order", 25,
                       *type_args, count=len(shapes))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("section", choices=("hashes", "flags", "finite", "all"))
    parser.add_argument("--vendor", type=Path, help="optional directory containing NumPy and SciPy")
    parser.add_argument("--jobs", type=int, default=1, help="parallel finite proof cases")
    args = parser.parse_args()
    if not __debug__ or os.environ.get("PYTHONOPTIMIZE"):
        parser.error("replay requires Python assertions")
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    if args.vendor:
        inherited = os.environ.get("PYTHONPATH")
        paths = [str(args.vendor.resolve())]
        if inherited:
            paths.append(inherited)
        os.environ["PYTHONPATH"] = os.pathsep.join(paths)

    if args.section in ("hashes", "all"):
        run(HERE, "归档哈希复验.py")
        run(HERE, "verify_supplemental_hashes.py")
    if args.section in ("flags", "all"):
        check_flags()
    if args.section in ("finite", "all"):
        check_finite(args.jobs)
    print(f"\nPASS {args.section}", flush=True)


if __name__ == "__main__":
    main()


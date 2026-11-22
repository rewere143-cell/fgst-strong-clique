"""Fixed-CNF search and replay for the five-bundle maximum-degree-eight case."""

import argparse
from fractions import Fraction
from itertools import combinations
import json
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory
from types import SimpleNamespace

HERE = Path(__file__).resolve().parent
BASE = HERE.parent
sys.path.insert(0, str(BASE))

from check_c5_dual import verify as verify_moment
from d7_parallel_sat import file_digest
from d7_verify_parallel import unpack
from d8_anchored_sat import instance, replay as replay_legacy, slack_patterns
from d8_parallel_sat import bounded_solve, gzip_file


DEGREE = 8
MARKS = 81
BUNDLES = 5
LEGACY = BASE / "d8_anchor_b5"
SLACK_CASES = (6, 8)


def verify_slack_cap():
    """Check the triangle-free projection certificate and its finite slack cap."""
    conditional_path = HERE / "triangle_free_projection_3_2.json"
    conditional = verify_moment(conditional_path, triangle_free=True, max_error=Fraction(1, 500))
    assert conditional["mode"] == "conditional"
    assert Fraction(conditional["anchor_ratio"]) == Fraction(3, 2)
    gamma = Fraction(conditional["gamma"])
    epsilon = Fraction(conditional["epsilon"])
    deficit = Fraction(1, 16)
    q_upper = Fraction(16, 27) * Fraction(186, 625)
    contradiction = gamma * (Fraction(3, 16) - q_upper / 4) - epsilon
    assert contradiction > deficit
    return {
        "projection_size": MARKS - BUNDLES,
        "slack_maximum": 8,
        "conditional_sha256": conditional["candidate_sha256"],
        "q_upper": str(q_upper),
        "gamma": str(gamma),
        "epsilon": str(epsilon),
        "deficit_required_if_all_slacks_at_least_10": str(contradiction),
    }


def name(slack):
    return "s" + "".join(map(str, slack))


def part_sizes(slack):
    return [DEGREE // 2 - sum(slack) // 2 + slack[(i + 2) % 5] + slack[(i + 3) % 5]
            for i in range(5)]


def rotated_bounds(slack):
    sizes = part_sizes(slack)
    for i in range(5):
        opposite = (i + 3) % 5
        left, right = (i + 2) % 5, (i + 4) % 5
        required = MARKS - (DEGREE**2 + sizes[left] * sizes[right] - slack[i] * slack[(i + 1) % 5])
        yield i, opposite, required


def ruled_out(slack):
    return any(
        DEGREE * (slack[i] + slack[(i + 1) % 5]) < required
        for i, _, required in rotated_bounds(slack)
    )


def add_constraints(formula, slack, parts, core_order, edge, mark, double):
    no = -formula.truth
    n = len(parts)
    vertices = range(n)
    pairs = tuple(combinations(vertices, 2))

    def get(table, u, v):
        return no if u == v else table[min(u, v), max(u, v)]

    # Deleting any two vertices leaves at least 76-16=60 projected
    # marks. Hence some surviving vertex must still have simple degree 8.
    full_support = [
        formula.count([get(edge, u, v) for v in vertices if u != v], DEGREE)[DEGREE]
        for u in vertices
    ]
    for u, v in pairs:
        formula.clause(*(
            formula.conjunction(full_support[x],
                formula.conjunction(-get(edge, u, x), -get(edge, v, x)))
            for x in vertices if x not in (u, v) and full_support[x] != no
        ))

    # The opposite-part bound controls the distinct exterior witnesses
    # for each marked cycle edge and the number of marks remaining on
    # its opposite part together with the exterior.
    for i, opposite, required in rotated_bounds(slack):
        if required <= 0:
            continue
        witnesses = [
            formula.disjunction(get(edge, i, x), get(edge, (i + 1) % 5, x))
            for x in range(core_order, n)
        ]
        minimum = (required + DEGREE - 1) // DEGREE
        formula.clause(formula.count(witnesses, minimum)[minimum])
        remaining = [
            table[u, v] for table in (mark, double) for u, v in pairs
            if parts[u] in (-1, opposite) and parts[v] in (-1, opposite)
        ]
        formula.clause(formula.count(remaining, required)[required])

    # Missing marked consecutive pairs use two core degree units.
    missing = [-mark[u, v] for u, v in pairs if v < core_order
               and (parts[u] - parts[v]) % 5 in (1, 4)]
    repeat_at_anchors = [double[u, v] for u, v in pairs for x in (u, v) if x < 5]
    total = sum(slack)
    multiplier = total if total <= DEGREE else DEGREE
    upper = total * (multiplier - DEGREE // 2) - 2
    formula.at_most(missing * 2 + repeat_at_anchors * multiplier, upper)


def build(slack):
    return instance(slack, BUNDLES, strengthened=True, anchor_swaps=True,
                    extra_constraints=add_constraints)


def legacy_metadata(slack):
    path = LEGACY / (name(slack) + ".result.json")
    if path.exists():
        row = json.loads(path.read_bytes())
        if row.get("result") == "VERIFIED_UNSAT":
            assert row["bundles"] == BUNDLES and tuple(row["slack"]) == slack
            return row
    return None


def process(args, slack):
    case = name(slack)
    if ruled_out(slack):
        return dict(name=case, result="COUNTED_OUT")
    old = legacy_metadata(slack)
    if old:
        if args.verify:
            old = replay_legacy(SimpleNamespace(out=LEGACY, checker=args.checker,
                                               bundles=BUNDLES, scratch=args.scratch), slack)
        return dict(name=case, result="LEGACY_VERIFIED_UNSAT", replay=old["replay"])
    record = args.out / (case + ".json")
    archived = json.loads(record.read_bytes()) if record.exists() else None
    if args.verify:
        if not archived or archived["result"] != "VERIFIED_UNSAT":
            return dict(name=case, result="UNRESOLVED")
        with TemporaryDirectory(prefix="d8_b5_replay_", dir=args.scratch) as directory:
            work = Path(directory)
            cnf, generated, proof = (work / item for item in ("input.cnf", "new.cnf", "proof.lrat"))
            build(slack).dump(generated)
            assert unpack(args.out / (case + ".cnf.gz"), cnf) == archived["cnf_sha256"]
            assert file_digest(generated) == archived["cnf_sha256"]
            assert unpack(args.out / (case + ".lrat.gz"), proof) == archived["lrat_sha256"]
            run = subprocess.run([str(args.checker), cnf.name, proof.name],
                                 cwd=work, capture_output=True, text=True, check=True)
            assert json.loads(run.stdout) == archived["replay"]
        return archived
    if not args.solver or archived and archived["result"] == "VERIFIED_UNSAT":
        return archived or dict(name=case, result="UNRESOLVED")
    cnf, proof, log = (args.out / (case + suffix) for suffix in (".cnf", ".lrat", ".log"))
    formula = build(slack)
    formula.dump(cnf)
    code, limit = bounded_solve(args.solver, cnf, proof, log, args.seconds,
                                args.proof_mib * 1024**2)
    row = dict(name=case, result="SAT" if code == 10 else "UNRESOLVED", code=code,
               limit=limit, variables=formula.variables, clauses=len(formula.clauses))
    if code == 20:
        replay = subprocess.run([str(args.checker), cnf.name, proof.name], cwd=args.out,
                                capture_output=True, text=True)
        if replay.returncode == 0:
            row.update(result="VERIFIED_UNSAT", cnf_sha256=file_digest(cnf),
                       lrat_sha256=file_digest(proof), replay=json.loads(replay.stdout))
            gzip_file(cnf)
            gzip_file(proof)
        else:
            row.update(result="CHECKER_FAILED", replay_error=replay.stderr)
    if row["result"] == "UNRESOLVED" and proof.exists():
        proof.unlink()
    record.write_text(json.dumps(row, indent=2) + "\n", encoding="utf-8")
    return row


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--solver", type=Path)
    parser.add_argument("--checker", type=Path, default=BASE / "d7_rup_replay.exe")
    parser.add_argument("--out", type=Path, default=HERE / "proofs")
    parser.add_argument("--scratch", type=Path, default=HERE)
    parser.add_argument("--seconds", type=int, default=80)
    parser.add_argument("--proof-mib", type=int, default=100)
    parser.add_argument("--select", nargs="+")
    parser.add_argument("--report", type=Path)
    parser.add_argument("--verify", action="store_true")
    parser.add_argument("--inventory", action="store_true")
    args = parser.parse_args()
    if not __debug__:
        raise RuntimeError("Run with Python assertions enabled")
    args.out = args.out.resolve()
    args.checker = args.checker.resolve()
    args.scratch = args.scratch.resolve()
    if args.solver:
        args.solver = args.solver.resolve()
        args.out.mkdir(parents=True, exist_ok=True)
    cases = [slack for total in SLACK_CASES for slack in slack_patterns(total)
             if args.select is None or name(slack) in args.select]
    if args.inventory:
        for total in SLACK_CASES:
            candidates = [slack for slack in cases if sum(slack) == total]
            counts = (
                sum(ruled_out(slack) for slack in candidates),
                sum(not ruled_out(slack) and legacy_metadata(slack) is not None for slack in candidates),
            )
            print(total, len(candidates), *counts, len(candidates) - sum(counts))
        return
    moments = verify_slack_cap()
    results = []
    for slack in cases:
        row = process(args, slack)
        results.append(row)
        if row["result"] not in ("COUNTED_OUT", "LEGACY_VERIFIED_UNSAT"):
            print(row["name"], row["result"], row.get("limit") or "", flush=True)
    unresolved = [row["name"] for row in results
                  if row["result"] not in ("COUNTED_OUT", "LEGACY_VERIFIED_UNSAT", "VERIFIED_UNSAT")]
    report = dict(moment_inputs=moments, cases=len(results), unresolved=unresolved, results=results)
    if args.report:
        args.report.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k: v for k, v in report.items() if k != "results"}), flush=True)


if __name__ == "__main__":
    main()

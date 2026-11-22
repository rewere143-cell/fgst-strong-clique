"""Replay the exact arithmetic for the sharp simple-graph odd-degree bound."""
from fractions import Fraction as F
import json
import runpy

from check_c5_dual import HERE, verify
from check_anchored_odd_small import one_degree as small
from check_anchored_odd_signature import one_degree as signature
from check_anchored_odd_threshold import one_degree as threshold


def check_moment(file, coefficient, error):
    result = verify(HERE/file)
    assert F(result["gamma"]) >= coefficient
    assert F(result["epsilon"]) <= error
    print(json.dumps({
        "verified_certificate": file,
        "gamma": result["gamma"],
        "epsilon": result["epsilon"],
        "sha256": result["candidate_sha256"],
    }), flush=True)


def main():
    if not __debug__:
        raise RuntimeError("Run without -O/-OO or PYTHONOPTIMIZE")
    error = F(1, 10**9)
    gamma_c, gamma_r = F(99999, 100000), F(56425, 100000)
    check_moment("c5_abundance_column_candidate_third.json", gamma_c, 2*error)
    check_moment("c5_abundance_column_candidate_second.json", F(6449, 10000), error)
    check_moment("c5_anchor_column_candidate_fifth.json", gamma_r, error)
    for degree in range(3, 34, 2):
        failures = small(degree, gamma_c, gamma_r, 2*error, error, step=1, relax=True)
        assert not failures, (degree, failures)
        print(json.dumps({"verified_odd_degree": degree, "upper_bound": (5*degree**2-2*degree+1)//4}),
              flush=True)
    for degree in range(35, 150, 2):
        failure = signature(degree, F(54199, 100000), error, deficit_step=0)
        assert failure is None, (degree, failure)
    print('{"verified_odd_degrees":[35,149],"proof":"anchor signatures"}', flush=True)
    for degree in range(151, 50000, 2):
        failure = threshold(degree)
        assert failure is None, (degree, failure)
    print('{"verified_odd_degrees":[151,49999],"proof":"anchor capacities"}', flush=True)
    runpy.run_path(str(HERE/"check_two_stage_odd_constants.py"), run_name="__main__")
    print('{"finite_arithmetic_passed":true,"degree_one":"matching","large_degrees":"two_stage_odd.md"}',
          flush=True)


if __name__ == "__main__":
    main()


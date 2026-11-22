"""Replay the projection bounds implied by a lower bound on every C5 slack."""
import argparse
from fractions import Fraction as F
import json
from pathlib import Path
import sys


HERE = Path(__file__).resolve().parent
BASE = HERE.parent
sys.path.insert(0, str(BASE))

from check_c5_dual import verify


ABUNDANCE = ("c5_abundance_column_candidate_third.json", F(99999, 100000), F(2, 10**9))
ANCHOR = ("c5_anchor_column_candidate_sixth.json", F(2841, 5000), F(1, 10**9))
CONDITIONAL = ("c5_conditional_candidate_032_fourth.json", F(4897, 10000), F(2, 10**9), F(8, 25))
UNIFORM = F(5, 4)


def lower_slack(mass_lower, coupled=False):
    """Safe lower bound on R / D for a strict uniform counterexample."""
    assert UNIFORM <= mass_lower <= F(129, 100)
    gap = mass_lower - UNIFORM
    lo, hi = 5000, 10001
    while hi - lo > 1:
        j = (lo + hi) // 2
        candidate = F(j, 10000)
        loss = candidate * (2 * candidate - 1)
        if coupled:
            loss *= (1 + candidate)/(2 + candidate)
        if loss <= 4*gap:
            lo = j
        else:
            hi = j
    return F(lo, 10000)


def upper_lines(alpha, direct_gamma=None):
    """(C, beta) represents S + beta q_C <= C, in simple normalization."""
    assert F(1, 2) <= alpha <= 1
    _, gamma_c, epsilon_c = ABUNDANCE
    _, gamma_a, epsilon_a = ANCHOR
    _, gamma_k, epsilon_k, rho_k = CONDITIONAL
    result = [
        (UNIFORM, F(0)),
        (UNIFORM - gamma_c / 8 + epsilon_c, -gamma_c),
        (UNIFORM + epsilon_a, alpha * gamma_a),
        (UNIFORM - gamma_k * rho_k / 8 + epsilon_k, (alpha - rho_k) * gamma_k),
    ]
    if direct_gamma is not None:
        result.append((UNIFORM - direct_gamma / 16 + F(2, 10**9), (alpha - F(1, 2)) * direct_gamma))
    return result


def maximum_support(lines):
    crossings = [F(0)]
    for i, (a, b) in enumerate(lines):
        for c, d in lines[:i]:
            if b != d:
                q = (a - c) / (b - d)
                if q >= 0:
                    crossings.append(q)
    assert any(beta > 0 for _, beta in lines)
    return max((min(a - b * q for a, b in lines), q) for q in crossings)


def replay_input(name, mode, gamma, epsilon, rho=None):
    file = BASE / name if isinstance(name, str) else name
    result = verify(file)
    assert result["mode"] == mode and result["exact_integer_dual_verified"]
    assert F(result["gamma"]) >= gamma and F(result["epsilon"]) <= epsilon
    if rho is not None:
        candidate = json.loads(file.read_bytes())
        assert F(candidate["anchor_ratio"]) == rho
    return {key: result[key] for key in ("mode", "gamma", "epsilon", "candidate_sha256")}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mass-low", type=F, default=UNIFORM)
    parser.add_argument("--direct-certificate", type=Path)
    parser.add_argument("--direct-gamma", type=F)
    parser.add_argument("--coupled-slack", action="store_true")
    args = parser.parse_args()
    inputs = [
        replay_input(ABUNDANCE[0], "abundance", *ABUNDANCE[1:]),
        replay_input(ANCHOR[0], "anchor", *ANCHOR[1:]),
        replay_input(CONDITIONAL[0], "conditional", *CONDITIONAL[1:]),
    ]
    if args.direct_certificate is not None:
        assert args.direct_gamma is not None and args.direct_gamma > 0
        inputs.append(replay_input(args.direct_certificate, "conditional", args.direct_gamma,
                                   F(2, 10**9), F(1, 2)))
    else:
        assert args.direct_gamma is None
    alpha = lower_slack(args.mass_low, args.coupled_slack)
    support, q = maximum_support(upper_lines(alpha, args.direct_gamma))
    print(json.dumps({
        "verified": True, "inputs": inputs, "mass_lower": str(args.mass_low),
        "minimum_normalized_slack": str(alpha), "support_upper": str(support),
        "support_upper_decimal": float(support), "envelope_max_at": str(q),
        "support_deficit": str(UNIFORM - support),
        "required_repeat_fraction": str(1 - support / args.mass_low),
    }, indent=2))


if __name__ == "__main__":
    main()

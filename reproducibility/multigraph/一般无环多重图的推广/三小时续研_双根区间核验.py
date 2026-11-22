"""Exact four-variable checks for combined one- and two-root clique bounds."""

from fractions import Fraction as Q
import json


BETA = Q(186, 625)
ALPHA = (1 + BETA) / 4
TARGET = Q(1249, 1000)


def bound(box):
    (a_low, a_high), (b_low, b_high), (p_low, p_high), (q_low, q_high) = box
    # A capped interval also records b,p <= a and q <= b.
    b_high = min(b_high, a_high)
    p_high = min(p_high, a_high)
    q_high = min(q_high, b_high)
    if b_low > b_high or p_low > p_high or q_low > q_high:
        return None
    b_low = max(b_low, q_low)
    a_low = max(a_low, b_low, p_low)
    concave_point = min(a_high, max(a_low, Q(1, 2)))
    incident = p_high * b_high + concave_point * (1 - concave_point)
    two_roots = a_high * (2 - a_high) + min(
        p_high * q_high,
        a_high * q_high + min(Q(0), p_high - a_low) * b_low,
    )
    remaining_x = (2 - p_low)**2
    remaining_y = (2 - q_low)**2
    return min(
        two_roots,
        (two_roots + min(BETA * remaining_y, incident) + BETA * remaining_x) / 2,
        incident + ALPHA * remaining_x,
    )


def verify(name, maximum_a, maximum_p, maximum_q, maximum_sum):
    zero = Q(0)
    pending = [(((zero, maximum_a), (zero, maximum_a),
                 (zero, maximum_p), (zero, maximum_q)), 0)]
    examined = 0
    max_depth = 0
    while pending:
        box, depth = pending.pop()
        examined += 1
        max_depth = max(max_depth, depth)
        if box[2][0] + box[3][0] > maximum_sum:
            continue
        certificate = bound(box)
        if certificate is None or certificate <= TARGET:
            continue
        if depth >= 56:
            raise ValueError(f"Unresolved box in {name}: {box}")
        axis = max(range(4), key=lambda j: box[j][1] - box[j][0])
        low, high = box[axis]
        middle = (low + high) / 2
        for interval in ((low, middle), (middle, high)):
            pending.append((box[:axis] + (interval,) + box[axis + 1:], depth + 1))
    return {"condition": name, "upper": str(TARGET), "boxes": examined, "maximum_depth": max_depth}


def main():
    one = Q(1)
    checks = (
        ("weighted_marked_maximum", Q(43, 50), one, one, Q(2)),
        ("simple_marked_maximum", one, Q(83, 100), Q(83, 100), Q(2)),
        ("root_marked_simple_degree_sum", one, one, one, Q(33, 20)),
    )
    for args in checks:
        print(json.dumps(verify(*args)), flush=True)


if __name__ == "__main__":
    main()

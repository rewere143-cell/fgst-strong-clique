"""Check the rational comparisons in 显式半度临界余量判据.md."""

from fractions import Fraction as Q


def main():
    epsilon = Q(1, 10**36)
    x = Q(1, 10**18)
    y = Q(1, 10**9)
    z_upper = Q("0.00009")
    w = Q("0.00001")
    rho_upper = Q(1, 2) + epsilon
    min_part = (1 - rho_upper) / 2

    # Initial missing-pair, cover, and weighted discharge estimates.
    assert x**2 == epsilon and y**2 == x
    assert (1 + rho_upper) / 2 < 1
    assert min_part > Q(".249")
    assert (3 - rho_upper) / 2 - epsilon / min_part >= Q("1.25") - 6 * epsilon
    assert Q("1.25") + 6 * epsilon <= Q("1.3")
    assert 1 + 12 * rho_upper <= 8

    # Selection of retained exterior points.
    assert 6 * epsilon <= x / 2
    assert rho_upper < 2 * (Q(".75") - 2 * x)
    assert epsilon <= x and epsilon / 2 <= x
    assert 40 * epsilon + 10 * x + 5 * y <= 6 * y
    assert 16 * epsilon + 30 * y <= 31 * y
    assert 3 * x + y <= 2 * y
    assert min_part > 3 * x + 2 * y
    assert (Q(".25") - 2 * x) * 100 * y >= Q("21.5") * y + rho_upper * x / 2

    # Capacity estimates and the star stability region.
    assert epsilon / 2 + 6 * y <= 7 * y
    assert epsilon / 2 + (7 + 106 + 6) * y <= 124 * y
    assert 7 * y < z_upper**2 and Q(".04") > 10 * z_upper
    assert rho_upper / 2 < Q(".26")

    # Lower bound from the residual center and upper bound from sparse support.
    center_remainder = Q(".25") - 11 * z_upper - epsilon / 2 - x - 14 * y / w
    assert center_remainder >= Q(".247")
    marked_lower = Q(".247") * (Q(".02") - 4 * z_upper) - (190 * y + 10 * z_upper) - 2 * x
    assert marked_lower > Q(".0039")
    support_upper = 7 * y + Q(".26") * (w + 2 * x) + Q(".13") * x
    assert support_upper < Q(".000003")
    assert Q(".0039")**2 > 2 * Q(".000003")
    assert Q(".020") + 6 * y + epsilon / 2 < Q(".02025")
    direct_support_cap = Q(6109001858179674853867, 5000000000000000000000)
    assert direct_support_cap < Q(5, 4) - Q(".028199")

    print("All comparisons passed in exact rational arithmetic.")
    print("Effective slack bound:", rho_upper)
    print("Degree threshold:", 1 // epsilon)


def check_pure_closure():
    y = Q(1, 10**9)
    epsilon = Q(1, 10**36)
    x = Q(1, 10**18)
    defect = 8 * y
    local_defect = Q(".0001")
    removal_allowance = Q(".0002")

    assert 7 * y + epsilon + x < defect
    assert 2 * defect / local_defect < removal_allowance
    assert Q(".04") + removal_allowance + 5 * local_defect < Q(".041")
    assert Q(".48") - removal_allowance - 2 * local_defect - Q(".041") > Q(".438")
    assert Q(".5202") / Q(".438") < Q("1.19")
    assert Q(".25") - Q(".062") * Q("1.19") > Q(1, 6)
    print("Pure combinatorial closure comparisons passed.")


if __name__ == "__main__":
    main()
    check_pure_closure()

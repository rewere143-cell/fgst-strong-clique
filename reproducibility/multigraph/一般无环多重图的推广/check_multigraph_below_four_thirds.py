"""Verify the scalar root bound 329/250 off the region p,q >= 17/20."""

from fractions import Fraction

scale = 2**18
square = scale**2
pending = [(0, scale, 0, scale, 0, scale, 0, scale, 0)]
counts = dict(empty=0, first=0, second=0, monotone=0, split=0)
max_depth = 0

while pending:
    a0, a1, b0, b1, p0, p1, q0, q1, depth = pending.pop()
    max_depth = max(max_depth, depth)
    # Tighten intervals with q <= b <= a and p <= a.
    b0 = max(b0, q0)
    a0 = max(a0, b0, p0)
    b1, p1 = min(b1, a1), min(p1, a1)
    q1 = min(q1, b1)
    if min(a1-a0, b1-b0, p1-p0, q1-q0) < 0:
        counts['empty'] += 1
        continue
    if 20 * min(p0, q0) >= 17 * scale:
        counts['monotone'] += 1
        continue

    x_upper = a1 * (2*scale-a1) + p1*q1 - max(0, a0-p1)*max(0, b0-q1)
    if 250*x_upper <= 329*square:
        counts['first'] += 1
        continue
    closest_half = max(a0, min(a1, scale//2))
    leg1_upper = min((2*scale-q0)**2, 3*(p1*b1 + closest_half*(scale-closest_half)))
    leg2_upper = (2*scale-p0)**2
    double_upper = 3*x_upper + leg1_upper + leg2_upper
    if 250*double_upper <= 1974*square:
        counts['second'] += 1
        continue

    limits = [a0, a1, b0, b1, p0, p1, q0, q1]
    axis = max(range(0, 8, 2), key=lambda i: limits[i+1]-limits[i])
    if limits[axis+1]-limits[axis] < 2:
        raise ValueError(f'Unresolved interval: {limits}')
    middle = (limits[axis]+limits[axis+1])//2
    left, right = limits.copy(), limits.copy()
    left[axis+1] = right[axis] = middle
    pending.extend([(*left, depth+1), (*right, depth+1)])
    counts['split'] += 1

epsilon = Fraction(1, 6000)
assert Fraction(17, 20)-Fraction(2, 3)*Fraction(23, 20) == Fraction(1, 12)
assert Fraction(1, 3)-40*epsilon > 2/Fraction(613, 100)
assert Fraction(4, 3)-epsilon-Fraction(329, 250) > Fraction(1, 59)
assert Fraction(120, 17) < 8
assert (59*Fraction(813, 100)+16)*epsilon < Fraction(1, 12)-epsilon

print('Exact root bounds passed.', counts, 'Maximum subdivision depth:', max_depth)


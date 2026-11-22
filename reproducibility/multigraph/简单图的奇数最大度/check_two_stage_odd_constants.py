"""Exact arithmetic for the two-stage near-core theorem."""
from fractions import Fraction as F

delta = F(5, 10**6)
alpha, beta = F(".132"), F(".0334")
assert 1 / beta < 4 / alpha
assert (4 / alpha) * F(50, 9) < 169
assert 1 + (2 + 4 * (1 - alpha) / alpha) * F(50, 9) < 160
assert 3 * (1 - alpha - 169 * delta) - F(5, 2) - 12 * delta > 3 * beta

drop = F(".106")
assert F(169, 1600) < drop
edge_lower = F(5, 4) - 160 * delta - drop
min_degree = 1 - drop - 1600 * delta
assert edge_lower > F("1.143")
assert F(5, 2) + 12 * delta - edge_lower < F("1.358")
b_upper = (169 * delta * (1 + 1 / F("1.143")) + drop + 1600 * delta * F("1.358")) / min_degree
assert b_upper < F(".143")
assert 2 * (F(5, 2) + 12 * delta) < 7 * min_degree

a, b = F(".5401"), F(".4599")
assert F(1, 2) + 8012 * delta < a
assert F(8193, 2) < 4097
assert F(8193, 2) + a * F(8024, 2) < 6264
assert 169 * a**4 < 1160 * (b**5 - 10361 * delta * a**3)

assert F(1, 2) + 1172 * delta < F(".506")
assert F(1353, 2) + F(".506") * F(1184, 2) < 977
assert 169 / F(".23") < 735
assert 1172 + 1160 + 735 == 3067
offset = 3067 * delta
epsilon, theta = F(".209"), F(".481")
assert F(".54") - 2 * (1184 + 1160 + 735 + 1172) * delta > theta
assert theta > max(4 * offset, 2 * epsilon) + 4 * offset
assert (epsilon - 2 * offset) * (epsilon - 6 * offset) > 4 * 977 * delta
g = F("1.3825")
assert F(3, 2) - 7 * offset - 977 * delta / (F(1, 2) - offset) > g
gamma = F(".94")
assert F(1, 2) + (epsilon + theta) / (2 * (1 - epsilon)) < gamma
assert F(1, 2) + max(epsilon, 3 - 2 * g) / (2 * g - 2) < gamma
assert (1 + max(epsilon, 3 - 2 * g)) / 2 < gamma
assert (1 - gamma) * 17 > 1

t0 = 1000
epsilon, theta, g = F(".07"), F(".157"), F("1.47")
eta = epsilon + theta
assert (epsilon - F(8, t0)) * (epsilon - F(24, t0)) > F(1, t0)
assert theta > max(2 * epsilon, F(16, t0)) + F(16, t0)
assert g < F(3, 2) - F(56, 2 * t0) - F(1, 2 * (t0 - 8))
assert 2 * (g - 1) > 1 - eta
assert eta * (g - 1 + eta) < g * (2 - g) / 2
assert F(1, 2) - eta / g > F(1, 3)
assert (1 - F(8, t0))**2 > F(1, t0)
print("All exact constants pass for delta=5e-6, D>=2000; simple threshold 100000.")

delta = F(8, 10**6)
alpha, beta = F(".132"), F(".0328")
assert (4 / alpha) * F(50, 9) < 169
assert max(4 / alpha, 1 / beta) * F(50, 9) < 170
assert 1 + max(2 + 4 * (1 - alpha) / alpha, 1 / (2 * beta)) * F(50, 9) < 160
assert 3 * (1 - alpha - 169 * delta) - F(5, 2) - 12 * delta > 3 * beta

drop = F(".1031")
assert F(170, 1650) < drop
edge_lower = F(5, 4) - 160 * delta - drop
min_degree = 1 - drop - 1650 * delta
assert edge_lower > F("1.145")
assert F(5, 2) + 12 * delta - edge_lower < F("1.355")
b_upper = (170 * delta * (1 + 1 / F("1.145")) + drop + 1650 * delta * F("1.355")) / min_degree
assert b_upper < F(".145")
assert 2 * (F(5, 2) + 12 * delta) < 7 * min_degree

small_part = F(1, 2) - 8262 * delta
large_part = 1 - small_part
assert F(8444, 2) + large_part * F(8274, 2) < 6564
probability_good = 1 - (6564 + 4222) * delta / small_part**2
assert probability_good > 0
assert (170 / small_part) / probability_good < 724
assert F(918, 2) + (F(1, 2) + 736 * delta) * F(748, 2) < 649
assert 170 / F(".207") < 822
assert 736 + 724 + 822 == 2282

offset = 2282 * delta
epsilon, theta = F(".224"), F(".522")
assert F(".586") - 2 * (748 + 724 + 822 + 736) * delta > theta
assert theta > max(4 * offset, 2 * epsilon) + 4 * offset
assert (epsilon - 2 * offset) * (epsilon - 6 * offset) > 4 * 649 * delta
g = F("1.361")
assert F(3, 2) - 7 * offset - 649 * delta / (F(1, 2) - offset) > g
gamma = F(".981")
assert F(1, 2) + (epsilon + theta) / (2 * (1 - epsilon)) < gamma
assert F(1, 2) + max(epsilon, 3 - 2 * g) / (2 * g - 2) < gamma
assert (1 + max(epsilon, 3 - 2 * g)) / 2 < gamma
assert (1 - gamma) * 53 > 1

t0 = 1500
epsilon, theta, g = F(".067"), F(".169"), F("1.438")
eta = epsilon + theta
assert (epsilon - F(26, t0)) * (epsilon - F(78, t0)) > F(1, t0)
assert theta > max(2 * epsilon, F(52, t0)) + F(52, t0)
assert g < F(3, 2) - F(182, 2 * t0) - F(1, 2 * (t0 - 26))
assert 2 * (g - 1) > 1 - eta
assert eta * (g - 1 + eta) < g * (2 - g) / 2
assert F(1, 2) - eta / g > F(1, 3)
assert (1 - F(26, t0))**2 > F(1, t0)
print("All exact constants pass for delta=8e-6, D>=3000; simple threshold 62500.")

delta = F(1, 10**5)
alpha, beta = F(".13"), F(".0333")
assert (4 / alpha) * F(50, 9) < 171
assert max(4 / alpha, 1 / beta) * F(50, 9) < 171
assert 1 + max(2 + 4 * (1 - alpha) / alpha, 1 / (2 * beta)) * F(50, 9) < 161
assert 3 * (1 - alpha - 171 * delta) - F(5, 2) - 12 * delta > 3 * beta

drop = F(171, 1125)
edge_lower = F(5, 4) - 161 * delta - drop
max_side = F(5, 2) + 12 * delta - edge_lower
min_degree = 1 - drop - 1125 * delta
assert 1 < edge_lower
assert edge_lower - 1 > (171 * delta * (1 + 1 / edge_lower)
                         + drop * (1 - min_degree / max_side)
                         + 1125 * delta * max_side) / min_degree
assert 2 * (F(5, 2) + 12 * delta) < 7 * min_degree

small_part = F(1, 2) - 5637 * delta
large_part = 1 - small_part
assert F(5820, 2) + large_part * F(5649, 2) < 4482
probability_good = 1 - (4482 + 2910) * delta / small_part**2
assert probability_good > 0
assert (171 / small_part) / probability_good < 618
assert F(813, 2) + (F(1, 2) + 630 * delta) * F(642, 2) < 570
assert 171 / F(".209") < 819
assert 630 + 618 + 819 == 2067
assert 618 + 642 + 618 + 819 == 2697

part_offset, wrong_degree = 2067 * delta, 2697 * delta
epsilon, theta = F(".226"), F(".507")
assert F(".582") - 2 * (642 + 618 + 819 + 630) * delta > theta
assert theta > max(2 * wrong_degree, 2 * epsilon) + 2 * wrong_degree
assert (epsilon - 2 * part_offset) * (epsilon - 2 * (part_offset + wrong_degree)) > 4 * 570 * delta
g = F("1.451")
assert F(3, 2) - (322 + 642 + 618 + 819 + 2 * 630) * delta - 570 * delta / (F(1, 2) - part_offset) > g
gamma = F(".975")
assert F(1, 2) + (epsilon + theta) / (2 * (1 - epsilon)) < gamma
assert F(1, 2) + max(epsilon, 3 - 2 * g) / (2 * g - 2) < gamma
assert (1 + max(epsilon, 3 - 2 * g)) / 2 < gamma
assert (1 - gamma) * 41 > 1

t0 = 1500
epsilon, theta, g = F(".067"), F(".161"), F("1.45")
eta = epsilon + theta
assert (epsilon - F(20, t0)) * (epsilon - F(60, t0)) > F(1, t0)
assert theta > max(2 * epsilon, F(40, t0)) + F(40, t0)
assert g < F(3, 2) - F(140, 2 * t0) - F(1, 2 * (t0 - 20))
assert 2 * (g - 1) > 1 - eta
assert eta * (g - 1 + eta) < g * (2 - g) / 2
assert F(1, 2) - eta / g > F(1, 3)
assert (1 - F(20, t0))**2 > F(1, t0)
print("All exact constants pass for delta=1e-5, D>=3000; simple threshold 50000.")

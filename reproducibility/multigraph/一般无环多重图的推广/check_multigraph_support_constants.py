"""Exact numerical checks for multigraph_support_1e6.md."""
from fractions import Fraction as F

minimum_degree = 500
delta = F(1, 10**6)
trim_fraction, popular_codegree = F(133, 1000), F(334, 10000)
assert 4 / trim_fraction > 1 / popular_codegree
assert 4 / trim_fraction * F(50, 9) < 168
assert 1 + (2 + 4 * (1 - trim_fraction) / trim_fraction) * F(50, 9) < 158
assert 3 * (1 - trim_fraction - 168 * delta) - F(5, 2) - 12 * delta > 3 * popular_codegree

trimmed_edge_density = F(5, 4) - F(84, 1000) - 158 * delta
trimmed_minimum_degree = 1 - F(84, 1000) - 2000 * delta
assert trimmed_edge_density > F(1165, 1000)
assert F(5, 2) + 12 * delta - trimmed_edge_density < F(1335, 1000)
assert 168 / trimmed_edge_density < 150
assert (150 * delta + (F(84, 1000) + 2150 * delta) * F(1335, 1000)) / trimmed_minimum_degree < F(165, 1000)
assert 2 * (F(5, 2) + 12 * delta) < 7 * trimmed_minimum_degree

large_part, small_part = F(511, 1000), F(489, 1000)
assert F(1, 2) + 10012 * delta < large_part
assert 5096 + large_part * F(10024, 2) < 7658
assert 168 * large_part**4 < 440 * (small_part**5 - 12754 * delta * large_part**3)
assert F(1, 2) + 452 * delta < F(501, 1000)
assert 316 + F(501, 1000) * F(464, 2) < 433
assert F(3, 2) - (7 * 452 + F(433) / F(499, 1000)) * delta > F(149, 100)
assert 632 / (F(49, 100) - F(1, minimum_degree)) < 1296
assert 168 / F(39, 100) < 431
assert 452 + 440 + 431 == 1323
assert 1296 + 440 + 431 < 2170

part_offset = 1323 * delta
outside_size = 2170 * delta
epsilon, theta = F(488, 10000), F(1953, 10000)
eta = epsilon + theta
assert F(22, 100) - 2 * (464 + 440 + 431 + 452) * delta > theta
assert theta > 2 * max(4 * part_offset, 2 * epsilon)
assert (epsilon - 2 * part_offset) * (epsilon - 6 * part_offset) > 1732 * delta

half_cover = F(1489, 1000)
assert F(3, 2) - (7 * 1323 + 433 / (F(1, 2) - part_offset)) * delta > half_cover
assert 2 * (half_cover - 1) > 1 - eta
assert eta * (half_cover - 1 + eta) < half_cover * (2 - half_cover) / 2
assert F(1, 2) - eta / half_cover * (1 + 4 * outside_size) > F(1, 3)
assert (F(1, 2) - part_offset)**2 > 433 * delta

print("Exact Fraction calculations for delta = 10^-6 passed.")

minimum_degree = 354
delta = F(2, 10**6)
trim_fraction, popular_codegree = F(132, 1000), F(334, 10000)
assert delta * (minimum_degree - 1)**2 < F(1, 4)
assert 4 / trim_fraction > 1 / popular_codegree
assert 4 / trim_fraction * F(50, 9) < 169
assert 1 + (2 + 4 * (1 - trim_fraction) / trim_fraction) * F(50, 9) < 160
assert 3 * (1 - trim_fraction - 169 * delta) - F(5, 2) - 12 * delta > 3 * popular_codegree

assert F(169, 1800) < F(94, 1000)
trimmed_edge_density = F(5, 4) - F(94, 1000) - 160 * delta
trimmed_minimum_degree = 1 - F(94, 1000) - 1800 * delta
assert trimmed_edge_density > F(1155, 1000)
assert F(5, 2) + 12 * delta - trimmed_edge_density < F(1345, 1000)
assert 169 / trimmed_edge_density < 150
assert (150 * delta + (F(94, 1000) + 1950 * delta) * F(1345, 1000)) / trimmed_minimum_degree < F(155, 1000)
assert 2 * (F(5, 2) + 12 * delta) < 7 * trimmed_minimum_degree

large_part, small_part = F(5181, 10000), F(4819, 10000)
assert F(1, 2) + 9012 * delta < large_part
assert F(169 + 9024, 2) < 4597
assert F(169 + 9024, 2) + large_part * F(9024, 2) < 6935
assert 169 * large_part**4 < 535 * (small_part**5 - 11532 * delta * large_part**3)
assert F(1, 2) + 547 * delta < F(5011, 10000)
assert F(169 + 559, 2) + F(5011, 10000) * F(559, 2) < 505
assert F(3, 2) - (7 * 547 + F(505) / F(4989, 10000)) * delta > F(149, 100)
assert 728 / (F(49, 100) - F(1, minimum_degree)) < 1495
assert 169 / F(39, 100) < 434
assert 547 + 535 + 434 == 1516
assert 1495 + 535 + 434 < 2465

part_offset = 1516 * delta
outside_size = 2465 * delta
epsilon, theta = F(763, 10000), F(1648, 10000)
eta = epsilon + theta
assert F(22, 100) - 2 * (559 + 535 + 434 + 547) * delta > theta
assert theta > max(4 * part_offset, 2 * epsilon) + 4 * part_offset
assert (epsilon - 2 * part_offset) * (epsilon - 6 * part_offset) > 4 * 505 * delta

half_cover = F(14767, 10000)
assert F(3, 2) - (7 * 1516 + 505 / (F(1, 2) - part_offset)) * delta > half_cover
assert 2 * (half_cover - 1) > 1 - eta
assert eta * (half_cover - 1 + eta) < half_cover * (2 - half_cover) / 2
assert F(1, 2) - eta / half_cover * (1 + 4 * outside_size) > F(1, 3)
assert (F(1, 2) - part_offset)**2 > 505 * delta

print("Exact Fraction calculations for delta = 2e-6 passed.")

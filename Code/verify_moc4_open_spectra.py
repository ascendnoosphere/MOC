"""Check the spectral neighborhoods in Docs/moc4_open_spectra.md and Docs/Cases/Spectra.md."""
from fractions import Fraction
from itertools import permutations


def multiply(u, v):
    return u[0] * v[0] - u[1] * v[1], u[0] * v[1] + u[1] * v[0]


def subtract(u, v):
    return u[0] - v[0], u[1] - v[1]


def area(u, v):
    return u[0] * v[1] - u[1] * v[0]


def norm_squared(z):
    return z[0] ** 2 + z[1] ** 2


def hull_data(a, b, cycle_labels):
    vertices = {}
    max_factor_squared = 0
    for p in permutations(range(4)):
        z = (1, 0)
        for i, j in enumerate(p):
            factor = (a[i] + b[j][0], b[j][1])
            max_factor_squared = max(max_factor_squared, norm_squared(factor))
            z = multiply(z, factor)
        vertices[p] = z

    assert len(set(vertices.values())) == 24
    cycle = [tuple(map(int, label)) for label in cycle_labels.split()]
    assert len(set(cycle)) == len(cycle)
    edge_minima = []
    for p, q in zip(cycle, cycle[1:] + cycle[:1]):
        assert sum(i != j for i, j in zip(p, q)) == 2
        edge = subtract(vertices[q], vertices[p])
        slacks = {r: area(edge, subtract(z, vertices[p])) for r, z in vertices.items()}
        assert slacks[p] == slacks[q] == 0
        excluded = [s for r, s in slacks.items() if r != p and r != q]
        assert min(excluded) > 0
        edge_minima.append(min(excluded))

    diameter_squared = max(
        norm_squared(subtract(v, w)) for v in vertices.values() for w in vertices.values()
    )
    return edge_minima, diameter_squared, max_factor_squared


def cross_ratio(b):
    num = multiply(subtract(b[0], b[2]), subtract(b[1], b[3]))
    den = multiply(subtract(b[0], b[3]), subtract(b[1], b[2]))
    scaled = multiply(num, (den[0], -den[1]))
    return tuple(Fraction(x, norm_squared(den)) for x in scaled)


a = (-3, -1, 2, 4)
b = ((6, -5), (-6, 3), (2, 4), (-7, 0))
edge_minima, diameter_squared, max_factor_squared = hull_data(
    a, b, "1302 1320 1230 2130 2103 2013 0213 0231 0321 0312 3012 3102"
)
assert edge_minima == [
    57600, 78750, 78750, 85680, 18576, 8880,
    204, 204, 143104, 270400, 1285440, 194240,
]
assert diameter_squared < 6000 ** 2
assert max_factor_squared < 12 ** 2
assert cross_ratio(b) == (Fraction(-17, 65), Fraction(-6, 65))
epsilon = Fraction(1, 10 ** 8)
vertex_change = 18000 * epsilon
assert 8 * 13 ** 3 < 18000
slack_change = 4 * vertex_change * (6000 + vertex_change)
assert 44 * slack_change < min(edge_minima)
print("12 exposed transposition edges; all 24 vertices distinct.")
print("Minimum positive edge slack:", min(edge_minima))
print("Squared diameter:", diameter_squared)
print("Absolute change in an edge slack is less than", slack_change)
print("Certified closed spectral radius:", epsilon)

# Spectra.md, W/X/AR. Keep the second spectrum fixed to retain cross-ratio i.
a = (-6, -3, 1, 2)
b = ((-1, -1), (4, -1), (-1, 4), (1, 0))
edge_minima, diameter_squared, max_factor_squared = hull_data(
    a, b, "0213 2013 3012 3021 3201 3210"
)
assert edge_minima == [20880, 35360, 15900, 22400, 7200, 19200]
assert cross_ratio(b) == (0, 1)
assert diameter_squared == 1114640 < 1060 ** 2
assert max_factor_squared == 65 < 9 ** 2
epsilon = Fraction(1, 10 ** 6)
assert 9 + 2 * epsilon < 10
vertex_change = 8 * 10 ** 3 * epsilon
slack_change = 4 * vertex_change * (1060 + vertex_change)
assert 44 * slack_change < min(edge_minima)
print("Cross-ratio i: 6 exposed transposition edges; all 24 vertices distinct.")
print("Minimum positive edge slack:", min(edge_minima))
print("Certified closed spectral radius:", epsilon)

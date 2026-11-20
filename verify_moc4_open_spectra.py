"""Check the integer polygon and rational radius in moc4_open_spectra.md."""
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


a = (-3, -1, 2, 4)
b = ((6, -5), (-6, 3), (2, 4), (-7, 0))
perms = list(permutations(range(4)))
vertices = {}
for p in perms:
    z = (1, 0)
    for i, j in enumerate(p):
        factor = (a[i] + b[j][0], b[j][1])
        assert norm_squared(factor) < 12 ** 2
        z = multiply(z, factor)
    vertices[p] = z

cycle = "1302 1320 1230 2130 2103 2013 0213 0231 0321 0312 3012 3102".split()
cycle = [tuple(map(int, label)) for label in cycle]
edge_minima = []
assert len(set(vertices.values())) == 24
for p, q in zip(cycle, cycle[1:] + cycle[:1]):
    assert sum(i != j for i, j in zip(p, q)) == 2
    edge = subtract(vertices[q], vertices[p])
    slacks = {r: area(edge, subtract(z, vertices[p])) for r, z in vertices.items()}
    assert slacks[p] == slacks[q] == 0
    excluded = [slacks[r] for r in perms if r != p and r != q]
    assert min(excluded) > 0
    edge_minima.append(min(excluded))

assert edge_minima == [
    57600, 78750, 78750, 85680, 18576, 8880,
    204, 204, 143104, 270400, 1285440, 194240,
]
diameter_squared = max(
    norm_squared(subtract(v, w)) for v in vertices.values() for w in vertices.values()
)
assert diameter_squared < 6000 ** 2
# A nonreal cross-ratio excludes a generalized circle for the second spectrum.
num = multiply(subtract(b[0], b[2]), subtract(b[1], b[3]))
den = multiply(subtract(b[0], b[3]), subtract(b[1], b[2]))
scaled = multiply(num, (den[0], -den[1]))
cross_ratio = tuple(Fraction(x, norm_squared(den)) for x in scaled)
assert cross_ratio == (Fraction(-17, 65), Fraction(-6, 65))

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

"""Exact certificate for four-dimensional one-sided principal-minor containment.

Run with Python 3.10+; there are no external dependencies. Indexing is zero based.
"""
from fractions import Fraction
from functools import lru_cache
from itertools import combinations, permutations, product
from collections import Counter

PERMS = list(permutations(range(4)))
INDEX = {p: i for i, p in enumerate(PERMS)}
PAIRS = list(combinations(range(4), 2))
FULL = (1 << 24) - 1


def indicator(rows, cols):
    rows = set(rows)
    return tuple(int({p[j] for j in cols} == rows) for p in PERMS)


def singleton(i, j):
    return indicator((i,), (j,))


def add(*vectors):
    return tuple(map(sum, zip(*vectors)))


def negate(vector):
    return tuple(-x for x in vector)


def zero_mask(vector):
    return sum(1 << i for i, v in enumerate(vector) if v == 0)


def change(vector, g):
    return tuple(vector[i] for i in g)


def make_group():
    return [tuple(INDEX[tuple(r[p[c[i]]] for i in range(4))] for p in PERMS)
            for r, c in product(PERMS, repeat=2)]


GROUP = make_group()
Q0 = indicator((2, 3), (2, 3))
Q1 = indicator((1, 2), (1, 2))
F = add(singleton(1, 2), singleton(2, 1), Q0,
        negate(indicator((1, 3), (0, 2))))
ORDINARY = sorted({singleton(i, j) for i, j in product(range(4), repeat=2)} |
                  {indicator(s, t) for s, t in product(PAIRS, repeat=2)})
MIXED = sorted({change(F, g) for g in GROUP})
RAYS = ORDINARY + MIXED
MASKS = [zero_mask(v) for v in RAYS]
assert (len(ORDINARY), len(MIXED), len(set(MASKS))) == (34, 48, 82)
assert min(min(v) for v in RAYS) >= 0


def maximal_proper_faces(face):
    candidates = {face & m for m in MASKS} - {face}
    maximal = []
    for test in sorted(candidates, key=int.bit_count, reverse=True):
        if all(test & other != test for other in maximal):
            maximal.append(test)
    return maximal


def mask_action(mask, g):
    # g is an arbitrary group permutation, so its image maps give the same orbits.
    return sum(1 << g[i] for i in range(24) if mask & (1 << i))


def verify_full_facets():
    # Each intersection is a true face because all proposed inequalities support
    # the hull. All vertices are exposed (each is a permutation matrix).
    representative = {}
    dimension = {0: -1}
    reps = Counter()

    def canonical(face):
        if face not in representative:
            for g in GROUP:
                representative[mask_action(face, g)] = face
        return representative[face]

    def visit(face):
        face = canonical(face)
        if face in dimension:
            return dimension[face]
        children = maximal_proper_faces(face)
        assert children
        sizes = {visit(child) for child in children}
        assert len(sizes) == 1
        d = sizes.pop() + 1
        if d == 0:
            assert face.bit_count() == 1
        if d >= 1:
            ridges = Counter(r for child in children for r in maximal_proper_faces(child))
            assert ridges and set(ridges.values()) == {2}
        dimension[face] = d
        reps[d] += 1
        return d

    assert visit(FULL) == 13
    assert set(maximal_proper_faces(FULL)) == set(MASKS)
    print("Full facet lattice, 82 facets; dimension-graded, with two facets at every ridge.")
    print("Numbers of point-set orbits by face dimension:", [reps[i] for i in range(14)])


def exact_coordinates():
    # A basis of the full span, followed by its four independent pair coordinates.
    singleton_indices = [0, 5, 10, 15, 7, 12, 1, 14, 6]
    basis = [(1,) * 24] + [singleton(k // 4, k % 4) for k in singleton_indices]
    for s in [PAIRS[5], PAIRS[1]]:
        for t in [(3, 1), (3, 2)]:
            basis.append(indicator(s, t))
    # Row reduce basis, carrying the 14x14 change of basis.
    n = len(basis)
    rows = [[Fraction(z) for z in list(basis[i]) + [int(i == j) for j in range(n)]]
            for i in range(n)]
    pivots = []
    for j in range(24):
        k = len(pivots)
        pivot = next((i for i in range(k, n) if rows[i][j]), None)
        if pivot is None:
            continue
        rows[k], rows[pivot] = rows[pivot], rows[k]
        h = rows[k][j]
        rows[k] = [x / h for x in rows[k]]
        for i in range(n):
            if i != k and rows[i][j]:
                h = rows[i][j]
                rows[i] = [x - h*y for x, y in zip(rows[i], rows[k])]
        pivots.append(j)
        if len(pivots) == n:
            break
    assert n == len(pivots) == 14
    def coeff(ray):
        c = [sum(ray[j]*rows[i][24+l] for i, j in enumerate(pivots))
             for l in range(n)]
        assert all(z.denominator == 1 for z in c)
        c = list(map(int, c))
        assert all(sum(c[k]*basis[k][i] for k in range(n)) == ray[i] for i in range(24))
        return c
    # All profile coordinates are in this 14-dimensional span. Complementary
    # pair coordinates coincide on permutations and unitaries.
    for s in PAIRS:
        for t in PAIRS:
            coeff(indicator(s, t))
    # Verify each of the six weighted pair rows belongs to the two-row quotient
    # span as an identity for every p.  Test coefficientwise in p.
    for s in PAIRS:
        x = coeff(indicator(s, (3, 1)))[10:]
        y = coeff(indicator(s, (3, 2)))[10:]
        for k in (0, 2):
            assert x[k+1] == y[k] == 0 and x[k] == y[k+1]
    return [coeff(ray) for ray in RAYS]


def determinant(a, b):
    a0, a1, a2, a3 = a
    b0, b1, b2, b3 = b
    return (a0*b2-a2*b0, a0*b3+a1*b2-a2*b1-a3*b0, a1*b3-a3*b1)


def sign(poly):
    if all(x == 0 for x in poly):
        return 0
    if all(x >= 0 for x in poly):
        return 1
    if all(x <= 0 for x in poly):
        return -1
    raise AssertionError(("Sign requires root isolation", poly))


def multiply(a, b):
    return tuple(sum(a[j]*b[k-j] for j in range(len(a)) if 0 <= k-j < len(b))
                 for k in range(len(a) + len(b) - 1))


def prove_one_sided():
    expression = exact_coordinates()
    verify_full_facets()
    lookup = {row: i for i, row in enumerate(RAYS)}
    patterns = {(lookup[change(Q0, g)], lookup[change(Q1, g)], lookup[change(F, g)])
                for g in GROUP}
    # p=h/(1+2h), h>0. Residual components are (1+h)c0-hc1.
    residual = [(row[10], row[10]-row[11], row[12], row[12]-row[13])
                for row in expression]
    accepted = Counter()
    contacts = set()
    for k in (1, 2, 3):
        for indices in combinations(range(82), k):
            if indices[-1] < 34:
                continue
            mask = FULL
            for i in indices:
                mask &= MASKS[i]
            if mask.bit_count() < 11:
                continue
            vec = [residual[i] for i in indices]
            if k == 1:
                assert any(vec[0])
                continue
            if k == 2:
                if any(determinant(*vec)):
                    continue
                coord = next((j for j in (0, 2)
                              if any(vec[0][j:j+2]) or any(vec[1][j:j+2])), None)
                if coord is None:
                    continue
                assert sign(vec[0][coord:coord+2])*sign(vec[1][coord:coord+2]) != -1
                continue
            a, b, c = vec
            weights = [determinant(b,c), determinant(c,a), determinant(a,b)]
            if any(not any(polynomial) for polynomial in weights):
                continue
            orientations = list(map(sign, weights))
            if len(set(orientations)) != 1:
                continue
            weights = [tuple(orientations[0]*x for x in v) for v in weights]
            i, j, kf = indices
            assert j < 34 <= kf and mask.bit_count() == 11
            if (i,j,kf) not in patterns:
                assert (j,i,kf) in patterns
                weights[0], weights[1] = weights[1], weights[0]
            w0, w1, wf = weights
            reduced = tuple(x-y for x,y in zip(w1,wf))
            assert sign(w0) == 1 and sign(reduced) >= 0 and sign(wf) == 1
            assert multiply(w0,reduced) == multiply(wf,wf)
            accepted[3] += 1
            contacts.add(mask)
    assert accepted == {3:96} and len(contacts) == 96
    print("One-sided section, 96 mixed circuits; each passes the analytic facet identity.")
    print("All parameter comparisons are exact for h>0.")
if __name__ == "__main__":
    prove_one_sided()

"""Exact fixture replay for C03 paths 03/05/10 and C04 paths 03/04/10.

No arithmetic check here substitutes for a Lean theorem. Assignment maxima
are found by subset dynamic programming, not permutation enumeration.
Requires SymPy and prints a deterministic JSON summary.
"""
import json
import random
from functools import lru_cache

import sympy as S
from sympy.polys.matrices import DomainMatrix
from sympy.polys.domains import QQ


def hv(h):
    """Real Hermitian coordinates, dimension k^2."""
    k = h.rows
    return [S.re(h[i, i]) for i in range(k)] + [
        t(h[i, j]) for i in range(k) for j in range(i + 1, k)
        for t in (S.re, S.im)
    ]


def householder(v):
    return S.eye(v.rows) - 2 * (v * v.conjugate().T) / (v.conjugate().T * v)[0, 0]


def exact_unitary(n, seed, complex_entries):
    rng = random.Random(seed)
    def vector():
        return S.Matrix([rng.choice((-3, -2, -1, 1, 2, 3)) +
                         (S.I * rng.randint(-3, 3) if complex_entries else 0)
                         for _ in range(n)])
    return (householder(vector()) * householder(vector())).applyfunc(S.expand)


def exact_frame(n, k, seed, complex_entries):
    rng = random.Random(seed)
    f = S.eye(n)[:, :k]
    for _ in range(k + 3):
        v = S.Matrix([rng.choice((-3, -2, -1, 1, 2, 3)) +
                      (S.I * rng.randint(-3, 3) if complex_entries else 0)
                      for _ in range(n)])
        left = (v.conjugate().T * f).applyfunc(S.expand)
        f = (f - 2 * v * left / (v.conjugate().T * v)[0, 0]).applyfunc(S.expand)
    return f


def exact_compression(k, p, q, seed, complex_entries, zero_free):
    frames = [exact_frame(n, k, seed + i, complex_entries)
              for i, n in enumerate((p, q))]
    palettes = ((2 + S.I, -2 * S.I, 1 - S.I, 3 * S.I, 0 if not zero_free else 1),
                (1 + 2 * S.I, -2, -S.I, 3, 0 if not zero_free else 2 * S.I))
    spectra = [[palettes[s][i % 5] for i in range(n)]
               for s, n in enumerate((p, q))]
    coords, metadata = [], []
    zero = [S.Integer(0)] * (k * k)
    for f, labels, side in zip(frames, spectra, range(2)):
        assert (f.conjugate().T * f).applyfunc(S.expand) == S.eye(k)
        for j, value in enumerate(labels):
            row = f[j, :]
            gram = (row.conjugate().T * row).applyfunc(S.expand)
            gram_coords = hv(gram)
            coords.append(((gram_coords + zero) if side == 0 else (zero + gram_coords)) +
                          [S.re(value) * x for x in gram_coords] +
                          [S.im(value) * x for x in gram_coords])
            metadata.append((side, gram, value))
    weights = {j: S.Integer(1) for j in range(len(coords))}
    dimension = 4 * k * k
    original = S.Matrix(coords).T
    before = original * S.ones(len(coords), 1)
    rank = DomainMatrix.from_Matrix(original).convert_to(QQ).rank()
    while len(weights) > dimension:
        active = list(weights)
        matrix = original[:, active]
        relation = DomainMatrix.from_Matrix(matrix).convert_to(QQ).nullspace().to_Matrix()[0, :]
        assert matrix * relation.T == S.zeros(dimension, 1)
        if not any(v > 0 for v in relation):
            relation = -relation
        step = min(weights[j] / v for j, v in zip(active, relation) if v > 0)
        for j, v in zip(active, relation):
            weights[j] -= step * v
            assert weights[j] >= 0
            if weights[j] == 0:
                del weights[j]
    assert original * S.Matrix([weights.get(j, 0) for j in range(len(coords))]) == before
    old_parts = [S.zeros(k), S.zeros(k)]
    parts = [S.zeros(k), S.zeros(k)]
    grams = [S.zeros(k), S.zeros(k)]
    counts = [0, 0]
    for j, (side, h, value) in enumerate(metadata):
        old_parts[side] += value * h
        w = weights.get(j, 0)
        counts[side] += bool(w)
        grams[side] += w * h
        parts[side] += w * value * h
    assert all(g.applyfunc(S.expand) == S.eye(k) for g in grams)
    assert (sum(parts, S.zeros(k)) - sum(old_parts, S.zeros(k))).applyfunc(S.expand).is_zero_matrix
    assert min(counts) >= k and sum(counts) <= dimension
    old_zero = p > k and q > k
    new_zero = min(counts) > k
    assert not new_zero or old_zero
    return dict(k=k, input=[p, q], output=counts, exact_moment_rank=rank,
                dense=all(all(e != 0 for e in f) for f in frames),
                genuinely_complex=complex_entries,
                spectra_distinct_counts=[len(set(a)) for a in spectra],
                old_optional_zero=old_zero, new_optional_zero=new_zero,
                separate_compressions_changed=[not (a-b).applyfunc(S.expand).is_zero_matrix
                                               for a, b in zip(parts, old_parts)])


def exact_pencil():
    a = list(map(S.Integer, [0, 1, 2]))
    b = list(map(S.Integer, [0, 3, 4]))
    U = householder(S.ones(3, 1))
    q = U[:, 0]
    base = S.diag(*a) + U * S.diag(*b) * U.T
    A, B = (base + q * q.T).det() - base.det(), base.det()
    m = [u ** 2 for u in q]
    intervals = []
    for i in range(3):
        j, k = [r for r in range(3) if r != i]
        caps = sorted([(a[j] + b[1]) * (a[k] + b[2]),
                       (a[k] + b[1]) * (a[j] + b[2])])
        intervals.append(caps)
    assert (S.Rational(-1, 27) * 24 + S.Rational(4, 27) * 25) / m[0] == S.Rational(76, 3)
    assert S.Rational(76, 3) > intervals[0][1]
    t = S.symbols("t", real=True)
    remA, remB = A - t, B - a[2] * t
    w = [(remB - a[1]*remA)/(a[0]-a[1]),
         (a[0]*remA-remB)/(a[0]-a[1]), t]
    exact_set = S.Intersection(*(S.solveset(cond, t, domain=S.S.Reals)
                                 for wi, mi, (lo, hi) in zip(w, m, intervals)
                                 for cond in (wi >= mi * lo, wi <= mi * hi)))
    assert isinstance(exact_set, S.Interval) and exact_set.measure > 0
    at = (exact_set.start + exact_set.end) / 2
    w = [wi.subs(t, at) for wi in w]
    assert sum(w) == A and sum(ai * wi for ai, wi in zip(a, w)) == B
    centers = [wi / mi for wi, mi in zip(w, m)]
    assert all(lo <= val <= hi for val, (lo, hi) in zip(centers, intervals))
    return dict(raw_centroid="76/3", raw_max=25, slope=str(A), intercept=str(B),
                eligible_last_coordinate=str(exact_set), alternative=[str(c) for c in centers])


def norm_sq(z):
    return S.expand(z * S.conjugate(z))


def exact_radial(n, seed, repeated, exact_opposite):
    U = exact_unitary(n, seed, True)
    a = [S.Integer(i+1) + S.I * (i*i % 7) for i in range(n)]
    b = [S.Integer(2*i-n) - S.I * ((i+2)**2 % 5) for i in range(n)]
    if repeated and n >= 6:
        a[-2] = a[-1]
    if exact_opposite:
        for j in range(max(1, n-4)):
            b[j] = -a[0]
    kernel = [[i + j for j in b] for i in a]
    cost = [[norm_sq(z) for z in row] for row in kernel]

    @lru_cache(None)
    def best(i, remaining):
        if i == n:
            return S.Integer(1), ()
        score = 0
        chosen = None
        for j in remaining:
            sub, suffix = best(i + 1, tuple(x for x in remaining if x != j))
            if (value := cost[i][j] * sub) >= score:
                score, chosen = value, (j,) + suffix
        return score, chosen

    R2, pivot = best(0, tuple(range(n)))
    assert R2 > 0
    C = [[cost[i][pivot[j]] / cost[i][pivot[i]] for j in range(n)] for i in range(n)]
    potentials = [S.Integer(1)] * n
    for _ in range(n - 1):
        potentials = [max(C[i][j] * potentials[j] for j in range(n)) for i in range(n)]
    tight = [[C[i][j] * potentials[j] / potentials[i] for j in range(n)] for i in range(n)]
    assert all(0 <= e <= 1 for row in tight for e in row)
    assert all(tight[i][i] == 1 for i in range(n))
    row_factors = [sum(norm_sq(U[i, pivot[j]]) * tight[i][j] for j in range(n))
                   for i in range(n)]
    assert all(0 <= s <= 1 for s in row_factors)
    A = S.Matrix(n, n, lambda i, j: S.expand(U[i,j] * kernel[i][j]))
    D2 = norm_sq(A.det(method="domain-ge"))
    cap = S.prod(row_factors)
    assert 0 <= D2/R2 <= cap <= 1
    return dict(n=n, repeated=(len(set(a)) < n or len(set(b)) < n),
                zero_cells=sum(e == 0 for row in cost for e in row),
                zero_bearing=any(e==0 for row in cost for e in row),
                shared_first_color=[a.count(a[0]), b.count(-a[0])],
                strict_radial=bool(D2/R2 < 1), strict_hadamard=bool(D2/R2 < cap),
                gap_to_cap_float=float(cap-D2/R2), radial_cap_float=float(cap),
                radial_value_sq_float=float(D2/R2), exact_comparisons=True)


def main():
    out = dict(
        joint_frame=[exact_compression(3, 20, 21, 20261125, True, False),
                     exact_compression(4, 35, 32, 20261126, False, True),
                     exact_compression(3, 3, 36, 20261127, False, True)],
        pencil=exact_pencil(),
        radial=[exact_radial(n, 20261125+n, repeated, zero)
                for n in (4, 5, 6)
                for repeated, zero in [(False,False),(True,True)]],
    )
    print(json.dumps(out, indent=2))

if __name__ == "__main__":
    main()

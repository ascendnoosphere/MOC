"""Verify a 6-by-6 MOC certificate with two rank-four normal matrices.

Run with Python 3 and SymPy. All calculations use exact rational arithmetic
in Q(i). The certificate table uses zero-based indices. An entry (i,k,j,l,m)
assigns mass m/360 to the matching with edges (i,j) and (k,l).
"""
from itertools import combinations
from math import prod

import sympy as sp


CERTIFICATE = [
    (0, 1, 0, 3, 11), (0, 1, 3, 1, 34),
    (0, 2, 1, 0, 3), (0, 2, 0, 2, 66), (0, 2, 2, 0, 4),
    (0, 2, 0, 3, 3), (0, 2, 3, 2, 14),
    (0, 3, 1, 2, 22), (0, 3, 3, 1, 17), (0, 3, 2, 3, 6),
    (1, 2, 0, 1, 3), (1, 2, 1, 0, 3), (1, 2, 3, 1, 39),
    (1, 3, 0, 1, 33), (1, 3, 1, 0, 3), (1, 3, 0, 2, 20),
    (1, 3, 0, 3, 9), (1, 3, 2, 3, 25),
    (2, 3, 3, 0, 22), (2, 3, 1, 2, 23),
]


def squared_wedge(v, w):
    value = v[0] * w[1] - v[1] * w[0]
    return sp.simplify(value * sp.conjugate(value))


def make_frames():
    fourier = sp.Matrix(4, 4, lambda i, j: sp.I ** (i * j) / 2)
    rotation = sp.Matrix([[1 + 2 * sp.I, -2], [2, 1 - 2 * sp.I]]) / 3
    rotated = fourier * sp.diag(rotation, sp.eye(2))
    assert sp.simplify(fourier.H * fourier - sp.eye(4)).is_zero_matrix
    assert sp.simplify(rotated.H * rotated - sp.eye(4)).is_zero_matrix
    return fourier, rotated


def check_matching(E, F):
    pairs = list(combinations(range(4), 2))
    row_totals = {pair: 0 for pair in pairs}
    column_totals = {pair: 0 for pair in pairs}
    edge_totals = sp.zeros(4)
    assert sum(entry[-1] for entry in CERTIFICATE) == 360
    for i, k, j, l, mass in CERTIFICATE:
        assert i < k and j != l and mass > 0
        row_totals[i, k] += mass
        column_totals[tuple(sorted((j, l)))] += mass
        edge_totals[i, j] += mass
        edge_totals[k, l] += mass
    for i, k in pairs:
        row_wedge = squared_wedge(E.row(i), E.row(k))
        column_wedge = squared_wedge(F.row(i), F.row(k))
        # Strict positivity also verifies four distinct rays in each frame.
        assert 0 < row_wedge == sp.Rational(row_totals[i, k], 360)
        assert 0 < column_wedge == sp.Rational(column_totals[i, k], 360)
    for i in range(4):
        for j in range(4):
            assert edge_totals[i, j] / 360 == squared_wedge(E.row(i), F.row(j))


def complete_permutation(i, k, j, l):
    # Cross the edges. The mixed terms of (x_i+y_l)(x_k+y_j) use (i,j),(k,l).
    sigma = [None] * 6
    sigma[i], sigma[k] = l, j
    row_remainder = sorted(set(range(4)) - {i, k})
    column_remainder = sorted(set(range(4)) - {j, l})
    for a, b in zip(row_remainder, (4, 5)):
        sigma[a] = b
    sigma[4], sigma[5] = column_remainder
    assert sorted(sigma) == list(range(6))
    return tuple(sigma)


def check_matrices(fourier, rotated):
    basis = sp.eye(6)
    X0 = basis[:, :4]
    Y0 = X0.copy()
    Y0[:, 2] = (4 * basis[:, 2] + 3 * basis[:, 4]) / 5
    Y0[:, 3] = (5 * basis[:, 3] + 12 * basis[:, 5]) / 13
    X, Y = X0 * fourier.H, Y0 * rotated.H
    E, F = fourier[:, :2], rotated[:, :2]
    assert (X.H * basis[:, :2] - E).applyfunc(sp.simplify).is_zero_matrix
    assert (Y.H * basis[:, :2] - F).applyfunc(sp.simplify).is_zero_matrix
    assert (X.H * X - sp.eye(4)).applyfunc(sp.simplify).is_zero_matrix
    assert (Y.H * Y - sp.eye(4)).applyfunc(sp.simplify).is_zero_matrix
    q = sp.simplify((X0 * X0.H + Y0 * Y0.H).det() / 4)
    assert q == sp.Rational(1296, 4225)
    a = (1, 2, 3, sp.I, 0, 0)
    b = (4, 7, -1 + sp.I, 2 - sp.I, 0, 0)
    A = (X * sp.diag(*a[:4]) * X.H).applyfunc(sp.simplify)
    B = (Y * sp.diag(*b[:4]) * Y.H).applyfunc(sp.simplify)
    assert A.rank() == B.rank() == 4
    assert (A * A.H - A.H * A).applyfunc(sp.simplify).is_zero_matrix
    assert (B * B.H - B.H * B).applyfunc(sp.simplify).is_zero_matrix
    # The identity permutation pairs two zero eigenvalues. It has vertex zero.
    weights = {tuple(range(6)): 1 - q}
    for i, k, j, l, mass in CERTIFICATE:
        sigma = complete_permutation(i, k, j, l)
        weights[sigma] = weights.get(sigma, 0) + q * mass / 360
    assert sum(weights.values()) == 1 and min(weights.values()) > 0
    weighted_value = sum(weight * prod(a[i] + b[sigma[i]] for i in range(6))
                         for sigma, weight in weights.items())
    direct = sp.simplify((A + B).det())
    assert sp.simplify(weighted_value - direct) == 0
    assert direct == (-225594 + 186786 * sp.I) / 4225
    return direct, len(weights)


if __name__ == '__main__':
    first, second = make_frames()
    check_matching(first[:, :2], second[:, :2])
    determinant, count = check_matrices(first, second)
    print(f'All 28 matching coefficients and {count} permutation weights verified.')
    print(f'det(A+B) = {determinant}')

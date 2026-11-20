"""Exact arithmetic checks for the four-dimensional spectral example."""
from itertools import permutations

import sympy as sp


def main():
    r = sp.Rational
    labels = tuple(range(4))
    unitary = sp.eye(4)
    for i, c, s in [(0, r(3, 5), r(4, 5)), (1, r(3, 5), r(4, 5)),
                    (2, r(3, 5), r(4, 5)), (3, r(5, 13), r(12, 13))]:
        j = (i + 1) % 4
        gate = sp.eye(4)
        gate[i, i] = gate[j, j] = c
        gate[i, j] = s
        gate[j, i] = -s
        unitary = gate * unitary
    assert unitary * unitary.T == sp.eye(4)
    assert unitary[1, :] == sp.Matrix([[-r(12, 25), r(9, 25), r(4, 5), 0]])
    terms = [(1, (0,), (1,)), (1, (1,), (3,)), (-1, (0, 2), (1, 2)),
             (1, (0, 3), (2, 3))]
    for perm in permutations(labels):
        bound = sum(w * int(set(rows) == {perm[j] for j in cols})
                    for w, rows, cols in terms)
        assert bound >= 0
    score = sum(w * unitary.extract(rows, cols).det()**2 for w, rows, cols in terms)
    assert score == -r(2048, 203125)

    a = tuple(map(sp.sympify, (sp.I, 3, 1 + 2*sp.I, 2 + 5*sp.I)))
    b = tuple(map(sp.sympify, (0, 1, 2, 2 + sp.I)))
    for t in (a, b):
        u, v, x, y = t
        assert sp.im(sp.simplify((u-x)*(v-y)/((u-y)*(v-x)))) != 0
    assert set(a).isdisjoint(b)
    determinant = sp.expand((sp.diag(*a) - unitary*sp.diag(*b)*unitary.T).det())
    assert determinant == (11280200 - 1893872*sp.I)/528125
    selected = [(0, 1, 3, 2), (1, 2, 3, 0), (3, 0, 1, 2)]
    vertices = [sp.expand(sp.prod(a[i]-b[p[i]] for i in labels)) for p in selected]
    assert vertices == [10-10*sp.I, 10-4*sp.I, 60]
    counts = [43548, 364598, 119979]
    assert sum(counts) == 528125
    assert sp.expand(sum(w*z for w, z in zip(counts, vertices)) - 528125*determinant) == 0
    print("Verified the common-law obstruction and the scalar determinant certificate.")


if __name__ == '__main__':
    main()

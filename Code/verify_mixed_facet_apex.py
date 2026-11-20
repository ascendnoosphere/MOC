"""Check the mixed-facet cap and its spectral obstruction in SimplexAttack.md."""

from collections import Counter
from itertools import combinations
from pathlib import Path
import sys

from sympy import I, Matrix, Rational, prod, re

sys.path.insert(0, str(Path(__file__).resolve().parent / "spin"))
from verify_scalar import COORDS, PS


def main():
    slots = [(a, b) for k in range(3) for a in combinations(range(4), k)
             for b in combinations(range(4), k)]
    cols = Matrix([[int({p[i] for i in a} == set(b)) for p in PS] for a, b in slots])
    face = cols[:, list(COORDS)]
    pivots = list(face.T.rref()[1])
    inverse = face[pivots, :].inv()
    selected = [slots[i] for i in pivots]
    special = {0, 3, 6, 7, 9, 10, 12}
    for j in range(13):
        expected = [int(k == j) + int(k == 13 and j in special) for k in range(14)]
        assert any(list(face.row(i)) == expected for i in range(len(slots)))
    ray = Matrix([int(j in special) - int(j == 13) for j in range(14)])
    virtual = face * ray / 6
    assert virtual[0] == 1 and min(virtual) == 0
    p = 2 * inverse[-1, :]
    actions = {}
    for r in PS:
        for c in PS:
            rows = [slots.index((tuple(sorted(r[i] for i in a)), tuple(sorted(c[j] for j in b))))
                    for a, b in selected]
            costs = tuple(p * cols[rows, :])
            actions[costs] = (p * virtual[rows, :])[0]
    assert len(actions) == 48
    assert Counter(actions.values()) == {
        -Rational(1, 3): 1, Rational(1, 3): 24, Rational(2, 3): 20, 1: 3
    }
    a, b = (20, 0, 1, 3 - 5*I), (-1 - I, -2, 1 + I, I)
    h = [re((1 + I)*prod(a[i] + b[p[i]] for i in range(4)).expand()) for p in PS]
    score = sum(ray[j]*h[k] for j, k in enumerate(COORDS)) / 6
    assert score == 168 and max(h) == 164
    print("Verified 13 minor identities and 48 distinct mixed facets with exactly one negative at the apex.")
    print("The virtual apex attains support 168. All 24 permutation products have support at most 164.")


if __name__ == "__main__":
    main()

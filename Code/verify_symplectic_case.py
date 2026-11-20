"""Replay the minor and Bernstein certificates in Docs/Cases/Symplectic.md."""

import os
import sys
from collections import Counter
from itertools import combinations
from pathlib import Path
from subprocess import run
from tempfile import TemporaryDirectory

from sympy import I, Matrix, Rational, diag, eye, im

SPIN = Path(__file__).resolve().parent / "spin"
sys.path.insert(0, str(SPIN))
from verify_scalar import COORDS, PS, R, make_tensor

NEW_RADII = (121, 262, 262, 31, 4, 262, 42, 3, 262, 3, 31, 3, 42)


def center(a, v, c, s):
    w = (c * a).row_join(s * v).col_join(
        (-s * v.H).row_join(-c * v.H * a * v)
    ).applyfunc(lambda z: z.expand())
    j = Matrix([[0, 1], [-1, 0]])
    omega = diag(j, j)
    assert (w * w + eye(4)).applyfunc(lambda z: z.expand()) == Matrix.zeros(4)
    assert w.H == -w and w * omega == omega * w.conjugate()
    plaquette = w[0, 0] * w[1, 3] * (w[0, 3] * w[1, 0]).conjugate()
    assert im(plaquette) != 0
    return w


def main():
    pairs = [(rows, cols) for k in range(3)
             for rows in combinations(range(4), k)
             for cols in combinations(range(4), k)]
    permutations = Matrix([[int({p[i] for i in rows} == set(cols)) for p in PS]
                           for rows, cols in pairs])
    basis = permutations[:, list(COORDS)]
    pivots = list(basis.T.rref()[1])
    inverse = basis[pivots, :].inv()
    assert permutations.rank() == len(COORDS) == 14
    costs = 2 * inverse[-1, :] * permutations[pivots, :]
    assert Counter(costs) == Counter({0: 13, 1: 10, 2: 1})

    def profile(w):
        return {(rows, cols): abs(w.extract(rows, cols).det().expand()) ** 2
                for rows, cols in pairs}

    def relabel(y, r, c, indices):
        return Matrix([y[tuple(sorted(r[i] for i in rows)),
                         tuple(sorted(c[j] for j in cols))]
                       for rows, cols in indices])

    def check_center(w, rows, cols, radii, expected):
        y = profile(w)
        y1 = relabel(y, rows, cols, pairs)
        weights = inverse * y1[pivots, :]
        assert basis * weights == y1
        p = 2 * weights[-1]
        margin = min(radius * weight + p for radius, weight in zip(radii, weights))
        assert (p, margin) == expected
        print(f"Verified 53 squared minors. Facet {p}, scalar margin {margin}.", flush=True)
        return y

    a = Matrix([[99 * I, 20], [-20, -99 * I]]) / 101
    v = Matrix([[3, 4], [-4, 3]]) / 5
    w = center(a, v, Rational(3, 5), Rational(4, 5))
    check_center(w, (2, 0, 1, 3), (3, 1, 0, 2), R,
                 (-Rational(2903967, 159390625), Rational(1148103, 63756250)))

    a = Matrix([[-9 * I, 12 + 8 * I], [-12 + 8 * I, 9 * I]]) / 17
    v = Matrix([[-29 + 50 * I, 50 + 20 * I], [-50 + 20 * I, -29 - 50 * I]]) / 79
    w = center(a, v, -Rational(9, 41), Rational(40, 41))
    radii = tuple(Rational(n, 100) for n in NEW_RADII)
    denominator = 31808386132789249
    profile2 = check_center(w, (0, 2, 3, 1), (1, 3, 2, 0), radii,
                            (-Rational(224829494664111, denominator),
                             Rational(437635081521, denominator)))

    previous = tuple(Rational(n, 12) for n in (4, 72, 72, 18, 72, 3, 18, 4, 3, 4, 2, 3, 18))
    selected = [pairs[k] for k in pivots]
    old_margins = []
    for r in PS:
        for c in PS:
            weights = inverse * relabel(profile2, r, c, selected)
            p = 2 * weights[-1]
            if p < 0:
                old_margins.append(tuple(min(t * w + p for t, w in zip(radii0, weights))
                                         for radii0 in (R, previous)))
    assert len(old_margins) == 12
    assert tuple(map(max, zip(*old_margins))) == (
        -Rational(77120738391213, 63616772265578498),
        -Rational(203334539535711, denominator),
    )
    print("The second center passes the new radii and escapes both prior simplex tests.", flush=True)

    with TemporaryDirectory() as tmp:
        directory = Path(tmp)
        make_tensor(directory)
        exe = directory / "bernstein"
        run(["g++", "-O3", "-fopenmp", "-std=c++17", SPIN / "bernstein.cpp",
             "-lgmpxx", "-lgmp", "-o", exe], check=True)
        env = dict(os.environ)
        env.setdefault("OMP_NUM_THREADS", "4")
        for mode in ("grid", "coeff"):
            run([exe, mode], cwd=directory, env=env, check=True)
        out = run([exe, "bern", "100", *map(str, NEW_RADII)],
                  cwd=directory, env=env, check=True, capture_output=True, text=True).stdout
        assert "grid 497420\nnegative 0 zero 0 min " in out
        print(out, end="")


if __name__ == "__main__":
    main()

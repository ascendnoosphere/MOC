"""Check the quaternion identities and the two scalar MOC certificates."""

import os
import sys
from itertools import combinations
from pathlib import Path
from subprocess import run
from tempfile import TemporaryDirectory

import sympy as sp

SPIN = Path(__file__).resolve().parent / "spin"
sys.path.insert(0, str(SPIN))
from verify_scalar import COORDS, PS, make_tensor
from verify_spin_moc import T, nonnegative_on_unit_interval


def quaternion(t, x, y, z):
    return sp.Matrix([[t, -x, -y, -z], [x, t, -z, y],
                      [y, z, t, -x], [z, -y, x, t]])


def check_matching_ratios():
    q = sp.symbols("q:4", real=True)
    a, b = sp.symbols("a:4"), sp.symbols("b:4")
    u = quaternion(*q)
    odd_sum = 0
    positive_mass = 0
    for p in PS:
        inversions = sum(p[i] > p[j] for i, j in combinations(range(4), 2))
        weight = (-1) ** inversions * sp.prod(u[i, p[i]] for i in range(4))
        if sum(i == p[i] for i in range(4)) == 1:
            sign = (weight / sp.prod(q)).cancel()
            assert sign in (-1, 1)
            odd_sum += sign * sp.prod(a[i] + b[p[i]] for i in range(4))
        else:
            assert sp.Poly(weight, *q).LC() == 1
            assert all(k % 2 == 0 for k in sp.Poly(weight, *q).monoms()[0])
            positive_mass += weight
    assert sp.expand(positive_mass - sum(v*v for v in q)**2) == 0

    def brackets(x):
        return ((x[0]-x[1])*(x[2]-x[3]), (x[0]-x[2])*(x[1]-x[3]))

    a1, a2 = brackets(a)
    b1, b2 = brackets(b)
    assert (odd_sum - 2*(a1*b2 - a2*b1)).expand() == 0


def check_profile_and_radii():
    u = quaternion(T, 1, 1, 1)[:, [3, 1, 2, 0]]
    d = T*T+3
    a, b, c, h = 1+2*T-T*T, (T-1)**2, 2*T, T*(T**3+3*T-2)
    classes = "ABB CBB CAB ACB C".replace(" ", "")
    weights = [{"A": a, "B": b, "C": c}[k] for k in classes] + [h]
    for size in range(3):
        for rows in combinations(range(4), size):
            for cols in combinations(range(4), size):
                mass = sum(w for i, w in zip(COORDS, weights)
                           if {PS[i][r] for r in rows} == set(cols))
                assert (mass - u.extract(rows, cols).det()**2*d**(2-size)).expand() == 0

    intervals = [(0, sp.Rational(1, 5), (1, 2, 4), 34194),
                 (sp.Rational(1, 5), sp.Rational(3, 5), (1, 4, 3), 0)]
    for lo, hi, twice_radii, zeros in intervals:
        numerators = [dict(zip("ABC", twice_radii))[k] for k in classes]
        for numerator, w in zip(numerators, weights):
            margin = numerator*w + 4*h
            assert nonnegative_on_unit_interval(margin.subs(T, lo + (hi-lo)*T).expand())
        yield numerators, zeros


def main():
    check_matching_ratios()
    intervals = list(check_profile_and_radii())
    with TemporaryDirectory() as tmp:
        folder = Path(tmp)
        make_tensor(folder)
        exe = folder / "bernstein"
        run(["g++", "-O3", "-std=c++17", "-fopenmp", str(SPIN / "bernstein.cpp"),
             "-lgmpxx", "-lgmp", "-o", str(exe)], check=True)
        env = dict(os.environ)
        env.setdefault("OMP_NUM_THREADS", "4")
        for mode in ("grid", "coeff"):
            run([exe, mode], cwd=folder, env=env, check=True)
        for numbers, zeros in intervals:
            result = run([exe, "bern", "2", *map(str, numbers)], cwd=folder,
                         env=env, check=True, capture_output=True, text=True)
            assert f"negative 0 zero {zeros} min " in result.stdout
            print(result.stdout.strip())
    print("Verified the matching-ratio identity and both uniform isoclinic certificates.")


if __name__ == "__main__":
    main()

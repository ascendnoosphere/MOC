"""Exact fixed-spectra distinction between scalar and singleton-matched MOC."""
from itertools import permutations
import sympy as sp


def main():
    U = sp.Matrix([[-7, 7, 7, 7], [-11, -7, -5, 1],
                   [1, 7, -11, 5], [-5, 7, -1, -11]]) / 14
    assert U * U.T == sp.eye(4)
    a = (0, 1, 2, (8+2*sp.I)/17)
    b = (1, 2, 3, sp.I)
    prices = sp.Matrix([[-108, -128, -144, -108], [-24, -9, -4, 0],
                        [-32, 0, 12, 0], [0, 0, 0, 0]])
    direction = 3-5*sp.I
    det_value = sp.expand((sp.diag(*a) + U*sp.diag(*b)*U.T).det())
    assert det_value == sp.Rational(7233,833)+sp.Rational(70745,3332)*sp.I
    vertices = {}
    slacks = set()
    for p in permutations(range(4)):
        z = sp.expand(sp.prod(a[i] + b[p[i]] for i in range(4)))
        vertices[p] = z
        slacks.add(sp.re(direction*z) + sum(prices[i,p[i]] for i in range(4)))
    assert slacks == {0, 4, 8}
    value = sp.re(direction*det_value) + sum(
        prices[i,j]*U[i,j]**2 for i in range(4) for j in range(4))
    assert value == -sp.Rational(6,49)
    law = {(0,3,2,1):sp.Rational(16,245),
           (1,3,0,2):sp.Rational(257,588),
           (3,1,2,0):sp.Rational(209,420)}
    assert sum(law.values()) == 1 and min(law.values()) > 0
    assert sp.expand(sum(w*vertices[p] for p,w in law.items())-det_value) == 0
    print('All 24 vertex costs are 0, 4, or 8. The singleton-matched cost is -6/49.')
    print('Three positive scalar weights give the determinant exactly.')


if __name__ == '__main__':
    main()

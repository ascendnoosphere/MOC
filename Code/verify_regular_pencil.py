"""Check the five-permutation pencil certificate in Docs/Cases/Regular.md."""

from math import prod

from sympy import I, Matrix, Rational, diag, eye, symbols


def main():
    rotation = Matrix([
        [-37, 16, 20, -24],
        [-8, -31, -26, -30],
        [-12, 30, -39, 6],
        [32, 22, 2, -33],
    ]) / 51
    assert rotation.T * rotation == eye(4) and rotation.det() == 1
    assert rotation.charpoly().as_poly().discriminant() != 0
    assert sum(abs(x) == Rational(37, 51) for x in rotation) == 1

    t = symbols("t")
    a = (-1, 0, 1, t)
    b = (1 + I, 2 - I, -1 + 2*I, -2 - 2*I)
    # d=det((D_a + R D_b R^T)R). Only the last row depends on t.
    entries = Matrix(4, 4, lambda i, j: (a[i] + b[j]) * rotation[i, j])
    determinant = entries.det(method="domain-ge").expand()

    labels = ("1234", "1243", "3421", "4312", "4321")
    vertices = []
    for label in labels:
        vertices.append(prod(a[i] + b[int(j) - 1] for i, j in enumerate(label)).expand())

    def column(polynomial):
        slope = polynomial.coeff(t)
        intercept = polynomial.subs(t, 0)
        assert (polynomial - t * slope - intercept).expand() == 0
        return Matrix([1, *slope.as_real_imag(), *intercept.as_real_imag()])

    basis = Matrix.hstack(*(column(z) for z in vertices))
    assert basis.det() == 182952
    weights = basis.inv() * column(determinant)
    expected = Matrix([13359257, 879638, 462132, 217210, 4909186]) / 19827423
    assert weights == expected and min(weights) > 0 and sum(weights) == 1
    assert (determinant - sum(w*z for w, z in zip(weights, vertices))).expand() == 0

    facet = (rotation[1, 0]**2 + rotation[3, 2]**2
             + rotation.extract([2, 3], [0, 3]).det()**2
             - rotation.extract([1, 2], [0, 1]).det()**2)
    assert facet == -Rational(20, 867)
    print("Five positive weights reproduce both complex coefficients for every t.")
    print(f"Coefficient matrix determinant {basis.det()}, squared-minor facet {facet}.")


if __name__ == "__main__":
    main()

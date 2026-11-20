"""Numerical common-weight experiments on real first jets and coefficient pencils.

Run with Python 3, NumPy, and SciPy. Counts are numerical LP outcomes.
"""
import argparse
from itertools import combinations, permutations

import numpy as np
from scipy.linalg import qr
from scipy.optimize import linprog


PERMUTATIONS = np.array(list(permutations(range(4))))
SIGNS = np.array([
    (-1) ** sum(p[i] > p[j] for i, j in combinations(range(4), 2))
    for p in PERMUTATIONS
])
REGULAR = np.array([
    [-37, 16, 20, -24], [-8, -31, -26, -30],
    [-12, 30, -39, 6], [32, 22, 2, -33],
]) / 51
HADAMARD = np.array([
    [1, 1, 1, 1], [-1, 1, 1, -1], [-1, -1, 1, 1], [-1, 1, -1, 1],
]) / 2


def jet_features(x, c):
    factors = x[None, :] - c[PERMUTATIONS]
    values = factors.prod(axis=1)
    cofactors = np.column_stack([
        np.delete(factors, j, axis=1).prod(axis=1) for j in range(4)
    ])
    partner_derivatives = -np.take_along_axis(cofactors, PERMUTATIONS.argsort(axis=1), axis=1)
    return np.column_stack([np.ones(24), values, cofactors[:, 3], partner_derivatives])


def pencil_features(x, c, y, d):
    real = x[None, :] - c[PERMUTATIONS]
    slope = y[None, :] - d[PERMUTATIONS]
    # Coefficients of the four factors in the variables s,t with constant 1.
    terms = {(0, 0): np.ones(24)}
    for j in range(4):
        product = {}
        for (k, l), weight in terms.items():
            for key, value in [
                ((k, l), weight), ((k+1, l), real[:, j]*weight),
                ((k, l+1), slope[:, j]*weight),
            ]:
                product[key] = product.get(key, 0) + value
        terms = product
    homogeneous = [v for (k, l), v in terms.items() if k+l == 4]
    return np.column_stack([np.ones(24), *homogeneous]), np.column_stack(list(terms.values()))


def maximum_minimum_weight(features, signed_law):
    normalized = features / np.maximum(abs(features).max(axis=0), 1)
    _, triangular, pivots = qr(normalized, mode="economic", pivoting=True)
    independent = pivots[abs(triangular.diagonal()) > 1e-10]
    matrix = normalized[:, independent].T
    # Write the 24 probabilities as nonnegative residuals plus a common floor.
    result = linprog(
        np.r_[np.zeros(24), -1.0], A_eq=np.c_[matrix, matrix @ np.ones(24)],
        b_eq=matrix @ signed_law, bounds=[(0, None)]*24 + [(None, None)], method="highs",
    )
    if not result.success:
        raise RuntimeError(result.message)
    return result.x[-1]


def run(count):
    rng = np.random.default_rng(3910)
    counts = np.zeros((3, 3), dtype=int)
    for i in range(count):
        x, c = rng.choice(np.arange(-16, 17), 8, replace=False).reshape(2, 4)
        y, d = rng.integers(-9, 10, (2, 4))
        rotation = (REGULAR, HADAMARD, None)[i % 3]
        if rotation is None:
            rotation = np.linalg.qr(rng.standard_normal((4, 4)))[0]
        law = SIGNS * rotation[np.arange(4), PERMUTATIONS].prod(axis=1) / np.linalg.det(rotation)
        features = (jet_features(x, c), *pencil_features(x, c, y, d))
        for k, feature in enumerate(features):
            floor = maximum_minimum_weight(feature, law)
            category = 0 if floor < -1e-8 else 1 if floor < 1e-8 else 2
            counts[k, category] += 1
    print("feature set: negative, near zero, positive")
    for label, row in zip(("first jet", "binary quartic", "translated pencil"), counts):
        print(label, *row)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--count", type=int, default=1600)
    run(parser.parse_args().count)

"""Standalone tests of the stated finite fixtures, not proofs of any theorem."""
from fractions import Fraction
from itertools import combinations, permutations
from math import comb, factorial


def parity(p):
    return (-1) ** sum(a > b for a, b in combinations(p, 2))


def det(a):
    from math import prod

    return sum(
        parity(p) * prod(a[i][j] for i, j in enumerate(p))
        for p in permutations(range(len(a)))
    )


def frame():
    u = [
        [-1, 32, 20, 16],
        [-32, -1, -16, 20],
        [-20, -16, 31, -8],
        [16, -20, 8, 31],
    ]
    assert all(
        sum(r[i] * r[j] for r in u) == (41**2 if i == j else 0)
        for i in range(4)
        for j in range(4)
    )
    z = [[int(i == j) for i in range(3)] for j in range(3)] + [
        [Fraction(x, 41) for x in r[:3]] for r in u
    ]
    test = [(1, 2, 3), (1, 3, 4), (2, 4, 5), (3, 4, 6)]
    coeffs = (1, -1, 1, 1)

    def cover(f, s):
        return int(all((i in s) != (j in s) for i, j in enumerate(f)))

    scores = [
        sum(c * cover(f, s) for c, s in zip(coeffs, test))
        for f in permutations(range(3, 7), 3)
    ]
    assert min(scores) == 0
    squares = [det([z[i] for i in s]) ** 2 for s in test]
    assert squares == [Fraction(c, 1681) for c in (1, 256, 144, 64)]
    score = sum(c * m for c, m in zip(coeffs, squares))
    assert score == Fraction(-47, 1681)
    print(f'Three-frame test: {len(scores)} injections; min 0; frame {score}.')


def rectangles(pairs, nrow, ncol, floor=0):
    yield ()
    for i in range(floor, len(pairs)):
        r, c = pairs[i]
        if r <= nrow and c <= ncol:
            yield from (
                ((r, c),) + rest
                for rest in rectangles(pairs, nrow - r, ncol - c, i)
            )


def rook_count(n, pattern):
    poly = [1]
    for r, c in pattern:
        new = [0] * (len(poly) + min(r, c))
        for j in range(min(r, c) + 1):
            a = comb(r, j) * comb(c, j) * factorial(j)
            for i, b in enumerate(poly):
                new[i + j] += a * b
        poly = new
    return sum((-1) ** i * a * factorial(n - i) for i, a in enumerate(poly))


def hall():
    expected = [(1, 24), (6, 44), (34, 176), (156, 672),
                (569, 3168), (1756, 12096), (4839, 82080)]
    for n in range(1, 11):
        admissible = [(r, c) for r in range(1, n) for c in range(1, n) if r + c <= n]
        eligible = []
        patterns = 0
        for pat in rectangles(admissible, n, n):
            patterns += 1
            m = max((sum(b) for b in pat), default=0)
            d = n - m
            lower = factorial((n-d)//2) * factorial((n+d+1)//2)
            original_lower = factorial(n//2)*factorial((n+1)//2)
            count = rook_count(n, pat)
            assert count >= lower
            if n >= 4:
                assert (count == original_lower) == any(
                    r+c == n and abs(r-c) <= 1 for r, c in pat)
            if d >= 3:
                eligible.append(count)
        if n >= 4:
            assert (len(eligible), min(eligible)) == expected[n-4]
            print(f'Hall n={n}: all {patterns}, eligible {len(eligible)}, min {min(eligible)}')


if __name__ == '__main__':
    frame()
    hall()

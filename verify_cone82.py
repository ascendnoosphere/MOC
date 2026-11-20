"""Verify the supplied integral boundary certificate for the four-letter minor polytope.

Run in any directory with cone82.json next to this script. No external package.
The common sign and zero boundary give nonzero degree on the convex boundary.
"""
from collections import Counter
from itertools import permutations
import json
from pathlib import Path


def determinant(matrix):
    """Integer determinant by pivoted fraction-free elimination."""
    a = [list(row) for row in matrix]
    previous, sign = 1, 1
    for j in range(len(a) - 1):
        if a[j][j] == 0:
            i = next((i for i in range(j+1, len(a)) if a[i][j]), None)
            if i is None:
                return 0
            a[i], a[j] = a[j], a[i]
            sign = -sign
        pivot = a[j][j]
        lead = a[j]
        for i in range(j+1, len(a)):
            row, entry = a[i], a[i][j]
            for k in range(j+1, len(a)):
                row[k] = (pivot * row[k] - entry * lead[k]) // previous
        previous = pivot
    return sign * a[-1][-1]


def image(pi, mask):
    return sum(1 << pi[i] for i in range(4) if mask & (1 << i))


def main():
    d = json.loads(Path(__file__).with_name('cone82.json').read_text())
    ps = list(permutations(range(4)))
    vertices = [[1]+[int(image(p, i) == j) for i, j in d['coordinate_pairs']] for p in ps]
    average_times_24 = [sum(c) for c in zip(*vertices)]
    active = []
    for facet in d['facets']:
        values = [sum(x*y for x,y in zip(v, facet['normal'])) for v in vertices]
        assert min(values) == 0 and max(values) > 0
        zero = frozenset(i for i,x in enumerate(values) if x == 0)
        assert zero == frozenset(facet['active'])
        active.append(zero)
    assert len(set(active)) == len(active) == 82
    boundary, multiplicity = Counter(), Counter()
    determinants, simplices, used_facets = Counter(), set(), set()
    for cell in d['chains']:
        v = tuple(cell['vertices'])
        orient, facet = cell['orientation'], cell['facet']
        assert len(v) == len(set(v)) == 13 and v == tuple(sorted(v)) and v not in simplices
        assert set(v) <= active[facet] and abs(orient) == 1
        simplices.add(v)
        volume = determinant([average_times_24] + [vertices[i] for i in v])
        determinants[(volume * orient > 0) - (volume * orient < 0)] += 1
        if volume:
            used_facets.add(facet)
        for i in range(13):
            ridge = v[:i]+v[i+1:]
            multiplicity[ridge] += 1
            boundary[ridge] += (-1)**i * orient
    assert len(used_facets) == 82 and len(simplices) == 9050
    assert len(multiplicity) == 58825 and set(multiplicity.values()) == {2}
    assert set(boundary.values()) == {0}
    assert determinants[0] == 2204 and max(determinants[-1],determinants[1]) == 6846
    # Any nonzero cone volume proves full affine dimension 13. Each facet
    # contains a nondegenerate 12-simplex. The resulting positive closed
    # chain covers the boundary sphere (after a common subdivision).
    print("82 distinct supporting facets, 9050 simplices, 58825 canceled ridges; coherent degree checked.")


if __name__ == '__main__':
    main()

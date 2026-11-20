"""Exact certificates for the spin-3/2 and spin-2 MOC families.

Run "python verify_spin_moc.py" with SymPy installed. This script requires no
optimization solver. It verifies exact polynomial identities and nonnegative
rational numbers. Row and column indices in the script start at zero.
"""

from itertools import combinations, permutations
from math import comb
from functools import reduce
from operator import mul
import sympy as sp

T, Z, Y, X = sp.symbols("t z y x")


def model(n):
    """Matrix of permutation-orbit profiles and polynomial spin profiles."""
    degree = n - 1

    def reverse(pi):
        return tuple(n - 1 - value for value in reversed(pi))

    def orbit(pi):
        inverse = tuple(pi.index(i) for i in range(n))
        return tuple(sorted({pi, inverse, reverse(pi), reverse(inverse)}))

    orbits = sorted({orbit(pi) for pi in permutations(range(n))})
    indices = [
        (rows, cols) for k in range(n // 2 + 1)
        for rows in combinations(range(n), k)
        for cols in combinations(range(n), k)
    ]
    orbit_matrix = sp.Matrix([
        [sp.Rational(sum({pi[i] for i in rows} == set(cols) for pi in block),
                     len(block)) for block in orbits] for rows, cols in indices
    ])
    # In the unnormalized symmetric power use z=tan(theta). Normalize each
    # column j by sqrt(C(m,j)), row i by its reciprocal, and divide by
    # (1+z**2)**(m/2). Squaring removes all square roots.
    columns = [
        sp.Poly((1 + Z*Y)**(degree - j) * (Y - Z)**j, Y)
        for j in range(n)
    ]
    spin = sp.Matrix(n, n, lambda i, j: columns[j].nth(i))

    def squared_minor(rows, cols):
        norm = sp.Rational(reduce(mul, (comb(degree, j) for j in cols), 1),
                           reduce(mul, (comb(degree, i) for i in rows), 1))
        square = sp.Poly(spin.extract(rows, cols).det()**2, Z)
        result = 0
        for (power,), coefficient in square.terms():
            assert power % 2 == 0
            result += coefficient * T**(power//2) * (1-T)**(degree*len(rows)-power//2)
        return sp.expand(norm * result)

    profile = sp.Matrix([squared_minor(rows, cols) for rows, cols in indices])
    return orbit_matrix, profile


def nonnegative_on_unit_interval(expression):
    """Remove endpoint zeros. Interior roots of a positive polynomial are even."""
    poly = sp.Poly(expression, T)
    if poly.is_zero:
        return True
    for factor in [sp.Poly(T, T), sp.Poly(T-1, T)]:
        while poly.rem(factor).is_zero:
            poly = poly.exquo(factor)
    if expression.subs(T, sp.Rational(1, 101)) <= 0:
        return False
    return all(mult % 2 == 0 or factor.count_roots(0, 1) == 0
               for factor, mult in poly.sqf_list()[1])


def check_four():
    whole, profile = model(4)
    rows = whole.T.rref()[1]
    matrix = whole.extract(rows, range(whole.cols))
    values = profile.extract(rows, [0])
    assert matrix.shape == (8, 13)
    basis = matrix.rref()[1]
    vector = whole.extract(range(whole.rows), basis) * matrix.extract(range(8), basis).inv() * values
    assert all(sp.expand(a - b) == 0 for a, b in zip(vector, profile))

    # An affine facet in dimension seven contains seven affinely independent
    # vertices. The first coordinate of each column is 1. Thus every facet
    # occurs among these exact null spaces.
    facets = set()
    for subset in combinations(range(matrix.cols), 7):
        normals = matrix.extract(range(8), subset).T.nullspace()
        if len(normals) != 1:
            continue
        normal = normals[0]
        signs = normal.T * matrix
        if all(x <= 0 for x in signs):
            normal = -normal
            signs = -signs
        if all(x >= 0 for x in signs):
            facets.add(tuple(normal / sp.gcd_list(list(normal))))
    assert len(facets) == 20
    exceptional = set()
    for normal in facets:
        value = sp.expand((sp.Matrix(normal).T * values)[0])
        if not nonnegative_on_unit_interval(value):
            exceptional.add(value)
    p = 1 - 4*T - 3*T**2 + 22*T**3 - 15*T**4
    assert exceptional == {p, sp.expand(p.subs(T, 1-T))}
    assert sp.Poly(p, T).count_roots(0, 1) == 2
    for a, b in [(30, 31), (46, 47)]:
        assert sp.Poly(p, T).count_roots(sp.Rational(a,100), sp.Rational(b,100)) == 1
    assert p.subs(T, sp.Rational(2,5)) == -sp.Rational(7,125)
    print("n=4: 20 facets. Exactly p(t) and p(1-t) change sign.")


def check_five():
    matrix, profile = model(5)
    assert matrix.shape == (126, 45)
    degree = max(sp.degree(value, T) for value in profile)
    assert degree == 6
    for (left, right), certificates in WEIGHTS.items():
        a, b = sp.Rational(left), sp.Rational(right)
        value_polys = [sp.Poly(v.subs(T, a+(b-a)*X), X) for v in profile]
        assert len(certificates) == degree + 1
        for i, certificate in enumerate(certificates):
            weights = sp.zeros(matrix.cols, 1)
            for j, weight in certificate:
                assert weights[j] == 0
                weights[j] = sp.Rational(weight)
            assert all(w >= 0 for w in weights) and sum(weights) == 1
            coeffs = sp.Matrix([
                sum(poly.nth(j)*sp.Rational(comb(i,j), comb(degree,j))
                    for j in range(i+1)) for poly in value_polys
            ])
            assert matrix * weights == coeffs
        print(f"n=5: all seven Bernstein profiles verified on [{a}, {b}].")


# Each pair assigns mass to one orbit. Distribute it uniformly over its members.
WEIGHTS = {('0', '1/8'): [[(0, '1')],
                [(0, '7/12'), (1, '1/6'), (2, '1/4')],
                [(0, '37/120'),
                 (1, '9/40'),
                 (2, '59/160'),
                 (4, '1/80'),
                 (5, '1/20'),
                 (6, '3/160'),
                 (16, '1/60')],
                [(0, '71/640'),
                 (1, '139/640'),
                 (2, '573/1280'),
                 (4, '9/320'),
                 (5, '39/320'),
                 (8, '3/640'),
                 (10, '3/128'),
                 (14, '1/1280'),
                 (16, '13/320'),
                 (18, '3/640')],
                [(1, '1307/7680'),
                 (2, '231/512'),
                 (3, '7/1280'),
                 (4, '223/6144'),
                 (5, '123/640'),
                 (7, '7/1280'),
                 (8, '13/640'),
                 (10, '559/15360'),
                 (12, '1/5120'),
                 (16, '21/320'),
                 (18, '1/64'),
                 (22, '1/1280'),
                 (27, '1/3840'),
                 (31, '1/30720')],
                [(1, '251/4096'),
                 (2, '1341/4096'),
                 (3, '839/8192'),
                 (5, '2177/8192'),
                 (6, '111/2048'),
                 (8, '253/8192'),
                 (10, '7/256'),
                 (14, '61/12288'),
                 (15, '7/8192'),
                 (16, '1435/16384'),
                 (18, '533/16384'),
                 (22, '27/8192'),
                 (23, '1/6144'),
                 (27, '21/16384'),
                 (34, '1/16384')],
                [(1, '1/32768'),
                 (2, '6753/32768'),
                 (3, '759/8192'),
                 (4, '859/131072'),
                 (5, '1323/4096'),
                 (6, '4489/32768'),
                 (8, '105/2048'),
                 (12, '293/131072'),
                 (14, '343/32768'),
                 (16, '441/4096'),
                 (18, '3533/65536'),
                 (22, '337/131072'),
                 (26, '409/65536'),
                 (32, '1/131072'),
                 (34, '5/65536'),
                 (42, '1/4096')]],
 ('49/100', '1/2'): [[(0, '6225013/62500000000'),
                      (1, '632275273/250000000000'),
                      (2, '7497/15625000000'),
                      (11, '119083268563/1000000000000'),
                      (12, '18735003/62500000000'),
                      (14, '11992690073/1000000000000'),
                      (15, '18735003/15625000000'),
                      (16, '55820849/200000000000'),
                      (18, '918015147/31250000000'),
                      (22, '4666485159/125000000000'),
                      (24, '43218713097/125000000000'),
                      (26, '41385621627/125000000000'),
                      (27, '120575819/1000000000000'),
                      (28, '104233390891/1000000000000'),
                      (32, '694664523/125000000000'),
                      (40, '11062629109/1000000000000')],
                     [(0, '499/7500000'),
                      (1, '293434129/60000000000'),
                      (2, '1/6250000'),
                      (11, '1152955349/10000000000'),
                      (14, '744970177/60000000000'),
                      (15, '2499/3125000'),
                      (18, '30735201/1250000000'),
                      (22, '155704801/5000000000'),
                      (23, '161314517/60000000000'),
                      (24, '109531219/312500000'),
                      (26, '845544147/2500000000'),
                      (28, '1026956553/10000000000'),
                      (32, '24767197/5000000000'),
                      (33, '2499/12500000'),
                      (39, '833/3125000'),
                      (40, '45122091/4000000000')],
                     [(0, '1499/37500000'),
                      (1, '41972383/6000000000'),
                      (2, '1/31250000'),
                      (11, '111053207/1000000000'),
                      (14, '79073503/6000000000'),
                      (15, '7499/15625000'),
                      (18, '617351/31250000'),
                      (22, '3117049/125000000'),
                      (23, '31547591/6000000000'),
                      (24, '17764999/50000000'),
                      (26, '86356783/250000000'),
                      (28, '100993231/1000000000'),
                      (32, '527661/125000000'),
                      (33, '7499/62500000'),
                      (39, '7499/46875000'),
                      (40, '72488327/6000000000')],
                     [(1, '360879/40000000'),
                      (5, '3/12500'),
                      (11, '2132741/20000000'),
                      (12, '3/50000'),
                      (14, '564047/40000000'),
                      (18, '37197/2500000'),
                      (22, '184791/10000000'),
                      (23, '319471/40000000'),
                      (24, '7203/20000'),
                      (26, '1763559/5000000'),
                      (27, '1/12500'),
                      (28, '1982541/20000000'),
                      (32, '36003/10000000'),
                      (40, '516239/40000000'),
                      (41, '1/50000')],
                     [(0, '1/150000'),
                      (1, '27047/2400000'),
                      (11, '122929/1200000'),
                      (14, '34919/2400000'),
                      (15, '1/12500'),
                      (18, '249/25000'),
                      (22, '1249/100000'),
                      (23, '25019/2400000'),
                      (24, '7301/20000'),
                      (26, '36007/100000'),
                      (27, '1/37500'),
                      (28, '116917/1200000'),
                      (32, '237/100000'),
                      (33, '1/50000'),
                      (40, '11049/800000')],
                     [(1, '43/3200'),
                      (11, '157/1600'),
                      (14, '29/1920'),
                      (18, '1/200'),
                      (22, '1/160'),
                      (23, '5/384'),
                      (24, '37/100'),
                      (26, '147/400'),
                      (28, '153/1600'),
                      (32, '1/800'),
                      (40, '47/3200')],
                     [(1, '1/64'),
                      (11, '3/32'),
                      (14, '1/64'),
                      (23, '1/64'),
                      (24, '3/8'),
                      (26, '3/8'),
                      (28, '3/32'),
                      (40, '1/64')]]}



# Certificates for all remaining spin-2 intervals, expressed as bases of the
# orbit matrix. On a boundary interval one indicated linear inequality is
# required. Each basis gives the barycentric coordinates as exact polynomials.
FIVE_BASES = [
    ("1/8","7/50",None,(1,2,3,5,6,8,10,11,13,16,17,22,23,26,29,32)),
    ("7/50","3/20",None,(2,3,5,6,7,8,12,13,16,17,18,22,25,26,35,37)),
    ("3/20","31/200",None,(2,3,4,5,6,8,9,14,15,16,17,20,22,25,33,35)),
    ("31/200","159/1000",None,(1,2,3,4,5,6,8,9,13,16,17,22,26,31,35,36)),
    ("159/1000","161/1000",0,(1,2,3,5,6,8,9,12,13,16,17,22,26,29,31,32)),
    ("191/1000","193/1000",0,(3,4,5,6,7,8,9,13,16,17,19,20,22,29,31,33)),
    ("193/1000","197/1000",None,(4,5,6,7,8,9,12,17,20,22,24,26,27,29,31,39)),
    ("197/1000","199/1000",None,(3,4,5,6,7,8,9,12,17,19,20,22,24,27,29,36)),
    ("199/1000","1/5",None,(3,4,5,6,7,8,9,10,12,17,19,20,22,34,42,43)),
    ("1/5","201/1000",None,(0,4,5,6,7,8,12,15,17,18,19,20,22,34,41,44)),
    ("201/1000","403/2000",1,(4,5,6,7,8,12,14,15,17,18,19,20,22,26,34,39)),
    ("489/1000","49/100",3,(0,1,5,8,11,12,14,18,22,24,26,27,28,32,34,40)),
]
FIVE_DUALS = [
    (1,-1,0,-2,0,0,2,-1,0,-2,0,0,3,0,-2,-1),
    (1,0,0,-1,0,1,-1,0,-1,0,-1,0,-1,0,0,-1),
    (1,-5,-6,-1,-2,-1,1,8,-1,8,2,6,-4,1,1,2),
    (1,-3,-4,-1,-2,-1,1,4,-1,4,2,4,-2,1,1,1),
]


def check_five_full():
    whole, profile = model(5)
    rows = whole.T.rref()[1]
    matrix = whole.extract(rows, range(whole.cols))
    values = profile.extract(rows, [0])
    assert matrix.shape == (16, 45)
    basis = matrix.rref()[1]
    recovered = whole.extract(range(whole.rows), basis)*matrix.extract(range(16),basis).inv()*values
    assert all(sp.expand(x-y) == 0 for x,y in zip(recovered,profile))
    A = 1-12*T+32*T**2+72*T**3-364*T**4+456*T**5-184*T**6
    B = 8-88*T+336*T**2-558*T**3+420*T**4-117*T**5
    C = 1-25*T**2+40*T**3+55*T**4-132*T**5+62*T**6
    D = 6-32*T+36*T**2+48*T**3-102*T**4+45*T**5
    half = sp.Rational(1,2)
    tests = [A, B, C, D]
    for dual, evaluated in zip(FIVE_DUALS,[A,T*B,C,T*D]):
        functional = sp.Matrix(dual).T
        assert all(x>=0 for x in functional*matrix)
        assert sp.expand((functional*values)[0]-evaluated) == 0
    covered = [(sp.Rational(a),sp.Rational(b)) for a,b in WEIGHTS]

    for left,right,required,cols in FIVE_BASES:
        a,b = sp.Rational(left),sp.Rational(right)
        covered.append((a,b))
        bary = matrix.extract(range(16), cols).inv()*values
        assert sp.expand(sum(bary)-1)==0
        def positive(f):
            return nonnegative_on_unit_interval(sp.expand(f.subs(T,a+(b-a)*T)))
        for entry in bary:
            f=sp.expand(entry)
            if positive(f):
                continue
            assert required is not None
            quotient,remainder=sp.div(f, tests[required],T)
            assert remainder==0 and positive(quotient)

    # Every point in these four closed gaps has a strictly negative dual.
    for left,right,j in [("161/1000","191/1000",0),("403/2000","315/1000",1),
                         ("315/1000","43/100",2),("43/100","489/1000",3)]:
        a,b=sp.Rational(left),sp.Rational(right)
        covered.append((a,b))
        h=sp.Poly(tests[j],T)
        assert h.eval(a)<0 and h.count_roots(a,b)==0

    # Check that the verified rational intervals cover the full half-domain.
    right=sp.Integer(0)
    for a,b in sorted(covered):
        assert a<=right
        right=max(right,b)
    assert right==half

    # Four algebraic endpoints on [0,1/2]. Two roots of A and one each of B,D
    # supply the points at which membership actually changes. C joins the two
    # overlapping negative regions between the third and fourth endpoints.
    for left,right,j in [("159/1000","161/1000",0),("191/1000","193/1000",0),
                         ("201/1000","403/2000",1),("489/1000","49/100",3)]:
        a,b=sp.Rational(left),sp.Rational(right)
        assert sp.Poly(tests[j],T).count_roots(a,b)==1
        assert tests[j].subs(T,a)*tests[j].subs(T,b)<0
        for i,h in enumerate(tests):
            if i!=j:
                assert h.subs(T,a)>0 and sp.Poly(h,T).count_roots(a,b)==0
    print("n=5: complete classification on [0,1/2]. Four dual inequalities are necessary and sufficient.")




def check_neighborhoods():
    """Recover a uniform positive lower bound on individual permutation weights."""
    from math import factorial
    for n, center, cols, delta, radius in [
        (4,sp.Rational(1,5),(0,1,2,3,5,6,7,9),sp.Rational(6,625),sp.Rational(1,20000)),
        (5,sp.Rational(2,15),FIVE_BASES[0][-1],sp.Rational(128,2278125),sp.Rational(8,170859375)),
    ]:
        matrix, profile = model(n)
        sizes = [k for k in range(n//2+1)
                 for i in combinations(range(n),k) for j in combinations(range(n),k)]
        uniform = sp.Matrix([sp.Rational(1,comb(n,k)) for k in sizes])
        rows = matrix.T.rref()[1]
        remaining = profile.subs(T,center)-delta*uniform
        block = matrix.extract(rows, cols)
        residue = block.inv()*remaining.extract(rows,[0])
        assert min(residue)>=0 and sum(residue)==1-delta
        assert matrix.extract(range(matrix.rows),cols)*residue==remaining
        assert delta/(2*n*factorial(n))==radius
        print(f"n={n}: operator-norm radius {radius} at t={center}.")


if __name__ == "__main__":
    check_four()
    check_five()
    check_five_full()
    check_neighborhoods()

"""An exact orthogonal profile outside all translates of the certified region."""
from itertools import combinations, permutations
from sympy import Matrix, Rational
from verify_scalar import COORDS, PS, R

n=4
u=Matrix([[-7,7,7,7],[-11,-7,-5,1],[1,7,-11,5],[-5,7,-1,-11]])/14
assert u.T*u==Matrix.eye(n)
ij=[(i,j) for k in range(3) for i in combinations(range(4),k) for j in combinations(range(4),k)]
P=Matrix([[int({p[i] for i in I}==set(J)) for p in PS] for I,J in ij])
L=P.extract(range(53),COORDS)
rows=L.T.rref()[1]
J=L.extract(rows,range(14)).inv()
costs=[(2*J*P.extract(rows,range(24)))[13,j] for j in range(24)]
assert min(costs)==0
rho={(a,b):u.extract(a,b).det()**2 for a,b in ij}
minimum=1
margins=[]
second=[Rational(i,12) for i in (4,72,72,18,72,3,18,4,3,4,2,3,18)]
new_margins=[]
for r in PS:
    for c in PS:
        vals=Matrix([rho[tuple(sorted(r[i] for i in ij[k][0])),
                         tuple(sorted(c[j] for j in ij[k][1]))] for k in rows])
        w=J*vals
        p=2*w[-1]
        minimum=min(p,minimum)
        if p<0:
            margins.append(min(R[i]*w[i]+p for i in range(13)))
            new_margins.append(min(second[i]*w[i]+p for i in range(13)))
assert max(new_margins)>=0
assert minimum == -Rational(3,98)
assert len(margins)==12 and max(margins)==-Rational(3,196)
print("All 576 relabelings checked; smallest facet is -3/98, and best relevant margin is -3/196.")
print("Another certified simplex contains this orthogonal profile.")

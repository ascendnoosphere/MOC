#!/usr/bin/env python3
"""Independent exact checks of Zheng's Appendix A and key T85 identities.
Requires SymPy. Does NOT establish the missing supplementary cases."""
from itertools import permutations,combinations
from sympy import Matrix, symbols, prod, expand, Poly
p=list(permutations(range(4)))
B=['12345678','12345867','12364578','12384567','12384756',
   '14235678','14235867','16234578','16253478','18234567',
   '18234756','18253467','18273456','18273645']
z=symbols('z1:9');m=symbols('m0:14')
def brackets(s):
    return expand(prod(z[int(s[i])-1]-z[int(s[i+1])-1]
                       for i in range(0,8,2)))
b=list(map(brackets,B))
mon=[prod(z[i] for i in I) for I in combinations(range(8),4)]
bc=[Poly(f,*z) for f in b]
M=Matrix([[f.coeff_monomial(t) for f in bc] for t in mon])
r=M.T.rref()[1];assert len(r)==14
BM=M[list(r),:];inv=BM.inv();rows=[]
for s in p:
    f=Poly(expand(prod(z[i]-z[4+s[i]] for i in range(4))),*z)
    q=Matrix([f.coeff_monomial(t) for t in mon])
    v=inv*q[list(r),:];assert M*v==q;rows.append(list(v))
P=Matrix(rows)
assert P[[0,1,2,3,4,6,7,8,9,10,12,13,16,18],:].det()==1
assert P[:,13]==Matrix([1]*24)
C=(m[13]*(m[0]*m[6]-m[1]*m[5])
   -m[0]*m[9]*(m[0]+m[1]+m[2]+m[3]+m[5]+m[7]+m[9])
   -m[1]*m[5]*m[9]
   +m[10]*(-m[0]*m[3]-m[0]*m[9]+m[1]*m[2]+m[1]*m[7])
   +m[11]*(-m[0]*m[7]-m[0]*m[9]+m[2]*m[5]+m[3]*m[5])
   +m[12]*(-m[0]*m[9]+m[1]*m[7]-m[2]*m[6]-m[2]*m[9]+m[3]*m[5]+m[3]*m[7])
   +m[2]*m[10]*m[11]-m[3]*m[8]*m[10]-m[4]*m[7]*m[11]+m[4]*m[8]*m[9])
D=[C.diff(v) for v in m]
assert all(expand(f.subs(dict(zip(m,b)),simultaneous=True))==0 for f in D)
mon2=[m[i]*m[j] for i,j in [(10,11),(9,12),(8,10),(8,9),
                             (7,12),(4,11),(4,9),(4,8),(4,7),
                             (3,12),(3,8),(3,7),(2,12),(1,5)]]
assert Matrix([[Poly(f,*m).coeff_monomial(t) for t in mon2]
               for f in D]).det()==1
print('Appendix A: matching coordinates and all 14 cubic-gradient identities passed',flush=True)
for k in range(7):
    ss={z[k]:z[k+1],z[k+1]:z[k]}
    b1=[Poly(f.subs(ss,simultaneous=True),*z) for f in b]
    T=(inv*Matrix([[f.coeff_monomial(mon[i]) for f in b1] for i in r])).T
    assert T*T==Matrix.eye(14)
    assert expand(C.subs(dict(zip(m,T*Matrix(m))),simultaneous=True)+C)==0
print('Appendix A: seven alternating cubic actions passed',flush=True)
a=symbols('z1:8');z1,z2,z3,z4,z5,z6,z7=a
w,z0,g5,g7,g9,g14,g18=symbols('w z0 gamma5 gamma7 gamma9 gamma14 gamma18')
coords=[-z4-z7-g7,z2+z4+z5+w+2*g7-g9,-w-g18+g5+2*g7-g9+g14,
        -z2-g7+g9-g14,z7,z3+z6+z7+w,z1-z2-z3-z5-z6-w,
        -z3-g5-g7+g9,z4,-z1+z2+z3,-z3-z7-w,-z2-z4-w,z4+z7+w,z1+w+z0]
variables=[*a,w,z0,g5,g7,g9,g14,g18]
assert Matrix(coords).jacobian(variables).det()==-1
F=P*Matrix(coords);H=[expand(v-F[0]) for v in F]
for k,g in zip([5,7,9,14,18],[g5,g7,g9,g14,g18]):
    assert H[k]==g
sub=dict(zip(m,coords))
Ds=[expand(f.subs(sub,simultaneous=True)) for f in D]
assert expand(sum(Ds[i]*sg for i,sg in [(2,-1),(3,1),(4,-1),(7,1),
             (8,-1),(9,-1),(10,1),(11,1),(12,-1),(13,1)])
              -(-g7*(z1+w)+g18*(g9-g7)-g5*g14))==0
assert expand(Ds[13]-Ds[2]-(-(w+z5)*(w+z6)+g7*(w+z5)+(g9-g7)*z6))==0
assert expand(Ds[1]-Ds[1].subs(z0,0)+(z3+w+z6+z7)*z0)==0
print('Section 5: coordinate determinant and (5.13), (5.14), (5.16) passed',flush=True)

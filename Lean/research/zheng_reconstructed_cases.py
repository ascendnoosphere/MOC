#!/usr/bin/env python3
"""Exact certificate for seven reconstructed exceptional contact cases.
Requires SymPy. The assertions are the certificate checks; do not use -O.
No original supplementary proofs or numerical feasibility assumptions.
"""
from itertools import combinations, permutations, combinations_with_replacement
from math import prod
from sympy import Matrix, symbols, Poly, expand, Rational

perms = list(permutations(range(4)))
idx = {p: i for i, p in enumerate(perms)}
z = symbols('z0:8')
B = ['12345678','12345867','12364578','12384567','12384756',
     '14235678','14235867','16234578','16253478','18234567',
     '18234756','18253467','18273456','18273645']
b = [expand(prod(z[int(s[i])-1]-z[int(s[i+1])-1]
                 for i in range(0,8,2))) for s in B]
mon = [prod(z[i] for i in I) for I in combinations(range(8),4)]
M = Matrix([[Poly(f,*z).coeff_monomial(t) for f in b] for t in mon])
rows = M.T.rref()[1]; assert len(rows)==14
inv = M[list(rows),:].inv()
P = []
for p in perms:
    f=Poly(expand(prod(z[i]-z[4+p[i]] for i in range(4))),*z)
    v=Matrix([f.coeff_monomial(t) for t in mon])
    q=inv*v[list(rows),:]; assert M*q==v
    P.append(list(q))
P=Matrix(P); rows=[0,1,2,3,4,6,7,8,9,10,12,13,16,18]
assert P[rows,:].det()==1
inv=P[rows,:].inv()
Fdesc=['1,4','12,34','13,34','14,34','1,3','12,24','4,1','3,1','12,23','14,23','13,24','13,23','14,24','2,1','1,2','12,14','2,4','3421+','3412-','2413-','2431+','4,2','3412+','14,12','4312+','3142-','4132-','3,2','3421-','13,12','4321-','4123+','3124+','12,13','4321+','4312-','2,3','2341+','2314-','14,13','4213+','4,3','4123-','2413+','2143-','13,14','3241-','3,4','3142+','2143+','2341-','1423-','1342+','13,13','4231-','3,3','4132+','2431-','2134+','14,14','3214+','4,4','3124-','2134-','2314+','1432+','1324-','2,2','4213-','3241+','4231+','3214-','12,12','1243+','1432-','1423+','1234-','1342-','1234+','1243-','1324+','1,1']
def evt(I,J):
    return tuple(int(tuple(sorted(p[i] for i in I))==tuple(sorted(J))) for p in perms)
F=[]; minor=[]
for s in Fdesc:
    minor.append(',' in s)
    if minor[-1]:
        I,J=s.split(','); v=evt(tuple(int(i)-1 for i in I),tuple(int(j)-1 for j in J))
    else:
        q=tuple(int(i)-1 for i in s[:4]); e=1 if s[-1]=='+' else -1
        t=[sum(a==b for a,b in zip(q,p)) for p in perms]
        A=evt((0,1),(q[0],q[2])); B0=evt((0,1),(q[1],q[3]))
        D=evt((0,2),(q[0],q[1])); E=evt((0,2),(q[2],q[3]))
        v0=[x+e*(a+b-d-f) for x,a,b,d,f in zip(t,A,B0,D,E)]
        assert all(x%2==0 for x in v0)
        v=tuple(x//2 for x in v0)
    F.append(v)
assert len(set(F))==82 and sum(minor)==34
L=[inv*Matrix(v)[rows,:] for v in F]
assert all(P*l==Matrix(f) for l,f in zip(L,F))
assert all(x.q==1 for l in L for x in l)
V=[tuple(int(x) for x in l) for l in L]

def C(m):
    return (m[13]*(m[0]*m[6]-m[1]*m[5])
      -m[0]*m[9]*(m[0]+m[1]+m[2]+m[3]+m[5]+m[7]+m[9])-m[1]*m[5]*m[9]
      +m[10]*(-m[0]*m[3]-m[0]*m[9]+m[1]*m[2]+m[1]*m[7])
      +m[11]*(-m[0]*m[7]-m[0]*m[9]+m[2]*m[5]+m[3]*m[5])
      +m[12]*(-m[0]*m[9]+m[1]*m[7]-m[2]*m[6]-m[2]*m[9]+m[3]*m[5]+m[3]*m[7])
      +m[2]*m[10]*m[11]-m[3]*m[8]*m[10]-m[4]*m[7]*m[11]+m[4]*m[8]*m[9])

def add(*v): return tuple(sum(x) for x in zip(*v))
def polar(a,b,c):
    return C(add(a,b,c))-C(add(a,b))-C(add(a,c))-C(add(b,c))+C(a)+C(b)+C(c)

def swap(p,i,j):
    p=list(p);p[i],p[j]=p[j],p[i];return tuple(p)
rect=set()
for p in perms:
    for k in range(1,4):
        i,j=[x for x in range(4) if x not in (0,k)]
        q=swap(p,0,k);r=swap(p,i,j);s=swap(q,i,j)
        rect.add(frozenset(idx[x] for x in (p,q,r,s)))
assert len(rect)==18

def sign(p):return (-1)**sum(p[i]>p[j] for i,j in combinations(range(4),2))
tri=[]
for i in range(4):
    for j in range(4):
        f=[p for p in perms if p[i]==j]
        tri.append((frozenset(idx[p] for p in f if sign(p)==1),
                    frozenset(idx[p] for p in f if sign(p)==-1)))

# The six-contact sets use the author's Appendix E numbering.
T={1:{0,1,2,3,6,7},18:{0,1,3,6,7,8},19:{0,1,4,6,7,8},20:{0,1,5,6,7,8},
   21:{0,3,5,9,11,12},22:{2,3,4,8,10,12},23:{2,3,5,9,11,12}}
# Certificate format: (i,j): tuple of minor indices, with repeated indices
# denoting multiplicities. Each identity is f_i+f_j=sum(right side).
R={1:{},
18:{(0,17):(1,3,6,15),(0,28):(1,2,5,27),(2,17):(4,6,15),(3,28):(4,5,27),(5,17):(3,6,16),(15,28):(2,16,27),(17,28):(4,6,16,27)},
19:{(0,22):(1,3,5,21),(2,22):(4,5,21),(2,34):(0,6,33),(4,34):(1,3,6,33),(6,22):(1,4,5,23),(21,34):(0,1,23,33),(22,34):(1,1,3,5,23,33)},
20:{(0,28):(1,2,5,27),(2,34):(0,6,33),(3,28):(4,5,27),(4,34):(1,3,6,33),(28,34):(1,5,6,27,33)},
21:{(1,40):(0,7,39),(9,40):(2,7,41)},
22:{(1,54):(0,6,53),(10,70):(0,6,72),(53,70):(1,55,67),(54,70):(0,6,55,67),(54,72):(10,55,67)},
23:{(1,40):(0,7,39),(12,68):(0,7,72),(39,68):(1,41,67),(40,68):(0,7,41,67),(40,72):(12,41,67)}}

def verify_case(n):
    t=set(T[n]); assert any(r<=t for r in rect) or any(a|b<=t for a,b in tri)
    while True:
        old=len(t)
        for r in rect:
            if len(r&t)>=3:t|=r
        for a,b in tri:
            if len(a&t)>=2 and len(b&t)>=2:t|=a|b
        if len(t)==old:break
    A=[i for i in range(82) if all(F[i][j]==0 for j in t)]
    for (i,j),rhs in R[n].items():
        assert i in A and j in A and not(minor[i] and minor[j])
        assert all(k in A and minor[k] for k in rhs)
        assert add(F[i],F[j])==add(*(F[k] for k in rhs))
    maximal=[]
    for bits in range(1<<len(A)):
        S={i for k,i in enumerate(A) if bits>>k&1}
        if all(minor[i] for i in S):continue
        if any(i in S and j in S for i,j in R[n]):continue
        if any(not any(tuple(sorted((i,j))) in R[n] for j in S) for i in A if i not in S):continue
        maximal.append(sorted(S))
    # Polar signs are the signs of cubic coefficients, including repeated
    # indices, up to positive factors.
    for S in maximal:
        assert any(all(e*polar(V[i],V[j],V[k])>=0 for i,j,k in combinations_with_replacement(S,3))
                   and all(e*C(V[i])>0 for i in S if not minor[i]) for e in (-1,1))
    return (n,sorted(t),A,maximal)

# Obstruction to using one common law on two disjoint coincidence
# hypersurfaces: z0=z1 or z2=z4.
def double_collision_obstruction():
    c=[]
    for i,j in [(0,1),(2,4)]:
        polys=[Poly(f.subs(z[j],z[i]),*z) for f in b]
        terms=sorted(set.union(*(set(f.monoms()) for f in polys)))
        c.extend([f.coeff_monomial(t) for f in polys] for t in terms)
    W=Matrix(c);assert W.rank()==12
    assert W.col_join(L[76].T).rank()==12
    Q=Matrix([[1,4,4,4],[-4,1,4,-4],[-4,-4,1,4],[-4,4,-4,1]])/7
    assert Q*Q.T==Matrix.eye(4) and Q.det()==1
    w=Matrix([sign(p)*prod(Q[i,p[i]] for i in range(4)) for p in perms])
    assert min(F[76])>=0 and (Matrix(F[76]).T*w)[0]==-Rational(158,2401)

if __name__=='__main__':
    from concurrent.futures import ProcessPoolExecutor
    with ProcessPoolExecutor(max_workers=4) as ex:
        results=list(ex.map(verify_case,sorted(T)))
    for n,t,A,S in results:
        print('T'+str(n),'VERIFIED; closure',t,'active rays',A,'maximal nonminor supports',S)
    double_collision_obstruction()
    print('Two-disjoint-coincidence common-law obstruction verified.')

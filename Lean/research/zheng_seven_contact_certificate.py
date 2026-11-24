#!/usr/bin/env python3
"""Exact checks for the seven-contact reduction and fifteen seven-contact cases.
Requires SymPy. Assertions are the certificate; do not use -O.
"""
from itertools import combinations, combinations_with_replacement, product
from math import prod
from sympy import symbols, Matrix, expand, cancel, rem, invert, fraction, Rational
from zheng_reconstructed_cases import perms as P,F,V,minor,C,polar,rect,tri
idx={p:i for i,p in enumerate(P)}
def comp(p,q):return tuple(p[q[i]] for i in range(4))
def inv(p):return tuple(p.index(i) for i in range(4))
G=[tuple(idx[comp(a,comp(inv(p) if tr else p,b))] for p in P)
   for a,b in product(P,repeat=2) for tr in (0,1)]
assert len(set(G))==1152
Z={i:frozenset(j for j,x in enumerate(f) if not x) for i,f in enumerate(F) if not minor[i]}
ref=Z[76]
assert {frozenset(g[i] for i in ref) for g in G}==set(Z.values())
def orbit(t):return {tuple(sorted(g[i] for i in t)) for g in G}
def mixed_orbits(k):
    todo=set(combinations(sorted(ref),k));out=[]
    while todo:
        o=orbit(min(todo));todo-=o;out.append(min(o))
    return set(out)
def has_swap(t):return any(sum(a!=b for a,b in zip(P[i],P[j]))==2 for i,j in combinations(t,2))
T6=mixed_orbits(6);T7=mixed_orbits(7)
assert len(T6)==90 and len(T7)==100
no_swap={min(orbit(t)) for t in [(1,5,6,10,13,14),(2,5,9,10,13,14),(1,5,6,9,14,18)]}
assert len(no_swap)==3 and no_swap=={t for t in T6 if not has_swap(t)}
print('Exact census: 87 swap-containing six-contact orbits, 3 exceptions, 100 seven-contact orbits.')

# Exact exceptional equal-complex-contact products, with anchor-normalized K.
a,b,c,d,e=symbols('a b c d e')
x=(0,1,a,b);y=(0,c,d,e)
p=[prod(1+x[i]*y[q[i]] for i in range(4)) for q in P]
T88=(1,5,6,10,13,14)
sub={b:a/(a+1),c:-2,d:-2/a,e:-2/(a+1)}
assert cancel(((1+e)*(1+b*c)-(1+b*e)).subs(sub,simultaneous=True))==cancel(-2*(a*a-a+1)/(a+1)**2)
q=a*a-a+1
pp=[]
for z in p:
    num,den=fraction(cancel(z.subs(sub,simultaneous=True)))
    pp.append(rem(rem(num,q,a)*invert(den,q,a),q,a))
assert all(pp[k]==-Rational(1,3) for k in T88)
A=(1,0,2,1,0,0,0,1,0,2,0,1,1,0,0,0,1,2,2,0,1,2,2,5)
B=(1,0,2,0,1,0,0,1,1,2,0,0,0,0,0,1,1,2,2,1,0,2,2,5)
assert all(expand(Rational(3,2)*(pp[k]-pp[1])-((1-a)*A[k]+a*B[k]))==0 for k in range(24))
assert A==tuple(sum(F[i][k] for i in (1,10,34,59)) for k in range(24))
assert B==tuple(sum(F[i][k] for i in (1,10,30,59)) for k in range(24))
sub90={b:(1-a)/(1+a*d),c:a*d,e:d*(a-1)/(1+a*d)}
assert expand(cancel((p[5]-p[1]).subs(sub90,simultaneous=True))+2*d*(a-1)**2)==0

# Quaternion identities for h_id +/- and the three principal 2-minors.
qv=symbols('q0:4');rv=symbols('r0:4');a0,a1,a2,a3=qv;b0,b1,b2,b3=rv
L=Matrix([[a0,-a1,-a2,-a3],[a1,a0,-a3,a2],[a2,a3,a0,-a1],[a3,-a2,a1,a0]])
R=Matrix([[b0,-b1,-b2,-b3],[b1,b0,b3,-b2],[b2,-b3,b0,b1],[b3,b2,-b1,b0]])
O=L*R;qn=sum(z*z for z in qv);rn=sum(z*z for z in rv)
assert expand(sum(O[i,i]**2 for i in range(4))-4*sum(qv[i]**2*rv[i]**2 for i in range(4)))==0
D=lambda i,j,k,l:expand(O[i,k]*O[j,l]-O[i,l]*O[j,k])
for i in (1,2,3):
    assert expand(D(0,i,0,i)-(rn*(qv[0]**2+qv[i]**2)+qn*(rv[0]**2+rv[i]**2)-qn*rn))==0
Dmix=D(0,1,0,2)**2+D(0,1,1,3)**2-D(0,2,0,1)**2-D(0,2,2,3)**2
assert expand(Dmix-8*(qn**2*prod(rv)-rn**2*prod(qv)))==0
u,v=symbols('u v',positive=True)
A0=u*u/(u*u+3);B0=1/(u*u+3);C0=v*v/(v*v+3);D0=1/(v*v+3)
F13=(A0+C0-Rational(1,2))**2+3*(B0+D0-Rational(1,2))**2+2*(A0*C0+3*B0*D0)-4*(u*B0**2+v*D0**2)
claim=(u-1)**4*(31*u**4+104*u**3+194*u**2-104*u+15)/(2*(u*u+3)**2*(7*u*u-4*u+1)**2)
assert cancel(F13.subs(v,(u+1)/(3*u-1))-claim)==0
print('Exceptional profile and quaternion identities verified exactly.')

CASES=[(0,1,2,3,6,7,12),(0,1,2,3,6,7,20),(0,1,2,6,7,10,15),(0,1,2,3,6,7,18),
(0,1,2,3,6,7,10),(0,1,2,3,6,7,8),(0,1,2,3,6,7,22),(0,1,2,6,7,11,17),
(0,1,2,6,7,9,19),(0,1,2,6,7,10,13),(0,1,2,6,7,17,21),(0,1,2,6,7,10,17),
(0,1,2,6,7,9,18),(0,1,2,6,7,9,23),(0,1,2,6,7,21,23)]
RPL={CASES[11]:{(2,24):(0,8,21)},CASES[12]:{(18,22):(4,7,16,21)},CASES[13]:{(18,22):(4,7,16,21)},
CASES[14]:{(3,18):(4,7,15),(8,22):(4,7,23),(15,22):(3,16,21),(18,22):(4,7,16,21),(18,23):(8,16,21)}}
assert len({min(orbit(t)) for t in CASES})==15 and all(min(orbit(t)) in T7 for t in CASES)
def verify(t):
    rpl=RPL.get(t,{})
    T=set(t);assert any(r<=T for r in rect) or any(a|b<=T for a,b in tri)
    while True:
        old=len(T)
        for r in rect:
            if len(r&T)>=3:T|=r
        for a,b in tri:
            if len(a&T)>=2 and len(b&T)>=2:T|=a|b
        if len(T)==old:break
    active=[i for i in range(82) if all(F[i][j]==0 for j in T)]
    for (i,j),rhs in rpl.items():
        assert i in active and j in active and not (minor[i] and minor[j])
        assert all(k in active and minor[k] for k in rhs)
        assert all(F[i][l]+F[j][l]==sum(F[k][l] for k in rhs) for l in range(24))
    count=0
    for bits in range(1<<len(active)):
        S={i for k,i in enumerate(active) if bits>>k&1}
        if all(minor[i] for i in S) or any(i in S and j in S for i,j in rpl):continue
        if any(not any(tuple(sorted((i,j))) in rpl for j in S) for i in active if i not in S):continue
        assert any(all(e*polar(V[i],V[j],V[k])>=0 for i,j,k in combinations_with_replacement(S,3))
                   and all(e*C(V[i])>0 for i in S if not minor[i]) for e in (-1,1))
        count+=1
    return t,len(T),count
if __name__=='__main__':
    from concurrent.futures import ProcessPoolExecutor
    with ProcessPoolExecutor(max_workers=4) as ex:
        for t,k,m in ex.map(verify,CASES):print('VERIFIED',t,'closure',k,'mixed supports',m)
    print('15 distinct exceptional seven-contact cases certified; 85 remain.')

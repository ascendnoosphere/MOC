"""Bounded transport searches and independent exact verification of the agenda fixtures.
Python 3 with SciPy and NumPy. Search scores are observations, not theorems.
"""
from collections import deque
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations, permutations
from pathlib import Path
from random import Random

import argparse
import numpy as np
from scipy.sparse import csr_matrix, hstack
from scipy.optimize import linprog

def cmul(x,y):
    a,b=x; c,d=y
    return a*c-b*d,a*d+b*c

def cadd(x,y):
    return x[0]+y[0],x[1]+y[1]

def csub(x,y):
    return x[0]-y[0],x[1]-y[1]

def cdiv(x,y):
    a,b=x; c,d=y
    k=c*c+d*d
    return F(a*c+b*d,k),F(b*c-a*d,k)

def cprod(xs):
    z=(1,0)
    for x in xs:
        z=cmul(z,x)
    return z

@lru_cache(None)
def moments(n):
    P=list(permutations(range(n)))
    sets=[[sum(1<<i for i in s) for s in combinations(range(n),k)] for k in range(n+1)]
    ij=[(I,J) for C in sets for I in C for J in C]
    m={key:i for i,key in enumerate(ij)}
    events=np.zeros((len(ij),len(P)),dtype=np.int64)
    for j,p in enumerate(P):
        for C in sets:
            for J in C:
                I=sum(1<<p[k] for k in range(n) if J>>k&1)
                events[m[I,J],j]=1
    laws=[]
    for tr in (False,True):
        atom=(lambda I,J:m[J,I]) if tr else (lambda I,J:m[I,J])
        for k,C in enumerate(sets[:-1]):
            edges=[(a,b) for a,I in enumerate(C) for b,L in enumerate(sets[k+1]) if I&L==I]
            for J in C:
                for j in range(n):
                    if J>>j&1: continue
                    K=J|1<<j
                    laws.append(('nested_col' if tr else 'nested_row',
                        [atom(I,J) for I in C],[atom(L,K) for L in sets[k+1]],edges))
    for k in range(n-1):
        for i in range(n):
            for j in range(n):
                a=[(I,J) for I in sets[k+1] if I>>i&1 for J in sets[k+1] if not J>>j&1]
                b=[(K,L) for K in sets[k+1] if not K>>i&1 for L in sets[k+1] if L>>j&1]
                edges=[(u,v) for u,(I,J) in enumerate(a) for v,(K,L) in enumerate(b)
                       if (I^(1<<i))&K==(I^(1<<i)) and (L^(1<<j))&J==(L^(1<<j))]
                laws.append(('crossed',[m[x] for x in a],[m[y] for y in b],edges))
    return P, m, events, laws

def hall_cut(src,snk,edges,tol=0):
    """Return a violated cut, or None. At tol=0 integer capacities are exact."""
    if abs(sum(src)-sum(snk))>tol:
        raise ValueError('different marginal totals')
    A=len(src); B=len(snk); s=A+B; t=s+1
    cap=[{} for _ in range(t+1)]
    def put(x,y,c):
        cap[x][y]=c
        cap[y][x]=0
    for i,c in enumerate(src): put(s,i,c)
    for j,c in enumerate(snk): put(A+j,t,c)
    upper=2*sum(src)+1
    for i,j in edges: put(i,A+j,upper)
    while True:
        seen={s:None}
        q=deque([s])
        while q and t not in seen:
            x=q.popleft()
            for y,c in cap[x].items():
                if c>tol and y not in seen:
                    seen[y]=x
                    q.append(y)
        if t not in seen: break
        path=[]
        y=t
        while y!=s:
            x=seen[y]; path.append((x,y)); y=x
        v=min(cap[x][y] for x,y in path)
        for x,y in path:
            cap[x][y]-=v; cap[y][x]+=v
    F=[i for i in range(A) if i in seen]
    N=sorted({j for i,j in edges if i in F})
    if sum(src[i] for i in F)-sum(snk[j] for j in N)>tol:
        return F,N

def matching_values(a,b,P):
    return [cprod(cadd(a[p[j]],b[j]) for j in range(len(a))) for p in P]

def objective(eta,z):
    return cmul(eta,z)[0]

def cycle1():
    n=5
    P,m,E,laws=moments(n)
    labels={''.join(map(str,p)):i for i,p in enumerate(P)}
    a=((3,2),(3,1),(5,-4),(1,6),(-6,7))
    b=((-6,4),(1,-3),(-1,8),(8,-8),(5,2))
    h=1228164224
    G=np.array([h-objective((34944,-130480),z) for z in matching_values(a,b,P)], dtype=np.int64)
    assert min(G)==0
    assert [p for p,k in labels.items() if G[k]==0]==['24310','41302']
    sl={'14023':1,'14230':1,'14320':-1,'24310':1,'32140':1,'41302':1}
    y=np.array([sl.get(''.join(map(str,p)),0) for p in P],dtype=np.int64)
    z=E@y
    assert sum(y)==4 and min(z)==0 and y@G==-226862720 and len(z)==252
    failed={k:0 for k in ('nested_row','nested_col','crossed')}
    totals=dict(failed)
    for kind,A,B,L in laws:
        totals[kind]+=1
        failed[kind]+=hall_cut(z[A].tolist(),z[B].tolist(),L) is not None
    assert failed=={'nested_row':4,'nested_col':4,'crossed':0}
    def bit(xs): return sum(1<<int(c) for c in xs)
    def e(I,J): return E[m[bit(I),bit(J)]]
    H=sum(e('234',L) for L in ['013','014','023','034','123','124','134','234'])-sum(
          e('34',J) for J in ['03','13','14','23','34'])
    A=['03','13','14','23','34']
    N=['013','014','023','034','123','124','134','234']
    assert set(N)=={''.join(map(str,C)) for C in combinations(range(5),3)
                    if any(bit(J)&bit(C)==bit(J) for J in A)}
    assert min(H)==0
    # Check that the designated cut separates y (negative source/target cost).
    assert H@y<0
    data=[(int(c),I,J) for c,I,J in (line.split() for line in Path(__file__).with_name('cycle01-hall-data.txt').read_text().splitlines())]
    assert len(data)==39 and all(c>0 for c,I,J in data)
    assert np.array_equal(G,112*(sum(c*e(I,J) for c,I,J in data)+26309360*H))
    print('Cycle01 six-label exact: signed objective',y@G,'failed cuts',failed,'total blocks',totals,flush=True)
    print('Cycle01 39 positive event terms + one Hall repair: all 120 exact labels passed',flush=True)
    return a,b

def mm(A,B,add=cadd,mul=cmul,zero=(0,0)):
    return [[sum_like((mul(x,y) for x,y in zip(r,v)),add,zero) for v in zip(*B)] for r in A]

def sum_like(xs,add,zero):
    for x in xs: zero=add(zero,x)
    return zero

def adj(A):
    return [[(a,-b) for a,b in r] for r in zip(*A)]

def ident(n):
    return [[(int(i==j),0) for j in range(n)] for i in range(n)]

def inv(A):
    n=len(A)
    M=[r+s for r,s in zip(A,ident(n))]
    for j in range(n):
        i=next(i for i in range(j,n) if M[i][j]!=(0,0))
        M[j],M[i]=M[i],M[j]
        c=M[j][j]
        M[j]=[cdiv(x,c) for x in M[j]]
        for i in range(n):
            if i==j: continue
            c=M[i][j]
            M[i]=[csub(x,cmul(c,y)) for x,y in zip(M[i],M[j])]
    return [r[n:] for r in M]

def det(A):
    M=[r[:] for r in A]
    n=len(M)
    z=(1,0)
    for j in range(n):
        i=next((i for i in range(j,n) if M[i][j]!=(0,0)),None)
        if i is None: return 0,0
        if i!=j:
            M[j],M[i]=M[i],M[j]
            z=cmul((-1,0),z)
        q=M[j][j]
        z=cmul(z,q)
        for i in range(j+1,n):
            c=cdiv(M[i][j],q)
            for k in range(j+1,n): M[i][k]=csub(M[i][k],cmul(c,M[j][k]))
    return z

def cayley(K,scale):
    n=len(K)
    S=[[(scale*int(i==j),0) for j in range(n)] for i in range(n)]
    V=mm(inv([[cadd(x,y) for x,y in zip(r,s)] for r,s in zip(S,K)]),
             [[csub(x,y) for x,y in zip(r,s)] for r,s in zip(S,K)])
    assert mm(V,adj(V))==ident(n) and mm(adj(V),V)==ident(n)
    return V

def cycle2():
    I=ident(3)
    K=[[0,-2,-1,0],[2,0,0,-1],[1,0,0,0],[0,1,0,0]]
    U=cayley([[(x,0) for x in s] for s in K],2)
    B=[[-1,32,20,16],[-32,-1,-16,20],[-20,-16,31,-8],[16,-20,8,31]]
    assert U==[[(F(x,41),0) for x in r] for r in B]
    Z=I+[r[:3] for r in U]
    sets=[{1,2,3},{1,3,4},{2,4,5},{3,4,6}]
    c=(1,-1,1,1)
    def incidence(e,S): return int(all(len(S&{i,3+j})==1 for i,j in enumerate(e)))
    for e in permutations(range(4),3):
        assert sum(cc*incidence(e,S) for cc,S in zip(c,sets))>=0
    v=[det([Z[j] for j in sorted(S)])[0]**2 for S in sets]
    assert v==[F(x,1681) for x in [1,256,144,64]]
    assert sum(cc*x for cc,x in zip(c,v))==F(-47,1681)
    print('Cycle02 Cayley and three-frame fixture: 24 exact incidences, residual -47/1681',flush=True)
    return U

def hull_directions(points):
    def turn(a,b,c): return ((b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0]))
    def part(S):
        H=[]
        for z in S:
            while len(H)>=2 and turn(H[-2],H[-1],z)<=0: H.pop()
            H.append(z)
        return H
    S=sorted(set(points)); H=part(S)[:-1]+part(S[::-1])[:-1]
    D={(1,0),(-1,0),(0,1),(0,-1)}
    for a,b in zip(H,H[1:]+H[:1]):
        dx,dy=b[0]-a[0],b[1]-a[1]
        D.add((dy,dx))
    return sorted(D)

def orbit_value(a,b,U):
    M=mm([[cmul(x,b[j]) for j,x in enumerate(r)] for r in U],adj(U))
    for i,v in enumerate(a): M[i][i]=cadd(M[i][i],v)
    return det(M)

def real_search(U,a5,b5,seed):
    rng=Random(seed)
    best={}; totals={}
    for n in (4,5,6):
        for kind in ('dense','near_zero','repeated'):
            for t in range(2):
                if n==4:
                    V=U
                else:
                    S=[[(0,0)]*n for _ in range(n)]
                    for i in range(n):
                        S[i][i]=(0,rng.randint(-1,1))
                        for j in range(i):
                            z=(rng.randint(-1,1),rng.randint(-1,1))
                            S[i][j]=z; S[j][i]=(-z[0],z[1])
                    V=cayley(S,2)
                a=[(rng.randint(-3,3),rng.randint(-3,3)) for _ in range(n)]
                b=[(rng.randint(-3,3),rng.randint(-3,3)) for _ in range(n)]
                if n==5 and kind=='dense' and t==0: a,b=a5,b5
                if kind=='near_zero': b[0]=cadd((-a[0][0],-a[0][1]),(F(1,64),F(1,127)))
                if kind=='repeated': a[0]=a[1]; b[0]=b[1]
                vertices=matching_values(a,b,list(permutations(range(n))))
                D=orbit_value(a,b,V)
                for e in hull_directions(vertices):
                    excess=objective(e,D)-max(objective(e,X) for X in vertices)
                    assert excess<=0, (n,kind,a,b,e,D,excess)
                    totals[n,kind]=totals.get((n,kind),0)+1
                    best[n,kind]=max(excess,best.get((n,kind),excess))
    print('Cycle02 exact scalar Cayley support: cases axis+facet totals',totals,flush=True)
    print('No strict excess on these samples; zeros include spectral-degeneracy directions.',flush=True)

def reciprocal_frames(U, seed):
    rng=Random(seed)
    s=ident(3)
    t=[r[:3] for r in U]
    for p,q,F0,H0,augment in [(3,4,s,t,False),(4,4,t,t,True)]:
        ntest=0
        for kind in ('generic','near_coincident','repeated'):
            a=[(rng.randint(-3,3),rng.randint(-3,3)) for _ in range(p)]
            b=[(rng.randint(-3,3),rng.randint(-3,3)) for _ in range(q)]
            if kind=='near_coincident':
                b[0]=cadd((-a[0][0],-a[0][1]),(F(1,101),F(1,97)))
            if kind=='repeated':
                a[0]=a[1]; b[0]=b[1]
            def comp(V,x): return mm(adj(V),[[cmul(y,k) for y in r] for r,k in zip(V,x)])
            A=comp(F0,a)
            B=comp(H0,b)
            D=det([[cadd(x,y) for x,y in zip(r,s)] for r,s in zip(A,B)])
            labels=[cprod(cadd(a[i],b[j]) for i,j in zip(I,J))
                    for I in combinations(range(p),3) for J in permutations(range(q),3)]
            if augment: labels.append((0,0))
            for e in hull_directions(labels):
                assert objective(e,D)<=max(objective(e,z) for z in labels)
                ntest+=1
        print('Exact scalar overlap-three compressed cases p,q=',p,q,'zero vertex',augment,
              '3 spectra, axis+facet directions',ntest,flush=True)

def lp_trial(n,a,b,max_passes=2):
    P,m,E,laws=moments(n)
    vertices=matching_values(a,b,P)
    D=hull_directions(vertices)
    # Each direction retains valid cuts found from preceding directions.
    cuts=[]; cut_provenance=[]; keys=set(); stats={'exact_dual':0,'numerical_only':0,'trivial':0,
                                'unresolved':0,'rational_negative':0}
    duals=[]
    def exact_dual(sol,M,g):
        # Ignore box multipliers: the output is an unrestricted conic certificate.
        # A positive constant from sum(y)=1 may also be used.
        scale=int(max(g))
        terms=[(i,F(float(-v*scale)).limit_denominator(100_000))
               for i,v in enumerate(sol.ineqlin.marginals) if v!=0]
        const=F(float(sol.eqlin.marginals[0]*scale)).limit_denominator(100_000)
        if const<0 or any(v<0 for i,v in terms): return
        total=np.full(len(g),const,dtype=object)
        for i,v in terms: total-=v*M[i].astype(object)
        if not all(a==b for a,b in zip(total,g.tolist())):
            # Reconstruct on the discovered sparse support over ZZ, not by rounding.
            from sympy import ZZ
            from sympy.polys.matrices import DM
            from sympy.polys.matrices.exceptions import DMNonInvertibleMatrixError
            indices=[i for i,v in terms if v!=0]
            if const!=0: indices.append(-1)
            if not indices: return
            lhs=[[(1 if i==-1 else -int(M[i,j])) for i in indices] for j in range(len(g))]
            try:
                sol,den=DM(lhs,ZZ).solve_den(DM([[int(v)] for v in g],ZZ))
            except DMNonInvertibleMatrixError:
                return
            exact={i:F(int(x[0]),int(den)) for i,x in zip(indices,sol.to_list())}
            if min(exact.values())<0: return
            const=exact.pop(-1,F(0))
            terms=list(exact.items())
        return str(const),[(i,str(v)) for i,v in terms if v!=0]
    for eta in D:
        v=np.array([objective(eta,z) for z in vertices],dtype=np.int64)
        g=v.max()-v
        if not any(g):
            stats['trivial']+=1; continue
        status='unresolved'
        for r in range(max_passes+1):
            M=np.vstack([-E,*cuts])
            sol=linprog(g/max(g),A_ub=csr_matrix(M),
                       b_ub=np.zeros(len(E)+len(cuts)),A_eq=np.ones((1,len(P))),
                       b_eq=[1],bounds=(-1,1),method='highs',
                       options={'time_limit':10,'primal_feasibility_tolerance':1e-8})
            # Event masses are nonnegative; each cut row is source minus neighbor mass.
            if not sol.success: break
            if sol.fun>=-1e-7:
                cert=exact_dual(sol,M,g)
                if cert is None:
                    unbounded=linprog(g/max(g),A_ub=csr_matrix(M),
                                      b_ub=np.zeros(len(M)),A_eq=np.ones((1,len(P))),
                                      b_eq=[1],bounds=(None,None),method='highs',
                                      options={'time_limit':10})
                    if unbounded.success and unbounded.fun>=-1e-7: cert=exact_dual(unbounded,M,g)
                if cert is None:
                    status='numerical_only'
                else:
                    status='exact_dual'
                    duals.append({'eta':eta,'const':cert[0],'terms':cert[1]})
                break
            z=E@sol.x
            found=0
            for c_i,(kind,A,B,L) in enumerate(laws):
                C=hall_cut(np.maximum(z[A],0).tolist(),np.maximum(z[B],0).tolist(),L,1e-7)
                if C is None: continue
                S,T=C
                row=E[[A[i] for i in S]].sum(axis=0)-E[[B[j] for j in T]].sum(axis=0)
                key=tuple(row)
                if key not in keys:
                    keys.add(key); cuts.append(row); cut_provenance.append([c_i,S]); found+=1
            if not found:
                Y=[F(float(y)).limit_denominator(1_000_000) for y in sol.x]
                if all(abs(y)<=1 for y in Y) and sum(Y)==1 and sum(int(k)*y for k,y in zip(g,Y))<0:
                    from math import lcm
                    L=lcm(*(y.denominator for y in Y))
                    V=[int(y*L) for y in Y]
                    Z=E.astype(object)@np.array(V,dtype=object)
                    if min(Z)>=0 and all(hall_cut(Z[A].tolist(),Z[B].tolist(),L0) is None
                                          for _,A,B,L0 in laws):
                        status='rational_negative'
                        print('Exact negative restricted combined-transport witness:',n,eta,V,L,flush=True)
                break
        stats[status]+=1
    print('Cut search n=',n,'directions',len(D),'cuts',len(cuts),'stats',stats,flush=True)
    import json
    import hashlib
    key=hashlib.sha256(repr((a,b)).encode()).hexdigest()[:10]
    if duals:
        Path(__file__).with_name(f'lp-duals-{n}-{key}.json').write_text(json.dumps({
            'spectra':(a,b),'cuts':cut_provenance,'duals':duals,
        },separators=(',',':'))+'\n')


def verify_duals():
    import json
    for file in sorted(Path(__file__).parent.glob('lp-duals-*.json')):
        data=json.loads(file.read_text())
        a,b=data['spectra']
        P,_,E,laws=moments(len(a))
        rows=[-v for v in E]
        for law,S in data['cuts']:
            _,A,B,L=laws[law]
            assert set(S)<=set(range(len(A))) and len(S)==len(set(S))
            N=sorted({j for i,j in L if i in S})
            rows.append(E[[A[i] for i in S]].sum(axis=0)-E[[B[j] for j in N]].sum(axis=0))
        vertices=matching_values(a,b,P)
        passed=set()
        for d in data['duals']:
            eta=tuple(d['eta'])
            assert eta not in passed
            passed.add(eta)
            v=[objective(eta,z) for z in vertices]
            h=max(v)
            c=F(d['const'])
            assert c>=0
            raw=[(i,F(x)) for i,x in d['terms']]
            assert all(0<=i<len(rows) and x>=0 for i,x in raw)
            val=np.full(len(v),c,dtype=object)
            for i,x in raw: val-=x*rows[i].astype(object)
            assert all(y==h-x for x,y in zip(v,val))
        missed=set(hull_directions(vertices))-passed
        print('Exact independent dual replay:',file.name,'directions',len(passed),'missed',sorted(missed),flush=True)

if __name__=='__main__':
    arg=argparse.ArgumentParser()
    arg.add_argument('--lp',action='store_true')
    arg.add_argument('--verify-duals',action='store_true')
    cfg=arg.parse_args()
    a5,b5=cycle1()
    U=cycle2()
    real_search(U,a5,b5,190501)
    reciprocal_frames(U,190505)
    if cfg.lp:
        rng=Random(2503)
        for n in (4,5,6):
            a=[(rng.randint(-4,4),rng.randint(-4,4)) for _ in range(n)]
            b=[(rng.randint(-4,4),rng.randint(-4,4)) for _ in range(n)]
            lp_trial(n,a,b)
            if n==5: lp_trial(n,a5,b5)
    if cfg.lp or cfg.verify_duals: verify_duals()

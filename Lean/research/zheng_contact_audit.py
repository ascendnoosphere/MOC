#!/usr/bin/env python3
"""Independent exact combinatorial audit of Zheng's Proposition 4.1,
six-contact census, and the corresponding order-five subset counts.

Python 3 + SymPy. The boundary-chain construction uses a modular rank
filter to generate candidates; every final determinant and boundary
cancellation is verified over the integers. No author data tables or
floating-point computation are used. This does not verify Proposition 4.3.
"""
from itertools import permutations, combinations
from functools import lru_cache
from collections import Counter
from math import comb
from sympy import Matrix

def audit_four():
    P=list(permutations(range(4))); idx={p:i for i,p in enumerate(P)}
    Q=list(combinations(range(4),2))
    def evt(I,J):
        return tuple(int(tuple(sorted(p[i] for i in I))==J) for p in P)
    minor=sorted(set(evt((i,),(j,)) for i in range(4) for j in range(4))
                 |set(evt(I,J) for I in Q for J in Q))
    mixed=[]
    for p in P:
        t=[sum(a==b for a,b in zip(p,s)) for s in P]
        A=evt((0,1),tuple(sorted((p[0],p[2]))))
        B=evt((0,1),tuple(sorted((p[1],p[3]))))
        C=evt((0,2),tuple(sorted((p[0],p[1]))))
        D=evt((0,2),tuple(sorted((p[2],p[3]))))
        d=[a+b-c-e for a,b,c,e in zip(A,B,C,D)]
        for eps in [-1,1]:
            vals=[a+eps*b for a,b in zip(t,d)]
            assert all(x%2==0 for x in vals)
            h=tuple(x//2 for x in vals)
            assert Counter(h)=={0:13,1:10,2:1}
            mixed.append(h)
    assert len(minor)==34 and len(set(mixed))==48
    facets=minor+mixed
    assert len(set(facets))==82
    Z=[sum(1<<i for i,x in enumerate(v) if x==0) for v in facets]
    assert len(set(Z))==82
    cols=[(1,)*24]+minor
    M=Matrix(24,len(cols),lambda i,j:cols[j][i])
    _,piv=M.rref()
    assert len(piv)==14 and piv[0]==0
    R=[[cols[j][i] for j in piv] for i in range(24)]
    assert all(Matrix([R[i] for i in range(24) if (mask>>i)&1]).rank()==13
               for mask in Z)
    print('82 distinct supporting facets verified',flush=True)
    @lru_cache(None)
    def ids(m):
        return tuple(i for i in range(24) if m>>i&1)
    @lru_cache(None)
    def rank_mod(m):
        a=[R[i][:] for i in ids(m)]; p=1009; rank=0
        for j in range(14):
            k=next((k for k in range(rank,len(a)) if a[k][j]%p),None)
            if k is None: continue
            a[rank],a[k]=a[k],a[rank]
            iv=pow(a[rank][j]%p,-1,p)
            row=[v*iv%p for v in a[rank]]
            for k in range(rank+1,len(a)):
                z=a[k][j]%p
                if z: a[k]=[(v-z*w)%p for v,w in zip(a[k],row)]
            rank+=1
            if rank==len(a): break
        return rank
    @lru_cache(None)
    def pull(m,d):
        ii=ids(m)
        assert len(ii)>=d+1
        if len(ii)==d+1: return (ii,)
        v=ii[0];subs={m&z for z in Z if not (z>>v&1)}
        out=[]
        for s in sorted(subs):
            if s.bit_count()>=d and rank_mod(s)==d:
                out.extend(tuple(sorted((v,)+t)) for t in pull(s,d-1))
        assert out
        return tuple(out)
    tri=set()
    for mask in Z: tri.update(pull(mask,12))
    def det(a):
        a=[list(row) for row in a]; n=len(a); prev=1; sgn=1
        for k in range(n-1):
            p=next((i for i in range(k,n) if a[i][k]),None)
            if p is None: return 0
            if p!=k: a[p],a[k]=a[k],a[p];sgn=-sgn
            pivot=a[k][k]
            for i in range(k+1,n):
                for j in range(k+1,n):
                    num=a[i][j]*pivot-a[i][k]*a[k][j]
                    assert num%prev==0
                    a[i][j]=num//prev
                a[i][k]=0
            prev=pivot
        return sgn*a[-1][-1]
    center=[sum(r[j] for r in R) for j in range(1,14)]
    scaled=[[24*r[j+1]-center[j] for j in range(13)] for r in R]
    chain=Counter()
    for t in sorted(tri):
        mask=sum(1<<i for i in t)
        assert len(t)==13 and sum(mask&z==mask for z in Z)==1
        D=det([scaled[i] for i in t]);assert D!=0
        sg=1 if D>0 else -1
        for k in range(13):
            chain[t[:k]+t[k+1:]]+=sg*(-1)**k
    assert len(tri)==6846 and all(v==0 for v in chain.values())
    print('exact oriented boundary cycle verified:',len(tri),'simplices',flush=True)
    def compose(p,q): return tuple(p[q[i]] for i in range(4))
    def inv(p): return tuple(p.index(i) for i in range(4))
    G=[]
    for k in range(3):
        t=list(range(4)); t[k],t[k+1]=t[k+1],t[k]; t=tuple(t)
        G.append([idx[compose(t,p)] for p in P])
        G.append([idx[compose(p,t)] for p in P])
    G.append([idx[inv(p)] for p in P])
    def action(mask,g): return sum(1<<g[i] for i in ids(mask))
    remaining={sum(1<<i for i in c) for c in combinations(range(24),6)}
    classes=Counter(); orbits=[]
    while remaining:
        r=min(remaining); orbit={r}; stack=[r]
        while stack:
            t=stack.pop()
            for g in G:
                m=action(t,g)
                if m not in orbit: orbit.add(m);stack.append(m)
        remaining.difference_update(orbit)
        exceptional=any(r&z==r for z in Z[34:])
        classes[exceptional]+=1
        orbits.append((r,exceptional,len(orbit)))
    assert sum(n for _,_,n in orbits)==comb(24,6)
    assert classes=={False:124,True:90}
    print('contact census',sum(classes.values()),'classes;',
          classes[False],'minor-only;',classes[True],'exceptional',flush=True)

def audit_five():
    n=5
    P=list(permutations(range(n)));ix={p:i for i,p in enumerate(P)}
    def C(p,q):return tuple(p[q[i]] for i in range(n))
    def inv(p):return tuple(p.index(i) for i in range(n))
    L=[[ix[C(p,q)] for q in P] for p in P]
    R=[[ix[C(q,p)] for q in P] for p in P]
    I=[ix[inv(p)] for p in P]
    E=[]
    for k in (0,1,2):
        sets=list(combinations(range(n),k))
        for a in sets:
            for b in sets:
                E.append([int(tuple(sorted(p[i] for i in a))==b) for p in P])
    assert Matrix(E).rank()==42
    print('order-five indicator rank: 42',flush=True)
    types=Counter()
    for l in L:
        for r in R:
            h=[l[j] for j in r]
            for g in (h,[h[j] for j in I]):
                seen=0; cs=[]
                for j in range(len(P)):
                    if seen>>j&1: continue
                    k=j;s=0
                    while not (seen>>k&1):
                        seen|=1<<k;s+=1;k=g[k]
                    cs.append(s)
                types[tuple(sorted(cs))]+=1
    assert sum(types.values())==2*len(P)**2 and len(types)==26
    expected={6:133816,7:2099444,8:29342815}
    for k in (6,7,8):
        tot=0
        for cs,m in types.items():
            f=[1]+[0]*k
            for d in cs:
                for j in range(k,d-1,-1): f[j]+=f[j-d]
            tot+=m*f[k]
        assert tot%(2*len(P)**2)==0
        count=tot//(2*len(P)**2)
        assert count==expected[k]
        print(k,'contacts:',comb(len(P),k),'subsets;',count,'orbits',flush=True)

if __name__=='__main__':
    audit_four()
    audit_five()

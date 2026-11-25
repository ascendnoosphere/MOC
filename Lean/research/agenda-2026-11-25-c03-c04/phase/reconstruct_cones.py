"""Reconstruct Cycle 03/04 finite cone obstructions from spectra alone.

Discovery uses scipy/HiGHS. Verification is exact Python integer arithmetic
and never imports scipy. This is a bounded relaxation experiment, not a
Lean proof or evidence of an actual-unitary MOC violation.
"""
import argparse
import itertools as it
import json
import math
from pathlib import Path

P = list(it.permutations(range(5)))
CONTACT = (71, 106)
A = ((3,2),(3,1),(5,-4),(1,6),(-6,7))
B = ((-6,4),(1,-3),(-1,8),(8,-8),(5,2))
ETA = (34944,-130480)
H = 1228164224

def mul(z,w):
    a,b=z; c,d=w
    return a*c-b*d,a*d+b*c

def objective():
    gap=[]
    for p in P:
        z=ETA
        for j,i in enumerate(p):
            z=mul(z,(A[i][0]+B[j][0],A[i][1]+B[j][1]))
        d=H-z[0]
        assert d>=0 and d%112==0
        gap.append(d//112)
    assert [i for i,d in enumerate(gap) if d==0]==list(CONTACT)
    return tuple(gap)

def ordinary_markers(require_contact=True):
    markers=set()
    for k in (1,2):
        blocks=list(it.combinations(range(5),k))
        for j in blocks:
            for i in blocks:
                col=tuple(int(tuple(sorted(p[s] for s in j))==i) for p in P)
                if not require_contact or all(col[k]==0 for k in CONTACT):
                    markers.add(col)
    return markers

def signs(require_contact=True):
    def enc(p):
        return sum(1<<(4*(i-1)+(j-1)) for j,i in enumerate(p) if i and j)
    ex=[enc(p)^enc(P[CONTACT[0]]) for p in P]
    for m in range(1<<16):
        if not require_contact or (ex[CONTACT[1]]&m).bit_count()%2==0:
            yield tuple((v&m).bit_count()%2 for v in ex)

def prim_vecs():
    return [(0,*xs) for xs in it.product(range(-2,3),repeat=4)
            if math.gcd(*xs)==1 and next(v for v in xs if v)!=0
            and next(v for v in xs if v)>0]

def score(x,y):
    return tuple(sum(x[i]*y[j] for j,i in enumerate(p)) for p in P)

def normalize_square(s):
    c=tuple((m-s[CONTACT[0]])**2 for m in s)
    n=math.gcd(*c)
    return tuple(v//n for v in c) if n else c

def columns():
    mark=ordinary_markers()
    phase=mark | set(signs())
    phase.discard((0,)*len(P))
    xs=prim_vecs()
    assert len(xs)==272
    squares=set()
    for x,y in it.product(xs, repeat=2):
        # The two old equalities are checked before evaluating all 120 scores.
        a,b=(sum(x[i]*y[j] for j,i in enumerate(P[k])) for k in CONTACT)
        if a==b:
            squares.add(normalize_square(score(x,y)))
    squares.discard((0,)*len(P))
    larger=normalize_square(score((0,0,2,1,-2),(0,-4,-1,-8,4)))
    assert larger[CONTACT[1]]==0
    return {"square":mark|squares, "phase":phase, "combined":phase|squares|{larger}}

def pairing(w,c):
    return sum(x*y for x,y in zip(w,c))

def verify(d, cs, g):
    for name,w in d.items():
        assert name in cs and len(w)==len(P) and all(isinstance(z,int) for z in w)
        min_col=min(pairing(w,c) for c in cs[name])
        obj=pairing(w,g)
        assert min_col>=0 and obj<0
        print(f"{name}: {len(cs[name])} exact columns, min {min_col}, objective {obj}",flush=True)
        if name=="phase":
            # Also independently replay all full sign orientations and
            # subset events after padding at the contact coordinates.
            M=1+sum(abs(x) for x in w)
            z=[x+(M if j in CONTACT else 0) for j,x in enumerate(w)]
            tot=sum(z)
            assert tot>0
            minimum=0
            for c in signs(False):
                x=pairing(z,c)
                assert 0<=x<=tot
                minimum=min(minimum,x,tot-x)
            assert all(pairing(z,c)>=0 for c in ordinary_markers(False))
            assert pairing(z,g)==obj
            print(f"phase padded: 65536 masks, both orientations and all subset events; mass {tot}",flush=True)

def discover(cs,g):
    import numpy as np
    from scipy.optimize import linprog
    from scipy.sparse import csr_matrix
    d={}
    ii=[j for j in range(len(P)) if j not in CONTACT]
    goal=np.array([g[j] for j in ii],dtype=float)
    goal/=goal.max()
    for name,cc in cs.items():
        matrix=np.asarray(sorted(cc),dtype=np.float64)[:,ii]
        # Scale each row independently for stable floating discovery.
        matrix/=matrix.sum(axis=1,keepdims=True)
        result=linprog(goal,A_ub=csr_matrix(-matrix),b_ub=np.zeros(len(matrix)),
                       bounds=(-1,1),method="highs",options={"time_limit":75})
        print(f"discovery {name}: {result.message}",flush=True)
        if not result.success or not result.fun<-1e-8:
            continue
        for scale in (10**6,10**8,10**10,10**12):
            w=[0]*len(P)
            for i,q in zip(ii,result.x):
                w[i]=round(q*scale)+1
            if pairing(w,g)<0 and min(pairing(w,c) for c in cc)>=0:
                d[name]=w
                break
    return d

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--discover",action="store_true")
    ap.add_argument("--cert",type=Path,default=Path(__file__).with_name("reconstructed_cones.json"))
    args=ap.parse_args()
    cs=columns(); g=objective()
    print("generator counts",{k:len(v) for k,v in cs.items()},flush=True)
    if args.discover:
        d=discover(cs,g)
        args.cert.write_text(json.dumps(d,indent=2)+"\n")
    else:
        d=json.loads(args.cert.read_text())
    verify(d,cs,g)

if __name__=="__main__":
    main()

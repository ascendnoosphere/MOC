"""Fresh bounded replay for Cycle 03/04 paths 07 and 13.

Every accept/reject decision, including unitarity, determinant values,
hull inequalities, variance bounds, and the finite signed fixtures,
uses integers and fractions only. No search result is a universal proof.
Pass --baseline pointing to the previous transport experiments.py.
"""
import argparse
from collections import defaultdict
from fractions import Fraction as F
import importlib.util
from itertools import combinations, permutations
from pathlib import Path
from random import Random
from bisect import bisect_right

def load_baseline(path):
    spec = importlib.util.spec_from_file_location("prior_transport", path)
    assert spec is not None and spec.loader is not None
    out = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(out)
    return out

def norm2(z):
    return z[0]**2 + z[1]**2

def complex_scale(k, z):
    return (k*z[0], k*z[1])

def penalty(mean, levels):
    i=bisect_right(levels, mean)
    assert i and mean <= levels[-1]
    if levels[i-1] == mean:
        return 0
    return (mean-levels[i-1])*(levels[i]-mean)

def lattice(mean):
    a = mean % 1
    return a*(1-a)

def random_skew(n, rng, complex_entries, active_pair=None):
    S=[[(0,0)]*n for _ in range(n)]
    for i in range(n):
        if complex_entries and active_pair is None:
            S[i][i]=(0,rng.randint(-2,2))
        for j in range(i):
            if active_pair is not None and (j,i) != active_pair:
                continue
            z= (rng.choice((-2,-1,1,2)),rng.randint(-2,2) if complex_entries else 0)
            S[i][j]=z
            S[j][i]=(-z[0],z[1])
    return S

def signed_expect(prior,U,scores):
    n=len(U)
    z=prior.det(U)
    w=[]
    for p in permutations(range(n)):
        inversions=sum(p[i]>p[j] for i in range(n) for j in range(i+1,n))
        coef=prior.cdiv(prior.cprod(U[p[j]][j] for j in range(n)),z)
        w.append((-1)**inversions*coef[0])
    assert sum(w)==1
    mu=sum(q*s for q,s in zip(w,scores))
    return mu,sum(q*s*s for q,s in zip(w,scores))-mu*mu

def variance_suite(prior, trials, seed):
    rng=Random(seed)
    stats=defaultdict(lambda:defaultdict(int))
    maxima={}
    example=None
    for n in (4,5,6):
        P=tuple(permutations(range(n)))
        for kind in ("large_gaps","near_two_levels","one_plane","two_level"):
            for t in range(trials):
                y=sorted(rng.sample(range(-40,41),n),reverse=True)
                if kind=="two_level":
                    y=[3]*(n//2)+[-5]*(n-n//2)
                if kind=="near_two_levels":
                    y=sorted([rng.choice((-40,40))+rng.randint(-2,2) for _ in range(n)],reverse=True)
                x=rng.sample(range(-40,41),n)
                pair=(0,n-1) if kind=="one_plane" else None
                A=random_skew(n,rng,bool(t%2),pair)
                U=prior.cayley(A,(32,256,4096)[t%3])
                X=prior.mm(prior.adj(U),[[complex_scale(x[i],z) for z in row] for i,row in enumerate(U)])
                assert all(X[i][i][1]==0 for i in range(n))
                scores=[sum(x[p[j]]*y[j] for j in range(n)) for p in P]
                levels=sorted(set(scores))
                mu=sum(y[j]*X[j][j][0] for j in range(n))
                delta=[y[j]-y[j+1] for j in range(n-1)]
                edge=[(i,j,norm2(X[i][j])) for i in range(n) for j in range(i+1,n)]
                v=sum(h*(y[i]-y[j])**2 for i,j,h in edge)
                relaxVar=sum(h*sum(delta[k]**2 for k in range(i,j)) for i,j,h in edge)
                # Independent subset convolution, no sampling.
                R={y[-1]*sum(x)}
                for j,d in enumerate(delta,1):
                    if not d:
                        continue
                    R={r+s for r in R for s in {d*sum(c) for c in combinations(x,j)}}
                assert set(levels)<=R
                relaxed=penalty(mu,sorted(R))
                discrete=penalty(mu,levels)
                lat=lattice(mu)
                assert v>=relaxVar>=relaxed>=lat
                if kind=="two_level":
                    assert v==relaxVar and relaxed==discrete
                if n<=5 and t==0:
                    assert signed_expect(prior,U,scores)==(mu,v)
                    stats[n,kind]["signed_verified"]+=1
                stats[n,kind]["cases"]+=1
                stats[n,kind]["actual_adjacent_failures"]+=int(v<discrete)
                stats[n,kind]["actual_stricter_than_relaxed"]+=int(discrete>relaxed)
                stats[n,kind]["relaxed_stricter_than_lattice"]+=int(relaxed>lat)
                stats[n,kind]["dominance_strict"]+=int(v>relaxVar)
                stats[n,kind]["variance_below_actual_bound_and_replay_exact"]+=int(v<discrete)
                if v<discrete:
                    # Independently evaluate the signed moments from the determinants.
                    assert signed_expect(prior,U,scores)==(mu,v)
                    print("ACTUAL ADJACENT VARIANCE FAILURE:",n,kind,t,x,y,A,mu,v,discrete,flush=True)
                gap=discrete-relaxed
                if gap>maxima.get(n,F(-1)):
                    maxima[n]=gap
                if example is None and discrete>relaxed and relaxed==0 and mu.denominator==1:
                    example=(n,kind,t,x,y,mu,v,discrete)
    for k,r in sorted(stats.items()):
        print("variance",k,dict(r),flush=True)
    print("variance maximum actual-minus-relaxed lower bounds:",{n:float(k) for n,k in maxima.items()}, "(display only)",flush=True)
    if example: print("example zero relaxed but strict actual:",example)

def exact_fixtures(prior):
    U=[[(F(x,41),0) for x in r] for r in [[-1,32,20,16],[-32,-1,-16,20],[-20,-16,31,-8],[16,-20,8,31]]]
    assert prior.mm(U,prior.adj(U))==prior.ident(4)
    assert prior.det(U)==(1,0)
    P=list(permutations(range(4)))
    r=[]
    for p in P:
        if {p[0],p[3]}!={0,1}: continue
        w=prior.cprod(U[p[j]][j] for j in range(4))[0]
        nneg=sum(p[i]>p[j] for i in range(4) for j in range(i+1,4))
        r.append((p,(-1)**nneg*w,sum(p[j]*j for j in range(4))))
    mass=sum(w for _,w,_ in r)
    assert mass==F(144,1681)
    mu=sum(w*s for _,w,s in r)/mass
    var=sum(w*s*s for _,w,s in r)/mass-mu*mu
    assert (mu,var)==(F(814,123),F(-10720,15129))
    assert [w/mass for _,w,_ in r]==[F(t,15129) for t in (160,-775,-4096,19840)]
    print("verified conditional variance fixture",mass,mu,var)
    def reflection(n):
        return [[(int(i==j)-F(2,n),0) for j in range(n)] for i in range(n)]
    Q=reflection(3)
    assert prior.mm(Q,prior.adj(Q))==prior.ident(3)
    c=defaultdict(F)
    for p in permutations(range(3)):
        w=prior.cprod(Q[p[j]][j] for j in range(3))[0]*(-1)**(1+sum(p[i]>p[j] for i in range(3) for j in range(i+1,3)))
        c[sum(p[j]*j for j in range(3))]+=w
    assert dict(c)=={1:F(4,27),2:F(16,27),4:F(8,27),5:F(-1,27)}
    assert sum(w*(s-1)*(s-2)*(s-4) for s,w in c.items())==F(-4,9)
    print("verified rank-one cubic signed obstruction",dict(sorted(c.items())))
    Q=reflection(5)
    assert prior.mm(Q,prior.adj(Q))==prior.ident(5) and prior.det(Q)==(-1,0)
    c=defaultdict(F)
    for p in permutations(range(5)):
        w=prior.cprod(Q[p[j]][j] for j in range(5))[0]*(-1)**(1+sum(p[i]>p[j] for i in range(5) for j in range(i+1,5)))
        c[sum((p[j]-j)%5 in (1,4) for j in range(5))]+=w
    assert min(c)==0 and 1 in c and 2 in c and sum(c.values())==1
    mu=sum(w*s for s,w in c.items())
    var=sum(w*s*s for s,w in c.items())-mu*mu
    assert (mu,var)==(F(8,5),0)
    assert sum(w*(s-1)*(s-2) for s,w in c.items())==F(-6,25)
    print("verified arbitrary-cost signed obstruction", mu,var)
    # Positive actual adjacent gap that the relaxed bound cannot see.
    x,y=[1,7,-7,2],[19,5,4,-6]
    S=[[(0,0)]*4 for _ in range(4)]
    S[3][0]=(1,0); S[0][3]=(-1,0)
    Q=prior.cayley(S,3)  # squared sine = 9/25
    scores=[sum(x[p[j]]*y[j] for j in range(4)) for p in permutations(range(4))]
    mu,var=signed_expect(prior,Q,scores)
    assert (mu,var)==(23,144)
    assert max(s for s in scores if s<mu)==14 and min(s for s in scores if s>mu)==25
    assert penalty(mu,sorted(set(scores)))==18
    assert y[-1]*sum(x) + 14*2 + (1+2) + 10*(1+7-7)==mu
    print("verified relaxed support hides strict genuine adjacent bound",mu,var,18,0)

def scalar_suite(prior,trials,seed):
    rng=Random(seed)
    for n in (4,5,6):
        P=tuple(permutations(range(n)))
        for kind in ("dense","near_zero","exact_zero","near_antipodal","repeated","near_commuting"):
            directions=on_boundary=candidates=tied=0
            for t in range(trials):
                V=prior.cayley(random_skew(n,rng,True),4096 if kind=="near_commuting" else (1,3,7)[t%3])
                a=[(rng.randint(-7,7),rng.randint(-7,7)) for _ in range(n)]
                b=[(rng.randint(-7,7),rng.randint(-7,7)) for _ in range(n)]
                if kind=="near_zero": b[0]=(-a[0][0]+F(1,251),-a[0][1]+F(1,257))
                if kind=="exact_zero": b[0]=complex_scale(-1,a[0])
                if kind=="repeated": a[0]=a[1]; b[-1]=b[-2]
                if kind=="near_antipodal":
                    for A in (a,b):
                        for i in range(0,n-1,2):
                            A[i+1]=(-A[i][0]+F(1,257),-A[i][1]-F(1,263))
                vertices=prior.matching_values(a,b,P)
                D=prior.orbit_value(a,b,V)
                for d in prior.hull_directions(vertices):
                    directions+=1
                    gaps=[prior.objective(d,p) for p in vertices]
                    H=max(gaps)
                    tied+=int(gaps.count(H)>1)
                    e=prior.objective(d,D)-H
                    if e>0:
                        candidates+=1
                        print("EXACT STRICT SCALAR EXCESS",n,kind,t,a,b,d,D,e,flush=True)
                    elif e==0:
                        on_boundary+=1
            print("scalar",n,kind,"mixers",trials,"directions",directions,
                  "tied_labels",tied,"boundary",on_boundary,"strict",candidates,flush=True)

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--baseline",required=True)
    p.add_argument("--variance-trials",type=int,default=32)
    p.add_argument("--scalar-trials",type=int,default=4)
    p.add_argument("--skip-scalar",action="store_true")
    p.add_argument("--skip-variance",action="store_true")
    a=p.parse_args()
    prior=load_baseline(Path(a.baseline))
    exact_fixtures(prior)
    if not a.skip_variance: variance_suite(prior,a.variance_trials,194103)
    if not a.skip_scalar: scalar_suite(prior,a.scalar_trials,194104)
if __name__=="__main__":
    main()

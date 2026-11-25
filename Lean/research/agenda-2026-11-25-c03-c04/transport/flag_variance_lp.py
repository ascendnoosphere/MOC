"""Floating-point LP with exact inputs: full-prefix flag marginals.

No infeasibility or certificate is asserted on numerical outcomes.
Each call minimizes and maximizes the centered score's second moment.
"""
import argparse
from collections import defaultdict
from itertools import combinations, permutations
from pathlib import Path
from random import Random

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csc_matrix
from variance_cayley_replay import load_baseline, random_skew, norm2, complex_scale

def run(prior,trials):
    rng=Random(194105)
    for n in (4,5,6):
        P=tuple(permutations(range(n)))
        rows=[(j,I) for j in range(1,n) for I in combinations(range(n),j)]
        rid={p:i for i,p in enumerate(rows)}
        ii,jj=zip(*[(rid[j,tuple(sorted(p[:j]))],col) for col,p in enumerate(P) for j in range(1,n)])
        M=csc_matrix((np.ones(len(ii)),(ii,jj)),shape=(len(rows),len(P)))
        results=defaultdict(int); best=0
        for t in range(trials):
            y=sorted(rng.sample(range(-40,41),n),reverse=True)
            if t%2:
                y=sorted([rng.choice((-40,40))+rng.randint(-2,2) for _ in range(n)],reverse=True)
            x=rng.sample(range(-40,41),n)
            U=prior.cayley(random_skew(n,rng,bool(t%2)),(32,256,4096)[t%3])
            b=[norm2(prior.det([[U[i][k] for k in range(j)] for i in I])) for j,I in rows]
            assert all(sum(z for z,(k,_I) in zip(b,rows) if k==j)==1 for j in range(1,n))
            X=prior.mm(prior.adj(U),[[complex_scale(x[i],z) for z in row] for i,row in enumerate(U)])
            mu=sum(y[j]*X[j][j][0] for j in range(n))
            var=sum(norm2(X[i][j])*(y[i]-y[j])**2 for i in range(n) for j in range(i+1,n))
            scores=[sum(x[p[j]]*y[j] for j in range(n)) for p in P]
            scale=max(abs(max(scores)-mu),abs(min(scores)-mu),1)**2
            target=float(var/scale)
            z=np.array([float((s-mu)**2/scale) for s in scores])
            sol=[]
            for sense in (1,-1):
                fit=linprog(sense*z,A_eq=M,b_eq=np.array([float(w) for w in b]),bounds=(0,None),method="highs",
                            options={"primal_feasibility_tolerance":1e-9,"dual_feasibility_tolerance":1e-9})
                if not fit.success:
                    results["solver_failures"]+=1
                    break
                sol.append(sense*fit.fun)
            else:
                residual=max(sol[0]-target,target-sol[1])
                best=max(best,residual)
                results["solved"]+=1
                results["outside_1e-8"]+=int(residual>1e-8)
                if residual>1e-8:
                    print("NUMERICAL ONLY",n,t,"residual",residual,flush=True)
        print(n,dict(results),"max normalized outward residual",best,flush=True)

if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--baseline",required=True);p.add_argument("--trials",type=int,default=24)
    args=p.parse_args()
    run(load_baseline(Path(args.baseline)),args.trials)

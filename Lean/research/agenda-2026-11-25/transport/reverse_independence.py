"""Seek a signed moment witness with nested flows but a violated crossed cut."""
from experiments import *
from itertools import combinations
from math import lcm
import json

def run(n=4):
    P,m,E,laws=moments(n)
    # Expected number of independent cuts is tiny compared with an explicit flow LP.
    active=[-r for r in E]
    seen=set()
    targets=[]
    for li,(kind,A,B,L) in enumerate(laws):
        # Gauge symmetry sends any fixed marked row and column to the first.
        if kind!='crossed' or (li-2*n*2**(n-1))%(n*n)!=0: continue
        for k in (1,2,3):
            for S in combinations(range(len(A)),k):
                T=sorted({j for i,j in L if i in S})
                row=E[[B[j] for j in T]].sum(axis=0)-E[[A[i] for i in S]].sum(axis=0)
                key=tuple(row)
                if key in seen or not any(row): continue
                seen.add(key); targets.append((row,li,S))
    print('targets',len(targets),flush=True)
    for row,cross,S in targets:
        for _ in range(6):
            r=linprog(row,A_ub=csr_matrix(np.array(active)),b_ub=np.zeros(len(active)),
                      A_eq=np.ones((1,len(P))),b_eq=[1],bounds=(-1,1),method='highs')
            if not r.success or r.fun>=-1e-8: break
            z=E@r.x
            num=0
            for kind,A,B,L in laws:
                if kind=='crossed': continue
                C=hall_cut(np.maximum(z[A],0).tolist(),np.maximum(z[B],0).tolist(),L,1e-7)
                if C is None: continue
                F1,T=C
                active.append(E[[A[i] for i in F1]].sum(axis=0)-E[[B[j] for j in T]].sum(axis=0))
                num+=1
            if num: continue
            y=[F(float(x)).limit_denominator(100_000) for x in r.x]
            den=lcm(*(x.denominator for x in y))
            v=[int(x*den) for x in y]
            z=(E.astype(object)@np.array(v,dtype=object)).tolist()
            g=sum(int(x)*c for x,c in zip(row,v))
            if sum(y)!=1 or min(z)<0 or g>=0: break
            assert all(hall_cut([z[i] for i in A],[z[j] for j in B],L) is None
                       for kind,A,B,L in laws if kind!='crossed')
            sparse={''.join(map(str,p)):x for p,x in zip(P,v) if x}
            data={'n':n,'denominator':den,'w':sparse,'crossed_block':cross,'source_family':list(S),'cut':g}
            print('EXACT',data,flush=True)
            Path(__file__).with_suffix('.json').write_text(json.dumps(data,separators=(',',':'))+'\n')
            return
    print('not found',flush=True)

if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--n',type=int,choices=(4,5),default=4)
    run(parser.parse_args().n)

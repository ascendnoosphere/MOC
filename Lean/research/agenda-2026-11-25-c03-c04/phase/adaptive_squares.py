"""Find a separating rank-one square beyond the finite dictionaries.

The eigenvector only proposes small integer coefficients. Every returned
contact tie and negative pairing is checked by exact integer arithmetic.
"""
import argparse
import json
from pathlib import Path
import itertools as it
import math

from reconstruct_cones import P, CONTACT, score, normalize_square, pairing

def propose(dual):
    import numpy as np
    ps=np.asarray(P,dtype=int)
    w=np.asarray(dual,dtype=np.int64)
    for rad in (2,3,4):
        for xs in it.product(range(-rad,rad+1),repeat=4):
            if max(map(abs,xs))!=rad or math.gcd(*xs)!=1 or next(x for x in xs if x)<0:
                continue
            x=(0,*xs)
            ss=np.asarray(x,dtype=np.int64)[ps][:,1:]
            sep=ss-ss[CONTACT[0],:]
            a=sep[CONTACT[1],:]
            idx=np.flatnonzero(a)
            if len(idx):
                p=idx[0]
                ns=np.column_stack([a[p]*np.eye(4,dtype=np.int64)[:,j]
                    -a[j]*np.eye(4,dtype=np.int64)[:,p] for j in range(4) if j!=p])
            else:
                ns=np.eye(4,dtype=np.int64)
            q=sep @ ns
            gram=q.T @ (w[:,None]*q)
            eig,vec=np.linalg.eigh(gram.astype(float))
            if eig[0]>=0:
                continue
            for scl in (2,4,8,16,32,128,512,2048):
                y=(0,*map(int,ns @ np.rint(scl*vec[:,0]).astype(np.int64)))
                s=score(x,y)
                assert s[CONTACT[0]]==s[CONTACT[1]]
                square=normalize_square(s)
                obj=pairing(dual,square)
                if obj<0:
                    return {"x":x,"y":y,"pairing":obj}
    return None

def main():
    p=Path(__file__).with_name("reconstructed_cones.json")
    d=json.loads(p.read_text())
    ap=argparse.ArgumentParser()
    ap.add_argument("--discover",action="store_true")
    args=ap.parse_args()
    result=p.with_name("adaptive_squares.json")
    if args.discover:
        output={name:propose(w) for name,w in d.items()}
        result.write_text(json.dumps(output,indent=2)+"\n")
    else:
        output=json.loads(result.read_text())
    assert output.keys()==d.keys()
    for name,h in output.items():
        if h is not None:
            x,y=h["x"],h["y"]
            assert all(type(v) is int for v in (*x,*y)) and len(x)==len(y)==5
            s=score(x,y)
            assert s[CONTACT[0]]==s[CONTACT[1]]
            assert pairing(d[name],normalize_square(s))==h["pairing"]<0
        print(name,h,flush=True)

if __name__=="__main__":
    main()

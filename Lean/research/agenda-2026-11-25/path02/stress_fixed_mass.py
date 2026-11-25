"""Diagnostic for the fixed-mass MOC one-entry pencil claim (not a proof)."""
import itertools
import json
import sys
import numpy as np
from scipy.optimize import linprog

SEED = 20261125
N_PER_CASE = 15
TOL = 5e-9
FAMILIES = ("generic", "repeated", "exact_opposite", "near_opposite", "near_real", "concentrated")

def solve(n, family, permutations, rng):
    a = (rng.integers(-3,4,n) + 1j*rng.integers(-3,4,n)).astype(complex)
    b = (rng.integers(-3,4,n) + 1j*rng.integers(-3,4,n)).astype(complex)
    z = rng.normal(size=(n,n)) + 1j*rng.normal(size=(n,n))
    if family == "repeated":
        a[1:3]=a[0]; b[1:3]=b[0]
    if family == "exact_opposite":
        b[:2]=-a[:2]
    if family == "near_opposite":
        b[:3]=-a[:3]+1e-7*(z[0,:3]+1)
    if family == "near_real":
        a=a.real+1e-5j*a.imag; b=b.real+1e-5j*b.imag
    if family == "concentrated":
        z=np.eye(n)+0.015*z
    u=np.linalg.qr(z)[0]
    mat=u@np.diag(b)@u.conj().T+np.diag(a)
    col=0
    ud=np.outer(u[:,col],u[:,col].conj())
    b0=np.linalg.det(mat-b[col]*ud)
    a0=np.linalg.det(mat+(1-b[col])*ud)-b0
    labels=permutations[:,col]
    slopes=np.prod(a[permutations[:,1:]]+b[None,1:],axis=1)
    offsets=a[labels]*slopes
    scale=max(1., np.max(np.abs(slopes)),np.max(np.abs(offsets)),abs(a0),abs(b0))
    coeff=np.array([slopes.real,slopes.imag,offsets.real,offsets.imag])/scale
    target=np.array([a0.real,a0.imag,b0.real,b0.imag])/scale
    groups=[np.flatnonzero(labels==i) for i in range(n)]
    mass=abs(u[:,col])**2
    indicators=(labels[None,:]==np.arange(n)[:,None]).astype(float)
    E=np.vstack((indicators,coeff))
    h=np.concatenate((mass,target))
    lp=linprog(np.zeros(len(labels)),A_eq=E,b_eq=h,bounds=(0,None),
              method="highs",options={"primal_feasibility_tolerance":1e-9,
                                       "dual_feasibility_tolerance":1e-9})
    err=np.max(np.abs(E@lp.x-h)) if lp.success else None
    # Probe the requested normals with a near-cancelled individual group.
    margins=[]
    for i in range(n):
        v=rng.normal()+1j*rng.normal()
        aa=-v*a[i]+1e-7*(rng.normal()+1j*rng.normal())
        vals=(aa*slopes+v*offsets).real/scale
        ub=sum(mass[j]*np.max(vals[g]) for j,g in enumerate(groups))
        margins.append(ub-(aa*a0+v*b0).real/scale)
    min_margin=min(margins)
    return lp.status, err, min_margin

def main():
    rng=np.random.default_rng(SEED)
    table={}
    for n in [4,5,6]:
        perms=np.array(list(itertools.permutations(range(n))),dtype=int)
        for family in FAMILIES:
            rows=[solve(n,family,perms,rng) for _ in range(N_PER_CASE)]
            feasible=sum(st==0 and err is not None and err<=TOL for st,err,_ in rows)
            table[f"{n}/{family}"]={"cases":len(rows),"feasible":feasible,
                "lp_statuses":sorted(set(st for st,_,_ in rows)),
                "max_scaled_residual":max((e for _,e,_ in rows if e is not None),default=None),
                "smallest_scaled_probed_margin":min(m for _,_,m in rows)}
    print(json.dumps({"seed":SEED,"solver":"SciPy HiGHS", "max_residual_for_feasible":TOL,
     "cases":sum(x["cases"] for x in table.values()),"table":table},default=lambda v: v.item(),indent=2))

if __name__=="__main__": main()

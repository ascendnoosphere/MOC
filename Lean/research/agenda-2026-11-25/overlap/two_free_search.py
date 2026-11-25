"""Bounded Cycle01 path 14 diagnostic, not a proof; exact recovery needed for hits."""
from itertools import combinations, permutations
import numpy as np
from scipy.optimize import linprog

U = np.array([[-1,32,20],[-32,-1,-16],[-20,-16,31],[16,-20,8]]) / 41.
Z = np.concatenate((np.eye(3), U))
SUBSETS = list(combinations(range(7), 3))
WEIGHTS = {s: abs(np.linalg.det(Z[list(s)]))**2 for s in SUBSETS}
INJECTIONS = list(permutations(range(3,7),3))
TRANSVERSALS = [
    {s for s in SUBSETS if all((i in s) != (j in s) for i,j in enumerate(f))}
    for f in INJECTIONS
]
rng=np.random.default_rng(20261125)
for free in combinations(range(7),2):
    mc=0
    normalsep=None
    for trial in range(64):
        x=rng.integers(-2, 3, 7)+1j*rng.integers(-2,3,7)
        def coeff(s):
            result = np.zeros(4,complex)
            mask = sum(2**b for b,label in enumerate(free) if label in s)
            result[mask] = np.prod([x[i] for i in s if i not in free])
            return result
        base = {s: coeff(s) for s in SUBSETS}
        target = sum(WEIGHTS[s]*base[s] for s in SUBSETS)
        vertices = np.array([sum(base[s] for s in ss) for ss in TRANSVERSALS])
        shifts = vertices - target
        delta=np.concatenate((shifts.real,shifts.imag),axis=1)
        sep=linprog(np.r_[np.zeros(8),-1],A_ub=np.c_[delta,np.ones(len(delta))],
                    b_ub=np.zeros(len(delta)),bounds=[(-1,1)]*8+[(None,None)],method="highs")
        if sep.success and sep.x[-1] > mc+1e-7:
            mc=sep.x[-1]
            normalsep = (trial, x, sep.x)
            if mc>.001:
                break
    if normalsep:
        print(f"HIT free={free} margin={mc} trial,spectra,normal={normalsep}", flush=True)
    else:
        print(f"no hit free={free}", flush=True)

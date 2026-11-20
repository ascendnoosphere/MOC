"""Verify the spin-3/2 scalar theorem. Run python verify_scalar.py.

Requirements: Python, SymPy, g++, and GMP C++ headers/libraries. Large
intermediate coefficient files are written in a temporary directory and removed
when this command finishes. OMP_NUM_THREADS controls the parallel determinant
stage. All verification arithmetic is integral or rational.
"""

from functools import lru_cache
from itertools import combinations, permutations, product
from pathlib import Path
from tempfile import TemporaryDirectory
from subprocess import run
import os
import sympy as sp

from verify_spin_moc import T, model, nonnegative_on_unit_interval, check_four

PS = list(permutations(range(4)))
FACE = ( "1324", "1342", "1423", "1432", "2143", "2314", "2341",
         "2413", "3124", "3142", "3214", "3412", "4123")
ANCHOR = "4231"
COORDS = tuple(PS.index(tuple(int(x)-1 for x in name)) for name in FACE + (ANCHOR,))
TWICE_RADII = (2,6,6,4,2,6,2,1,6,1,4,8,2)
R = tuple(sp.Rational(a,2) for a in TWICE_RADII)


@lru_cache(None)
def matchings(labels):
    if not labels:
        return ((),)
    return tuple(
        ((labels[0], labels[j]),) + rest
        for j in range(1,len(labels))
        for rest in matchings(labels[1:j] + labels[j+1:])
    )


def matching_expansion(matching):
    # [ij]=u_i v_j-v_i u_j. Every term has four u factors and four v factors.
    return {tuple(sorted(edge[t] for edge,t in zip(matching,bits))):(-1)**sum(bits)
            for bits in product((0,1), repeat=4)}


def make_tensor(directory):
    ms = matchings(tuple(range(8)))
    keys = list(combinations(range(8),4))
    ex = [matching_expansion(m) for m in ms]
    all_columns = sp.Matrix([[z.get(k,0) for z in ex] for k in keys])
    bipartite = [tuple((i,4+p[i]) for i in range(4)) for p in PS]
    cols = tuple(ms.index(bipartite[j]) for j in COORDS)
    basis = all_columns.extract(range(len(keys)),cols)
    rows = basis.T.rref()[1]
    assert len(rows)==14
    # Twice the invariant linear forms in the chosen matching coordinates.
    forms = 2*basis.extract(rows,range(14)).inv()*all_columns.extract(rows,range(105))
    assert all(x.is_Integer for x in forms)
    assert basis*forms == 2*all_columns

    tensor = [[[0]*14 for _ in range(14)] for _ in range(14)]
    for s,m in enumerate(ms):
        word = sum(m,())
        sign = (-1)**sum(x>y for j,x in enumerate(word) for y in word[j+1:])
        terms = [(i,int(forms[i,s])) for i in range(14) if forms[i,s]]
        for i,x in terms:
            for j,y in terms:
                for k,z in terms:
                    tensor[i][j][k] += sign*x*y*z
    # With H[i,j](h)=sum_k tensor[i,j,k]h[k], F(h)=h' H(h) h/6.
    e = sp.ones(14,1)
    f = sp.Matrix([0]*13+[2])
    def hess(h):
        return sp.Matrix(14,14,lambda i,j:sum(tensor[i][j][k]*h[k] for k in range(14)))
    he = hess(e)
    assert he.rank()==4 and he*e==sp.zeros(14,1)
    hf = hess(f)
    F = (f.T*hf*f)[0]/6
    Q = (e.T*hf*f)[0]/2
    assert F==Q==-8
    assert Q**2*(hf-F/Q*he).det()==-2**48
    # Check that Q is nonzero on the parametrized family of true costs.
    vals = (0,1,2,sp.I)
    probe=sp.Matrix([sp.re(sp.prod(vals[i]+vals[PS[j][i]] for i in range(4))) for j in COORDS])
    assert (e.T*hess(probe)*probe)[0]/2==-32
    # C++ uses signed 64-bit longs to assemble the initial small integer
    # matrices. In the interpolation grid, ||h||_1 <= 11*9+2.
    largest = max(abs(x) for row in tensor for block in row for x in block)
    assert largest<=12
    assert 12**2*14*(11*9+2)**3 < 2**63
    (directory/'spin_facet_tensor.dat').write_text(
        ' '.join(str(x) for row in tensor for block in row for x in block)+'\n')


def verify_spin_weights():
    unused, full = model(4)
    ij = [(i,j) for k in range(3) for i in combinations(range(4),k)
          for j in combinations(range(4),k)]
    orbit = sp.Matrix([[int({p[i] for i in I}==set(J)) for p in PS] for I,J in ij])
    block = orbit.extract(range(53),COORDS)
    rows = block.T.rref()[1]
    assert len(rows)==14
    weights = block.extract(rows,range(14)).inv()*full.extract(rows,[0])
    assert all(sp.expand(x)==0 for x in block*weights-full)
    p = 1-4*T-3*T**2+22*T**3-15*T**4
    assert sp.expand(2*weights[-1]-p)==0 and sp.expand(sum(weights)-1)==0
    a,b=sp.Rational(3,10),sp.Rational(47,100)
    for w,r in zip(weights[:13],R):
        assert nonnegative_on_unit_interval(sp.expand((r*w+p).subs(T,a+(b-a)*T)))
    print('Verified the 13 inequalities on the complete gap interval.',flush=True)


def main():
    check_four()
    verify_spin_weights()
    with TemporaryDirectory() as tmp:
        directory=Path(tmp)
        make_tensor(directory)
        exe=directory/'bernstein'
        src=Path(__file__).with_name('bernstein.cpp')
        run(['g++','-O3','-fopenmp','-std=c++17',str(src),'-lgmpxx','-lgmp','-o',str(exe)],check=True)
        env=dict(os.environ)
        env.setdefault('OMP_NUM_THREADS','4')
        for args in (['grid'],['coeff']):
            run([str(exe),*args],cwd=directory,env=env,check=True)
        for denominator,numerators,wanted in [(2,TWICE_RADII,17123),(12,(4,72,72,18,72,3,18,4,3,4,2,3,18),0)]:
            args=['bern',str(denominator),*map(str,numerators)]
            out=run([str(exe),*args],cwd=directory,env=env,check=True,capture_output=True,text=True).stdout
            assert f'negative 0 zero {wanted} min ' in out
            print(out,end='')
    print('Verified scalar MOC for every spin-3/2 parameter and every pair of complex spectra.')


if __name__=='__main__':
    main()

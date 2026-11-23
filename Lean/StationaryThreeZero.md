# Stationary support at order four: three zero entries

Status: exact mathematical proof, with a reproducible symbolic check of
the coefficient identity below. Not yet a Lean theorem. The general
order-four conjecture remains open.

## Theorem

Let \(a,b\in\mathbb C^4\), \(\eta\in\mathbb C\), and let \(U\) be a
relative unitary at a stationary point of
\[
F_\eta(U)=\operatorname{Re}(\eta\det(\operatorname{diag}(a)+
 U\operatorname{diag}(b)U^*)).
\]
If \(U\) has at least three zero entries, its support value is at most
the largest projected matching product.

Indeed, if two zeros share a row or column, apply SparseRow.lean
and the order-three theorem. If at least four zeros occur, apply
SparseMaximizerOrderFour.md, Section 1. The only remaining pattern is
exactly three zeros in distinct rows and columns. Reindex them to the
first three diagonal entries. The real normal form in that note, Section 2,
puts \(U\), up to diagonal phases, in the normalized real form below.
The objective and stationarity are invariant under these phase changes
and simultaneous relabeling of spectral coordinates.

### 1. Notation

Use row-to-column permutations \(p\), inverse to the convention of
Weights.lean. Write
\[
P_p=\prod_{i=1}^4(a_i+b_{p(i)}),\quad
s_p=\operatorname{Re}(\eta P_p).
\]
Set \(X=x^2,Y=y^2,Z=z^2,\rho=X/(YZ)\), where \(x,y,z>0\). Let
\[
T=\begin{pmatrix}
0&x&y&1\\
z&0&-1/y&1\\
-1/z&-1/x&0&1\\
(X+Y+1)/(xy)&-(YZ+Y+1)/(yz)&(XZ+X+Z)/(xz)&x/(yz)-yz/x
\end{pmatrix}.
\]
Its rows are orthogonal; their squared norms are
\(N_1=1+X+Y\), \(N_2=1+Z+1/Y\), \(N_3=1+1/X+1/Z\),
and \(N_4=N_1N_2N_3=D=\det T\).
The normalized rows give a real orthogonal representative.
The signed weights are invariant under row rescaling:
\[
w_p=\operatorname{sgn}(p)\prod_iT_{i,p(i)}/D.
\]

The two signed weights that fix position four and cycle the first
three labels have numerators \(\rho-1\) and \(1/\rho-1\).
If \(\rho=1\), there is a fourth zero and all weights are nonnegative.
If \(\rho>1\), simultaneously exchange the first two row and column
labels (or any transposition among the first three) and renormalize
phases to the displayed form. This interchanges the two cyclic
permutations, so the new negative cycle is 2314 and the new
\(\rho<1\). It suffices to prove the case \(0<\rho<1\).

### 2. An exact tangent identity

Let \(R(\theta)\) rotate rows one and two, with block
\(\begin{pmatrix}\cos\theta&\sin\theta\\-\sin\theta&\cos\theta\end{pmatrix}\).
At \(\theta=0\), after undoing fixed row normalization and multiplying
the derivative by the positive scalar \(\sqrt{N_2/N_1}\), the tangent
to \(T\) is
\[
\dot T_{1,:}=T_{2,:},\qquad
\dot T_{2,:}=-(N_2/N_1)T_{1,:},\qquad
\dot T_{3,:}=\dot T_{4,:}=0.
\]
In particular \(\dot{\det T}=0\). Put
\[
h_p=\frac{\operatorname{sgn}(p)}{2N_2}
 \sum_{k=1}^2\dot T_{k,p(k)}\prod_{i\ne k}T_{i,p(i)}.
\]
The derivative of the spectral objective is a positive scalar times
\(\sum_p h_p s_p\). Hence stationarity implies this sum is zero.

There are simpler coefficients \(d_p\), supported on the eleven
permitted permutations, with the following exact table. Entries not
listed have \(w_p=d_p=0\).

| \(p\) | \(Dw_p\) | \(d_p\) |
| --- | --- | --- |
| 2143 | \(XZ+X+Z\) | 0 |
| 2314 | \(\rho-1\) | -1 |
| 2341 | \(X/Y+1+1/Y\) | 1 |
| 2413 | \(X+X/Z+1\) | 0 |
| 3124 | \(1/\rho-1\) | 1 |
| 3142 | \(YZ+Y+1\) | -1 |
| 3412 | \(Y+Y/Z+1/Z\) | \(-1/Z\) |
| 3421 | \(1+Y/X+1/X\) | \(-1-1/X\) |
| 4123 | \(Z+1+Z/X\) | 0 |
| 4312 | \(1+1/Z+1/(YZ)\) | \(1+1/Z\) |
| 4321 | \(1/Y+1/X+1/(XY)\) | \(1/X\) |

The identity \(\sum_p h_p P_p=\sum_p d_p P_p\) uses only that
\(K_{ij}=a_i+b_j\) has rank at most two. For completeness define a
matrix \(E\) with the only nonzero entries
\[
E_{13}=-1/2,\quad E_{23}=1/2,\quad
E_{31}=\frac{XZ+X+Z}{2ZN_1},\quad
E_{32}=-\frac{XYZ+XY+YZ}{2XN_2Y}.
\]
(The last denominator \(2XN_2Y=2X(YZ+Y+1)\).)
Direct expansion for each of the 24 permutations gives
\[
h_p-d_p=\operatorname{sgn}(p)\sum_i E_{i,p(i)}.
\tag{*}
\]
To check signs and factors independently, use the script below.
For fixed \(i,j\),
\[
\sum_{p:p(i)=j}\operatorname{sgn}(p)P_p
=(-1)^{i+j}K_{ij}\det K_{\hat i,\hat j}=0,
\]
because that three-by-three submatrix has rank at most two. Summing
(*) against \(P_p\) proves the identity. Taking real parts after
multiplication by \(\eta\) gives
\[
\sum_p d_p s_p=0.
\tag{1}
\]
This is the step that would fail for arbitrary independent permutation
scores. It also applies to any real score in the linear span of
subset-image indicators: each alternating singleton fiber sums to
zero against such an indicator in order four (one of the two
remaining row groups has at least two interchangeable labels).

### 3. Nonnegative corrected weights

Set
\[
\widetilde w_p=w_p+(\rho-1)d_p/D.
\]
The correction removes the negative weight at 2314. At 3124 the
corrected numerator equals \(1/\rho-1+\rho-1=(1-\rho)^2/\rho>0\).
Every entry whose \(d_p\le0\), other than 2314, is unchanged or
increases because \(\rho-1<0\). For the three remaining positive
correction entries, the corrected numerators are
\[
\begin{array}{c|l}
2341 & X/Y+1/Y+\rho\\
4312 & 1/(YZ)+\rho(1+1/Z)\\
4321 & 1/Y+1/(XY)+\rho/X.
\end{array}
\]
They are positive. The table has \(\sum_p d_p=0\), so the corrected
weights sum to one. Equation (1) and the signed determinant identity
give \(F_\eta(U)=\sum_p\widetilde w_p s_p\le\max_p s_p\). QED.

At a global maximum, the other inequality follows from feasibility
of permutations. Thus a permutation matrix realizes the same support
maximum; in particular it has a degree-one row/column and is
reindexed Hessenberg. This eliminates all global maximizers with
three or more zeros as strict support violations. It does NOT prove
MOC for a nonstationary three-zero unitary: the derivative of its
objective need not vanish and the correction can change the support.

### 4. Reproducible exact coefficient check (Python/SymPy)

Run this code in an environment with SymPy. It verifies the table,
normalization identities and (*) as rational-function identities in
three independent symbols, rather than by numerical sampling.

```python
import itertools as it
import sympy as S
x,y,z = S.symbols('x y z', positive=True)
X,Y,Z = x*x,y*y,z*z
rho = X/(Y*Z)
N1,N2,N3 = 1+X+Y,1+Z+1/Y,1+1/X+1/Z
D = N1*N2*N3
T = S.Matrix([[0,x,y,1],[z,0,-1/y,1],[-1/z,-1/x,0,1],
              [(X+Y+1)/(x*y),-(Y*Z+Y+1)/(y*z),
               (X*Z+X+Z)/(x*z),x/(y*z)-y*z/x]])
def zero(q): return S.cancel(q)==0
assert all(zero(q) for q in T*T.T-S.diag(N1,N2,N3,D))
assert zero(T.det()-D)
dT=S.zeros(4)
dT[0,:]=T[1,:]
dT[1,:]=-N2/N1*T[0,:]
E=S.zeros(4)
E[0,2]=-S.Rational(1,2)
E[1,2]=S.Rational(1,2)
E[2,0]=(X*Z+X+Z)/(2*Z*N1)
E[2,1]=-(X*Y*Z+X*Y+Y*Z)/(2*X*N2*Y)
table={
'2143':(X*Z+X+Z,0),'2314':(rho-1,-1),
'2341':(X/Y+1+1/Y,1),'2413':(X+X/Z+1,0),
'3124':(1/rho-1,1),'3142':(Y*Z+Y+1,-1),
'3412':(Y+Y/Z+1/Z,-1/Z),'3421':(1+Y/X+1/X,-1-1/X),
'4123':(Z+1+Z/X,0),'4312':(1+1/Z+1/(Y*Z),1+1/Z),
'4321':(1/Y+1/X+1/(X*Y),1/X)}
for p in it.permutations(range(4)):
    sign=(-1)**sum(p[i]>p[j] for i in range(4) for j in range(i+1,4))
    key=''.join(str(i+1) for i in p)
    w,d=table.get(key,(0,0))
    assert zero(sign*S.prod(T[i,p[i]] for i in range(4))-w)
    h=sign*sum(dT[k,p[k]]*S.prod(T[i,p[i]] for i in range(4) if i!=k)
               for k in range(2))/(2*N2)
    assert zero(h-d-sign*sum(E[i,p[i]] for i in range(4)))
assert zero(sum(d for w,d in table.values()))
assert zero(sum(w for w,d in table.values())-D)
print("All exact identities verified.")
```


### 5. Residual problem

By four_minor_mixture (FourMinorTransport.lean), a global maximum
always has a real orthogonal representative, and any existing zero
entries can be preserved. A strict order-four violation therefore
requires real orthogonal maximizing representatives with at most two
zero entries, in distinct rows/columns, with no degree-two row or
column. One must exclude the remaining zero-, one-, and two-zero
patterns; the dense case is indispensable. The stationary weight
correction is not claimed for all those patterns.

Suggested Lean formalization: prove the finite alternating singleton
fiber identity for the rank-two additive kernel, verify the table
after clearing positive denominators, use the real two-row derivative
stationarity, and combine the nonnegative corrected weights with
holds_iff_directional. No unchecked theorem or axiom has been added.

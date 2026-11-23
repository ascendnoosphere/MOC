# Dense stationary order-four reduction

Status: exact sign-class reduction and an equivalent residual polynomial
feasibility problem. The latter has NOT been proved empty. The unrestricted
order-four conjecture is not proved by this note.

Use StationaryPivotReduction.md: an admissible nonzero pivot of a real
orthogonal stationary mixer gives a nonnegative permutation representation
of its support value. Any order-four support violation has a real orthogonal
global maximizer; that maximizer must have no zero entry or admissible pivot.

## 1. Only one dense sign class remains

Normalize the signs of a dense real orthogonal \(4\times4\) matrix so
its first row and column are positive. Use indices 0,1,2,3 in this note.
Orthogonality implies every pair of distinct rows has at least one
agreement and one disagreement in signs, and the same for columns.
The normalized sign matrices satisfying these necessary conditions,
up to independent permutations and re-normalization of row/column
signs, have exactly the following three representatives:
\[
S_A=\begin{pmatrix}
+&+&+&+\\+&-&-&-\\+&-&-&+\\+&-&+&-
\end{pmatrix},\quad
S_B=\begin{pmatrix}
+&+&+&+\\+&-&-&-\\+&-&-&+\\+&-&+&+
\end{pmatrix},
\quad
S_C=\begin{pmatrix}
+&+&+&+\\+&-&-&+\\+&-&+&-\\+&+&-&-
\end{pmatrix}.
\]
The exact finite census in Section 4 verifies this from all \(2^9\)
normalized sign matrices: 174 satisfy the necessary conditions, with
orbit sizes 96, 72, 6 respectively.

For ordered row pair \(I=(i,r)\) and column pair \(J=(j,s)\),
write \(\Delta_{I;J}=\det U[I,J]\). For the increasing order on
each pair, orthogonality gives the complementary cofactor identity
\[
\Delta_{I;J}=(-1)^{\sum I+\sum J}\det(U)\Delta_{I^c;J^c}.
\tag{1}
\]
In each of the three normalized sign classes, \(\det U=+1\):
one can select a complementary pair of two-minors both of whose
two Leibniz terms have the same sign. In class A use
\(I=(0,1),J=(0,2)\); in classes B,C use
\(I=(0,1),J=(0,1)\). Substitute their forced signs into (1).

A pivot \(U_{ij}\ne0\) is admissible exactly when for every complementary
entry \(U_{rs}\) either
\[
U_{ij}U_{rs}U_{rj}U_{is}<0
\quad\text{or}\quad
|U_{ij}U_{rs}|\ge |U_{rj}U_{is}|.
\tag{2}
\]
Indeed, (2) is exactly nonnegativity of
\(U_{rs}(U_{rs}-U_{rj}U_{is}/U_{ij})\).
Thus a rectangle with negative product never forbids a pivot.
A positive-product rectangle with nonzero determinant forbids
its two corners on the smaller-magnitude diagonal, and a zero
determinant forbids neither diagonal.

### Class A

The pivot (0,0) is always admissible. For its row-1 constraints,
all three complementary rectangles have negative sign product.
The only positive-product rectangles for rows 2 and 3 that
involve (0,0) use column 3 or 2, respectively.
Their determinants \(\Delta_{02;03}\), \(\Delta_{03;02}\)
are positive by (1), since their complementary determinants
\(\Delta_{13;12}\), \(\Delta_{12;13}\) are negative.
This gives (2) for the two remaining comparisons.

### Class B

The same argument gives positive determinants
\(\Delta_{02;03}\), \(\Delta_{03;02}\).
The only additional comparison for pivot (0,0) is
\(\Delta_{03;03}\ge0\), which therefore suffices for admissibility.

Suppose \(\Delta_{03;03}<0\). Write
\(r_k=U_{1k}/U_{0k}\) and \(t_k=U_{3k}/U_{0k}\).
Then \(r_0>0\), \(r_k<0\) for \(k>0\);
\(t_0,t_2,t_3>0\), \(t_1<0\);
and \(t_0>t_3\) by the strict determinant inequality.
If \(\Delta_{03;23}\ge0\), then \(t_3\ge t_2\).
Hence \(t_0\) is strictly greater than every other \(t_k\).
Using the orthogonality of rows 0 and 1,
\[
\sum_k U_{0k}^2 r_k t_k
=\sum_{k>0}U_{0k}^2 r_k(t_k-t_0)>0,
\]
contrary to orthogonality of rows 1 and 3.
Therefore \(\Delta_{03;23}<0\).

Now pivot (1,0) is admissible: the constraints from row 0
are automatic by the signs; the positive-product rectangles
from row 2 use columns 1 and 2 and have negative determinants
\(\Delta_{12;01}=\Delta_{03;23}<0\) and
\(\Delta_{12;02}=-\Delta_{03;13}<0\).
The positive-product rectangle from row 3 uses column 1
and has negative determinant
\(\Delta_{13;01}=-\Delta_{02;23}<0\).
All their main diagonal products are negative, so these
inequalities give (2). This settles class B.

Consequently a strictly violating global maximizer must have the
balanced Hadamard sign class \(S_C\). In particular, each pair of
rows (and columns) has exactly two sign agreements and two
sign disagreements.

## 2. One strict minor-sign chamber is sufficient

In class C, there are exactly twelve positive-product rectangles.
The complement operation pairs them into six pairs. Choose the
following representatives, in the stated order:
\[
(01;03),\quad(01;12),\quad(02;02),\quad(02;13),
\quad(03;01),\quad(03;23).
\tag{3}
\]
Their determinant signs belong to \(\{-1,0,1\}^6\).
Equation (1) fixes the signs of their complementary rectangles.
For each such six-tuple, delete the forbidden corners according to (2).
The exact census in Section 4 gives just eight tuples for which
all sixteen pivots are forbidden. None has a zero sign.

The independent row and column permutations followed by sign
normalization that preserve \(S_C\) act transitively on the eight
tuples (96 sign-normalized transformations suffice).
Thus a single canonical tuple is enough:
\[
\boxed{(-,-,-,+,-,-).}
\tag{4}
\]
The census also verifies that in (4) four pivots
\((0,0),(1,1),(2,3),(3,2)\) are each forbidden by three
rectangles; every other pivot is forbidden by exactly one
rectangle. These are necessary sign restrictions only, not
a claim that every assignment is realizable by an orthogonal matrix.

By Sections 1--2 and StationaryPivotReduction.md, if order-four MOC
fails, it has a real orthogonal violating global maximizer in the
explicit open sign chamber \(S_C,(4)\), after reindexing spectra
together with their rows and columns.

## 3. An exact residual semialgebraic feasibility problem

The following formulation gives a finite, explicit remaining task.
It must not be treated as an already solved quantifier elimination.

Let \(P\) exchange columns 2 and 3, and \(L=\operatorname{diag}(1,-1,-1,-1)\).
For a normalized matrix \(U\) in the residual chamber, the matrix
\(V=LUP\) has positive diagonal and determinant +1. In particular
\(\operatorname{tr}V>0\). A real special orthogonal four-matrix with
a -1 eigenvalue has at least two -1 eigenvalues (their multiplicity
is even), and hence trace at most zero. Therefore \(V+I\) is
invertible, and there is a real skew-symmetric \(4\times4\) matrix
\(T\) with
\[
V=(I-T)(I+T)^{-1}.
\]
Conversely every real skew \(T\) gives such a special orthogonal
matrix \(V\) (require the chamber and positive-diagonal conditions
through \(U=LVP\)). The denominator
\(q(T)=\det(I+T)\) is strictly positive: the nonzero eigenvalues of
a real skew matrix come in conjugate pairs \(\pm i\lambda\).
Write the polynomial matrix
\[
W(T)=L(I-T)\operatorname{adj}(I+T)P,\qquad U=W/q.
\]
Require \(W\) to have the sign matrix \(S_C\), and the six
two-minors of \(W\) in (3) to have strict signs (4).
Because \(q>0\), these are exactly the chamber constraints.

For distinct spectra with no vanishing cross-sum, row and column
rescaling puts the additive kernel into the form
\[
K_{ij}=1+x_i y_j,\quad x_0=y_0=0,\quad x_1=1,
\]
with five complex free variables \(x_2,x_3,y_1,y_2,y_3\).
Indeed, for the original additive kernel \(C_{ij}=a_i+b_j\)
set
\[
K_{ij}=\frac{C_{ij}C_{00}}{C_{i0}C_{0j}}.
\]
The first row and column are ones; the remaining block of
\(K-1\) is rank one, as follows either from the rank-two
Schur complement or directly from
\(C_{ij}C_{00}-C_{i0}C_{0j}=-(a_i-a_0)(b_j-b_0)\).
Distinctness lets one normalize \(x_1=1\).
Every matching product and weighted determinant acquires the
same nonzero complex factor under this rescaling, so its phase
and modulus can be absorbed into the support direction.

Conversely every finite kernel \(1+x_i y_j\) is an additive
kernel up to nonzero row and column factors: choose a complex
\(\lambda\) such that \(x_i\ne\lambda\) and
\(1+\lambda y_j\ne0\) for all labels, then
\[
1+x_i y_j=(x_i-\lambda)(1+\lambda y_j)
 \left(\frac1{x_i-\lambda}+\frac{y_j}{1+\lambda y_j}\right).
\]
This justifies using the normalized kernels for testing MOC.

Let \(\eta\in\mathbb C\), \(|\eta|^2=1\), and
\[
N(T,x,y,\eta)=\operatorname{Re}(\eta\det(K\circ W(T))),
\qquad
s_p=\operatorname{Re}(\eta\prod_i K_{i,p(i)}).
\]
Since \(\det U=+1\), the support objective equals \(N/q^4\).
A strict violation is equivalent to the 24 polynomial inequalities
\[
N-q^4s_p>0\qquad(p\in S_4).
\tag{5}
\]
At an orbit maximum, first-order stationarity in the six independent
entries \(t_l\) of \(T\) adds the six polynomial equations
\[
q\,\partial_{t_l}N-4N\,\partial_{t_l}q=0,\quad l=1,\ldots,6.
\tag{6}
\]

The unrestricted order-four conjecture is equivalent to
infeasibility of the system consisting of the chamber constraints,
\(|\eta|^2=1\), (5), and (6), in 18 real variables:
six skew entries, ten real/imaginary parts of normalized spectral
variables, and two direction components. For the reverse implication,
any solution violates MOC for an actual additive spectral kernel by
the factorization above, regardless of whether it is a global maximum.
For the forward reduction from a failure, continuity permits distinct
spectra with no vanishing cross-sums while preserving the strict
violation; realification, compactness, the stationary pivot theorem,
and the sign census supply a maximum in the chamber, which must
satisfy (6).

Adding the negative semidefinite Hessian of \(N/q^4\) at (6) is
also legitimate as a necessary condition for the violating global
maximum. The point of this reduction is to restrict exact algebraic
or analytic attempts to one explicit chamber. No proof of its
infeasibility has been obtained.

## 4. Exact finite sign verifier

The following script uses only Python's standard library. It enumerates
the 512 sign matrices, computes sign equivalence classes, and certifies
the eight possible no-pivot orientations and their symmetry orbit.

```python
from itertools import permutations, combinations, product
P = tuple(permutations(range(4)))
Q = tuple(combinations(range(4), 2))
R = tuple(product(Q,Q))
index = {r:i for i,r in enumerate(R)}
def comp(I): return tuple(i for i in range(4) if i not in I)
def normalize(S):
    return tuple(tuple(S[i][j]*S[i][0]*S[0][j]*S[0][0]
                       for j in range(4)) for i in range(4))
def reorder(S,p,q):
    return tuple(tuple(S[i][j] for j in q) for i in p)
A=((1,1,1,1),(1,-1,-1,-1),(1,-1,-1,1),(1,-1,1,-1))
B=((1,1,1,1),(1,-1,-1,-1),(1,-1,-1,1),(1,-1,1,1))
C=((1,1,1,1),(1,-1,-1,1),(1,-1,1,-1),(1,1,-1,-1))
valid=set()
for k in product((-1,1),repeat=9):
    S=((1,1,1,1),)+tuple((1,)+k[3*i:3*i+3] for i in range(3))
    if len(set(S))==4 and len(set(zip(*S)))==4:
        valid.add(S)
orbits=[{normalize(reorder(S,p,q)) for p in P for q in P}
        for S in (A,B,C)]
assert [len(o) for o in orbits]==[96,72,6]
assert set.union(*orbits)==valid and len(valid)==174
assert sum(map(len,orbits))==len(valid)

S=C
positive=[]; signs=[]
for (i,r),(j,s) in R:
    a,b=S[i][j]*S[r][s],S[i][s]*S[r][j]
    positive.append(a if a==b else 0)
    signs.append(None if a==b else a)
amb=[]; fixed=[None]*36
for k,(I,J) in enumerate(R):
    l=index[comp(I),comp(J)]
    if l<k: continue
    f=(-1)**(sum(I)+sum(J))
    a,b=signs[k],signs[l]
    if a is None and b is None: amb.append((k,l,f))
    elif a is None: fixed[k],fixed[l]=f*b,b
    else:
        assert b is None or b==f*a
        fixed[k],fixed[l]=a,f*a
assert [R[k] for k,l,f in amb]==[
    ((0,1),(0,3)),((0,1),(1,2)),((0,2),(0,2)),
    ((0,2),(1,3)),((0,3),(0,1)),((0,3),(2,3))]
def counts(v):
    d={(i,j):0 for i in range(4) for j in range(4)}
    for k,((i,r),(j,s)) in enumerate(R):
        if not positive[k] or not v[k]: continue
        bad=((i,s),(r,j)) if v[k]==positive[k] else ((i,j),(r,s))
        for pt in bad: d[pt]+=1
    return d
bad=set(); canonical=None
for x in product((-1,0,1),repeat=6):
    v=fixed[:]
    for z,(k,l,f) in zip(x,amb): v[k],v[l]=z,f*z
    if all(counts(v).values()):
        assert all(x)
        bad.add(tuple(v))
        if x==(-1,-1,-1,1,-1,-1): canonical=tuple(v)
assert len(bad)==8 and canonical is not None
d=counts(canonical)
assert {pt for pt,n in d.items() if n==3}=={(0,0),(1,1),(2,3),(3,2)}
assert all(n in (1,3) for n in d.values())
orbit=set(); nsym=0
for p in P:
    for q in P:
        Z=reorder(S,p,q)
        if normalize(Z)!=S: continue
        nsym+=1
        c=Z[0]; r=tuple(Z[i][0]*Z[0][0] for i in range(4))
        v=[]
        for I,J in R:
            a=[p[i] for i in I]; b=[q[j] for j in J]
            factor=r[I[0]]*r[I[1]]*c[J[0]]*c[J[1]]
            factor*=(-1)**((a[0]>a[1])+(b[0]>b[1]))
            v.append(factor*canonical[index[tuple(sorted(a)),tuple(sorted(b))]])
        orbit.add(tuple(v))
assert nsym==96 and orbit==bad
print("Exact sign census passed.")
```

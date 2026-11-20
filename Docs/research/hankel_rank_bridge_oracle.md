## 1. Original-source verification and the legitimate rank threshold

Original versioned sources:

- https://arxiv.org/pdf/1010.3465v2
- https://arxiv.org/src/1010.3465v2


**Theorem 1.7**, printed page 4, states:

> “Suppose that \(\ell\) spans an extreme ray of \(\Sigma_{4,4}^*\). Then \(\operatorname{rank}Q_\ell=1\) or \(\operatorname{rank}Q_\ell=6\).”

Original source: Blekherman, *Nonnegative polynomials and sums of squares*, arXiv:1010.3465v2, Theorem 1.7, printed p. 4.

Here \(Q_\ell(f)=\ell(f^2)\) acts on **all ten quaternary quadrics**. Lemma 2.1 explicitly requires the **full Hankel subspace**, not merely PSD plus selected quadratic equations.

### Proof and needed lemmas

The relevant original chain is Lemmas 2.1–2.2, Corollary 2.3, Lemma 2.4, Theorem 2.5, Lemma 2.6, and Theorem 2.7:

- A non-rank-one extreme ray has a kernel with no common complex projective zero.
- Choose four parameter quadrics in that kernel.
- Their complete intersection is Gorenstein with socle degree four.
- Any additional independent kernel quadric pairs nontrivially into the degree-four socle, forcing the functional to vanish identically.
- Thus the kernel has dimension four and the Hankel rank is \(10-4=6\).

The unified proof is on printed page 7, source lines 253–265.

### Corollary that genuinely pays rent

If
\[
H\succeq0,\qquad H\text{ is full quaternary-quartic Hankel},
\qquad \operatorname{rank}H\le5,
\]
then \(H\) is a finite positive sum of real point-evaluation matrices.

**Proof.** Decompose \(H\) into extreme rays of the Hankel PSD cone, using its compact trace-one base. Every PSD summand has range contained in \(\operatorname{range}H\), hence rank at most five. Theorem 1.7 forces each summand to have rank one; Lemma 2.4 identifies those summands as real evaluations. No extremality assumption on \(H\) itself is needed.

This is the usable theorem. **The missing issue is membership in the full Hankel cone.**

---

## 2. Exactly what the project’s fourteen directions impose

The project establishes the rank-five certificate guarantee separately from its alternative parity guarantee; it does not guarantee both simultaneously (`organized/research/JOINT_CERTIFICATE_RANK.md:71–99`). Its existing rank-one computation identifies the eight pure-parity gauges with \(TC=0\) (`organized/research/verify_joint_certificate_rank.py:107–156`).

I extended that calculation using the exact arrays in `organized/research/actual_fiber_allocation/criterion.json:5248`.

On **each** pure-parity block, exact rational row reduction gives
\[
\operatorname{span}(\text{fourteen project quadrics})
=
\operatorname{span}\bigl(TC,\operatorname{adj}C-dT\bigr),
\]
of dimension fourteen: eight independent \(TC\) equations and six symmetric adjugate equations.

This is an equality of polynomial spaces—not a claim that each allocation basis matrix individually equals an adjugate equation.

### The full twenty Hankel relations

Write the ten quadratic coordinates as
\[
(z,u,v)=(\beta^2,\ \beta p,\ pp^T).
\]
Their full quadratic relation space has dimension
\[
\dim\operatorname{Sym}_{10}-\dim H_{4,4}=55-35=20.
\]

It consists of:

| Relations | Number |
|---|---:|
| Entries of \(\operatorname{adj}V\) | 6 |
| Entries of \(V[u]_\times\) | 8 independent |
| \(u_i u_j-zv_{ij}\), \(i\le j\) | 6 |

For moment matrices, these mean **linear equalities between matrix entries corresponding to equal monomial products**.

- **Plus:** \(z=\beta^2\) is omitted. Its 45 quadratic products span 31 quartics, leaving exactly fourteen relations.
- **Minus:** all ten coordinates remain, but the project imposes only fourteen of the twenty relations.

These counts were recomputed exactly.

---

## 3. A sharp rank-preserving bridge for the plus block

Identify
\[
T=i[u]_\times,\qquad C=V,
\]
and write a plus-block moment matrix as
\[
Y=\begin{pmatrix}A&B\\B^T&D\end{pmatrix}\succeq0
\]
in \((u,v)\) order. Assume its fourteen project moment relations vanish. Define
\[
a=(A_{11},A_{22},A_{33},A_{12},A_{13},A_{23})^T.
\]

### Exact completion theorem

A full PSD Hankel completion adding the \(\beta^2\) row and column exists **if and only if**
\[
\boxed{a\in\operatorname{range}D.}
\]

When it exists, it can preserve rank exactly.

**Necessity.** The new \((z,v)\) principal block must be
\[
\begin{pmatrix}t&a^T\\a&D\end{pmatrix}\succeq0,
\]
which forces \(a\in\operatorname{range}D\).

**Sufficiency.** Set \(k=D^\dagger a\). Then
\[
H=
\begin{pmatrix}
a^Tk &(Bk)^T&a^T\\
Bk&A&B\\
a&B^T&D
\end{pmatrix}.
\]
The new row is a linear combination, with coefficients \(k\), of the old \(v\)-rows. Therefore
\[
H\succeq0,\qquad \operatorname{rank}H=\operatorname{rank}Y.
\]
The fourteen old relations and six new \(uu=zv\) relations make \(H\) full Hankel.

Consequently:

> **A plus-block PSD matrix of rank at most five, annihilating all fourteen directions and satisfying this range test, decomposes positively into projected Veronese atoms.**

This is a concrete conditional bridge, with no unsupported range assertion.

### Exact examples

- Two evaluations at
  \[
  (\beta,p)=(1,1,0,0),\qquad(2,0,1,0)
  \]
  give \(\operatorname{rank}H=\operatorname{rank}Y=2\). Here
  \[
  a=(1,4,0,0,0,0),\quad Bk=(1,8,0),\quad t=17.
  \]
  The displayed completion formula reproduces their full moment matrix exactly.

- Conversely,
  \[
  Y=\operatorname{diag}(I_3,0_6)
  \]
  has rank three and satisfies all fourteen relations, but \(D=0\) and
  \(a=(1,1,1,0,0,0)\ne0\). **No PSD full-Hankel completion exists, of any rank.**

Shorting is legitimate:
\[
S=A-BD^\dagger B^T\succeq0.
\]
Subtracting this pure-\(T\) part leaves a PSD residual of rank \(\operatorname{rank}D\). But the residual still requires the explicit test
\[
\operatorname{vech}(BD^\dagger B^T)\in\operatorname{range}D.
\]
I have not assumed that condition holds automatically.

---


## 5. Rank-one classification: the sketch is correct with the stated distinction

The following classification requires **all fourteen quadratic evaluations to vanish**, not just the eight gauges.

### Plus

Here \(T=i[u]_\times\), \(C\) is real symmetric, and \(d=0\). The equations give:

- \(C=0\), with arbitrary \(u\); or
- \(C=\lambda pp^T\ne0\), with \(u=\beta p\).

Indeed, \(\operatorname{adj}C=0\) forces \(\operatorname{rank}C\le1\), and \(TC=0\) forces \(u\parallel p\).

These are exactly the real points of the inner-projected Veronese closure. They are actual projective Cayley limits: use
\[
q(i r[u]_\times)
=(i r[u]_\times,-r^2uu^T,0),
\]
with suitable scaling; the pure-\(T\) and pure-\(C\) cases arise at zero and infinity.

### Minus

If \(d\ne0\), then
\[
T=\frac{\operatorname{adj}C}{d}.
\]
After projectively normalizing \(d=1\),
\[
(T,C,d)=(-pp^T,i[p]_\times,1).
\]

If \(d=0\), then
\[
\operatorname{adj}(i[u]_\times)=-uu^T=0,
\]
so \(C=0\), while real-symmetric \(T\) is arbitrary.

Thus the zero set is the Veronese component
\[
(-pp^T,\ i\beta[p]_\times,\ \beta^2)
\]
**together with** the exceptional linear space \(C=d=0\).

The proposed inverse-Cayley limit works. With \(C_0=C/d\) and
\(X_\varepsilon=(C_0+\varepsilon I)^{-1}\),
\[
[\det(C_0+\varepsilon I)q(X_\varepsilon)]
=
[\operatorname{adj}(C_0+\varepsilon I),C_0+\varepsilon I,1]
\longrightarrow[\operatorname{adj}C_0,C_0,1].
\]
Exceptional linear points follow from
\(q(\varepsilon T)/\varepsilon\to(T,0,0)\).

---


### 1. Proved larger family

Set
\[
a=(0,\tau,1,z),\qquad b=(i,-i,1+i,-1+2i),
\qquad \tau\in\left\{\tfrac13,\tfrac12,\tfrac23\right\},
\]
and
\[
K_r=\begin{pmatrix}
1&-ir\\ ir&1\\ ir&ir\\ ir&-ir
\end{pmatrix},\quad
G_r=K_r^*K_r,\quad
Y_r=K_rG_r^{-1/2},\qquad r\in\mathbb R.
\]

**Exact-certificate result.** For every \(z,\eta\in\mathbb C\) satisfying the essential supporting-base hypothesis
\[
F(I)=h=\max_\pi\Re\!\left(\eta\prod_i(a_i+b_{\pi(i)})\right),
\]
these planes satisfy
\[
\boxed{E\le g_R,\qquad R=I-2Y_rY_r^*.}
\]
Consequently,
\[
\boxed{F\!\left(I+Y_r(V-I)Y_r^*\right)\le h
       \quad\text{for every }V\in U(2).}
\]

This contains the supplied result at \(\tau=\tfrac12,\ r=1/\sqrt3\). The enlargement is genuine: at \(r=3/5\), \(P_{11}=217/451\), whereas the supplied plane has \(P_{11}=1/2\); diagonal row phases cannot remove that difference.

The recovery uses the Cayley identity and budget in [branch_B_positive_gap_budget.md](branch_B_positive_gap_budget.md), Section 1, “The full complex two-plane update.” Explicitly, put
\[
F(U)=\Re\!\left(\eta\det(\operatorname{diag}(a)+U\operatorname{diag}(b)U^*)\right),\quad
c_\pi=\Re\!\left(\eta\prod_i(a_i+b_{\pi(i)})\right),\quad
g_\pi=h-c_\pi.
\]
The supporting-base hypothesis is \(c_e=F(I)=h\), and \(g_R=h-F(R)\). For an orthonormal frame \(Y\), with rows \(y_i\), write
\[
\delta_{ij}=g_{(ij)},\qquad s_{ijk}=c_{(ijk)}-c_{(ikj)},\qquad p_{ij}=\det Y[\{i,j\},\{1,2\}],
\]
\[
\mathcal A(T)=\sum_{i<j}\delta_{ij}|y_iTy_j^*|^2,\qquad
\ell(T)=-4\sum_{i<j<k}s_{ijk}\Im\!\left(p_{ik}\overline{p_{ij}}\,y_jTy_k^*\right).
\]
If \(\mathcal A(u)=u^TMu\) and \(\ell(u)=l^Tu\) in real Hermitian coordinates, the budget is \(E=\tfrac14l^TM^+l\), together with the range condition \(l\in\operatorname{range}M\). These are exactly the conditions encoded by the Schur PSD block below. For its raw-frame coordinates choose
\[
S=\begin{pmatrix}s&x+iy\\x-iy&t\end{pmatrix},\quad
u=(s,t,x,y)^T,\quad T=G_r^{1/2}SG_r^{1/2}.
\]
Then \(Y_rTY_r^*=K_rSK_r^*\); \(M\) and \(l\) below mean the coefficient matrix and vector of \(\mathcal A(T)\) and \(\ell(T)\) in these coordinates. Raw-frame Plücker products must be divided by \(d=\det G_r\), since \(Y_r=K_rG_r^{-1/2}\). Thus the displayed \(\widehat H\) is the congruence by \(\operatorname{diag}(I_4,d)\) of \(\begin{pmatrix}M&l/2\\l^T/2&g_R\end{pmatrix}\).

#### Executed certificate

* Retained actual complex products using \(w=\eta z\) and four real coordinates \((\Re w,\Im w,\Re\eta,\Im\eta)\), as in [branch_B_positive_gap_budget.md](branch_B_positive_gap_budget.md), Section 3.A, “Retain actual complex products in four real coordinates.” The cone enumeration includes the closure in independent \((w,\eta)\); the asserted theorem concerns the actual points \(w=\eta z\).
* Completely enumerated each supporting cone using all \(\binom{23}{3}=1771\) active triples. Exact rank and strict-interior checks establish pointedness and full dimension.
* In raw-frame coordinates, write \(\mathcal A(u)=u^TMu\), \(\ell(u)=l^Tu\). With
  \[
  d=\det G_r=(3r^2-2r+1)(3r^2+2r+1)>0,
  \]
  checked the polynomial Schur block
  \[
  \widehat H(r)=
  \begin{pmatrix}
  M&dl/2\\ dl^T/2&d^2g_R
  \end{pmatrix}\succeq0
  \]
  on every cone ray. This is a congruence of the block equivalent to \(E\le g_R\).
* For full-rank rays, checked its five leading principal minors. For each of the two singular rays per cone, verified the **symbolic kernel**
  \[
  \widehat H(r)(1,1,1,0,0)^T=0
  \]
  and checked the four leading minors of the complementary principal restriction.
* Every determinant is even in \(r\). After setting \(x=r^2\) and removing its monomial factor, **exact Sturm computations show no positive roots and positive value at \(x=1\)**.

| \(\tau\) | Complete cone rays | Polynomial positivity checks |
|---|---:|---:|
| \(1/3\) | 14 | 68 |
| \(1/2\) | 14 | 68 |
| \(2/3\) | 16 | 78 |
| **Total** | **44** | **214** |

Thus positivity holds for **all \(r\ne0\)**, not just a sampled interval. Closedness of the Schur PSD condition includes \(r=0\). Linearity in the cost coordinates extends the ray certificates to **every supporting direction**.

**Reproducing the positive certificate.** The original positive-proof sources are retained in [code/research/plane_family_extension/](../../code/research/plane_family_extension/). The earlier `/tmp/moc_bridge_investigation` paths were scratch paths, not dependencies on an external archive.

From the project root, run:

```sh
python code/run.py --timeout 1800 --output build/plane_family_extension research/plane_family_extension/global_plane.py
```

The manifest runs `extend_slices.py` and `plane_interval.py` first, then `global_plane.py`, entirely inside a temporary workspace. The three programs use SymPy and Python's standard library. Their directory settings have been relocated to the staged source directory; no original absolute scratch directory is written.

- `extend_slices.py` completely enumerates the three actual cost cones and rebuilds `slice_1_2.json`, `slice_1_3.json`, and `slice_2_3.json`, including rays, exact rank and strict-interior checks.
- With no parameter, `plane_interval.py` processes all three slice values. It rebuilds the symbolic raw-frame Schur blocks, leading-minor polynomials, singular-kernel checks, and the three `plane_interval_*.json` files. Its Bernstein certificates cover only [1/2,2/3]; they are not the justification for the all-r conclusion.
- `global_plane.py` consumes those leading-minor polynomials, substitutes x=r², removes powers of x, and performs the exact global Sturm tests. It asserts that all 214 checks have no positive roots and a positive value at x=1, and rebuilds `global_plane.json`.

These intermediate and final JSON outputs are regenerable and are deliberately not stored as source inputs. `--output` exports them under the requested ignored build directory if an inspection copy is wanted. The all-r argument uses the exact leading-minor polynomials and Sturm tests, not numerical sampling or the interval-only Bernstein checks. The original hypotheses and the distinction between saved-record checking and full regeneration are unchanged; the launcher command above regenerates the complete cone → block → Sturm chain.



## 1. Projector encoding: verified, including orientation

Assume \(d_i=a_i+b_i\ne0\). Define
\[
u_i=\binom{a_i}{1},\qquad
v_i^T=(1,b_i),\qquad
P_i=\frac{u_iv_i^T}{d_i}.
\]
Since \(v_i^Tu_i=d_i\),
\[
P_i^2=P_i,\qquad \operatorname{tr}P_i=1,\qquad \operatorname{rank}P_i=1.
\]

For distinct indices,
\[
\operatorname{tr}(P_{i_1}\cdots P_{i_m})
=\frac{\prod_{r=1}^m(a_{i_{r+1}}+b_{i_r})}
       {\prod_{r=1}^m d_{i_r}},
\qquad i_{m+1}=i_1.
\]
Thus a cycle of \(\pi\) contributes the trace in **reverse cycle orientation**, as proposed.

Set
\[
\kappa=\eta\prod_i d_i,\qquad x_{ij}=\operatorname{tr}(P_iP_j).
\]
At identity support,
\[
\Delta_\pi=\operatorname{Re}\{\kappa(1-r_\pi)\}\ge0,
\]
where \(r_\pi=z_\pi/z_{\rm id}\). In particular,
\[
\Delta_{(ij)}=\operatorname{Re}\{\kappa(1-x_{ij})\},
\qquad
r_{(ij)(k\ell)}=x_{ij}x_{k\ell}.
\]

The proposed triple identities are correct:
\[
t_{ijk}+t_{ikj}=x_{ij}+x_{ik}+x_{jk}-1,
\]
\[
t_{ijk}t_{ikj}=x_{ij}x_{ik}x_{jk}.
\]
So is the cleared linkage
\[
t_{ijk}t_{ik\ell}=x_{ik}\operatorname{tr}(P_iP_jP_kP_\ell).
\]

**No positivity or Hermitian hypothesis is used here.**

---

## 2. Stronger division-free formulation: mixed Gram identities

Put
\[
Q_i=2P_i-I,\qquad
q_{ij}=\frac12\operatorname{tr}(Q_iQ_j)=2x_{ij}-1,
\]
and
\[
\omega_{ijk}=\frac12\operatorname{tr}(Q_iQ_jQ_k)
            =2(t_{ijk}-t_{ikj}).
\]
Then \(Q_i^2=I\), \(\operatorname{tr}Q_i=0\), and \(q_{ii}=1\).

Using Pauli matrices, write \(Q_i=n_i\cdot\sigma\), with \(n_i\in\mathbb C^3\). These are **complex bilinear**, not Hermitian, products:
\[
q_{ij}=n_i\cdot n_j,\qquad
\omega_{ijk}=i\det(n_i,n_j,n_k).
\]

Consequently:

1. The \(4\times4\) matrix \(q\) has rank at most three.

2. For increasing triples \(I,J\),
   \[
   \boxed{\omega_I\omega_J=-\det q_{I,J}.}
   \]
   The case \(I=J\) recovers the individual triple discriminant identity. The mixed cases link the different triple orientations.

3. There are linear compatibility identities
   \[
   q_{pi}\omega_{jk\ell}
   -q_{pj}\omega_{ik\ell}
   +q_{pk}\omega_{ij\ell}
   -q_{p\ell}\omega_{ijk}=0.
   \]

These mixed relations are preferable to treating four independent triple quadratic equations as independent sign choices.

### Four-cycle traces without division

Let
\[
r_{ijk\ell}=\operatorname{tr}(P_iP_jP_kP_\ell).
\]
Direct Pauli expansion gives
\[
\boxed{
r_{ijk\ell}+r_{i\ell kj}
=x_{ij}x_{k\ell}+x_{i\ell}x_{jk}
-x_{ik}x_{j\ell}+x_{ik}+x_{j\ell}-1,
}
\]
and
\[
\boxed{
r_{ijk\ell}-r_{i\ell kj}
=\frac14\bigl(
\omega_{ijk}+\omega_{ij\ell}
+\omega_{ik\ell}+\omega_{jk\ell}
\bigr).
}
\]

Thus all six four-cycle traces are explicitly determined by the pair traces and globally linked triple orientations, **even when some \(x_{ij}=0\)**. This avoids the apparent divisions in \(t_{ijk}t_{ik\ell}/x_{ik}\).

### Why this is an exact algebraic model

Over \(\mathbb C\), a symmetric \(q\) of rank at most three factors as \(q=N^TN\). With \(q_{ii}=1\), its columns give suitable \(n_i\). In rank three, the mixed determinant identities fix the triple volumes up to one global orientation; in lower rank, all triple volumes vanish. Choosing the orientation appropriately reconstructs \(Q_i\), hence \(P_i\).

A simultaneous generic conjugation makes every \((P_i)_{21}\ne0\). Then
\[
d_i=\frac1{(P_i)_{21}},\qquad
a_i=\frac{(P_i)_{11}}{(P_i)_{21}},\qquad
b_i=\frac{(P_i)_{22}}{(P_i)_{21}}
\]
recovers the stated spectral chart, because \(a_i+b_i=d_i\).

**Therefore the fully linked trace system is not merely a relaxation of actual projector ratios.** It gives an exact algebraic reformulation. What remains missing is an order inequality on its supporting real slice.

---


## 5. A universal analytic piece of the scalar Schur bound

The target necessary inequality is
\[
\mathcal R(v):=
g\,v^TD_0v+
2g^{3/2}\sqrt{\ell_v^TA\ell_v}
-(e^Tv)^2\ge0,
\]
as recorded in [universal_sos_mechanism_lemmas.md](universal_sos_mechanism_lemmas.md), Section 3.

Using the repository’s coordinate convention
(`organized/research/rational_sinkhorn_certificates.py:105–106`)
and canonical blocks
([COFACTOR_PLANE_BOUNDS.md](COFACTOR_PLANE_BOUNDS.md), “Statement and exact coefficient identities”),
I checked the following identities exactly across **all 70 cost directions plus the height direction**.

Let the cofactor matrix have only
\[
C_{12}=x+iy,\qquad C_{21}=x-iy
\]
nonzero. Define
\[
\delta_+=\Delta_{(1243)},\qquad
\delta_-=\Delta_{(1342)},\qquad S=\delta_++\delta_-,
\]
and let \(e_*\) denote the \(\Im C_{12}\) coefficient. Then
\[
A_{33}=g,\qquad
(D_0)_{\Re12,\Re12}=2g,\qquad
(D_0)_{\Re12,\Im12}=0,
\]
\[
(D_0)_{\Im12,\Im12}+2g=2S,\qquad
e_*=\frac{\delta_--\delta_+}{2}.
\]

Since
\[
\ell_v=\operatorname{coords}\operatorname{diag}
(0,0,-x^2-y^2),
\]
we obtain exactly
\[
\mathcal R(v)=4g^2x^2+(2gS-e_*^2)y^2.
\]

Original24 support gives \(S\ge2|e_*|\). The established universal bound \(|e_*|\le2g\) gives
\[
e_*^2\le2g|e_*|\le gS.
\]
Therefore
\[
\boxed{
\mathcal R(v)\ge4g^2x^2+gS\,y^2\ge0.
}
\]

This proves the scalar Schur bound on the **entire complex \(C_{12}\) coordinate plane**, uniformly for actual supported spectra with \(g>0\). It is not favorable-instance counting.

The inputs \(g=\frac14\sum\Delta_{\rm trans}\) and \(|e_{\Im C_{ij}}|\le2g\) are the already-established identities in [universal_sos_boundary_completion_lemmas.md](universal_sos_boundary_completion_lemmas.md), Sections 2–3.

**Limitation:** this calculation does not control mixtures of cofactor-coordinate planes or general diagonal/off-diagonal coupling.

---


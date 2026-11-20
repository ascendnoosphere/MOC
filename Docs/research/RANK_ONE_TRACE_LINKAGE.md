# Actual-spectral linkage by complex rank-one idempotents

This is an elementary exact encoding, not an unrestricted MOC proof or a positivity theorem. It gives concrete additional identities beyond arbitrary real common-minor costs and a scalar-coordinate-plane bound. See the [full report](projector_trace_schur_lemmas.md).

## 1. Projectors and the original comparison products

Assume \(d_i=a_i+b_i\ne0\). Define ordinary complex matrices
\[
 u_i=\binom{a_i}{1},\qquad v_i^T=(1,b_i),\qquad
 P_i=\frac{u_iv_i^T}{d_i}.
\]
The transpose here is **not** conjugate transpose. Since \(v_i^Tu_i=d_i\),
\[
 P_i^2=P_i,\qquad \operatorname{tr}P_i=1,\qquad \operatorname{rank}P_i=1.
\]
In general these matrices are neither Hermitian nor positive.

For an ordered cycle \((i_1,\ldots,i_r)\), rank-one multiplication gives
\[
 \operatorname{tr}(P_{i_1}\cdots P_{i_r})
 =\prod_{k=1}^r\frac{a_{i_{k+1}}+b_{i_k}}{d_{i_k}},
 \qquad i_{r+1}=i_1.
\]
Consequently, if \(z_\pi=\prod_i(a_i+b_{\pi(i)})\) and \(z_{\rm id}=\prod_i d_i\), then
\[
 \frac{z_\pi}{z_{\rm id}}
 =\prod_{(i_1\ldots i_r)\text{ a cycle of }\pi}
   \operatorname{tr}(P_{i_r}\cdots P_{i_1}).
\]
The reversal is essential: the forward trace corresponds to the inverse cycle. Fixed points contribute trace one. There are exactly the original 24 products, not independently selected cycle factors.

Set \(\kappa=\eta z_{\rm id}\) and \(x_{ij}=\operatorname{tr}(P_iP_j)=x_{ji}\). At an identity support contact,
\[
 \Delta_{(ij)}=\Re\bigl[\kappa(1-x_{ij})\bigr],
\quad
 \Delta_{(ij)(k\ell)}=\Re\bigl[\kappa(1-x_{ij}x_{k\ell})\bigr].
\]
All these gaps are nonnegative because of the **same original** comparison height. They are not separately assumed positive complex numbers.

## 2. Cleared trace identities

Write \(t_{ijk}=\operatorname{tr}(P_iP_jP_k)\). For distinct indices,
\[
 \boxed{t_{ijk}+t_{ikj}=x_{ij}+x_{ik}+x_{jk}-1,}
\]
\[
 \boxed{t_{ijk}t_{ikj}=x_{ij}x_{ik}x_{jk}.}
\]
The sum is the three-index alternating determinant identity. For the product, multiply the two rank-one trace formulas; each directed contraction occurs with its reverse, giving the three pair traces.

For four distinct indices, put \(t_{ijk\ell}=\operatorname{tr}(P_iP_jP_kP_\ell)\). Then
\[
 \boxed{t_{ijk}t_{ik\ell}=x_{ik}t_{ijk\ell}.}
\]
Keep this identity in its cleared form. Dividing by \(x_{ik}\) would improperly remove cases where a pair trace vanishes.

The sum identity recovers the gap relation used in the [completed boundary lemma](universal_sos_boundary_completion_lemmas.md):
\[
 \Delta_{(ijk)}+\Delta_{(ikj)}
 =\Delta_{(ij)}+\Delta_{(ik)}+\Delta_{(jk)}.
\]
The **product** and four-cycle identities are additional nonlinear constraints; arbitrary real common-minor costs need not have this representation.

## 3. Complex Bloch Gram constraint

Using the Pauli matrices, write
\[
 P_i=\tfrac12(I+n_i\cdot\sigma),\qquad
 n_i=(P_{i,12}+P_{i,21},\ i(P_{i,12}-P_{i,21}),\ P_{i,11}-P_{i,22}).
\]
Here \(n_i\in\mathbb C^3\) and the dot product is complex bilinear. Idempotence gives \(n_i\cdot n_i=1\), while
\[
 2x_{ij}-1=n_i\cdot n_j.
\]
Thus the symmetric matrix \(H_{ij}=2x_{ij}-1\) has diagonal one and rank at most three, in particular \(\det H=0\). This is **not** a Hermitian PSD Gram matrix: complex bilinear and Hermitian positivity must not be interchanged.

## 4. Globally linked orientations and division-free four-cycle recovery

Put \(Q_i=2P_i-I\) and
\[
 \omega_{ijk}=\tfrac12\operatorname{tr}(Q_iQ_jQ_k)
 =2(t_{ijk}-t_{ikj})=i\det(n_i,n_j,n_k).
\]
For increasing triples \(I,J\), determinant multiplicativity gives the mixed identities
\[
 \boxed{\omega_I\omega_J=-\det H_{I,J}.}
\]
In addition, contraction of the linear dependence of four vectors in dimension three gives
\[
 H_{pi}\omega_{jk\ell}-H_{pj}\omega_{ik\ell}
 +H_{pk}\omega_{ij\ell}-H_{p\ell}\omega_{ijk}=0.
\]
The mixed equations prevent treating the four triple orientations as independent square-root signs. The exact verifier checks all 16 mixed determinant identities and all four linear compatibility identities symbolically for arbitrary complex three-vectors.

Writing \(r_{ijk\ell}=\operatorname{tr}(P_iP_jP_kP_\ell)\), Pauli expansion gives
\[
 \boxed{r_{ijk\ell}+r_{i\ell kj}
 =x_{ij}x_{k\ell}+x_{i\ell}x_{jk}-x_{ik}x_{j\ell}
   +x_{ik}+x_{j\ell}-1,}
\]
\[
 \boxed{r_{ijk\ell}-r_{i\ell kj}
 =\tfrac14(\omega_{ijk}+\omega_{ij\ell}
                 +\omega_{ik\ell}+\omega_{jk\ell}).}
\]
Thus every four-cycle trace is recoverable without division by a pair trace, including when some \(x_{ij}=0\). The main verifier checks both formulas for all 24 ordered quadruples over the eight symbolic spectral variables.

